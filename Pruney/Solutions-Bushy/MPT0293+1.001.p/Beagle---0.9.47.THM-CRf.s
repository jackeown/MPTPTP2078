%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0293+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:04 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   24 (  25 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   24 (  27 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_45,negated_conjecture,(
    ~ ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_3'(A_6,B_7),A_6)
      | r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,k3_tarski(B_12))
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [C_5,A_1] :
      ( r2_hidden(C_5,k1_zfmisc_1(A_1))
      | ~ r1_tarski(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [A_19,B_20] :
      ( ~ r2_hidden('#skF_3'(A_19,B_20),B_20)
      | r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_74,plain,(
    ! [A_34,A_35] :
      ( r1_tarski(A_34,k1_zfmisc_1(A_35))
      | ~ r1_tarski('#skF_3'(A_34,k1_zfmisc_1(A_35)),A_35) ) ),
    inference(resolution,[status(thm)],[c_4,c_30])).

tff(c_153,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(A_50,k1_zfmisc_1(k3_tarski(B_51)))
      | ~ r2_hidden('#skF_3'(A_50,k1_zfmisc_1(k3_tarski(B_51))),B_51) ) ),
    inference(resolution,[status(thm)],[c_20,c_74])).

tff(c_177,plain,(
    ! [A_6] : r1_tarski(A_6,k1_zfmisc_1(k3_tarski(A_6))) ),
    inference(resolution,[status(thm)],[c_18,c_153])).

tff(c_22,plain,(
    ~ r1_tarski('#skF_4',k1_zfmisc_1(k3_tarski('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_22])).

%------------------------------------------------------------------------------
