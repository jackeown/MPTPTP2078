%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0731+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:46 EST 2020

% Result     : Theorem 1.50s
% Output     : CNFRefutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   15 (  20 expanded)
%              Number of leaves         :    9 (  11 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  16 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > #nlpp > k1_ordinal1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_35,negated_conjecture,(
    ~ ! [A] : A != k1_ordinal1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).

tff(f_31,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_6,plain,(
    k1_ordinal1('#skF_1') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_11,plain,(
    ! [A_4] : r2_hidden(A_4,k1_ordinal1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    r2_hidden('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_11])).

tff(c_15,plain,(
    ! [B_5,A_6] :
      ( ~ r2_hidden(B_5,A_6)
      | ~ r2_hidden(A_6,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_17,plain,(
    ~ r2_hidden('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_15])).

tff(c_23,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_17])).

%------------------------------------------------------------------------------
