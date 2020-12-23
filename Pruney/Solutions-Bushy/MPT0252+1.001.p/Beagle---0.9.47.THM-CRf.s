%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0252+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:59 EST 2020

% Result     : Theorem 1.36s
% Output     : CNFRefutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   28 (  29 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   28 (  30 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_8

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_44,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [D_6,B_2] : r2_hidden(D_6,k2_tarski(D_6,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_46,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_30,plain,(
    ! [D_17,A_12,B_13] :
      ( ~ r2_hidden(D_17,A_12)
      | r2_hidden(D_17,k2_xboole_0(A_12,B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_69,plain,(
    ! [C_33,B_34,A_35] :
      ( r2_hidden(C_33,B_34)
      | ~ r2_hidden(C_33,A_35)
      | ~ r1_tarski(A_35,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_129,plain,(
    ! [D_48,B_49,A_50,B_51] :
      ( r2_hidden(D_48,B_49)
      | ~ r1_tarski(k2_xboole_0(A_50,B_51),B_49)
      | ~ r2_hidden(D_48,A_50) ) ),
    inference(resolution,[status(thm)],[c_30,c_69])).

tff(c_148,plain,(
    ! [D_55] :
      ( r2_hidden(D_55,'#skF_8')
      | ~ r2_hidden(D_55,k2_tarski('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_46,c_129])).

tff(c_160,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_6,c_148])).

tff(c_166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_160])).

%------------------------------------------------------------------------------
