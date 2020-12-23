%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0216+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:55 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   22 (  27 expanded)
%              Number of leaves         :   11 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   19 (  28 expanded)
%              Number of equality atoms :   18 (  27 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_35,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k1_tarski(A) = k2_tarski(B,C)
       => B = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_zfmisc_1)).

tff(f_30,axiom,(
    ! [A,B,C] :
      ( k1_tarski(A) = k2_tarski(B,C)
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_zfmisc_1)).

tff(f_26,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(c_8,plain,(
    k2_tarski('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_63,plain,(
    ! [B_8,A_9,C_10] :
      ( B_8 = A_9
      | k2_tarski(B_8,C_10) != k1_tarski(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_75,plain,(
    ! [A_9] :
      ( A_9 = '#skF_2'
      | k1_tarski(A_9) != k1_tarski('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_63])).

tff(c_80,plain,(
    '#skF_2' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_75])).

tff(c_6,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_85,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_6])).

tff(c_13,plain,(
    ! [B_6,A_7] : k2_tarski(B_6,A_7) = k2_tarski(A_7,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_28,plain,(
    k2_tarski('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_13,c_8])).

tff(c_66,plain,(
    ! [A_9] :
      ( A_9 = '#skF_3'
      | k1_tarski(A_9) != k1_tarski('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_63])).

tff(c_122,plain,(
    '#skF_3' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_66])).

tff(c_124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_122])).

%------------------------------------------------------------------------------
