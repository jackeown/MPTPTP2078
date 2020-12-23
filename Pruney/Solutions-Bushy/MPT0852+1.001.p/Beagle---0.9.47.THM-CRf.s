%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0852+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:57 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   27 (  32 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   23 (  31 expanded)
%              Number of equality atoms :   22 (  30 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_mcart_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ! [B] :
          ( B = k2_mcart_1(A)
        <=> ! [C,D] :
              ( A = k4_tarski(C,D)
             => B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_mcart_1)).

tff(f_35,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ! [B] :
          ( B = k1_mcart_1(A)
        <=> ! [C,D] :
              ( A = k4_tarski(C,D)
             => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_mcart_1)).

tff(c_16,plain,(
    k4_tarski('#skF_6','#skF_7') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ! [C_41,D_42,B_34,C_35] :
      ( k2_mcart_1(k4_tarski(C_41,D_42)) = D_42
      | k4_tarski(C_41,D_42) != k4_tarski(B_34,C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_70,plain,(
    ! [B_63,C_64] : k2_mcart_1(k4_tarski(B_63,C_64)) = C_64 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_8])).

tff(c_79,plain,(
    k2_mcart_1('#skF_5') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_70])).

tff(c_2,plain,(
    ! [C_20,D_21,B_13,C_14] :
      ( k1_mcart_1(k4_tarski(C_20,D_21)) = C_20
      | k4_tarski(C_20,D_21) != k4_tarski(B_13,C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    ! [B_49,C_50] : k1_mcart_1(k4_tarski(B_49,C_50)) = B_49 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2])).

tff(c_39,plain,(
    k1_mcart_1('#skF_5') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_30])).

tff(c_14,plain,(
    k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_42,plain,(
    k4_tarski('#skF_6',k2_mcart_1('#skF_5')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_14])).

tff(c_83,plain,(
    k4_tarski('#skF_6','#skF_7') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_42])).

tff(c_86,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_83])).

%------------------------------------------------------------------------------
