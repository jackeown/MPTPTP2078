%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:11 EST 2020

% Result     : Theorem 5.84s
% Output     : CNFRefutation 5.84s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 100 expanded)
%              Number of leaves         :   30 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :   82 ( 116 expanded)
%              Number of equality atoms :   29 (  42 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_75,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_71,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_79,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_97,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_42,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_66,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_490,plain,(
    ! [A_85,B_86] : k2_xboole_0(k3_xboole_0(A_85,B_86),k4_xboole_0(A_85,B_86)) = A_85 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_526,plain,(
    ! [B_4,A_3] : k2_xboole_0(k3_xboole_0(B_4,A_3),k4_xboole_0(A_3,B_4)) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_490])).

tff(c_44,plain,(
    r1_tarski('#skF_3',k4_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_171,plain,(
    ! [A_55,B_56] :
      ( k3_xboole_0(A_55,B_56) = A_55
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_181,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_44,c_171])).

tff(c_4135,plain,(
    ! [B_186,A_187] : k2_xboole_0(k3_xboole_0(B_186,A_187),k4_xboole_0(A_187,B_186)) = A_187 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_490])).

tff(c_4260,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0(k4_xboole_0('#skF_4','#skF_5'),'#skF_3')) = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_4135])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    ! [A_27] : k4_xboole_0(A_27,k1_xboole_0) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_55,plain,(
    ! [A_38,B_39] : r1_tarski(k4_xboole_0(A_38,B_39),A_38) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_58,plain,(
    ! [A_27] : r1_tarski(A_27,A_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_55])).

tff(c_1530,plain,(
    ! [A_128,C_129,B_130] :
      ( r1_tarski(A_128,C_129)
      | ~ r1_tarski(k2_xboole_0(A_128,B_130),C_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1558,plain,(
    ! [A_131,B_132] : r1_tarski(A_131,k2_xboole_0(A_131,B_132)) ),
    inference(resolution,[status(thm)],[c_58,c_1530])).

tff(c_20,plain,(
    ! [A_18,C_20,B_19] :
      ( r1_tarski(A_18,C_20)
      | ~ r1_tarski(k2_xboole_0(A_18,B_19),C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3167,plain,(
    ! [A_167,B_168,B_169] : r1_tarski(A_167,k2_xboole_0(k2_xboole_0(A_167,B_168),B_169)) ),
    inference(resolution,[status(thm)],[c_1558,c_20])).

tff(c_3239,plain,(
    ! [A_167,A_1,B_168] : r1_tarski(A_167,k2_xboole_0(A_1,k2_xboole_0(A_167,B_168))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3167])).

tff(c_4968,plain,(
    ! [A_204] : r1_tarski('#skF_3',k2_xboole_0(A_204,k4_xboole_0('#skF_4','#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4260,c_3239])).

tff(c_4975,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_526,c_4968])).

tff(c_5006,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_4975])).

tff(c_5007,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_32,plain,(
    ! [A_30] : r1_xboole_0(A_30,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_5096,plain,(
    ! [A_214,B_215] :
      ( k3_xboole_0(A_214,B_215) = k1_xboole_0
      | ~ r1_xboole_0(A_214,B_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_5112,plain,(
    ! [A_30] : k3_xboole_0(A_30,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_5096])).

tff(c_5289,plain,(
    ! [A_225,B_226] : k5_xboole_0(A_225,k3_xboole_0(A_225,B_226)) = k4_xboole_0(A_225,B_226) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_5316,plain,(
    ! [A_30] : k5_xboole_0(A_30,k1_xboole_0) = k4_xboole_0(A_30,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5112,c_5289])).

tff(c_5325,plain,(
    ! [A_30] : k5_xboole_0(A_30,k1_xboole_0) = A_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_5316])).

tff(c_40,plain,(
    ! [A_34,B_35] : r1_xboole_0(k4_xboole_0(A_34,B_35),B_35) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_5009,plain,(
    ! [B_205,A_206] :
      ( r1_xboole_0(B_205,A_206)
      | ~ r1_xboole_0(A_206,B_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5014,plain,(
    ! [B_35,A_34] : r1_xboole_0(B_35,k4_xboole_0(A_34,B_35)) ),
    inference(resolution,[status(thm)],[c_40,c_5009])).

tff(c_5335,plain,(
    ! [B_228,A_229] : k3_xboole_0(B_228,k4_xboole_0(A_229,B_228)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5014,c_5096])).

tff(c_18,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_5340,plain,(
    ! [B_228,A_229] : k4_xboole_0(B_228,k4_xboole_0(A_229,B_228)) = k5_xboole_0(B_228,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5335,c_18])).

tff(c_5353,plain,(
    ! [B_228,A_229] : k4_xboole_0(B_228,k4_xboole_0(A_229,B_228)) = B_228 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5325,c_5340])).

tff(c_5182,plain,(
    ! [A_220,B_221] :
      ( k3_xboole_0(A_220,B_221) = A_220
      | ~ r1_tarski(A_220,B_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_5196,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_44,c_5182])).

tff(c_5804,plain,(
    ! [A_252,B_253] : k2_xboole_0(k3_xboole_0(A_252,B_253),k4_xboole_0(A_252,B_253)) = A_252 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_8360,plain,(
    ! [B_327,A_328] : k2_xboole_0(k3_xboole_0(B_327,A_328),k4_xboole_0(A_328,B_327)) = A_328 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_5804])).

tff(c_6231,plain,(
    ! [A_259,B_260,C_261] :
      ( r1_xboole_0(A_259,B_260)
      | ~ r1_xboole_0(A_259,k2_xboole_0(B_260,C_261)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_6269,plain,(
    ! [A_34,B_260,C_261] : r1_xboole_0(k4_xboole_0(A_34,k2_xboole_0(B_260,C_261)),B_260) ),
    inference(resolution,[status(thm)],[c_40,c_6231])).

tff(c_8517,plain,(
    ! [A_329,A_330,B_331] : r1_xboole_0(k4_xboole_0(A_329,A_330),k3_xboole_0(B_331,A_330)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8360,c_6269])).

tff(c_8620,plain,(
    ! [A_332] : r1_xboole_0(k4_xboole_0(A_332,k4_xboole_0('#skF_4','#skF_5')),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5196,c_8517])).

tff(c_8634,plain,(
    r1_xboole_0('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5353,c_8620])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( r1_xboole_0(B_8,A_7)
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8647,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_8634,c_10])).

tff(c_8652,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5007,c_8647])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:43:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.84/2.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.84/2.25  
% 5.84/2.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.84/2.25  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 5.84/2.25  
% 5.84/2.25  %Foreground sorts:
% 5.84/2.25  
% 5.84/2.25  
% 5.84/2.25  %Background operators:
% 5.84/2.25  
% 5.84/2.25  
% 5.84/2.25  %Foreground operators:
% 5.84/2.25  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.84/2.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.84/2.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.84/2.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.84/2.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.84/2.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.84/2.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.84/2.25  tff('#skF_5', type, '#skF_5': $i).
% 5.84/2.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.84/2.25  tff('#skF_3', type, '#skF_3': $i).
% 5.84/2.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.84/2.25  tff('#skF_4', type, '#skF_4': $i).
% 5.84/2.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.84/2.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.84/2.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.84/2.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.84/2.25  
% 5.84/2.27  tff(f_104, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 5.84/2.27  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.84/2.27  tff(f_77, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 5.84/2.27  tff(f_69, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.84/2.27  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.84/2.27  tff(f_75, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 5.84/2.27  tff(f_71, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.84/2.27  tff(f_65, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 5.84/2.27  tff(f_79, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.84/2.27  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.84/2.27  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.84/2.27  tff(f_97, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 5.84/2.27  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 5.84/2.27  tff(f_95, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 5.84/2.27  tff(c_42, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.84/2.27  tff(c_66, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_42])).
% 5.84/2.27  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.84/2.27  tff(c_490, plain, (![A_85, B_86]: (k2_xboole_0(k3_xboole_0(A_85, B_86), k4_xboole_0(A_85, B_86))=A_85)), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.84/2.27  tff(c_526, plain, (![B_4, A_3]: (k2_xboole_0(k3_xboole_0(B_4, A_3), k4_xboole_0(A_3, B_4))=A_3)), inference(superposition, [status(thm), theory('equality')], [c_4, c_490])).
% 5.84/2.27  tff(c_44, plain, (r1_tarski('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.84/2.27  tff(c_171, plain, (![A_55, B_56]: (k3_xboole_0(A_55, B_56)=A_55 | ~r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.84/2.27  tff(c_181, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))='#skF_3'), inference(resolution, [status(thm)], [c_44, c_171])).
% 5.84/2.27  tff(c_4135, plain, (![B_186, A_187]: (k2_xboole_0(k3_xboole_0(B_186, A_187), k4_xboole_0(A_187, B_186))=A_187)), inference(superposition, [status(thm), theory('equality')], [c_4, c_490])).
% 5.84/2.27  tff(c_4260, plain, (k2_xboole_0('#skF_3', k4_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), '#skF_3'))=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_181, c_4135])).
% 5.84/2.27  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.84/2.27  tff(c_28, plain, (![A_27]: (k4_xboole_0(A_27, k1_xboole_0)=A_27)), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.84/2.27  tff(c_55, plain, (![A_38, B_39]: (r1_tarski(k4_xboole_0(A_38, B_39), A_38))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.84/2.27  tff(c_58, plain, (![A_27]: (r1_tarski(A_27, A_27))), inference(superposition, [status(thm), theory('equality')], [c_28, c_55])).
% 5.84/2.27  tff(c_1530, plain, (![A_128, C_129, B_130]: (r1_tarski(A_128, C_129) | ~r1_tarski(k2_xboole_0(A_128, B_130), C_129))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.84/2.27  tff(c_1558, plain, (![A_131, B_132]: (r1_tarski(A_131, k2_xboole_0(A_131, B_132)))), inference(resolution, [status(thm)], [c_58, c_1530])).
% 5.84/2.27  tff(c_20, plain, (![A_18, C_20, B_19]: (r1_tarski(A_18, C_20) | ~r1_tarski(k2_xboole_0(A_18, B_19), C_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.84/2.27  tff(c_3167, plain, (![A_167, B_168, B_169]: (r1_tarski(A_167, k2_xboole_0(k2_xboole_0(A_167, B_168), B_169)))), inference(resolution, [status(thm)], [c_1558, c_20])).
% 5.84/2.27  tff(c_3239, plain, (![A_167, A_1, B_168]: (r1_tarski(A_167, k2_xboole_0(A_1, k2_xboole_0(A_167, B_168))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3167])).
% 5.84/2.27  tff(c_4968, plain, (![A_204]: (r1_tarski('#skF_3', k2_xboole_0(A_204, k4_xboole_0('#skF_4', '#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_4260, c_3239])).
% 5.84/2.27  tff(c_4975, plain, (r1_tarski('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_526, c_4968])).
% 5.84/2.27  tff(c_5006, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_4975])).
% 5.84/2.27  tff(c_5007, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_42])).
% 5.84/2.27  tff(c_32, plain, (![A_30]: (r1_xboole_0(A_30, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.84/2.27  tff(c_5096, plain, (![A_214, B_215]: (k3_xboole_0(A_214, B_215)=k1_xboole_0 | ~r1_xboole_0(A_214, B_215))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.84/2.27  tff(c_5112, plain, (![A_30]: (k3_xboole_0(A_30, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_5096])).
% 5.84/2.27  tff(c_5289, plain, (![A_225, B_226]: (k5_xboole_0(A_225, k3_xboole_0(A_225, B_226))=k4_xboole_0(A_225, B_226))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.84/2.27  tff(c_5316, plain, (![A_30]: (k5_xboole_0(A_30, k1_xboole_0)=k4_xboole_0(A_30, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_5112, c_5289])).
% 5.84/2.27  tff(c_5325, plain, (![A_30]: (k5_xboole_0(A_30, k1_xboole_0)=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_5316])).
% 5.84/2.27  tff(c_40, plain, (![A_34, B_35]: (r1_xboole_0(k4_xboole_0(A_34, B_35), B_35))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.84/2.27  tff(c_5009, plain, (![B_205, A_206]: (r1_xboole_0(B_205, A_206) | ~r1_xboole_0(A_206, B_205))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.84/2.27  tff(c_5014, plain, (![B_35, A_34]: (r1_xboole_0(B_35, k4_xboole_0(A_34, B_35)))), inference(resolution, [status(thm)], [c_40, c_5009])).
% 5.84/2.27  tff(c_5335, plain, (![B_228, A_229]: (k3_xboole_0(B_228, k4_xboole_0(A_229, B_228))=k1_xboole_0)), inference(resolution, [status(thm)], [c_5014, c_5096])).
% 5.84/2.27  tff(c_18, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.84/2.27  tff(c_5340, plain, (![B_228, A_229]: (k4_xboole_0(B_228, k4_xboole_0(A_229, B_228))=k5_xboole_0(B_228, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_5335, c_18])).
% 5.84/2.27  tff(c_5353, plain, (![B_228, A_229]: (k4_xboole_0(B_228, k4_xboole_0(A_229, B_228))=B_228)), inference(demodulation, [status(thm), theory('equality')], [c_5325, c_5340])).
% 5.84/2.27  tff(c_5182, plain, (![A_220, B_221]: (k3_xboole_0(A_220, B_221)=A_220 | ~r1_tarski(A_220, B_221))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.84/2.27  tff(c_5196, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))='#skF_3'), inference(resolution, [status(thm)], [c_44, c_5182])).
% 5.84/2.27  tff(c_5804, plain, (![A_252, B_253]: (k2_xboole_0(k3_xboole_0(A_252, B_253), k4_xboole_0(A_252, B_253))=A_252)), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.84/2.27  tff(c_8360, plain, (![B_327, A_328]: (k2_xboole_0(k3_xboole_0(B_327, A_328), k4_xboole_0(A_328, B_327))=A_328)), inference(superposition, [status(thm), theory('equality')], [c_4, c_5804])).
% 5.84/2.27  tff(c_6231, plain, (![A_259, B_260, C_261]: (r1_xboole_0(A_259, B_260) | ~r1_xboole_0(A_259, k2_xboole_0(B_260, C_261)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.84/2.27  tff(c_6269, plain, (![A_34, B_260, C_261]: (r1_xboole_0(k4_xboole_0(A_34, k2_xboole_0(B_260, C_261)), B_260))), inference(resolution, [status(thm)], [c_40, c_6231])).
% 5.84/2.27  tff(c_8517, plain, (![A_329, A_330, B_331]: (r1_xboole_0(k4_xboole_0(A_329, A_330), k3_xboole_0(B_331, A_330)))), inference(superposition, [status(thm), theory('equality')], [c_8360, c_6269])).
% 5.84/2.27  tff(c_8620, plain, (![A_332]: (r1_xboole_0(k4_xboole_0(A_332, k4_xboole_0('#skF_4', '#skF_5')), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5196, c_8517])).
% 5.84/2.27  tff(c_8634, plain, (r1_xboole_0('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5353, c_8620])).
% 5.84/2.27  tff(c_10, plain, (![B_8, A_7]: (r1_xboole_0(B_8, A_7) | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.84/2.27  tff(c_8647, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_8634, c_10])).
% 5.84/2.27  tff(c_8652, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5007, c_8647])).
% 5.84/2.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.84/2.27  
% 5.84/2.27  Inference rules
% 5.84/2.27  ----------------------
% 5.84/2.27  #Ref     : 0
% 5.84/2.27  #Sup     : 2166
% 5.84/2.27  #Fact    : 0
% 5.84/2.27  #Define  : 0
% 5.84/2.27  #Split   : 5
% 5.84/2.27  #Chain   : 0
% 5.84/2.27  #Close   : 0
% 5.84/2.27  
% 5.84/2.27  Ordering : KBO
% 5.84/2.27  
% 5.84/2.27  Simplification rules
% 5.84/2.27  ----------------------
% 5.84/2.27  #Subsume      : 57
% 5.84/2.27  #Demod        : 1536
% 5.84/2.27  #Tautology    : 1608
% 5.84/2.27  #SimpNegUnit  : 18
% 5.84/2.27  #BackRed      : 19
% 5.84/2.27  
% 5.84/2.27  #Partial instantiations: 0
% 5.84/2.27  #Strategies tried      : 1
% 5.84/2.27  
% 5.84/2.27  Timing (in seconds)
% 5.84/2.27  ----------------------
% 5.84/2.27  Preprocessing        : 0.31
% 5.84/2.27  Parsing              : 0.17
% 5.84/2.27  CNF conversion       : 0.02
% 5.84/2.27  Main loop            : 1.08
% 5.84/2.27  Inferencing          : 0.34
% 5.84/2.27  Reduction            : 0.45
% 5.84/2.27  Demodulation         : 0.36
% 5.84/2.27  BG Simplification    : 0.03
% 5.84/2.27  Subsumption          : 0.18
% 5.84/2.27  Abstraction          : 0.04
% 5.84/2.27  MUC search           : 0.00
% 5.84/2.27  Cooper               : 0.00
% 5.84/2.27  Total                : 1.42
% 5.84/2.27  Index Insertion      : 0.00
% 5.84/2.27  Index Deletion       : 0.00
% 5.84/2.27  Index Matching       : 0.00
% 5.84/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
