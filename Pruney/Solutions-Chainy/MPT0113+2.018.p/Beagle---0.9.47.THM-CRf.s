%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:13 EST 2020

% Result     : Theorem 6.63s
% Output     : CNFRefutation 6.63s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 137 expanded)
%              Number of leaves         :   28 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :   92 ( 171 expanded)
%              Number of equality atoms :   42 (  71 expanded)
%              Maximal formula depth    :    8 (   3 average)
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

tff(f_55,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_75,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_71,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_228,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(A_51,B_52)
      | k4_xboole_0(A_51,B_52) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_36,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_66,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_232,plain,(
    k4_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_228,c_66])).

tff(c_117,plain,(
    ! [A_43,B_44] : k3_xboole_0(A_43,k2_xboole_0(A_43,B_44)) = A_43 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_20,plain,(
    ! [A_18,B_19] : r1_tarski(k3_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_126,plain,(
    ! [A_43] : r1_tarski(A_43,A_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_20])).

tff(c_315,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(A_60,B_61) = A_60
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_337,plain,(
    ! [A_43] : k3_xboole_0(A_43,A_43) = A_43 ),
    inference(resolution,[status(thm)],[c_126,c_315])).

tff(c_32,plain,(
    ! [A_31] : k5_xboole_0(A_31,A_31) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_387,plain,(
    ! [A_63,B_64] : r1_xboole_0(k3_xboole_0(A_63,B_64),k5_xboole_0(A_63,B_64)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_417,plain,(
    ! [A_31] : r1_xboole_0(k3_xboole_0(A_31,A_31),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_387])).

tff(c_419,plain,(
    ! [A_31] : r1_xboole_0(A_31,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_417])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_773,plain,(
    ! [A_82,B_83,C_84] :
      ( ~ r1_xboole_0(A_82,B_83)
      | ~ r2_hidden(C_84,k3_xboole_0(A_82,B_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_809,plain,(
    ! [A_88,B_89] :
      ( ~ r1_xboole_0(A_88,B_89)
      | k3_xboole_0(A_88,B_89) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_773])).

tff(c_833,plain,(
    ! [A_31] : k3_xboole_0(A_31,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_419,c_809])).

tff(c_22,plain,(
    ! [A_20,B_21] : k3_xboole_0(A_20,k2_xboole_0(A_20,B_21)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_916,plain,(
    ! [A_92,B_93,C_94] : k4_xboole_0(k3_xboole_0(A_92,B_93),C_94) = k3_xboole_0(A_92,k4_xboole_0(B_93,C_94)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6921,plain,(
    ! [A_187,B_188,C_189] : k3_xboole_0(A_187,k4_xboole_0(k2_xboole_0(A_187,B_188),C_189)) = k4_xboole_0(A_187,C_189) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_916])).

tff(c_236,plain,(
    ! [A_53,B_54] :
      ( k4_xboole_0(A_53,B_54) = k1_xboole_0
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_259,plain,(
    ! [A_18,B_19] : k4_xboole_0(k3_xboole_0(A_18,B_19),A_18) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_236])).

tff(c_7187,plain,(
    ! [A_192,C_193] : k4_xboole_0(k4_xboole_0(A_192,C_193),A_192) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6921,c_259])).

tff(c_38,plain,(
    r1_tarski('#skF_3',k4_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_340,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_315])).

tff(c_959,plain,(
    ! [C_94] : k3_xboole_0('#skF_3',k4_xboole_0(k4_xboole_0('#skF_4','#skF_5'),C_94)) = k4_xboole_0('#skF_3',C_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_340,c_916])).

tff(c_7231,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_7187,c_959])).

tff(c_7310,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_7231])).

tff(c_7312,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_232,c_7310])).

tff(c_7313,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_7314,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_7476,plain,(
    ! [A_205,B_206] :
      ( k3_xboole_0(A_205,B_206) = A_205
      | ~ r1_tarski(A_205,B_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_7494,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_7314,c_7476])).

tff(c_8817,plain,(
    ! [A_258,B_259,C_260] : k4_xboole_0(k3_xboole_0(A_258,B_259),C_260) = k3_xboole_0(A_258,k4_xboole_0(B_259,C_260)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_10110,plain,(
    ! [C_287] : k3_xboole_0('#skF_3',k4_xboole_0('#skF_4',C_287)) = k4_xboole_0('#skF_3',C_287) ),
    inference(superposition,[status(thm),theory(equality)],[c_7494,c_8817])).

tff(c_7496,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_7476])).

tff(c_10147,plain,(
    k4_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_10110,c_7496])).

tff(c_28,plain,(
    ! [A_27] : k5_xboole_0(A_27,k1_xboole_0) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_7658,plain,(
    ! [A_218,B_219] :
      ( k4_xboole_0(A_218,B_219) = k1_xboole_0
      | ~ r1_tarski(A_218,B_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_7685,plain,(
    ! [A_18,B_19] : k4_xboole_0(k3_xboole_0(A_18,B_19),A_18) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_7658])).

tff(c_9501,plain,(
    ! [C_274,B_275] : k3_xboole_0(C_274,k4_xboole_0(B_275,C_274)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8817,c_7685])).

tff(c_18,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_9537,plain,(
    ! [C_274,B_275] : k4_xboole_0(C_274,k4_xboole_0(B_275,C_274)) = k5_xboole_0(C_274,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_9501,c_18])).

tff(c_9655,plain,(
    ! [C_278,B_279] : k4_xboole_0(C_278,k4_xboole_0(B_279,C_278)) = C_278 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_9537])).

tff(c_7412,plain,(
    ! [A_201,B_202] : k3_xboole_0(A_201,k2_xboole_0(A_201,B_202)) = A_201 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_7421,plain,(
    ! [A_201] : r1_tarski(A_201,A_201) ),
    inference(superposition,[status(thm),theory(equality)],[c_7412,c_20])).

tff(c_7492,plain,(
    ! [A_201] : k3_xboole_0(A_201,A_201) = A_201 ),
    inference(resolution,[status(thm)],[c_7421,c_7476])).

tff(c_7552,plain,(
    ! [A_208,B_209] : r1_xboole_0(k3_xboole_0(A_208,B_209),k5_xboole_0(A_208,B_209)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_7585,plain,(
    ! [A_31] : r1_xboole_0(k3_xboole_0(A_31,A_31),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_7552])).

tff(c_7588,plain,(
    ! [A_31] : r1_xboole_0(A_31,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7492,c_7585])).

tff(c_7863,plain,(
    ! [A_230,B_231,C_232] :
      ( ~ r1_xboole_0(A_230,B_231)
      | ~ r2_hidden(C_232,k3_xboole_0(A_230,B_231)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8251,plain,(
    ! [A_244,C_245] :
      ( ~ r1_xboole_0(A_244,A_244)
      | ~ r2_hidden(C_245,A_244) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7492,c_7863])).

tff(c_8255,plain,(
    ! [C_245] : ~ r2_hidden(C_245,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_7588,c_8251])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),k3_xboole_0(A_5,B_6))
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_9519,plain,(
    ! [C_274,B_275] :
      ( r2_hidden('#skF_1'(C_274,k4_xboole_0(B_275,C_274)),k1_xboole_0)
      | r1_xboole_0(C_274,k4_xboole_0(B_275,C_274)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9501,c_6])).

tff(c_9591,plain,(
    ! [C_274,B_275] : r1_xboole_0(C_274,k4_xboole_0(B_275,C_274)) ),
    inference(negUnitSimplification,[status(thm)],[c_8255,c_9519])).

tff(c_9664,plain,(
    ! [B_279,C_278] : r1_xboole_0(k4_xboole_0(B_279,C_278),C_278) ),
    inference(superposition,[status(thm),theory(equality)],[c_9655,c_9591])).

tff(c_10203,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_10147,c_9664])).

tff(c_10224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7313,c_10203])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:46:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.63/2.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.63/2.47  
% 6.63/2.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.63/2.47  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 6.63/2.47  
% 6.63/2.47  %Foreground sorts:
% 6.63/2.47  
% 6.63/2.47  
% 6.63/2.47  %Background operators:
% 6.63/2.47  
% 6.63/2.47  
% 6.63/2.47  %Foreground operators:
% 6.63/2.47  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.63/2.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.63/2.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.63/2.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.63/2.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.63/2.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.63/2.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.63/2.47  tff('#skF_5', type, '#skF_5': $i).
% 6.63/2.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.63/2.47  tff('#skF_3', type, '#skF_3': $i).
% 6.63/2.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.63/2.47  tff('#skF_4', type, '#skF_4': $i).
% 6.63/2.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.63/2.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.63/2.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.63/2.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.63/2.47  
% 6.63/2.48  tff(f_55, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.63/2.48  tff(f_84, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 6.63/2.48  tff(f_63, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 6.63/2.48  tff(f_61, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 6.63/2.48  tff(f_67, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.63/2.48  tff(f_75, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.63/2.48  tff(f_57, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 6.63/2.48  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 6.63/2.48  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.63/2.48  tff(f_69, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 6.63/2.48  tff(f_71, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 6.63/2.48  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.63/2.48  tff(c_228, plain, (![A_51, B_52]: (r1_tarski(A_51, B_52) | k4_xboole_0(A_51, B_52)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.63/2.48  tff(c_36, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.63/2.48  tff(c_66, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_36])).
% 6.63/2.48  tff(c_232, plain, (k4_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_228, c_66])).
% 6.63/2.48  tff(c_117, plain, (![A_43, B_44]: (k3_xboole_0(A_43, k2_xboole_0(A_43, B_44))=A_43)), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.63/2.48  tff(c_20, plain, (![A_18, B_19]: (r1_tarski(k3_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.63/2.48  tff(c_126, plain, (![A_43]: (r1_tarski(A_43, A_43))), inference(superposition, [status(thm), theory('equality')], [c_117, c_20])).
% 6.63/2.48  tff(c_315, plain, (![A_60, B_61]: (k3_xboole_0(A_60, B_61)=A_60 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.63/2.48  tff(c_337, plain, (![A_43]: (k3_xboole_0(A_43, A_43)=A_43)), inference(resolution, [status(thm)], [c_126, c_315])).
% 6.63/2.48  tff(c_32, plain, (![A_31]: (k5_xboole_0(A_31, A_31)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.63/2.48  tff(c_387, plain, (![A_63, B_64]: (r1_xboole_0(k3_xboole_0(A_63, B_64), k5_xboole_0(A_63, B_64)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.63/2.48  tff(c_417, plain, (![A_31]: (r1_xboole_0(k3_xboole_0(A_31, A_31), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_387])).
% 6.63/2.48  tff(c_419, plain, (![A_31]: (r1_xboole_0(A_31, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_337, c_417])).
% 6.63/2.48  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.63/2.48  tff(c_773, plain, (![A_82, B_83, C_84]: (~r1_xboole_0(A_82, B_83) | ~r2_hidden(C_84, k3_xboole_0(A_82, B_83)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.63/2.48  tff(c_809, plain, (![A_88, B_89]: (~r1_xboole_0(A_88, B_89) | k3_xboole_0(A_88, B_89)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_773])).
% 6.63/2.48  tff(c_833, plain, (![A_31]: (k3_xboole_0(A_31, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_419, c_809])).
% 6.63/2.48  tff(c_22, plain, (![A_20, B_21]: (k3_xboole_0(A_20, k2_xboole_0(A_20, B_21))=A_20)), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.63/2.48  tff(c_916, plain, (![A_92, B_93, C_94]: (k4_xboole_0(k3_xboole_0(A_92, B_93), C_94)=k3_xboole_0(A_92, k4_xboole_0(B_93, C_94)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.63/2.48  tff(c_6921, plain, (![A_187, B_188, C_189]: (k3_xboole_0(A_187, k4_xboole_0(k2_xboole_0(A_187, B_188), C_189))=k4_xboole_0(A_187, C_189))), inference(superposition, [status(thm), theory('equality')], [c_22, c_916])).
% 6.63/2.48  tff(c_236, plain, (![A_53, B_54]: (k4_xboole_0(A_53, B_54)=k1_xboole_0 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.63/2.48  tff(c_259, plain, (![A_18, B_19]: (k4_xboole_0(k3_xboole_0(A_18, B_19), A_18)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_236])).
% 6.63/2.48  tff(c_7187, plain, (![A_192, C_193]: (k4_xboole_0(k4_xboole_0(A_192, C_193), A_192)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6921, c_259])).
% 6.63/2.48  tff(c_38, plain, (r1_tarski('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.63/2.48  tff(c_340, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))='#skF_3'), inference(resolution, [status(thm)], [c_38, c_315])).
% 6.63/2.48  tff(c_959, plain, (![C_94]: (k3_xboole_0('#skF_3', k4_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), C_94))=k4_xboole_0('#skF_3', C_94))), inference(superposition, [status(thm), theory('equality')], [c_340, c_916])).
% 6.63/2.48  tff(c_7231, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7187, c_959])).
% 6.63/2.48  tff(c_7310, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_833, c_7231])).
% 6.63/2.48  tff(c_7312, plain, $false, inference(negUnitSimplification, [status(thm)], [c_232, c_7310])).
% 6.63/2.48  tff(c_7313, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_36])).
% 6.63/2.48  tff(c_7314, plain, (r1_tarski('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_36])).
% 6.63/2.48  tff(c_7476, plain, (![A_205, B_206]: (k3_xboole_0(A_205, B_206)=A_205 | ~r1_tarski(A_205, B_206))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.63/2.48  tff(c_7494, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_7314, c_7476])).
% 6.63/2.48  tff(c_8817, plain, (![A_258, B_259, C_260]: (k4_xboole_0(k3_xboole_0(A_258, B_259), C_260)=k3_xboole_0(A_258, k4_xboole_0(B_259, C_260)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.63/2.48  tff(c_10110, plain, (![C_287]: (k3_xboole_0('#skF_3', k4_xboole_0('#skF_4', C_287))=k4_xboole_0('#skF_3', C_287))), inference(superposition, [status(thm), theory('equality')], [c_7494, c_8817])).
% 6.63/2.48  tff(c_7496, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))='#skF_3'), inference(resolution, [status(thm)], [c_38, c_7476])).
% 6.63/2.48  tff(c_10147, plain, (k4_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_10110, c_7496])).
% 6.63/2.48  tff(c_28, plain, (![A_27]: (k5_xboole_0(A_27, k1_xboole_0)=A_27)), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.63/2.48  tff(c_7658, plain, (![A_218, B_219]: (k4_xboole_0(A_218, B_219)=k1_xboole_0 | ~r1_tarski(A_218, B_219))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.63/2.48  tff(c_7685, plain, (![A_18, B_19]: (k4_xboole_0(k3_xboole_0(A_18, B_19), A_18)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_7658])).
% 6.63/2.48  tff(c_9501, plain, (![C_274, B_275]: (k3_xboole_0(C_274, k4_xboole_0(B_275, C_274))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8817, c_7685])).
% 6.63/2.48  tff(c_18, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.63/2.48  tff(c_9537, plain, (![C_274, B_275]: (k4_xboole_0(C_274, k4_xboole_0(B_275, C_274))=k5_xboole_0(C_274, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_9501, c_18])).
% 6.63/2.48  tff(c_9655, plain, (![C_278, B_279]: (k4_xboole_0(C_278, k4_xboole_0(B_279, C_278))=C_278)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_9537])).
% 6.63/2.48  tff(c_7412, plain, (![A_201, B_202]: (k3_xboole_0(A_201, k2_xboole_0(A_201, B_202))=A_201)), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.63/2.48  tff(c_7421, plain, (![A_201]: (r1_tarski(A_201, A_201))), inference(superposition, [status(thm), theory('equality')], [c_7412, c_20])).
% 6.63/2.48  tff(c_7492, plain, (![A_201]: (k3_xboole_0(A_201, A_201)=A_201)), inference(resolution, [status(thm)], [c_7421, c_7476])).
% 6.63/2.48  tff(c_7552, plain, (![A_208, B_209]: (r1_xboole_0(k3_xboole_0(A_208, B_209), k5_xboole_0(A_208, B_209)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.63/2.48  tff(c_7585, plain, (![A_31]: (r1_xboole_0(k3_xboole_0(A_31, A_31), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_7552])).
% 6.63/2.48  tff(c_7588, plain, (![A_31]: (r1_xboole_0(A_31, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_7492, c_7585])).
% 6.63/2.48  tff(c_7863, plain, (![A_230, B_231, C_232]: (~r1_xboole_0(A_230, B_231) | ~r2_hidden(C_232, k3_xboole_0(A_230, B_231)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.63/2.48  tff(c_8251, plain, (![A_244, C_245]: (~r1_xboole_0(A_244, A_244) | ~r2_hidden(C_245, A_244))), inference(superposition, [status(thm), theory('equality')], [c_7492, c_7863])).
% 6.63/2.48  tff(c_8255, plain, (![C_245]: (~r2_hidden(C_245, k1_xboole_0))), inference(resolution, [status(thm)], [c_7588, c_8251])).
% 6.63/2.48  tff(c_6, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), k3_xboole_0(A_5, B_6)) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.63/2.48  tff(c_9519, plain, (![C_274, B_275]: (r2_hidden('#skF_1'(C_274, k4_xboole_0(B_275, C_274)), k1_xboole_0) | r1_xboole_0(C_274, k4_xboole_0(B_275, C_274)))), inference(superposition, [status(thm), theory('equality')], [c_9501, c_6])).
% 6.63/2.48  tff(c_9591, plain, (![C_274, B_275]: (r1_xboole_0(C_274, k4_xboole_0(B_275, C_274)))), inference(negUnitSimplification, [status(thm)], [c_8255, c_9519])).
% 6.63/2.48  tff(c_9664, plain, (![B_279, C_278]: (r1_xboole_0(k4_xboole_0(B_279, C_278), C_278))), inference(superposition, [status(thm), theory('equality')], [c_9655, c_9591])).
% 6.63/2.48  tff(c_10203, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_10147, c_9664])).
% 6.63/2.48  tff(c_10224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7313, c_10203])).
% 6.63/2.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.63/2.48  
% 6.63/2.48  Inference rules
% 6.63/2.48  ----------------------
% 6.63/2.48  #Ref     : 0
% 6.63/2.48  #Sup     : 2576
% 6.63/2.48  #Fact    : 0
% 6.63/2.48  #Define  : 0
% 6.63/2.48  #Split   : 6
% 6.63/2.48  #Chain   : 0
% 6.63/2.48  #Close   : 0
% 6.63/2.48  
% 6.63/2.48  Ordering : KBO
% 6.63/2.48  
% 6.63/2.48  Simplification rules
% 6.63/2.48  ----------------------
% 6.63/2.48  #Subsume      : 67
% 6.63/2.48  #Demod        : 2032
% 6.63/2.48  #Tautology    : 1892
% 6.63/2.48  #SimpNegUnit  : 48
% 6.63/2.48  #BackRed      : 14
% 6.63/2.48  
% 6.63/2.48  #Partial instantiations: 0
% 6.63/2.48  #Strategies tried      : 1
% 6.63/2.48  
% 6.63/2.48  Timing (in seconds)
% 6.63/2.48  ----------------------
% 6.63/2.49  Preprocessing        : 0.32
% 6.63/2.49  Parsing              : 0.18
% 6.63/2.49  CNF conversion       : 0.02
% 6.63/2.49  Main loop            : 1.38
% 6.63/2.49  Inferencing          : 0.42
% 6.63/2.49  Reduction            : 0.62
% 6.63/2.49  Demodulation         : 0.50
% 6.63/2.49  BG Simplification    : 0.04
% 6.63/2.49  Subsumption          : 0.21
% 6.63/2.49  Abstraction          : 0.06
% 6.63/2.49  MUC search           : 0.00
% 6.63/2.49  Cooper               : 0.00
% 6.63/2.49  Total                : 1.74
% 6.63/2.49  Index Insertion      : 0.00
% 6.63/2.49  Index Deletion       : 0.00
% 6.63/2.49  Index Matching       : 0.00
% 6.63/2.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
