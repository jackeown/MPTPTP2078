%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:01 EST 2020

% Result     : Theorem 6.54s
% Output     : CNFRefutation 6.99s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 117 expanded)
%              Number of leaves         :   42 (  57 expanded)
%              Depth                    :   13
%              Number of atoms          :   78 ( 121 expanded)
%              Number of equality atoms :   66 (  99 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_75,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_79,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_81,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_83,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_71,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_69,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_enumset1)).

tff(c_80,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_82,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_68,plain,(
    ! [A_41,B_42,C_43] : k2_enumset1(A_41,A_41,B_42,C_43) = k1_enumset1(A_41,B_42,C_43) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_66,plain,(
    ! [A_39,B_40] : k1_enumset1(A_39,A_39,B_40) = k2_tarski(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_70,plain,(
    ! [A_44,B_45,C_46,D_47] : k3_enumset1(A_44,A_44,B_45,C_46,D_47) = k2_enumset1(A_44,B_45,C_46,D_47) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_72,plain,(
    ! [B_49,A_48,D_51,E_52,C_50] : k4_enumset1(A_48,A_48,B_49,C_50,D_51,E_52) = k3_enumset1(A_48,B_49,C_50,D_51,E_52) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_74,plain,(
    ! [A_53,D_56,E_57,C_55,F_58,B_54] : k5_enumset1(A_53,A_53,B_54,C_55,D_56,E_57,F_58) = k4_enumset1(A_53,B_54,C_55,D_56,E_57,F_58) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2950,plain,(
    ! [C_226,F_225,B_222,E_223,A_224,D_221,G_227] : k2_xboole_0(k4_enumset1(A_224,B_222,C_226,D_221,E_223,F_225),k1_tarski(G_227)) = k5_enumset1(A_224,B_222,C_226,D_221,E_223,F_225,G_227) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2959,plain,(
    ! [B_49,A_48,D_51,E_52,C_50,G_227] : k5_enumset1(A_48,A_48,B_49,C_50,D_51,E_52,G_227) = k2_xboole_0(k3_enumset1(A_48,B_49,C_50,D_51,E_52),k1_tarski(G_227)) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_2950])).

tff(c_6314,plain,(
    ! [B_315,E_318,C_317,D_314,G_313,A_316] : k2_xboole_0(k3_enumset1(A_316,B_315,C_317,D_314,E_318),k1_tarski(G_313)) = k4_enumset1(A_316,B_315,C_317,D_314,E_318,G_313) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2959])).

tff(c_6323,plain,(
    ! [C_46,A_44,B_45,G_313,D_47] : k4_enumset1(A_44,A_44,B_45,C_46,D_47,G_313) = k2_xboole_0(k2_enumset1(A_44,B_45,C_46,D_47),k1_tarski(G_313)) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_6314])).

tff(c_6327,plain,(
    ! [C_320,G_322,D_319,B_321,A_323] : k2_xboole_0(k2_enumset1(A_323,B_321,C_320,D_319),k1_tarski(G_322)) = k3_enumset1(A_323,B_321,C_320,D_319,G_322) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_6323])).

tff(c_6336,plain,(
    ! [A_41,B_42,C_43,G_322] : k3_enumset1(A_41,A_41,B_42,C_43,G_322) = k2_xboole_0(k1_enumset1(A_41,B_42,C_43),k1_tarski(G_322)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_6327])).

tff(c_6340,plain,(
    ! [A_324,B_325,C_326,G_327] : k2_xboole_0(k1_enumset1(A_324,B_325,C_326),k1_tarski(G_327)) = k2_enumset1(A_324,B_325,C_326,G_327) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_6336])).

tff(c_6379,plain,(
    ! [A_39,B_40,G_327] : k2_xboole_0(k2_tarski(A_39,B_40),k1_tarski(G_327)) = k2_enumset1(A_39,A_39,B_40,G_327) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_6340])).

tff(c_6383,plain,(
    ! [A_328,B_329,G_330] : k2_xboole_0(k2_tarski(A_328,B_329),k1_tarski(G_330)) = k1_enumset1(A_328,B_329,G_330) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_6379])).

tff(c_14,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_159,plain,(
    ! [A_89,B_90] :
      ( k3_xboole_0(A_89,B_90) = A_89
      | ~ r1_tarski(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_189,plain,(
    ! [A_93] : k3_xboole_0(k1_xboole_0,A_93) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_159])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_194,plain,(
    ! [A_93] : k3_xboole_0(A_93,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_2])).

tff(c_270,plain,(
    ! [A_95,B_96] : k5_xboole_0(A_95,k3_xboole_0(A_95,B_96)) = k4_xboole_0(A_95,B_96) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_282,plain,(
    ! [A_93] : k5_xboole_0(A_93,k1_xboole_0) = k4_xboole_0(A_93,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_270])).

tff(c_297,plain,(
    ! [A_93] : k4_xboole_0(A_93,k1_xboole_0) = A_93 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_282])).

tff(c_426,plain,(
    ! [A_104,B_105] : k4_xboole_0(A_104,k4_xboole_0(A_104,B_105)) = k3_xboole_0(A_104,B_105) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_451,plain,(
    ! [A_93] : k4_xboole_0(A_93,A_93) = k3_xboole_0(A_93,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_426])).

tff(c_463,plain,(
    ! [A_93] : k4_xboole_0(A_93,A_93) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_451])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_294,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_270])).

tff(c_84,plain,(
    r1_tarski(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_166,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_159])).

tff(c_279,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_270])).

tff(c_418,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_279])).

tff(c_16,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_422,plain,(
    k5_xboole_0(k2_tarski('#skF_6','#skF_7'),k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5'))) = k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_16])).

tff(c_681,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k2_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_463,c_422])).

tff(c_6389,plain,(
    k1_enumset1('#skF_6','#skF_7','#skF_5') = k2_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_6383,c_681])).

tff(c_20,plain,(
    ! [E_21,A_15,B_16] : r2_hidden(E_21,k1_enumset1(A_15,B_16,E_21)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6435,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6389,c_20])).

tff(c_559,plain,(
    ! [C_109,B_110,A_111] : k1_enumset1(C_109,B_110,A_111) = k1_enumset1(A_111,B_110,C_109) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_575,plain,(
    ! [C_109,B_110] : k1_enumset1(C_109,B_110,B_110) = k2_tarski(B_110,C_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_559,c_66])).

tff(c_1260,plain,(
    ! [E_139,C_140,B_141,A_142] :
      ( E_139 = C_140
      | E_139 = B_141
      | E_139 = A_142
      | ~ r2_hidden(E_139,k1_enumset1(A_142,B_141,C_140)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1284,plain,(
    ! [E_139,B_110,C_109] :
      ( E_139 = B_110
      | E_139 = B_110
      | E_139 = C_109
      | ~ r2_hidden(E_139,k2_tarski(B_110,C_109)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_575,c_1260])).

tff(c_6453,plain,
    ( '#skF_5' = '#skF_6'
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_6435,c_1284])).

tff(c_6460,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_82,c_82,c_6453])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:40:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.54/2.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.91/2.49  
% 6.91/2.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.91/2.49  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1
% 6.91/2.49  
% 6.91/2.49  %Foreground sorts:
% 6.91/2.49  
% 6.91/2.49  
% 6.91/2.49  %Background operators:
% 6.91/2.49  
% 6.91/2.49  
% 6.91/2.49  %Foreground operators:
% 6.91/2.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.91/2.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.91/2.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.91/2.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.91/2.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.91/2.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.91/2.49  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.91/2.49  tff('#skF_7', type, '#skF_7': $i).
% 6.91/2.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.91/2.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.91/2.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.91/2.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.91/2.49  tff('#skF_5', type, '#skF_5': $i).
% 6.91/2.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 6.91/2.49  tff('#skF_6', type, '#skF_6': $i).
% 6.91/2.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.91/2.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.91/2.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.91/2.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.91/2.49  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.91/2.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.91/2.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.91/2.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.91/2.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.91/2.49  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 6.91/2.49  
% 6.99/2.51  tff(f_97, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 6.99/2.51  tff(f_77, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 6.99/2.51  tff(f_75, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.99/2.51  tff(f_79, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 6.99/2.51  tff(f_81, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 6.99/2.51  tff(f_83, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 6.99/2.51  tff(f_71, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_enumset1)).
% 6.99/2.51  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 6.99/2.51  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.99/2.51  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.99/2.51  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.99/2.51  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.99/2.51  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.99/2.51  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 6.99/2.51  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 6.99/2.51  tff(f_58, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 6.99/2.51  tff(f_69, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_enumset1)).
% 6.99/2.51  tff(c_80, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.99/2.51  tff(c_82, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.99/2.51  tff(c_68, plain, (![A_41, B_42, C_43]: (k2_enumset1(A_41, A_41, B_42, C_43)=k1_enumset1(A_41, B_42, C_43))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.99/2.51  tff(c_66, plain, (![A_39, B_40]: (k1_enumset1(A_39, A_39, B_40)=k2_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.99/2.51  tff(c_70, plain, (![A_44, B_45, C_46, D_47]: (k3_enumset1(A_44, A_44, B_45, C_46, D_47)=k2_enumset1(A_44, B_45, C_46, D_47))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.99/2.51  tff(c_72, plain, (![B_49, A_48, D_51, E_52, C_50]: (k4_enumset1(A_48, A_48, B_49, C_50, D_51, E_52)=k3_enumset1(A_48, B_49, C_50, D_51, E_52))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.99/2.51  tff(c_74, plain, (![A_53, D_56, E_57, C_55, F_58, B_54]: (k5_enumset1(A_53, A_53, B_54, C_55, D_56, E_57, F_58)=k4_enumset1(A_53, B_54, C_55, D_56, E_57, F_58))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.99/2.51  tff(c_2950, plain, (![C_226, F_225, B_222, E_223, A_224, D_221, G_227]: (k2_xboole_0(k4_enumset1(A_224, B_222, C_226, D_221, E_223, F_225), k1_tarski(G_227))=k5_enumset1(A_224, B_222, C_226, D_221, E_223, F_225, G_227))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.99/2.51  tff(c_2959, plain, (![B_49, A_48, D_51, E_52, C_50, G_227]: (k5_enumset1(A_48, A_48, B_49, C_50, D_51, E_52, G_227)=k2_xboole_0(k3_enumset1(A_48, B_49, C_50, D_51, E_52), k1_tarski(G_227)))), inference(superposition, [status(thm), theory('equality')], [c_72, c_2950])).
% 6.99/2.51  tff(c_6314, plain, (![B_315, E_318, C_317, D_314, G_313, A_316]: (k2_xboole_0(k3_enumset1(A_316, B_315, C_317, D_314, E_318), k1_tarski(G_313))=k4_enumset1(A_316, B_315, C_317, D_314, E_318, G_313))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2959])).
% 6.99/2.51  tff(c_6323, plain, (![C_46, A_44, B_45, G_313, D_47]: (k4_enumset1(A_44, A_44, B_45, C_46, D_47, G_313)=k2_xboole_0(k2_enumset1(A_44, B_45, C_46, D_47), k1_tarski(G_313)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_6314])).
% 6.99/2.51  tff(c_6327, plain, (![C_320, G_322, D_319, B_321, A_323]: (k2_xboole_0(k2_enumset1(A_323, B_321, C_320, D_319), k1_tarski(G_322))=k3_enumset1(A_323, B_321, C_320, D_319, G_322))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_6323])).
% 6.99/2.51  tff(c_6336, plain, (![A_41, B_42, C_43, G_322]: (k3_enumset1(A_41, A_41, B_42, C_43, G_322)=k2_xboole_0(k1_enumset1(A_41, B_42, C_43), k1_tarski(G_322)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_6327])).
% 6.99/2.51  tff(c_6340, plain, (![A_324, B_325, C_326, G_327]: (k2_xboole_0(k1_enumset1(A_324, B_325, C_326), k1_tarski(G_327))=k2_enumset1(A_324, B_325, C_326, G_327))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_6336])).
% 6.99/2.51  tff(c_6379, plain, (![A_39, B_40, G_327]: (k2_xboole_0(k2_tarski(A_39, B_40), k1_tarski(G_327))=k2_enumset1(A_39, A_39, B_40, G_327))), inference(superposition, [status(thm), theory('equality')], [c_66, c_6340])).
% 6.99/2.51  tff(c_6383, plain, (![A_328, B_329, G_330]: (k2_xboole_0(k2_tarski(A_328, B_329), k1_tarski(G_330))=k1_enumset1(A_328, B_329, G_330))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_6379])).
% 6.99/2.51  tff(c_14, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.99/2.51  tff(c_10, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.99/2.51  tff(c_159, plain, (![A_89, B_90]: (k3_xboole_0(A_89, B_90)=A_89 | ~r1_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.99/2.51  tff(c_189, plain, (![A_93]: (k3_xboole_0(k1_xboole_0, A_93)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_159])).
% 6.99/2.51  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.99/2.51  tff(c_194, plain, (![A_93]: (k3_xboole_0(A_93, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_189, c_2])).
% 6.99/2.51  tff(c_270, plain, (![A_95, B_96]: (k5_xboole_0(A_95, k3_xboole_0(A_95, B_96))=k4_xboole_0(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.99/2.51  tff(c_282, plain, (![A_93]: (k5_xboole_0(A_93, k1_xboole_0)=k4_xboole_0(A_93, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_194, c_270])).
% 6.99/2.51  tff(c_297, plain, (![A_93]: (k4_xboole_0(A_93, k1_xboole_0)=A_93)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_282])).
% 6.99/2.51  tff(c_426, plain, (![A_104, B_105]: (k4_xboole_0(A_104, k4_xboole_0(A_104, B_105))=k3_xboole_0(A_104, B_105))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.99/2.51  tff(c_451, plain, (![A_93]: (k4_xboole_0(A_93, A_93)=k3_xboole_0(A_93, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_297, c_426])).
% 6.99/2.51  tff(c_463, plain, (![A_93]: (k4_xboole_0(A_93, A_93)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_194, c_451])).
% 6.99/2.51  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.99/2.51  tff(c_294, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_270])).
% 6.99/2.51  tff(c_84, plain, (r1_tarski(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.99/2.51  tff(c_166, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_84, c_159])).
% 6.99/2.51  tff(c_279, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_166, c_270])).
% 6.99/2.51  tff(c_418, plain, (k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_294, c_279])).
% 6.99/2.51  tff(c_16, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.99/2.51  tff(c_422, plain, (k5_xboole_0(k2_tarski('#skF_6', '#skF_7'), k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5')))=k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_418, c_16])).
% 6.99/2.51  tff(c_681, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k2_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_463, c_422])).
% 6.99/2.51  tff(c_6389, plain, (k1_enumset1('#skF_6', '#skF_7', '#skF_5')=k2_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_6383, c_681])).
% 6.99/2.51  tff(c_20, plain, (![E_21, A_15, B_16]: (r2_hidden(E_21, k1_enumset1(A_15, B_16, E_21)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.99/2.51  tff(c_6435, plain, (r2_hidden('#skF_5', k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_6389, c_20])).
% 6.99/2.51  tff(c_559, plain, (![C_109, B_110, A_111]: (k1_enumset1(C_109, B_110, A_111)=k1_enumset1(A_111, B_110, C_109))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.99/2.51  tff(c_575, plain, (![C_109, B_110]: (k1_enumset1(C_109, B_110, B_110)=k2_tarski(B_110, C_109))), inference(superposition, [status(thm), theory('equality')], [c_559, c_66])).
% 6.99/2.51  tff(c_1260, plain, (![E_139, C_140, B_141, A_142]: (E_139=C_140 | E_139=B_141 | E_139=A_142 | ~r2_hidden(E_139, k1_enumset1(A_142, B_141, C_140)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.99/2.51  tff(c_1284, plain, (![E_139, B_110, C_109]: (E_139=B_110 | E_139=B_110 | E_139=C_109 | ~r2_hidden(E_139, k2_tarski(B_110, C_109)))), inference(superposition, [status(thm), theory('equality')], [c_575, c_1260])).
% 6.99/2.51  tff(c_6453, plain, ('#skF_5'='#skF_6' | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_6435, c_1284])).
% 6.99/2.51  tff(c_6460, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_82, c_82, c_6453])).
% 6.99/2.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.99/2.51  
% 6.99/2.51  Inference rules
% 6.99/2.51  ----------------------
% 6.99/2.51  #Ref     : 0
% 6.99/2.51  #Sup     : 1592
% 6.99/2.51  #Fact    : 0
% 6.99/2.51  #Define  : 0
% 6.99/2.51  #Split   : 0
% 6.99/2.51  #Chain   : 0
% 6.99/2.51  #Close   : 0
% 6.99/2.51  
% 6.99/2.51  Ordering : KBO
% 6.99/2.51  
% 6.99/2.51  Simplification rules
% 6.99/2.51  ----------------------
% 6.99/2.51  #Subsume      : 147
% 6.99/2.51  #Demod        : 2523
% 6.99/2.51  #Tautology    : 988
% 6.99/2.51  #SimpNegUnit  : 1
% 6.99/2.51  #BackRed      : 2
% 6.99/2.51  
% 6.99/2.51  #Partial instantiations: 0
% 6.99/2.51  #Strategies tried      : 1
% 6.99/2.51  
% 6.99/2.51  Timing (in seconds)
% 6.99/2.51  ----------------------
% 6.99/2.51  Preprocessing        : 0.37
% 6.99/2.51  Parsing              : 0.19
% 6.99/2.51  CNF conversion       : 0.03
% 6.99/2.51  Main loop            : 1.31
% 6.99/2.51  Inferencing          : 0.36
% 6.99/2.51  Reduction            : 0.66
% 6.99/2.51  Demodulation         : 0.58
% 6.99/2.51  BG Simplification    : 0.05
% 6.99/2.51  Subsumption          : 0.20
% 6.99/2.51  Abstraction          : 0.07
% 6.99/2.51  MUC search           : 0.00
% 6.99/2.51  Cooper               : 0.00
% 6.99/2.51  Total                : 1.71
% 6.99/2.51  Index Insertion      : 0.00
% 6.99/2.51  Index Deletion       : 0.00
% 6.99/2.51  Index Matching       : 0.00
% 6.99/2.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
