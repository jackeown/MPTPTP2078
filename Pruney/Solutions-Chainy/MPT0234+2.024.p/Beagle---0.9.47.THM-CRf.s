%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:44 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   45 (  52 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :   36 (  44 expanded)
%              Number of equality atoms :   35 (  43 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] : k6_enumset1(A,A,A,A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( A != B
       => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_10,plain,(
    ! [A_19,B_20] : k1_enumset1(A_19,A_19,B_20) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_103,plain,(
    ! [E_61,B_62,A_64,D_60,F_58,C_59,G_63] : k6_enumset1(A_64,A_64,B_62,C_59,D_60,E_61,F_58,G_63) = k5_enumset1(A_64,B_62,C_59,D_60,E_61,F_58,G_63) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_34,B_35,C_36] : k6_enumset1(A_34,A_34,A_34,A_34,A_34,A_34,B_35,C_36) = k1_enumset1(A_34,B_35,C_36) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_119,plain,(
    ! [E_65,F_66,G_67] : k5_enumset1(E_65,E_65,E_65,E_65,E_65,F_66,G_67) = k1_enumset1(E_65,F_66,G_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_16])).

tff(c_12,plain,(
    ! [A_21,B_22,D_24,C_23,F_26,E_25] : k5_enumset1(A_21,A_21,B_22,C_23,D_24,E_25,F_26) = k4_enumset1(A_21,B_22,C_23,D_24,E_25,F_26) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_125,plain,(
    ! [E_65,F_66,G_67] : k4_enumset1(E_65,E_65,E_65,E_65,F_66,G_67) = k1_enumset1(E_65,F_66,G_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_12])).

tff(c_145,plain,(
    ! [E_72,B_77,F_74,G_71,D_73,C_76,A_75] : k2_xboole_0(k4_enumset1(A_75,B_77,C_76,D_73,E_72,F_74),k1_tarski(G_71)) = k5_enumset1(A_75,B_77,C_76,D_73,E_72,F_74,G_71) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_158,plain,(
    ! [E_78,F_79,G_80,G_81] : k5_enumset1(E_78,E_78,E_78,E_78,F_79,G_80,G_81) = k2_xboole_0(k1_enumset1(E_78,F_79,G_80),k1_tarski(G_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_145])).

tff(c_110,plain,(
    ! [E_61,F_58,G_63] : k5_enumset1(E_61,E_61,E_61,E_61,E_61,F_58,G_63) = k1_enumset1(E_61,F_58,G_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_16])).

tff(c_168,plain,(
    ! [F_79,G_80,G_81] : k2_xboole_0(k1_enumset1(F_79,F_79,G_80),k1_tarski(G_81)) = k1_enumset1(F_79,G_80,G_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_110])).

tff(c_195,plain,(
    ! [F_82,G_83,G_84] : k2_xboole_0(k2_tarski(F_82,G_83),k1_tarski(G_84)) = k1_enumset1(F_82,G_83,G_84) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_168])).

tff(c_204,plain,(
    ! [A_18,G_84] : k2_xboole_0(k1_tarski(A_18),k1_tarski(G_84)) = k1_enumset1(A_18,A_18,G_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_195])).

tff(c_207,plain,(
    ! [A_18,G_84] : k2_xboole_0(k1_tarski(A_18),k1_tarski(G_84)) = k2_tarski(A_18,G_84) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_204])).

tff(c_24,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_54,plain,(
    ! [A_45,B_46] :
      ( k4_xboole_0(k1_tarski(A_45),k1_tarski(B_46)) = k1_tarski(A_45)
      | B_46 = A_45 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k4_xboole_0(B_2,A_1)) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_72,plain,(
    ! [B_47,A_48] :
      ( k5_xboole_0(k1_tarski(B_47),k1_tarski(A_48)) = k2_xboole_0(k1_tarski(B_47),k1_tarski(A_48))
      | B_47 = A_48 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_2])).

tff(c_22,plain,(
    k5_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_78,plain,
    ( k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_22])).

tff(c_83,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_78])).

tff(c_227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_83])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:01:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.33  
% 2.11/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.33  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 2.11/1.33  
% 2.11/1.33  %Foreground sorts:
% 2.11/1.33  
% 2.11/1.33  
% 2.11/1.33  %Background operators:
% 2.11/1.33  
% 2.11/1.33  
% 2.11/1.33  %Foreground operators:
% 2.11/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.11/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.11/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.11/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.11/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.11/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.11/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.33  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.11/1.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.33  
% 2.11/1.35  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.11/1.35  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.11/1.35  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 2.11/1.35  tff(f_41, axiom, (![A, B, C]: (k6_enumset1(A, A, A, A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_enumset1)).
% 2.11/1.35  tff(f_37, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 2.11/1.35  tff(f_29, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_enumset1)).
% 2.11/1.35  tff(f_52, negated_conjecture, ~(![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 2.11/1.35  tff(f_46, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.11/1.35  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.11/1.35  tff(c_10, plain, (![A_19, B_20]: (k1_enumset1(A_19, A_19, B_20)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.11/1.35  tff(c_8, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.11/1.35  tff(c_103, plain, (![E_61, B_62, A_64, D_60, F_58, C_59, G_63]: (k6_enumset1(A_64, A_64, B_62, C_59, D_60, E_61, F_58, G_63)=k5_enumset1(A_64, B_62, C_59, D_60, E_61, F_58, G_63))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.11/1.35  tff(c_16, plain, (![A_34, B_35, C_36]: (k6_enumset1(A_34, A_34, A_34, A_34, A_34, A_34, B_35, C_36)=k1_enumset1(A_34, B_35, C_36))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.11/1.35  tff(c_119, plain, (![E_65, F_66, G_67]: (k5_enumset1(E_65, E_65, E_65, E_65, E_65, F_66, G_67)=k1_enumset1(E_65, F_66, G_67))), inference(superposition, [status(thm), theory('equality')], [c_103, c_16])).
% 2.11/1.35  tff(c_12, plain, (![A_21, B_22, D_24, C_23, F_26, E_25]: (k5_enumset1(A_21, A_21, B_22, C_23, D_24, E_25, F_26)=k4_enumset1(A_21, B_22, C_23, D_24, E_25, F_26))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.11/1.35  tff(c_125, plain, (![E_65, F_66, G_67]: (k4_enumset1(E_65, E_65, E_65, E_65, F_66, G_67)=k1_enumset1(E_65, F_66, G_67))), inference(superposition, [status(thm), theory('equality')], [c_119, c_12])).
% 2.11/1.35  tff(c_145, plain, (![E_72, B_77, F_74, G_71, D_73, C_76, A_75]: (k2_xboole_0(k4_enumset1(A_75, B_77, C_76, D_73, E_72, F_74), k1_tarski(G_71))=k5_enumset1(A_75, B_77, C_76, D_73, E_72, F_74, G_71))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.11/1.35  tff(c_158, plain, (![E_78, F_79, G_80, G_81]: (k5_enumset1(E_78, E_78, E_78, E_78, F_79, G_80, G_81)=k2_xboole_0(k1_enumset1(E_78, F_79, G_80), k1_tarski(G_81)))), inference(superposition, [status(thm), theory('equality')], [c_125, c_145])).
% 2.11/1.35  tff(c_110, plain, (![E_61, F_58, G_63]: (k5_enumset1(E_61, E_61, E_61, E_61, E_61, F_58, G_63)=k1_enumset1(E_61, F_58, G_63))), inference(superposition, [status(thm), theory('equality')], [c_103, c_16])).
% 2.11/1.35  tff(c_168, plain, (![F_79, G_80, G_81]: (k2_xboole_0(k1_enumset1(F_79, F_79, G_80), k1_tarski(G_81))=k1_enumset1(F_79, G_80, G_81))), inference(superposition, [status(thm), theory('equality')], [c_158, c_110])).
% 2.11/1.35  tff(c_195, plain, (![F_82, G_83, G_84]: (k2_xboole_0(k2_tarski(F_82, G_83), k1_tarski(G_84))=k1_enumset1(F_82, G_83, G_84))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_168])).
% 2.11/1.35  tff(c_204, plain, (![A_18, G_84]: (k2_xboole_0(k1_tarski(A_18), k1_tarski(G_84))=k1_enumset1(A_18, A_18, G_84))), inference(superposition, [status(thm), theory('equality')], [c_8, c_195])).
% 2.11/1.35  tff(c_207, plain, (![A_18, G_84]: (k2_xboole_0(k1_tarski(A_18), k1_tarski(G_84))=k2_tarski(A_18, G_84))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_204])).
% 2.11/1.35  tff(c_24, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.11/1.35  tff(c_54, plain, (![A_45, B_46]: (k4_xboole_0(k1_tarski(A_45), k1_tarski(B_46))=k1_tarski(A_45) | B_46=A_45)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.11/1.35  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k4_xboole_0(B_2, A_1))=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.11/1.35  tff(c_72, plain, (![B_47, A_48]: (k5_xboole_0(k1_tarski(B_47), k1_tarski(A_48))=k2_xboole_0(k1_tarski(B_47), k1_tarski(A_48)) | B_47=A_48)), inference(superposition, [status(thm), theory('equality')], [c_54, c_2])).
% 2.11/1.35  tff(c_22, plain, (k5_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.11/1.35  tff(c_78, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_72, c_22])).
% 2.11/1.35  tff(c_83, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_24, c_78])).
% 2.11/1.35  tff(c_227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_207, c_83])).
% 2.11/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.35  
% 2.11/1.35  Inference rules
% 2.11/1.35  ----------------------
% 2.11/1.35  #Ref     : 0
% 2.11/1.35  #Sup     : 46
% 2.11/1.35  #Fact    : 0
% 2.11/1.35  #Define  : 0
% 2.11/1.35  #Split   : 0
% 2.11/1.35  #Chain   : 0
% 2.11/1.35  #Close   : 0
% 2.11/1.35  
% 2.11/1.35  Ordering : KBO
% 2.11/1.35  
% 2.11/1.35  Simplification rules
% 2.11/1.35  ----------------------
% 2.11/1.35  #Subsume      : 0
% 2.11/1.35  #Demod        : 13
% 2.11/1.35  #Tautology    : 33
% 2.11/1.35  #SimpNegUnit  : 1
% 2.11/1.35  #BackRed      : 2
% 2.11/1.35  
% 2.11/1.35  #Partial instantiations: 0
% 2.11/1.35  #Strategies tried      : 1
% 2.11/1.35  
% 2.11/1.35  Timing (in seconds)
% 2.11/1.35  ----------------------
% 2.11/1.35  Preprocessing        : 0.38
% 2.11/1.35  Parsing              : 0.21
% 2.11/1.35  CNF conversion       : 0.02
% 2.11/1.35  Main loop            : 0.16
% 2.11/1.35  Inferencing          : 0.07
% 2.11/1.35  Reduction            : 0.05
% 2.11/1.35  Demodulation         : 0.04
% 2.11/1.35  BG Simplification    : 0.02
% 2.11/1.35  Subsumption          : 0.02
% 2.11/1.35  Abstraction          : 0.01
% 2.11/1.35  MUC search           : 0.00
% 2.11/1.35  Cooper               : 0.00
% 2.11/1.35  Total                : 0.57
% 2.11/1.35  Index Insertion      : 0.00
% 2.11/1.35  Index Deletion       : 0.00
% 2.11/1.35  Index Matching       : 0.00
% 2.11/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
