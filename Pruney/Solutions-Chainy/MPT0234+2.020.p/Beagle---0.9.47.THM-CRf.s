%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:43 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   52 (  61 expanded)
%              Number of leaves         :   27 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :   40 (  50 expanded)
%              Number of equality atoms :   39 (  49 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( A != B
       => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_12,plain,(
    ! [A_21,B_22] : k1_enumset1(A_21,A_21,B_22) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_23,B_24,C_25] : k2_enumset1(A_23,A_23,B_24,C_25) = k1_enumset1(A_23,B_24,C_25) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_26,B_27,C_28,D_29] : k3_enumset1(A_26,A_26,B_27,C_28,D_29) = k2_enumset1(A_26,B_27,C_28,D_29) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [D_33,A_30,C_32,B_31,E_34] : k4_enumset1(A_30,A_30,B_31,C_32,D_33,E_34) = k3_enumset1(A_30,B_31,C_32,D_33,E_34) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_35,F_40,B_36,C_37,D_38,E_39] : k5_enumset1(A_35,A_35,B_36,C_37,D_38,E_39,F_40) = k4_enumset1(A_35,B_36,C_37,D_38,E_39,F_40) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_145,plain,(
    ! [G_89,A_92,C_91,F_88,D_87,B_90,E_93] : k2_xboole_0(k4_enumset1(A_92,B_90,C_91,D_87,E_93,F_88),k1_tarski(G_89)) = k5_enumset1(A_92,B_90,C_91,D_87,E_93,F_88,G_89) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_154,plain,(
    ! [G_89,D_33,A_30,C_32,B_31,E_34] : k5_enumset1(A_30,A_30,B_31,C_32,D_33,E_34,G_89) = k2_xboole_0(k3_enumset1(A_30,B_31,C_32,D_33,E_34),k1_tarski(G_89)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_145])).

tff(c_158,plain,(
    ! [A_96,G_99,B_95,C_94,E_97,D_98] : k2_xboole_0(k3_enumset1(A_96,B_95,C_94,D_98,E_97),k1_tarski(G_99)) = k4_enumset1(A_96,B_95,C_94,D_98,E_97,G_99) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_154])).

tff(c_167,plain,(
    ! [B_27,D_29,G_99,A_26,C_28] : k4_enumset1(A_26,A_26,B_27,C_28,D_29,G_99) = k2_xboole_0(k2_enumset1(A_26,B_27,C_28,D_29),k1_tarski(G_99)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_158])).

tff(c_171,plain,(
    ! [G_103,A_102,C_104,D_100,B_101] : k2_xboole_0(k2_enumset1(A_102,B_101,C_104,D_100),k1_tarski(G_103)) = k3_enumset1(A_102,B_101,C_104,D_100,G_103) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_167])).

tff(c_180,plain,(
    ! [A_23,B_24,C_25,G_103] : k3_enumset1(A_23,A_23,B_24,C_25,G_103) = k2_xboole_0(k1_enumset1(A_23,B_24,C_25),k1_tarski(G_103)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_171])).

tff(c_184,plain,(
    ! [A_105,B_106,C_107,G_108] : k2_xboole_0(k1_enumset1(A_105,B_106,C_107),k1_tarski(G_108)) = k2_enumset1(A_105,B_106,C_107,G_108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_180])).

tff(c_193,plain,(
    ! [A_21,B_22,G_108] : k2_xboole_0(k2_tarski(A_21,B_22),k1_tarski(G_108)) = k2_enumset1(A_21,A_21,B_22,G_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_184])).

tff(c_214,plain,(
    ! [A_117,B_118,G_119] : k2_xboole_0(k2_tarski(A_117,B_118),k1_tarski(G_119)) = k1_enumset1(A_117,B_118,G_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_193])).

tff(c_223,plain,(
    ! [A_20,G_119] : k2_xboole_0(k1_tarski(A_20),k1_tarski(G_119)) = k1_enumset1(A_20,A_20,G_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_214])).

tff(c_226,plain,(
    ! [A_20,G_119] : k2_xboole_0(k1_tarski(A_20),k1_tarski(G_119)) = k2_tarski(A_20,G_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_223])).

tff(c_30,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_69,plain,(
    ! [A_58,B_59] :
      ( k4_xboole_0(k1_tarski(A_58),k1_tarski(B_59)) = k1_tarski(A_58)
      | B_59 = A_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_105,plain,(
    ! [B_67,A_68] :
      ( k5_xboole_0(k1_tarski(B_67),k1_tarski(A_68)) = k2_xboole_0(k1_tarski(B_67),k1_tarski(A_68))
      | B_67 = A_68 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_4])).

tff(c_28,plain,(
    k5_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_111,plain,
    ( k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_28])).

tff(c_116,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_111])).

tff(c_230,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_116])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:56:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.29  
% 1.99/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.29  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.99/1.29  
% 1.99/1.29  %Foreground sorts:
% 1.99/1.29  
% 1.99/1.29  
% 1.99/1.29  %Background operators:
% 1.99/1.29  
% 1.99/1.29  
% 1.99/1.29  %Foreground operators:
% 1.99/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.99/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.99/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.99/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.99/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.99/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.99/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.99/1.29  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.29  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.99/1.29  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.99/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.99/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.99/1.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.99/1.29  
% 2.20/1.30  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.20/1.30  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.20/1.30  tff(f_39, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.20/1.30  tff(f_41, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.20/1.30  tff(f_43, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.20/1.30  tff(f_45, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 2.20/1.30  tff(f_31, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_enumset1)).
% 2.20/1.30  tff(f_58, negated_conjecture, ~(![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 2.20/1.30  tff(f_52, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.20/1.30  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.20/1.30  tff(c_12, plain, (![A_21, B_22]: (k1_enumset1(A_21, A_21, B_22)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.20/1.30  tff(c_10, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.20/1.30  tff(c_14, plain, (![A_23, B_24, C_25]: (k2_enumset1(A_23, A_23, B_24, C_25)=k1_enumset1(A_23, B_24, C_25))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.20/1.30  tff(c_16, plain, (![A_26, B_27, C_28, D_29]: (k3_enumset1(A_26, A_26, B_27, C_28, D_29)=k2_enumset1(A_26, B_27, C_28, D_29))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.20/1.30  tff(c_18, plain, (![D_33, A_30, C_32, B_31, E_34]: (k4_enumset1(A_30, A_30, B_31, C_32, D_33, E_34)=k3_enumset1(A_30, B_31, C_32, D_33, E_34))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.20/1.30  tff(c_20, plain, (![A_35, F_40, B_36, C_37, D_38, E_39]: (k5_enumset1(A_35, A_35, B_36, C_37, D_38, E_39, F_40)=k4_enumset1(A_35, B_36, C_37, D_38, E_39, F_40))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.20/1.30  tff(c_145, plain, (![G_89, A_92, C_91, F_88, D_87, B_90, E_93]: (k2_xboole_0(k4_enumset1(A_92, B_90, C_91, D_87, E_93, F_88), k1_tarski(G_89))=k5_enumset1(A_92, B_90, C_91, D_87, E_93, F_88, G_89))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.20/1.30  tff(c_154, plain, (![G_89, D_33, A_30, C_32, B_31, E_34]: (k5_enumset1(A_30, A_30, B_31, C_32, D_33, E_34, G_89)=k2_xboole_0(k3_enumset1(A_30, B_31, C_32, D_33, E_34), k1_tarski(G_89)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_145])).
% 2.20/1.30  tff(c_158, plain, (![A_96, G_99, B_95, C_94, E_97, D_98]: (k2_xboole_0(k3_enumset1(A_96, B_95, C_94, D_98, E_97), k1_tarski(G_99))=k4_enumset1(A_96, B_95, C_94, D_98, E_97, G_99))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_154])).
% 2.20/1.30  tff(c_167, plain, (![B_27, D_29, G_99, A_26, C_28]: (k4_enumset1(A_26, A_26, B_27, C_28, D_29, G_99)=k2_xboole_0(k2_enumset1(A_26, B_27, C_28, D_29), k1_tarski(G_99)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_158])).
% 2.20/1.30  tff(c_171, plain, (![G_103, A_102, C_104, D_100, B_101]: (k2_xboole_0(k2_enumset1(A_102, B_101, C_104, D_100), k1_tarski(G_103))=k3_enumset1(A_102, B_101, C_104, D_100, G_103))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_167])).
% 2.20/1.30  tff(c_180, plain, (![A_23, B_24, C_25, G_103]: (k3_enumset1(A_23, A_23, B_24, C_25, G_103)=k2_xboole_0(k1_enumset1(A_23, B_24, C_25), k1_tarski(G_103)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_171])).
% 2.20/1.30  tff(c_184, plain, (![A_105, B_106, C_107, G_108]: (k2_xboole_0(k1_enumset1(A_105, B_106, C_107), k1_tarski(G_108))=k2_enumset1(A_105, B_106, C_107, G_108))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_180])).
% 2.20/1.30  tff(c_193, plain, (![A_21, B_22, G_108]: (k2_xboole_0(k2_tarski(A_21, B_22), k1_tarski(G_108))=k2_enumset1(A_21, A_21, B_22, G_108))), inference(superposition, [status(thm), theory('equality')], [c_12, c_184])).
% 2.20/1.30  tff(c_214, plain, (![A_117, B_118, G_119]: (k2_xboole_0(k2_tarski(A_117, B_118), k1_tarski(G_119))=k1_enumset1(A_117, B_118, G_119))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_193])).
% 2.20/1.30  tff(c_223, plain, (![A_20, G_119]: (k2_xboole_0(k1_tarski(A_20), k1_tarski(G_119))=k1_enumset1(A_20, A_20, G_119))), inference(superposition, [status(thm), theory('equality')], [c_10, c_214])).
% 2.20/1.30  tff(c_226, plain, (![A_20, G_119]: (k2_xboole_0(k1_tarski(A_20), k1_tarski(G_119))=k2_tarski(A_20, G_119))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_223])).
% 2.20/1.30  tff(c_30, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.20/1.30  tff(c_69, plain, (![A_58, B_59]: (k4_xboole_0(k1_tarski(A_58), k1_tarski(B_59))=k1_tarski(A_58) | B_59=A_58)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.20/1.30  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.20/1.30  tff(c_105, plain, (![B_67, A_68]: (k5_xboole_0(k1_tarski(B_67), k1_tarski(A_68))=k2_xboole_0(k1_tarski(B_67), k1_tarski(A_68)) | B_67=A_68)), inference(superposition, [status(thm), theory('equality')], [c_69, c_4])).
% 2.20/1.30  tff(c_28, plain, (k5_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.20/1.30  tff(c_111, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_105, c_28])).
% 2.20/1.30  tff(c_116, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_30, c_111])).
% 2.20/1.30  tff(c_230, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_226, c_116])).
% 2.20/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.30  
% 2.20/1.30  Inference rules
% 2.20/1.30  ----------------------
% 2.20/1.30  #Ref     : 0
% 2.20/1.30  #Sup     : 44
% 2.20/1.30  #Fact    : 0
% 2.20/1.30  #Define  : 0
% 2.20/1.30  #Split   : 0
% 2.20/1.30  #Chain   : 0
% 2.20/1.30  #Close   : 0
% 2.20/1.30  
% 2.20/1.30  Ordering : KBO
% 2.20/1.30  
% 2.20/1.30  Simplification rules
% 2.20/1.30  ----------------------
% 2.20/1.30  #Subsume      : 0
% 2.20/1.30  #Demod        : 9
% 2.20/1.30  #Tautology    : 35
% 2.20/1.30  #SimpNegUnit  : 1
% 2.20/1.30  #BackRed      : 2
% 2.20/1.30  
% 2.20/1.30  #Partial instantiations: 0
% 2.20/1.30  #Strategies tried      : 1
% 2.20/1.30  
% 2.20/1.30  Timing (in seconds)
% 2.20/1.30  ----------------------
% 2.20/1.31  Preprocessing        : 0.33
% 2.20/1.31  Parsing              : 0.17
% 2.20/1.31  CNF conversion       : 0.02
% 2.20/1.31  Main loop            : 0.17
% 2.20/1.31  Inferencing          : 0.08
% 2.20/1.31  Reduction            : 0.05
% 2.20/1.31  Demodulation         : 0.03
% 2.20/1.31  BG Simplification    : 0.02
% 2.20/1.31  Subsumption          : 0.02
% 2.20/1.31  Abstraction          : 0.01
% 2.20/1.31  MUC search           : 0.00
% 2.20/1.31  Cooper               : 0.00
% 2.20/1.31  Total                : 0.53
% 2.20/1.31  Index Insertion      : 0.00
% 2.20/1.31  Index Deletion       : 0.00
% 2.20/1.31  Index Matching       : 0.00
% 2.20/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
