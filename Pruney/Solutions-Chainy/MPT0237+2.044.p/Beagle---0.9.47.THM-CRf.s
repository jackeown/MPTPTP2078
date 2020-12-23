%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:50 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   58 (  96 expanded)
%              Number of leaves         :   29 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :   50 (  98 expanded)
%              Number of equality atoms :   45 (  89 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_14,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_15,B_16] : k1_enumset1(A_15,A_15,B_16) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_17,B_18,C_19] : k2_enumset1(A_17,A_17,B_18,C_19) = k1_enumset1(A_17,B_18,C_19) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_272,plain,(
    ! [A_85,E_84,B_81,D_83,C_82] : k2_xboole_0(k1_tarski(A_85),k2_enumset1(B_81,C_82,D_83,E_84)) = k3_enumset1(A_85,B_81,C_82,D_83,E_84) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_284,plain,(
    ! [A_86,A_87,B_88,C_89] : k3_enumset1(A_86,A_87,A_87,B_88,C_89) = k2_xboole_0(k1_tarski(A_86),k1_enumset1(A_87,B_88,C_89)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_272])).

tff(c_20,plain,(
    ! [A_20,B_21,C_22,D_23] : k3_enumset1(A_20,A_20,B_21,C_22,D_23) = k2_enumset1(A_20,B_21,C_22,D_23) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_294,plain,(
    ! [A_87,B_88,C_89] : k2_xboole_0(k1_tarski(A_87),k1_enumset1(A_87,B_88,C_89)) = k2_enumset1(A_87,A_87,B_88,C_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_20])).

tff(c_323,plain,(
    ! [A_96,B_97,C_98] : k2_xboole_0(k1_tarski(A_96),k1_enumset1(A_96,B_97,C_98)) = k1_enumset1(A_96,B_97,C_98) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_294])).

tff(c_339,plain,(
    ! [A_15,B_16] : k2_xboole_0(k1_tarski(A_15),k2_tarski(A_15,B_16)) = k1_enumset1(A_15,A_15,B_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_323])).

tff(c_343,plain,(
    ! [A_99,B_100] : k2_xboole_0(k1_tarski(A_99),k2_tarski(A_99,B_100)) = k2_tarski(A_99,B_100) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_339])).

tff(c_352,plain,(
    ! [A_14] : k2_xboole_0(k1_tarski(A_14),k1_tarski(A_14)) = k2_tarski(A_14,A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_343])).

tff(c_356,plain,(
    ! [A_101] : k2_xboole_0(k1_tarski(A_101),k1_tarski(A_101)) = k1_tarski(A_101) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_352])).

tff(c_86,plain,(
    ! [A_48,B_49] : k3_tarski(k2_tarski(A_48,B_49)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_95,plain,(
    ! [A_14] : k3_tarski(k1_tarski(A_14)) = k2_xboole_0(A_14,A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_86])).

tff(c_365,plain,(
    ! [A_101] : k3_tarski(k1_tarski(k1_tarski(A_101))) = k1_tarski(A_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_95])).

tff(c_28,plain,(
    ! [A_37,B_38] :
      ( r1_xboole_0(k1_tarski(A_37),k1_tarski(B_38))
      | B_38 = A_37 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_116,plain,(
    ! [A_53,B_54] :
      ( k4_xboole_0(A_53,B_54) = A_53
      | ~ r1_xboole_0(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_187,plain,(
    ! [A_64,B_65] :
      ( k4_xboole_0(k1_tarski(A_64),k1_tarski(B_65)) = k1_tarski(A_64)
      | B_65 = A_64 ) ),
    inference(resolution,[status(thm)],[c_28,c_116])).

tff(c_10,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_217,plain,(
    ! [B_72,A_73] :
      ( k5_xboole_0(k1_tarski(B_72),k1_tarski(A_73)) = k2_xboole_0(k1_tarski(B_72),k1_tarski(A_73))
      | B_72 = A_73 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_10])).

tff(c_30,plain,(
    ! [A_39,B_40] :
      ( k5_xboole_0(k1_tarski(A_39),k1_tarski(B_40)) = k2_tarski(A_39,B_40)
      | B_40 = A_39 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_232,plain,(
    ! [B_74,A_75] :
      ( k2_xboole_0(k1_tarski(B_74),k1_tarski(A_75)) = k2_tarski(B_74,A_75)
      | B_74 = A_75
      | B_74 = A_75 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_30])).

tff(c_26,plain,(
    ! [A_35,B_36] : k3_tarski(k2_tarski(A_35,B_36)) = k2_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_32,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_33,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_32])).

tff(c_251,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_33])).

tff(c_257,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) != k2_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_251,c_33])).

tff(c_258,plain,(
    k3_tarski(k1_tarski(k1_tarski('#skF_1'))) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_14,c_257])).

tff(c_430,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_258])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:26:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.33  
% 1.94/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.33  %$ r1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 2.24/1.33  
% 2.24/1.33  %Foreground sorts:
% 2.24/1.33  
% 2.24/1.33  
% 2.24/1.33  %Background operators:
% 2.24/1.33  
% 2.24/1.33  
% 2.24/1.33  %Foreground operators:
% 2.24/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.24/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.24/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.24/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.24/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.24/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.24/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.24/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.24/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.24/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.24/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.24/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.24/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.24/1.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.24/1.33  
% 2.24/1.35  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.24/1.35  tff(f_41, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.24/1.35  tff(f_43, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.24/1.35  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 2.24/1.35  tff(f_45, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.24/1.35  tff(f_51, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.24/1.35  tff(f_56, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 2.24/1.35  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.24/1.35  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.24/1.35  tff(f_61, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 2.24/1.35  tff(f_64, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 2.24/1.35  tff(c_14, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.24/1.35  tff(c_16, plain, (![A_15, B_16]: (k1_enumset1(A_15, A_15, B_16)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.24/1.35  tff(c_18, plain, (![A_17, B_18, C_19]: (k2_enumset1(A_17, A_17, B_18, C_19)=k1_enumset1(A_17, B_18, C_19))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.24/1.35  tff(c_272, plain, (![A_85, E_84, B_81, D_83, C_82]: (k2_xboole_0(k1_tarski(A_85), k2_enumset1(B_81, C_82, D_83, E_84))=k3_enumset1(A_85, B_81, C_82, D_83, E_84))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.24/1.35  tff(c_284, plain, (![A_86, A_87, B_88, C_89]: (k3_enumset1(A_86, A_87, A_87, B_88, C_89)=k2_xboole_0(k1_tarski(A_86), k1_enumset1(A_87, B_88, C_89)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_272])).
% 2.24/1.35  tff(c_20, plain, (![A_20, B_21, C_22, D_23]: (k3_enumset1(A_20, A_20, B_21, C_22, D_23)=k2_enumset1(A_20, B_21, C_22, D_23))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.24/1.35  tff(c_294, plain, (![A_87, B_88, C_89]: (k2_xboole_0(k1_tarski(A_87), k1_enumset1(A_87, B_88, C_89))=k2_enumset1(A_87, A_87, B_88, C_89))), inference(superposition, [status(thm), theory('equality')], [c_284, c_20])).
% 2.24/1.35  tff(c_323, plain, (![A_96, B_97, C_98]: (k2_xboole_0(k1_tarski(A_96), k1_enumset1(A_96, B_97, C_98))=k1_enumset1(A_96, B_97, C_98))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_294])).
% 2.24/1.35  tff(c_339, plain, (![A_15, B_16]: (k2_xboole_0(k1_tarski(A_15), k2_tarski(A_15, B_16))=k1_enumset1(A_15, A_15, B_16))), inference(superposition, [status(thm), theory('equality')], [c_16, c_323])).
% 2.24/1.35  tff(c_343, plain, (![A_99, B_100]: (k2_xboole_0(k1_tarski(A_99), k2_tarski(A_99, B_100))=k2_tarski(A_99, B_100))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_339])).
% 2.24/1.35  tff(c_352, plain, (![A_14]: (k2_xboole_0(k1_tarski(A_14), k1_tarski(A_14))=k2_tarski(A_14, A_14))), inference(superposition, [status(thm), theory('equality')], [c_14, c_343])).
% 2.24/1.35  tff(c_356, plain, (![A_101]: (k2_xboole_0(k1_tarski(A_101), k1_tarski(A_101))=k1_tarski(A_101))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_352])).
% 2.24/1.35  tff(c_86, plain, (![A_48, B_49]: (k3_tarski(k2_tarski(A_48, B_49))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.24/1.35  tff(c_95, plain, (![A_14]: (k3_tarski(k1_tarski(A_14))=k2_xboole_0(A_14, A_14))), inference(superposition, [status(thm), theory('equality')], [c_14, c_86])).
% 2.24/1.35  tff(c_365, plain, (![A_101]: (k3_tarski(k1_tarski(k1_tarski(A_101)))=k1_tarski(A_101))), inference(superposition, [status(thm), theory('equality')], [c_356, c_95])).
% 2.24/1.35  tff(c_28, plain, (![A_37, B_38]: (r1_xboole_0(k1_tarski(A_37), k1_tarski(B_38)) | B_38=A_37)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.24/1.35  tff(c_116, plain, (![A_53, B_54]: (k4_xboole_0(A_53, B_54)=A_53 | ~r1_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.24/1.35  tff(c_187, plain, (![A_64, B_65]: (k4_xboole_0(k1_tarski(A_64), k1_tarski(B_65))=k1_tarski(A_64) | B_65=A_64)), inference(resolution, [status(thm)], [c_28, c_116])).
% 2.24/1.35  tff(c_10, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.24/1.35  tff(c_217, plain, (![B_72, A_73]: (k5_xboole_0(k1_tarski(B_72), k1_tarski(A_73))=k2_xboole_0(k1_tarski(B_72), k1_tarski(A_73)) | B_72=A_73)), inference(superposition, [status(thm), theory('equality')], [c_187, c_10])).
% 2.24/1.35  tff(c_30, plain, (![A_39, B_40]: (k5_xboole_0(k1_tarski(A_39), k1_tarski(B_40))=k2_tarski(A_39, B_40) | B_40=A_39)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.24/1.35  tff(c_232, plain, (![B_74, A_75]: (k2_xboole_0(k1_tarski(B_74), k1_tarski(A_75))=k2_tarski(B_74, A_75) | B_74=A_75 | B_74=A_75)), inference(superposition, [status(thm), theory('equality')], [c_217, c_30])).
% 2.24/1.35  tff(c_26, plain, (![A_35, B_36]: (k3_tarski(k2_tarski(A_35, B_36))=k2_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.24/1.35  tff(c_32, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.24/1.35  tff(c_33, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_32])).
% 2.24/1.35  tff(c_251, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_232, c_33])).
% 2.24/1.35  tff(c_257, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))!=k2_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_251, c_251, c_33])).
% 2.24/1.35  tff(c_258, plain, (k3_tarski(k1_tarski(k1_tarski('#skF_1')))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_14, c_257])).
% 2.24/1.35  tff(c_430, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_365, c_258])).
% 2.24/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.35  
% 2.24/1.35  Inference rules
% 2.24/1.35  ----------------------
% 2.24/1.35  #Ref     : 0
% 2.24/1.35  #Sup     : 92
% 2.24/1.35  #Fact    : 0
% 2.24/1.35  #Define  : 0
% 2.24/1.35  #Split   : 0
% 2.24/1.35  #Chain   : 0
% 2.24/1.35  #Close   : 0
% 2.24/1.35  
% 2.24/1.35  Ordering : KBO
% 2.24/1.35  
% 2.24/1.35  Simplification rules
% 2.24/1.35  ----------------------
% 2.24/1.35  #Subsume      : 1
% 2.24/1.35  #Demod        : 25
% 2.24/1.35  #Tautology    : 72
% 2.24/1.35  #SimpNegUnit  : 0
% 2.24/1.35  #BackRed      : 2
% 2.24/1.35  
% 2.24/1.35  #Partial instantiations: 0
% 2.24/1.35  #Strategies tried      : 1
% 2.24/1.35  
% 2.24/1.35  Timing (in seconds)
% 2.24/1.35  ----------------------
% 2.24/1.35  Preprocessing        : 0.30
% 2.24/1.35  Parsing              : 0.16
% 2.24/1.35  CNF conversion       : 0.02
% 2.24/1.35  Main loop            : 0.21
% 2.24/1.35  Inferencing          : 0.09
% 2.24/1.35  Reduction            : 0.07
% 2.24/1.35  Demodulation         : 0.05
% 2.24/1.35  BG Simplification    : 0.02
% 2.24/1.35  Subsumption          : 0.02
% 2.24/1.35  Abstraction          : 0.02
% 2.24/1.35  MUC search           : 0.00
% 2.24/1.35  Cooper               : 0.00
% 2.24/1.35  Total                : 0.54
% 2.24/1.35  Index Insertion      : 0.00
% 2.24/1.35  Index Deletion       : 0.00
% 2.24/1.35  Index Matching       : 0.00
% 2.24/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
