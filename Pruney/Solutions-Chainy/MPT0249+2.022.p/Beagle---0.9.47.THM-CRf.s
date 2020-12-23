%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:26 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 140 expanded)
%              Number of leaves         :   30 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :   59 ( 187 expanded)
%              Number of equality atoms :   48 ( 160 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_44,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_14] : k5_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_274,plain,(
    ! [A_73,B_74] : k5_xboole_0(k5_xboole_0(A_73,B_74),k2_xboole_0(A_73,B_74)) = k3_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_310,plain,(
    ! [A_3] : k5_xboole_0(k5_xboole_0(A_3,A_3),A_3) = k3_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_274])).

tff(c_317,plain,(
    ! [A_3] : k5_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14,c_310])).

tff(c_443,plain,(
    ! [A_78,B_79,C_80] : k5_xboole_0(k5_xboole_0(A_78,B_79),C_80) = k5_xboole_0(A_78,k5_xboole_0(B_79,C_80)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_523,plain,(
    ! [A_14,C_80] : k5_xboole_0(A_14,k5_xboole_0(A_14,C_80)) = k5_xboole_0(k1_xboole_0,C_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_443])).

tff(c_538,plain,(
    ! [A_81,C_82] : k5_xboole_0(A_81,k5_xboole_0(A_81,C_82)) = C_82 ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_523])).

tff(c_593,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_538])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_46,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_86,plain,(
    ! [A_54,B_55] : r1_tarski(A_54,k2_xboole_0(A_54,B_55)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_89,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_86])).

tff(c_164,plain,(
    ! [B_66,A_67] :
      ( k1_tarski(B_66) = A_67
      | k1_xboole_0 = A_67
      | ~ r1_tarski(A_67,k1_tarski(B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_171,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_89,c_164])).

tff(c_182,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_171])).

tff(c_188,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_46])).

tff(c_295,plain,(
    k5_xboole_0(k5_xboole_0('#skF_2','#skF_3'),'#skF_2') = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_274])).

tff(c_316,plain,(
    k5_xboole_0('#skF_2',k5_xboole_0('#skF_3','#skF_2')) = k3_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_295])).

tff(c_612,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_316])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    ! [B_46,A_45] :
      ( k1_tarski(B_46) = A_45
      | k1_xboole_0 = A_45
      | ~ r1_tarski(A_45,k1_tarski(B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_193,plain,(
    ! [A_45] :
      ( k1_tarski('#skF_1') = A_45
      | k1_xboole_0 = A_45
      | ~ r1_tarski(A_45,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_32])).

tff(c_215,plain,(
    ! [A_68] :
      ( A_68 = '#skF_2'
      | k1_xboole_0 = A_68
      | ~ r1_tarski(A_68,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_193])).

tff(c_231,plain,(
    ! [B_8] :
      ( k3_xboole_0('#skF_2',B_8) = '#skF_2'
      | k3_xboole_0('#skF_2',B_8) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_215])).

tff(c_701,plain,
    ( k3_xboole_0('#skF_2','#skF_3') = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_612,c_231])).

tff(c_710,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_701])).

tff(c_712,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_44,c_710])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:06:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.32  
% 2.27/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.32  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.59/1.32  
% 2.59/1.32  %Foreground sorts:
% 2.59/1.32  
% 2.59/1.32  
% 2.59/1.32  %Background operators:
% 2.59/1.32  
% 2.59/1.32  
% 2.59/1.32  %Foreground operators:
% 2.59/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.59/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.59/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.59/1.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.59/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.59/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.59/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.59/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.59/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.59/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.59/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.59/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.59/1.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.59/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.59/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.59/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.59/1.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.59/1.32  
% 2.59/1.33  tff(f_76, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 2.59/1.33  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 2.59/1.33  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.59/1.33  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.59/1.33  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.59/1.33  tff(f_41, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 2.59/1.33  tff(f_37, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 2.59/1.33  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.59/1.33  tff(f_61, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.59/1.33  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.59/1.33  tff(c_40, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.59/1.33  tff(c_44, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.59/1.33  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.59/1.33  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.59/1.33  tff(c_14, plain, (![A_14]: (k5_xboole_0(A_14, A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.59/1.33  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.59/1.33  tff(c_274, plain, (![A_73, B_74]: (k5_xboole_0(k5_xboole_0(A_73, B_74), k2_xboole_0(A_73, B_74))=k3_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.59/1.33  tff(c_310, plain, (![A_3]: (k5_xboole_0(k5_xboole_0(A_3, A_3), A_3)=k3_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_274])).
% 2.59/1.33  tff(c_317, plain, (![A_3]: (k5_xboole_0(k1_xboole_0, A_3)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14, c_310])).
% 2.59/1.33  tff(c_443, plain, (![A_78, B_79, C_80]: (k5_xboole_0(k5_xboole_0(A_78, B_79), C_80)=k5_xboole_0(A_78, k5_xboole_0(B_79, C_80)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.59/1.33  tff(c_523, plain, (![A_14, C_80]: (k5_xboole_0(A_14, k5_xboole_0(A_14, C_80))=k5_xboole_0(k1_xboole_0, C_80))), inference(superposition, [status(thm), theory('equality')], [c_14, c_443])).
% 2.59/1.33  tff(c_538, plain, (![A_81, C_82]: (k5_xboole_0(A_81, k5_xboole_0(A_81, C_82))=C_82)), inference(demodulation, [status(thm), theory('equality')], [c_317, c_523])).
% 2.59/1.33  tff(c_593, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_538])).
% 2.59/1.33  tff(c_42, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.59/1.33  tff(c_46, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.59/1.33  tff(c_86, plain, (![A_54, B_55]: (r1_tarski(A_54, k2_xboole_0(A_54, B_55)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.59/1.33  tff(c_89, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_86])).
% 2.59/1.33  tff(c_164, plain, (![B_66, A_67]: (k1_tarski(B_66)=A_67 | k1_xboole_0=A_67 | ~r1_tarski(A_67, k1_tarski(B_66)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.59/1.33  tff(c_171, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_89, c_164])).
% 2.59/1.33  tff(c_182, plain, (k1_tarski('#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_42, c_171])).
% 2.59/1.33  tff(c_188, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_182, c_46])).
% 2.59/1.33  tff(c_295, plain, (k5_xboole_0(k5_xboole_0('#skF_2', '#skF_3'), '#skF_2')=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_188, c_274])).
% 2.59/1.33  tff(c_316, plain, (k5_xboole_0('#skF_2', k5_xboole_0('#skF_3', '#skF_2'))=k3_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_295])).
% 2.59/1.33  tff(c_612, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_593, c_316])).
% 2.59/1.33  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.59/1.33  tff(c_32, plain, (![B_46, A_45]: (k1_tarski(B_46)=A_45 | k1_xboole_0=A_45 | ~r1_tarski(A_45, k1_tarski(B_46)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.59/1.33  tff(c_193, plain, (![A_45]: (k1_tarski('#skF_1')=A_45 | k1_xboole_0=A_45 | ~r1_tarski(A_45, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_182, c_32])).
% 2.59/1.33  tff(c_215, plain, (![A_68]: (A_68='#skF_2' | k1_xboole_0=A_68 | ~r1_tarski(A_68, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_193])).
% 2.59/1.33  tff(c_231, plain, (![B_8]: (k3_xboole_0('#skF_2', B_8)='#skF_2' | k3_xboole_0('#skF_2', B_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_215])).
% 2.59/1.33  tff(c_701, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2' | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_612, c_231])).
% 2.59/1.33  tff(c_710, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_612, c_701])).
% 2.59/1.33  tff(c_712, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_44, c_710])).
% 2.59/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.33  
% 2.59/1.33  Inference rules
% 2.59/1.33  ----------------------
% 2.59/1.33  #Ref     : 0
% 2.59/1.33  #Sup     : 165
% 2.59/1.33  #Fact    : 1
% 2.59/1.33  #Define  : 0
% 2.59/1.33  #Split   : 0
% 2.59/1.33  #Chain   : 0
% 2.59/1.33  #Close   : 0
% 2.59/1.33  
% 2.59/1.33  Ordering : KBO
% 2.59/1.33  
% 2.59/1.33  Simplification rules
% 2.59/1.33  ----------------------
% 2.59/1.33  #Subsume      : 2
% 2.59/1.33  #Demod        : 62
% 2.59/1.33  #Tautology    : 102
% 2.59/1.33  #SimpNegUnit  : 6
% 2.59/1.33  #BackRed      : 3
% 2.59/1.33  
% 2.59/1.33  #Partial instantiations: 0
% 2.59/1.33  #Strategies tried      : 1
% 2.59/1.33  
% 2.59/1.33  Timing (in seconds)
% 2.59/1.33  ----------------------
% 2.59/1.34  Preprocessing        : 0.30
% 2.59/1.34  Parsing              : 0.16
% 2.59/1.34  CNF conversion       : 0.02
% 2.59/1.34  Main loop            : 0.29
% 2.59/1.34  Inferencing          : 0.10
% 2.59/1.34  Reduction            : 0.11
% 2.59/1.34  Demodulation         : 0.09
% 2.59/1.34  BG Simplification    : 0.02
% 2.59/1.34  Subsumption          : 0.04
% 2.59/1.34  Abstraction          : 0.02
% 2.59/1.34  MUC search           : 0.00
% 2.59/1.34  Cooper               : 0.00
% 2.59/1.34  Total                : 0.61
% 2.59/1.34  Index Insertion      : 0.00
% 2.59/1.34  Index Deletion       : 0.00
% 2.59/1.34  Index Matching       : 0.00
% 2.59/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
