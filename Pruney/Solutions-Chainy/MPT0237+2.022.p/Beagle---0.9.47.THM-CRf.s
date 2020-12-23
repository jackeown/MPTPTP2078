%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:47 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   62 (  96 expanded)
%              Number of leaves         :   34 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :   53 (  99 expanded)
%              Number of equality atoms :   44 (  82 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_14,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_140,plain,(
    ! [A_64,B_65] :
      ( k3_xboole_0(A_64,B_65) = A_64
      | ~ r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_145,plain,(
    ! [A_66] : k3_xboole_0(k1_xboole_0,A_66) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_140])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_150,plain,(
    ! [A_66] : k3_xboole_0(A_66,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_2])).

tff(c_263,plain,(
    ! [A_76,B_77] : k5_xboole_0(A_76,k3_xboole_0(A_76,B_77)) = k4_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_272,plain,(
    ! [A_66] : k5_xboole_0(A_66,k1_xboole_0) = k4_xboole_0(A_66,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_263])).

tff(c_314,plain,(
    ! [A_79] : k4_xboole_0(A_79,k1_xboole_0) = A_79 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_272])).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_324,plain,(
    ! [A_79] : k4_xboole_0(A_79,A_79) = k3_xboole_0(A_79,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_12])).

tff(c_349,plain,(
    ! [A_81] : k4_xboole_0(A_81,A_81) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_324])).

tff(c_20,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_364,plain,(
    ! [A_81] : k5_xboole_0(A_81,k1_xboole_0) = k2_xboole_0(A_81,A_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_20])).

tff(c_378,plain,(
    ! [A_81] : k2_xboole_0(A_81,A_81) = A_81 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_364])).

tff(c_22,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_38,plain,(
    ! [A_47,B_48] :
      ( r1_xboole_0(k1_tarski(A_47),k1_tarski(B_48))
      | B_48 = A_47 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_135,plain,(
    ! [A_62,B_63] :
      ( k4_xboole_0(A_62,B_63) = A_62
      | ~ r1_xboole_0(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_559,plain,(
    ! [A_93,B_94] :
      ( k4_xboole_0(k1_tarski(A_93),k1_tarski(B_94)) = k1_tarski(A_93)
      | B_94 = A_93 ) ),
    inference(resolution,[status(thm)],[c_38,c_135])).

tff(c_811,plain,(
    ! [B_112,A_113] :
      ( k5_xboole_0(k1_tarski(B_112),k1_tarski(A_113)) = k2_xboole_0(k1_tarski(B_112),k1_tarski(A_113))
      | B_112 = A_113 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_559,c_20])).

tff(c_40,plain,(
    ! [A_49,B_50] :
      ( k5_xboole_0(k1_tarski(A_49),k1_tarski(B_50)) = k2_tarski(A_49,B_50)
      | B_50 = A_49 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1118,plain,(
    ! [B_135,A_136] :
      ( k2_xboole_0(k1_tarski(B_135),k1_tarski(A_136)) = k2_tarski(B_135,A_136)
      | B_135 = A_136
      | B_135 = A_136 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_811,c_40])).

tff(c_36,plain,(
    ! [A_45,B_46] : k3_tarski(k2_tarski(A_45,B_46)) = k2_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_42,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_43,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_42])).

tff(c_1139,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1118,c_43])).

tff(c_1143,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) != k2_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1139,c_1139,c_43])).

tff(c_1146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_22,c_1143])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:17:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.42  
% 2.95/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.42  %$ r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.95/1.42  
% 2.95/1.42  %Foreground sorts:
% 2.95/1.42  
% 2.95/1.42  
% 2.95/1.42  %Background operators:
% 2.95/1.42  
% 2.95/1.42  
% 2.95/1.42  %Foreground operators:
% 2.95/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.95/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.95/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.95/1.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.95/1.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.95/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.95/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.95/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.95/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.95/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.95/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.95/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.95/1.42  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.42  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.42  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.95/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.95/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.95/1.42  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.42  
% 3.21/1.43  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.21/1.43  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.21/1.43  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.21/1.43  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.21/1.43  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.21/1.43  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.21/1.43  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.21/1.43  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.21/1.43  tff(f_68, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 3.21/1.43  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.21/1.43  tff(f_73, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 3.21/1.43  tff(f_63, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.21/1.43  tff(f_76, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 3.21/1.43  tff(c_14, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.21/1.43  tff(c_10, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.21/1.43  tff(c_140, plain, (![A_64, B_65]: (k3_xboole_0(A_64, B_65)=A_64 | ~r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.21/1.43  tff(c_145, plain, (![A_66]: (k3_xboole_0(k1_xboole_0, A_66)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_140])).
% 3.21/1.43  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.21/1.43  tff(c_150, plain, (![A_66]: (k3_xboole_0(A_66, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_145, c_2])).
% 3.21/1.43  tff(c_263, plain, (![A_76, B_77]: (k5_xboole_0(A_76, k3_xboole_0(A_76, B_77))=k4_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.21/1.43  tff(c_272, plain, (![A_66]: (k5_xboole_0(A_66, k1_xboole_0)=k4_xboole_0(A_66, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_150, c_263])).
% 3.21/1.43  tff(c_314, plain, (![A_79]: (k4_xboole_0(A_79, k1_xboole_0)=A_79)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_272])).
% 3.21/1.43  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.21/1.43  tff(c_324, plain, (![A_79]: (k4_xboole_0(A_79, A_79)=k3_xboole_0(A_79, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_314, c_12])).
% 3.21/1.43  tff(c_349, plain, (![A_81]: (k4_xboole_0(A_81, A_81)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_150, c_324])).
% 3.21/1.43  tff(c_20, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.21/1.43  tff(c_364, plain, (![A_81]: (k5_xboole_0(A_81, k1_xboole_0)=k2_xboole_0(A_81, A_81))), inference(superposition, [status(thm), theory('equality')], [c_349, c_20])).
% 3.21/1.43  tff(c_378, plain, (![A_81]: (k2_xboole_0(A_81, A_81)=A_81)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_364])).
% 3.21/1.43  tff(c_22, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.21/1.43  tff(c_38, plain, (![A_47, B_48]: (r1_xboole_0(k1_tarski(A_47), k1_tarski(B_48)) | B_48=A_47)), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.21/1.43  tff(c_135, plain, (![A_62, B_63]: (k4_xboole_0(A_62, B_63)=A_62 | ~r1_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.21/1.43  tff(c_559, plain, (![A_93, B_94]: (k4_xboole_0(k1_tarski(A_93), k1_tarski(B_94))=k1_tarski(A_93) | B_94=A_93)), inference(resolution, [status(thm)], [c_38, c_135])).
% 3.21/1.43  tff(c_811, plain, (![B_112, A_113]: (k5_xboole_0(k1_tarski(B_112), k1_tarski(A_113))=k2_xboole_0(k1_tarski(B_112), k1_tarski(A_113)) | B_112=A_113)), inference(superposition, [status(thm), theory('equality')], [c_559, c_20])).
% 3.21/1.43  tff(c_40, plain, (![A_49, B_50]: (k5_xboole_0(k1_tarski(A_49), k1_tarski(B_50))=k2_tarski(A_49, B_50) | B_50=A_49)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.21/1.43  tff(c_1118, plain, (![B_135, A_136]: (k2_xboole_0(k1_tarski(B_135), k1_tarski(A_136))=k2_tarski(B_135, A_136) | B_135=A_136 | B_135=A_136)), inference(superposition, [status(thm), theory('equality')], [c_811, c_40])).
% 3.21/1.43  tff(c_36, plain, (![A_45, B_46]: (k3_tarski(k2_tarski(A_45, B_46))=k2_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.21/1.43  tff(c_42, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.21/1.43  tff(c_43, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_42])).
% 3.21/1.43  tff(c_1139, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1118, c_43])).
% 3.21/1.43  tff(c_1143, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))!=k2_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1139, c_1139, c_43])).
% 3.21/1.43  tff(c_1146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_378, c_22, c_1143])).
% 3.21/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.43  
% 3.21/1.43  Inference rules
% 3.21/1.43  ----------------------
% 3.21/1.43  #Ref     : 0
% 3.21/1.43  #Sup     : 256
% 3.21/1.43  #Fact    : 0
% 3.21/1.43  #Define  : 0
% 3.21/1.43  #Split   : 0
% 3.21/1.43  #Chain   : 0
% 3.21/1.43  #Close   : 0
% 3.21/1.43  
% 3.21/1.43  Ordering : KBO
% 3.21/1.43  
% 3.21/1.43  Simplification rules
% 3.21/1.43  ----------------------
% 3.21/1.43  #Subsume      : 9
% 3.21/1.43  #Demod        : 217
% 3.21/1.43  #Tautology    : 187
% 3.21/1.43  #SimpNegUnit  : 0
% 3.21/1.43  #BackRed      : 2
% 3.21/1.43  
% 3.21/1.43  #Partial instantiations: 0
% 3.21/1.43  #Strategies tried      : 1
% 3.21/1.43  
% 3.21/1.43  Timing (in seconds)
% 3.21/1.43  ----------------------
% 3.21/1.43  Preprocessing        : 0.31
% 3.21/1.43  Parsing              : 0.17
% 3.21/1.43  CNF conversion       : 0.02
% 3.21/1.43  Main loop            : 0.35
% 3.21/1.43  Inferencing          : 0.13
% 3.21/1.43  Reduction            : 0.14
% 3.21/1.43  Demodulation         : 0.11
% 3.21/1.43  BG Simplification    : 0.02
% 3.21/1.43  Subsumption          : 0.04
% 3.21/1.43  Abstraction          : 0.02
% 3.21/1.43  MUC search           : 0.00
% 3.21/1.43  Cooper               : 0.00
% 3.21/1.43  Total                : 0.70
% 3.21/1.43  Index Insertion      : 0.00
% 3.21/1.43  Index Deletion       : 0.00
% 3.21/1.43  Index Matching       : 0.00
% 3.21/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
