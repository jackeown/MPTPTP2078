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
% DateTime   : Thu Dec  3 09:49:49 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   56 (  89 expanded)
%              Number of leaves         :   31 (  45 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 (  94 expanded)
%              Number of equality atoms :   41 (  80 expanded)
%              Maximal formula depth    :   10 (   4 average)
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

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_10,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_72,plain,(
    ! [B_54,C_55] : r1_tarski(k1_tarski(B_54),k2_tarski(B_54,C_55)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_75,plain,(
    ! [A_12] : r1_tarski(k1_tarski(A_12),k1_tarski(A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_72])).

tff(c_144,plain,(
    ! [A_71,B_72] :
      ( k4_xboole_0(A_71,B_72) = k1_xboole_0
      | ~ r1_tarski(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_165,plain,(
    ! [A_12] : k4_xboole_0(k1_tarski(A_12),k1_tarski(A_12)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_75,c_144])).

tff(c_272,plain,(
    ! [A_88,B_89] : k5_xboole_0(A_88,k4_xboole_0(B_89,A_88)) = k2_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_287,plain,(
    ! [A_12] : k2_xboole_0(k1_tarski(A_12),k1_tarski(A_12)) = k5_xboole_0(k1_tarski(A_12),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_272])).

tff(c_319,plain,(
    ! [A_94] : k2_xboole_0(k1_tarski(A_94),k1_tarski(A_94)) = k1_tarski(A_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_287])).

tff(c_169,plain,(
    ! [A_73,B_74] : k3_tarski(k2_tarski(A_73,B_74)) = k2_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_178,plain,(
    ! [A_12] : k3_tarski(k1_tarski(A_12)) = k2_xboole_0(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_169])).

tff(c_325,plain,(
    ! [A_94] : k3_tarski(k1_tarski(k1_tarski(A_94))) = k1_tarski(A_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_178])).

tff(c_121,plain,(
    ! [A_65,B_66] :
      ( r1_xboole_0(k1_tarski(A_65),k1_tarski(B_66))
      | B_66 = A_65 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = A_8
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_423,plain,(
    ! [A_108,B_109] :
      ( k4_xboole_0(k1_tarski(A_108),k1_tarski(B_109)) = k1_tarski(A_108)
      | B_109 = A_108 ) ),
    inference(resolution,[status(thm)],[c_121,c_12])).

tff(c_16,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_526,plain,(
    ! [B_123,A_124] :
      ( k5_xboole_0(k1_tarski(B_123),k1_tarski(A_124)) = k2_xboole_0(k1_tarski(B_123),k1_tarski(A_124))
      | B_123 = A_124 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_16])).

tff(c_46,plain,(
    ! [A_47,B_48] :
      ( k5_xboole_0(k1_tarski(A_47),k1_tarski(B_48)) = k2_tarski(A_47,B_48)
      | B_48 = A_47 ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_541,plain,(
    ! [B_125,A_126] :
      ( k2_xboole_0(k1_tarski(B_125),k1_tarski(A_126)) = k2_tarski(B_125,A_126)
      | B_125 = A_126
      | B_125 = A_126 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_526,c_46])).

tff(c_42,plain,(
    ! [A_43,B_44] : k3_tarski(k2_tarski(A_43,B_44)) = k2_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_48,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_49,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_48])).

tff(c_571,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_49])).

tff(c_586,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) != k2_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_571,c_571,c_49])).

tff(c_589,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_178,c_18,c_586])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:30:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.34  
% 2.75/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.34  %$ r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.75/1.34  
% 2.75/1.34  %Foreground sorts:
% 2.75/1.34  
% 2.75/1.34  
% 2.75/1.34  %Background operators:
% 2.75/1.34  
% 2.75/1.34  
% 2.75/1.34  %Foreground operators:
% 2.75/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.75/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.75/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.75/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.75/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.75/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.75/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.75/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.75/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.75/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.75/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.75/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.75/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.75/1.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.75/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.75/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.75/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.75/1.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.75/1.34  
% 2.75/1.35  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.75/1.35  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.75/1.35  tff(f_70, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 2.75/1.35  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.75/1.35  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.75/1.35  tff(f_72, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.75/1.35  tff(f_77, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 2.75/1.35  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.75/1.35  tff(f_82, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 2.75/1.35  tff(f_85, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 2.75/1.35  tff(c_10, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.75/1.35  tff(c_18, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.75/1.35  tff(c_72, plain, (![B_54, C_55]: (r1_tarski(k1_tarski(B_54), k2_tarski(B_54, C_55)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.75/1.35  tff(c_75, plain, (![A_12]: (r1_tarski(k1_tarski(A_12), k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_72])).
% 2.75/1.35  tff(c_144, plain, (![A_71, B_72]: (k4_xboole_0(A_71, B_72)=k1_xboole_0 | ~r1_tarski(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.75/1.35  tff(c_165, plain, (![A_12]: (k4_xboole_0(k1_tarski(A_12), k1_tarski(A_12))=k1_xboole_0)), inference(resolution, [status(thm)], [c_75, c_144])).
% 2.75/1.35  tff(c_272, plain, (![A_88, B_89]: (k5_xboole_0(A_88, k4_xboole_0(B_89, A_88))=k2_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.75/1.35  tff(c_287, plain, (![A_12]: (k2_xboole_0(k1_tarski(A_12), k1_tarski(A_12))=k5_xboole_0(k1_tarski(A_12), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_165, c_272])).
% 2.75/1.35  tff(c_319, plain, (![A_94]: (k2_xboole_0(k1_tarski(A_94), k1_tarski(A_94))=k1_tarski(A_94))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_287])).
% 2.75/1.35  tff(c_169, plain, (![A_73, B_74]: (k3_tarski(k2_tarski(A_73, B_74))=k2_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.75/1.35  tff(c_178, plain, (![A_12]: (k3_tarski(k1_tarski(A_12))=k2_xboole_0(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_18, c_169])).
% 2.75/1.35  tff(c_325, plain, (![A_94]: (k3_tarski(k1_tarski(k1_tarski(A_94)))=k1_tarski(A_94))), inference(superposition, [status(thm), theory('equality')], [c_319, c_178])).
% 2.75/1.35  tff(c_121, plain, (![A_65, B_66]: (r1_xboole_0(k1_tarski(A_65), k1_tarski(B_66)) | B_66=A_65)), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.75/1.35  tff(c_12, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=A_8 | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.75/1.35  tff(c_423, plain, (![A_108, B_109]: (k4_xboole_0(k1_tarski(A_108), k1_tarski(B_109))=k1_tarski(A_108) | B_109=A_108)), inference(resolution, [status(thm)], [c_121, c_12])).
% 2.75/1.35  tff(c_16, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.75/1.35  tff(c_526, plain, (![B_123, A_124]: (k5_xboole_0(k1_tarski(B_123), k1_tarski(A_124))=k2_xboole_0(k1_tarski(B_123), k1_tarski(A_124)) | B_123=A_124)), inference(superposition, [status(thm), theory('equality')], [c_423, c_16])).
% 2.75/1.35  tff(c_46, plain, (![A_47, B_48]: (k5_xboole_0(k1_tarski(A_47), k1_tarski(B_48))=k2_tarski(A_47, B_48) | B_48=A_47)), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.75/1.35  tff(c_541, plain, (![B_125, A_126]: (k2_xboole_0(k1_tarski(B_125), k1_tarski(A_126))=k2_tarski(B_125, A_126) | B_125=A_126 | B_125=A_126)), inference(superposition, [status(thm), theory('equality')], [c_526, c_46])).
% 2.75/1.35  tff(c_42, plain, (![A_43, B_44]: (k3_tarski(k2_tarski(A_43, B_44))=k2_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.75/1.35  tff(c_48, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.75/1.35  tff(c_49, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_48])).
% 2.75/1.35  tff(c_571, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_541, c_49])).
% 2.75/1.35  tff(c_586, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))!=k2_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_571, c_571, c_49])).
% 2.75/1.35  tff(c_589, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_325, c_178, c_18, c_586])).
% 2.75/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.35  
% 2.75/1.35  Inference rules
% 2.75/1.35  ----------------------
% 2.75/1.35  #Ref     : 0
% 2.75/1.35  #Sup     : 126
% 2.75/1.35  #Fact    : 0
% 2.75/1.35  #Define  : 0
% 2.75/1.35  #Split   : 0
% 2.75/1.35  #Chain   : 0
% 2.75/1.35  #Close   : 0
% 2.75/1.35  
% 2.75/1.35  Ordering : KBO
% 2.75/1.35  
% 2.75/1.35  Simplification rules
% 2.75/1.35  ----------------------
% 2.75/1.35  #Subsume      : 0
% 2.75/1.35  #Demod        : 55
% 2.75/1.35  #Tautology    : 103
% 2.75/1.35  #SimpNegUnit  : 0
% 2.75/1.35  #BackRed      : 1
% 2.75/1.35  
% 2.75/1.35  #Partial instantiations: 0
% 2.75/1.35  #Strategies tried      : 1
% 2.75/1.35  
% 2.75/1.35  Timing (in seconds)
% 2.75/1.35  ----------------------
% 2.75/1.36  Preprocessing        : 0.33
% 2.75/1.36  Parsing              : 0.18
% 2.75/1.36  CNF conversion       : 0.02
% 2.75/1.36  Main loop            : 0.26
% 2.75/1.36  Inferencing          : 0.11
% 2.75/1.36  Reduction            : 0.09
% 2.75/1.36  Demodulation         : 0.07
% 2.75/1.36  BG Simplification    : 0.02
% 2.75/1.36  Subsumption          : 0.03
% 2.75/1.36  Abstraction          : 0.02
% 2.75/1.36  MUC search           : 0.00
% 2.75/1.36  Cooper               : 0.00
% 2.75/1.36  Total                : 0.62
% 2.75/1.36  Index Insertion      : 0.00
% 2.75/1.36  Index Deletion       : 0.00
% 2.75/1.36  Index Matching       : 0.00
% 2.75/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
