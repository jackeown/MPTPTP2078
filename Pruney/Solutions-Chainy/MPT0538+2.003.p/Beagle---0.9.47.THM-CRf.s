%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:23 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   51 (  73 expanded)
%              Number of leaves         :   31 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   36 (  66 expanded)
%              Number of equality atoms :   23 (  35 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_33,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k3_xboole_0(B,k2_zfmisc_1(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_64,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_6,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_53,plain,(
    ! [A_42] :
      ( v1_relat_1(A_42)
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_57,plain,(
    v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_53])).

tff(c_227,plain,(
    ! [B_59,A_60] :
      ( k3_xboole_0(B_59,k2_zfmisc_1(k1_relat_1(B_59),A_60)) = k8_relat_1(A_60,B_59)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_42,plain,(
    ! [A_41] :
      ( k1_xboole_0 = A_41
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_42])).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_59,plain,(
    ! [A_6] : k4_xboole_0('#skF_1',A_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_10])).

tff(c_187,plain,(
    ! [A_53,B_54] : k5_xboole_0(A_53,k3_xboole_0(A_53,B_54)) = k4_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_106,plain,(
    ! [A_47] : k5_xboole_0(A_47,'#skF_1') = A_47 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_112,plain,(
    ! [A_47] : k5_xboole_0('#skF_1',A_47) = A_47 ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_2])).

tff(c_194,plain,(
    ! [B_54] : k4_xboole_0('#skF_1',B_54) = k3_xboole_0('#skF_1',B_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_112])).

tff(c_203,plain,(
    ! [B_54] : k3_xboole_0('#skF_1',B_54) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_194])).

tff(c_234,plain,(
    ! [A_60] :
      ( k8_relat_1(A_60,'#skF_1') = '#skF_1'
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_203])).

tff(c_247,plain,(
    ! [A_60] : k8_relat_1(A_60,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_234])).

tff(c_32,plain,(
    k8_relat_1('#skF_2',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_58,plain,(
    k8_relat_1('#skF_2','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_32])).

tff(c_253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:41:55 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.27  
% 1.94/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.28  %$ v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.94/1.28  
% 1.94/1.28  %Foreground sorts:
% 1.94/1.28  
% 1.94/1.28  
% 1.94/1.28  %Background operators:
% 1.94/1.28  
% 1.94/1.28  
% 1.94/1.28  %Foreground operators:
% 1.94/1.28  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.94/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.94/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.94/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.94/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.94/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.94/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.94/1.28  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.28  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.94/1.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.94/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.94/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.94/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.94/1.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.94/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.94/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.94/1.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.94/1.28  
% 1.94/1.29  tff(f_33, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 1.94/1.29  tff(f_57, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.94/1.29  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k3_xboole_0(B, k2_zfmisc_1(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t124_relat_1)).
% 1.94/1.29  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.94/1.29  tff(f_37, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 1.94/1.29  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.94/1.29  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 1.94/1.29  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 1.94/1.29  tff(f_64, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_relat_1)).
% 1.94/1.29  tff(c_6, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.94/1.29  tff(c_53, plain, (![A_42]: (v1_relat_1(A_42) | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.94/1.29  tff(c_57, plain, (v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_53])).
% 1.94/1.29  tff(c_227, plain, (![B_59, A_60]: (k3_xboole_0(B_59, k2_zfmisc_1(k1_relat_1(B_59), A_60))=k8_relat_1(A_60, B_59) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.94/1.29  tff(c_42, plain, (![A_41]: (k1_xboole_0=A_41 | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.94/1.29  tff(c_46, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_6, c_42])).
% 1.94/1.29  tff(c_10, plain, (![A_6]: (k4_xboole_0(k1_xboole_0, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.94/1.29  tff(c_59, plain, (![A_6]: (k4_xboole_0('#skF_1', A_6)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_10])).
% 1.94/1.29  tff(c_187, plain, (![A_53, B_54]: (k5_xboole_0(A_53, k3_xboole_0(A_53, B_54))=k4_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.94/1.29  tff(c_12, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.94/1.29  tff(c_106, plain, (![A_47]: (k5_xboole_0(A_47, '#skF_1')=A_47)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_12])).
% 1.94/1.29  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.94/1.29  tff(c_112, plain, (![A_47]: (k5_xboole_0('#skF_1', A_47)=A_47)), inference(superposition, [status(thm), theory('equality')], [c_106, c_2])).
% 1.94/1.29  tff(c_194, plain, (![B_54]: (k4_xboole_0('#skF_1', B_54)=k3_xboole_0('#skF_1', B_54))), inference(superposition, [status(thm), theory('equality')], [c_187, c_112])).
% 1.94/1.29  tff(c_203, plain, (![B_54]: (k3_xboole_0('#skF_1', B_54)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_194])).
% 1.94/1.29  tff(c_234, plain, (![A_60]: (k8_relat_1(A_60, '#skF_1')='#skF_1' | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_227, c_203])).
% 1.94/1.29  tff(c_247, plain, (![A_60]: (k8_relat_1(A_60, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_234])).
% 1.94/1.29  tff(c_32, plain, (k8_relat_1('#skF_2', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.94/1.29  tff(c_58, plain, (k8_relat_1('#skF_2', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_32])).
% 1.94/1.29  tff(c_253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_247, c_58])).
% 1.94/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.29  
% 1.94/1.29  Inference rules
% 1.94/1.29  ----------------------
% 1.94/1.29  #Ref     : 0
% 1.94/1.29  #Sup     : 49
% 1.94/1.29  #Fact    : 0
% 1.94/1.29  #Define  : 0
% 1.94/1.29  #Split   : 0
% 1.94/1.29  #Chain   : 0
% 1.94/1.29  #Close   : 0
% 1.94/1.29  
% 1.94/1.29  Ordering : KBO
% 1.94/1.29  
% 1.94/1.29  Simplification rules
% 1.94/1.29  ----------------------
% 1.94/1.29  #Subsume      : 0
% 1.94/1.29  #Demod        : 21
% 1.94/1.29  #Tautology    : 42
% 1.94/1.29  #SimpNegUnit  : 0
% 1.94/1.29  #BackRed      : 3
% 1.94/1.29  
% 1.94/1.29  #Partial instantiations: 0
% 1.94/1.29  #Strategies tried      : 1
% 1.94/1.29  
% 1.94/1.29  Timing (in seconds)
% 1.94/1.29  ----------------------
% 1.94/1.29  Preprocessing        : 0.29
% 1.94/1.29  Parsing              : 0.15
% 1.94/1.29  CNF conversion       : 0.02
% 1.94/1.29  Main loop            : 0.21
% 1.94/1.29  Inferencing          : 0.08
% 1.94/1.29  Reduction            : 0.07
% 1.94/1.29  Demodulation         : 0.06
% 1.94/1.29  BG Simplification    : 0.01
% 1.94/1.29  Subsumption          : 0.02
% 1.94/1.29  Abstraction          : 0.01
% 1.94/1.29  MUC search           : 0.00
% 1.94/1.29  Cooper               : 0.00
% 1.94/1.29  Total                : 0.53
% 1.94/1.29  Index Insertion      : 0.00
% 1.94/1.29  Index Deletion       : 0.00
% 1.94/1.29  Index Matching       : 0.00
% 1.94/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
