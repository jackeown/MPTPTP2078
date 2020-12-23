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
% DateTime   : Thu Dec  3 09:59:58 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
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
%$ v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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
     => k7_relat_1(B,A) = k3_xboole_0(B,k2_zfmisc_1(A,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).

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
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

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
      ( k3_xboole_0(B_59,k2_zfmisc_1(A_60,k2_relat_1(B_59))) = k7_relat_1(B_59,A_60)
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
      ( k7_relat_1('#skF_1',A_60) = '#skF_1'
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_203])).

tff(c_247,plain,(
    ! [A_60] : k7_relat_1('#skF_1',A_60) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_234])).

tff(c_32,plain,(
    k7_relat_1(k1_xboole_0,'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_58,plain,(
    k7_relat_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_32])).

tff(c_253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n003.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 14:12:12 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.19  
% 1.96/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.19  %$ v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.96/1.19  
% 1.96/1.19  %Foreground sorts:
% 1.96/1.19  
% 1.96/1.19  
% 1.96/1.19  %Background operators:
% 1.96/1.19  
% 1.96/1.19  
% 1.96/1.19  %Foreground operators:
% 1.96/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.96/1.19  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.96/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.96/1.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.96/1.19  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.96/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.96/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.96/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.96/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.96/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.19  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.96/1.19  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.96/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.96/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.96/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.96/1.19  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.96/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.96/1.19  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.96/1.19  
% 1.96/1.20  tff(f_33, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 1.96/1.20  tff(f_57, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.96/1.20  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k3_xboole_0(B, k2_zfmisc_1(A, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_relat_1)).
% 1.96/1.20  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.96/1.20  tff(f_37, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 1.96/1.20  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.96/1.20  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 1.96/1.20  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 1.96/1.20  tff(f_64, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 1.96/1.20  tff(c_6, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.96/1.20  tff(c_53, plain, (![A_42]: (v1_relat_1(A_42) | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.96/1.20  tff(c_57, plain, (v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_53])).
% 1.96/1.20  tff(c_227, plain, (![B_59, A_60]: (k3_xboole_0(B_59, k2_zfmisc_1(A_60, k2_relat_1(B_59)))=k7_relat_1(B_59, A_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.96/1.20  tff(c_42, plain, (![A_41]: (k1_xboole_0=A_41 | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.96/1.20  tff(c_46, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_6, c_42])).
% 1.96/1.20  tff(c_10, plain, (![A_6]: (k4_xboole_0(k1_xboole_0, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.96/1.20  tff(c_59, plain, (![A_6]: (k4_xboole_0('#skF_1', A_6)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_10])).
% 1.96/1.20  tff(c_187, plain, (![A_53, B_54]: (k5_xboole_0(A_53, k3_xboole_0(A_53, B_54))=k4_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.96/1.20  tff(c_12, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.96/1.20  tff(c_106, plain, (![A_47]: (k5_xboole_0(A_47, '#skF_1')=A_47)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_12])).
% 1.96/1.20  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.96/1.20  tff(c_112, plain, (![A_47]: (k5_xboole_0('#skF_1', A_47)=A_47)), inference(superposition, [status(thm), theory('equality')], [c_106, c_2])).
% 1.96/1.20  tff(c_194, plain, (![B_54]: (k4_xboole_0('#skF_1', B_54)=k3_xboole_0('#skF_1', B_54))), inference(superposition, [status(thm), theory('equality')], [c_187, c_112])).
% 1.96/1.20  tff(c_203, plain, (![B_54]: (k3_xboole_0('#skF_1', B_54)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_194])).
% 1.96/1.20  tff(c_234, plain, (![A_60]: (k7_relat_1('#skF_1', A_60)='#skF_1' | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_227, c_203])).
% 1.96/1.20  tff(c_247, plain, (![A_60]: (k7_relat_1('#skF_1', A_60)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_234])).
% 1.96/1.20  tff(c_32, plain, (k7_relat_1(k1_xboole_0, '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.96/1.20  tff(c_58, plain, (k7_relat_1('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_32])).
% 1.96/1.20  tff(c_253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_247, c_58])).
% 1.96/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.20  
% 1.96/1.20  Inference rules
% 1.96/1.20  ----------------------
% 1.96/1.20  #Ref     : 0
% 1.96/1.20  #Sup     : 49
% 1.96/1.20  #Fact    : 0
% 1.96/1.20  #Define  : 0
% 1.96/1.20  #Split   : 0
% 1.96/1.20  #Chain   : 0
% 1.96/1.20  #Close   : 0
% 1.96/1.20  
% 1.96/1.20  Ordering : KBO
% 1.96/1.20  
% 1.96/1.20  Simplification rules
% 1.96/1.20  ----------------------
% 1.96/1.20  #Subsume      : 0
% 1.96/1.20  #Demod        : 21
% 1.96/1.20  #Tautology    : 42
% 1.96/1.21  #SimpNegUnit  : 0
% 1.96/1.21  #BackRed      : 3
% 1.96/1.21  
% 1.96/1.21  #Partial instantiations: 0
% 1.96/1.21  #Strategies tried      : 1
% 1.96/1.21  
% 1.96/1.21  Timing (in seconds)
% 1.96/1.21  ----------------------
% 1.96/1.21  Preprocessing        : 0.32
% 1.96/1.21  Parsing              : 0.17
% 1.96/1.21  CNF conversion       : 0.02
% 1.96/1.21  Main loop            : 0.14
% 1.96/1.21  Inferencing          : 0.05
% 1.96/1.21  Reduction            : 0.05
% 1.96/1.21  Demodulation         : 0.04
% 1.96/1.21  BG Simplification    : 0.01
% 1.96/1.21  Subsumption          : 0.02
% 1.96/1.21  Abstraction          : 0.01
% 1.96/1.21  MUC search           : 0.00
% 1.96/1.21  Cooper               : 0.00
% 1.96/1.21  Total                : 0.49
% 1.96/1.21  Index Insertion      : 0.00
% 1.96/1.21  Index Deletion       : 0.00
% 1.96/1.21  Index Matching       : 0.00
% 1.96/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
