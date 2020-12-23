%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:03 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   43 (  43 expanded)
%              Number of leaves         :   28 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   26 (  26 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_48,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_47,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k3_xboole_0(B,k2_zfmisc_1(A,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_55,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_24,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_33,plain,(
    ! [A_32] : v1_relat_1(k6_relat_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_35,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_33])).

tff(c_206,plain,(
    ! [B_52,A_53] :
      ( k3_xboole_0(B_52,k2_zfmisc_1(A_53,k2_relat_1(B_52))) = k7_relat_1(B_52,A_53)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_157,plain,(
    ! [A_42,B_43] : k5_xboole_0(A_42,k3_xboole_0(A_42,B_43)) = k4_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_52,plain,(
    ! [B_35,A_36] : k5_xboole_0(B_35,A_36) = k5_xboole_0(A_36,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_68,plain,(
    ! [A_36] : k5_xboole_0(k1_xboole_0,A_36) = A_36 ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_8])).

tff(c_164,plain,(
    ! [B_43] : k4_xboole_0(k1_xboole_0,B_43) = k3_xboole_0(k1_xboole_0,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_68])).

tff(c_173,plain,(
    ! [B_43] : k3_xboole_0(k1_xboole_0,B_43) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_164])).

tff(c_213,plain,(
    ! [A_53] :
      ( k7_relat_1(k1_xboole_0,A_53) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_173])).

tff(c_226,plain,(
    ! [A_53] : k7_relat_1(k1_xboole_0,A_53) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_213])).

tff(c_28,plain,(
    k7_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:18:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.20  
% 1.91/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.20  %$ v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_1
% 1.91/1.20  
% 1.91/1.20  %Foreground sorts:
% 1.91/1.20  
% 1.91/1.20  
% 1.91/1.20  %Background operators:
% 1.91/1.20  
% 1.91/1.20  
% 1.91/1.20  %Foreground operators:
% 1.91/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.91/1.20  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.91/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.91/1.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.91/1.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.91/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.91/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.91/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.91/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.91/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.20  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.91/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.91/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.91/1.20  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.91/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.91/1.20  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.91/1.20  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.91/1.20  
% 2.00/1.21  tff(f_48, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.00/1.21  tff(f_47, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.00/1.21  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k3_xboole_0(B, k2_zfmisc_1(A, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_relat_1)).
% 2.00/1.21  tff(f_31, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.00/1.21  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.00/1.21  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 2.00/1.21  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.00/1.21  tff(f_55, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 2.00/1.21  tff(c_24, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.00/1.21  tff(c_33, plain, (![A_32]: (v1_relat_1(k6_relat_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.00/1.21  tff(c_35, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_33])).
% 2.00/1.21  tff(c_206, plain, (![B_52, A_53]: (k3_xboole_0(B_52, k2_zfmisc_1(A_53, k2_relat_1(B_52)))=k7_relat_1(B_52, A_53) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.00/1.21  tff(c_6, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.00/1.21  tff(c_157, plain, (![A_42, B_43]: (k5_xboole_0(A_42, k3_xboole_0(A_42, B_43))=k4_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.00/1.21  tff(c_52, plain, (![B_35, A_36]: (k5_xboole_0(B_35, A_36)=k5_xboole_0(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.00/1.21  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.00/1.21  tff(c_68, plain, (![A_36]: (k5_xboole_0(k1_xboole_0, A_36)=A_36)), inference(superposition, [status(thm), theory('equality')], [c_52, c_8])).
% 2.00/1.21  tff(c_164, plain, (![B_43]: (k4_xboole_0(k1_xboole_0, B_43)=k3_xboole_0(k1_xboole_0, B_43))), inference(superposition, [status(thm), theory('equality')], [c_157, c_68])).
% 2.00/1.21  tff(c_173, plain, (![B_43]: (k3_xboole_0(k1_xboole_0, B_43)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_164])).
% 2.00/1.21  tff(c_213, plain, (![A_53]: (k7_relat_1(k1_xboole_0, A_53)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_206, c_173])).
% 2.00/1.21  tff(c_226, plain, (![A_53]: (k7_relat_1(k1_xboole_0, A_53)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_35, c_213])).
% 2.00/1.21  tff(c_28, plain, (k7_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.00/1.21  tff(c_241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_226, c_28])).
% 2.00/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.21  
% 2.00/1.21  Inference rules
% 2.00/1.21  ----------------------
% 2.00/1.21  #Ref     : 0
% 2.00/1.21  #Sup     : 49
% 2.00/1.21  #Fact    : 0
% 2.00/1.21  #Define  : 0
% 2.00/1.21  #Split   : 0
% 2.00/1.21  #Chain   : 0
% 2.00/1.21  #Close   : 0
% 2.00/1.21  
% 2.00/1.21  Ordering : KBO
% 2.00/1.21  
% 2.00/1.21  Simplification rules
% 2.00/1.21  ----------------------
% 2.00/1.21  #Subsume      : 0
% 2.00/1.21  #Demod        : 15
% 2.00/1.21  #Tautology    : 43
% 2.00/1.21  #SimpNegUnit  : 0
% 2.00/1.21  #BackRed      : 1
% 2.00/1.21  
% 2.00/1.21  #Partial instantiations: 0
% 2.00/1.21  #Strategies tried      : 1
% 2.00/1.21  
% 2.00/1.21  Timing (in seconds)
% 2.00/1.21  ----------------------
% 2.00/1.21  Preprocessing        : 0.31
% 2.00/1.21  Parsing              : 0.17
% 2.00/1.21  CNF conversion       : 0.02
% 2.00/1.21  Main loop            : 0.14
% 2.00/1.21  Inferencing          : 0.05
% 2.00/1.21  Reduction            : 0.05
% 2.00/1.21  Demodulation         : 0.04
% 2.00/1.21  BG Simplification    : 0.01
% 2.00/1.21  Subsumption          : 0.02
% 2.00/1.21  Abstraction          : 0.01
% 2.00/1.21  MUC search           : 0.00
% 2.00/1.21  Cooper               : 0.00
% 2.00/1.21  Total                : 0.47
% 2.00/1.21  Index Insertion      : 0.00
% 2.00/1.21  Index Deletion       : 0.00
% 2.00/1.21  Index Matching       : 0.00
% 2.00/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
