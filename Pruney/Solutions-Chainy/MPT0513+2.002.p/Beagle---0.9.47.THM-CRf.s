%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:58 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   44 (  44 expanded)
%              Number of leaves         :   29 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   28 (  28 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_1

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

tff(f_28,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k3_xboole_0(B,k2_zfmisc_1(A,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).

tff(f_32,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_30,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_34,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_59,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_4,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_47,plain,(
    ! [A_41] :
      ( v1_relat_1(A_41)
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_51,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_47])).

tff(c_197,plain,(
    ! [B_55,A_56] :
      ( k3_xboole_0(B_55,k2_zfmisc_1(A_56,k2_relat_1(B_55))) = k7_relat_1(B_55,A_56)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_157,plain,(
    ! [A_49,B_50] : k5_xboole_0(A_49,k3_xboole_0(A_49,B_50)) = k4_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_52,plain,(
    ! [B_42,A_43] : k5_xboole_0(B_42,A_43) = k5_xboole_0(A_43,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_68,plain,(
    ! [A_43] : k5_xboole_0(k1_xboole_0,A_43) = A_43 ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_10])).

tff(c_164,plain,(
    ! [B_50] : k4_xboole_0(k1_xboole_0,B_50) = k3_xboole_0(k1_xboole_0,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_68])).

tff(c_173,plain,(
    ! [B_50] : k3_xboole_0(k1_xboole_0,B_50) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_164])).

tff(c_204,plain,(
    ! [A_56] :
      ( k7_relat_1(k1_xboole_0,A_56) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_173])).

tff(c_217,plain,(
    ! [A_56] : k7_relat_1(k1_xboole_0,A_56) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_204])).

tff(c_30,plain,(
    k7_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:05:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.19  
% 1.91/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.19  %$ v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_1
% 1.91/1.19  
% 1.91/1.19  %Foreground sorts:
% 1.91/1.19  
% 1.91/1.19  
% 1.91/1.19  %Background operators:
% 1.91/1.19  
% 1.91/1.19  
% 1.91/1.19  %Foreground operators:
% 1.91/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.91/1.19  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.91/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.91/1.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.91/1.19  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.91/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.91/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.91/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.91/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.91/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.19  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.91/1.19  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.91/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.91/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.91/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.91/1.19  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.91/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.91/1.19  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.91/1.19  
% 1.91/1.20  tff(f_28, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.91/1.20  tff(f_52, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.91/1.20  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k3_xboole_0(B, k2_zfmisc_1(A, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_relat_1)).
% 1.91/1.20  tff(f_32, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 1.91/1.20  tff(f_30, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.91/1.20  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 1.91/1.20  tff(f_34, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 1.91/1.20  tff(f_59, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 1.91/1.20  tff(c_4, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.91/1.20  tff(c_47, plain, (![A_41]: (v1_relat_1(A_41) | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.91/1.20  tff(c_51, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_47])).
% 1.91/1.20  tff(c_197, plain, (![B_55, A_56]: (k3_xboole_0(B_55, k2_zfmisc_1(A_56, k2_relat_1(B_55)))=k7_relat_1(B_55, A_56) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.91/1.20  tff(c_8, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.91/1.20  tff(c_157, plain, (![A_49, B_50]: (k5_xboole_0(A_49, k3_xboole_0(A_49, B_50))=k4_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.91/1.20  tff(c_52, plain, (![B_42, A_43]: (k5_xboole_0(B_42, A_43)=k5_xboole_0(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.91/1.20  tff(c_10, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.91/1.20  tff(c_68, plain, (![A_43]: (k5_xboole_0(k1_xboole_0, A_43)=A_43)), inference(superposition, [status(thm), theory('equality')], [c_52, c_10])).
% 1.91/1.20  tff(c_164, plain, (![B_50]: (k4_xboole_0(k1_xboole_0, B_50)=k3_xboole_0(k1_xboole_0, B_50))), inference(superposition, [status(thm), theory('equality')], [c_157, c_68])).
% 1.91/1.20  tff(c_173, plain, (![B_50]: (k3_xboole_0(k1_xboole_0, B_50)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_164])).
% 1.91/1.20  tff(c_204, plain, (![A_56]: (k7_relat_1(k1_xboole_0, A_56)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_197, c_173])).
% 1.91/1.20  tff(c_217, plain, (![A_56]: (k7_relat_1(k1_xboole_0, A_56)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_51, c_204])).
% 1.91/1.20  tff(c_30, plain, (k7_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.91/1.20  tff(c_223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_217, c_30])).
% 1.91/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.20  
% 1.91/1.20  Inference rules
% 1.91/1.20  ----------------------
% 1.91/1.20  #Ref     : 0
% 1.91/1.20  #Sup     : 43
% 1.91/1.20  #Fact    : 0
% 1.91/1.20  #Define  : 0
% 1.91/1.20  #Split   : 0
% 1.91/1.20  #Chain   : 0
% 1.91/1.20  #Close   : 0
% 1.91/1.20  
% 1.91/1.20  Ordering : KBO
% 1.91/1.20  
% 1.91/1.20  Simplification rules
% 1.91/1.20  ----------------------
% 1.91/1.20  #Subsume      : 0
% 1.91/1.20  #Demod        : 15
% 1.91/1.20  #Tautology    : 37
% 1.91/1.20  #SimpNegUnit  : 0
% 1.91/1.20  #BackRed      : 1
% 1.91/1.20  
% 1.91/1.20  #Partial instantiations: 0
% 1.91/1.20  #Strategies tried      : 1
% 1.91/1.20  
% 1.91/1.20  Timing (in seconds)
% 1.91/1.20  ----------------------
% 1.91/1.20  Preprocessing        : 0.30
% 1.91/1.20  Parsing              : 0.16
% 1.91/1.20  CNF conversion       : 0.02
% 1.91/1.20  Main loop            : 0.13
% 1.91/1.20  Inferencing          : 0.05
% 1.91/1.20  Reduction            : 0.04
% 1.91/1.20  Demodulation         : 0.03
% 1.91/1.20  BG Simplification    : 0.01
% 1.91/1.20  Subsumption          : 0.01
% 1.91/1.20  Abstraction          : 0.01
% 1.91/1.20  MUC search           : 0.00
% 1.91/1.20  Cooper               : 0.00
% 1.91/1.20  Total                : 0.46
% 1.91/1.20  Index Insertion      : 0.00
% 1.91/1.20  Index Deletion       : 0.00
% 1.91/1.20  Index Matching       : 0.00
% 1.91/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
