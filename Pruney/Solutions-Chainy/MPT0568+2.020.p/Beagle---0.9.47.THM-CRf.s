%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:23 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   40 (  40 expanded)
%              Number of leaves         :   27 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   28 (  28 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

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

tff(f_32,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_57,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_39,plain,(
    ! [A_36] :
      ( v1_relat_1(A_36)
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_43,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_39])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_70,plain,(
    ! [B_44,A_45] :
      ( r1_tarski(k10_relat_1(B_44,A_45),k1_relat_1(B_44))
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_76,plain,(
    ! [A_45] :
      ( r1_tarski(k10_relat_1(k1_xboole_0,A_45),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_70])).

tff(c_80,plain,(
    ! [A_46] : r1_tarski(k10_relat_1(k1_xboole_0,A_46),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_76])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_83,plain,(
    ! [A_46] : k3_xboole_0(k10_relat_1(k1_xboole_0,A_46),k1_xboole_0) = k10_relat_1(k1_xboole_0,A_46) ),
    inference(resolution,[status(thm)],[c_80,c_4])).

tff(c_85,plain,(
    ! [A_46] : k10_relat_1(k1_xboole_0,A_46) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_83])).

tff(c_30,plain,(
    k10_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_89,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:36:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.21  
% 1.87/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.21  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.87/1.21  
% 1.87/1.21  %Foreground sorts:
% 1.87/1.21  
% 1.87/1.21  
% 1.87/1.21  %Background operators:
% 1.87/1.21  
% 1.87/1.21  
% 1.87/1.21  %Foreground operators:
% 1.87/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.87/1.21  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.87/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.87/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.87/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.87/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.87/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.21  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.87/1.21  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.87/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.21  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.87/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.87/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.87/1.21  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.87/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.87/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.87/1.21  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.87/1.21  
% 1.92/1.22  tff(f_32, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.92/1.22  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.92/1.22  tff(f_50, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.92/1.22  tff(f_57, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.92/1.22  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 1.92/1.22  tff(f_30, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.92/1.22  tff(f_60, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 1.92/1.22  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.92/1.22  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.92/1.22  tff(c_39, plain, (![A_36]: (v1_relat_1(A_36) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.92/1.22  tff(c_43, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_39])).
% 1.92/1.22  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.92/1.22  tff(c_70, plain, (![B_44, A_45]: (r1_tarski(k10_relat_1(B_44, A_45), k1_relat_1(B_44)) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.92/1.22  tff(c_76, plain, (![A_45]: (r1_tarski(k10_relat_1(k1_xboole_0, A_45), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_70])).
% 1.92/1.22  tff(c_80, plain, (![A_46]: (r1_tarski(k10_relat_1(k1_xboole_0, A_46), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_76])).
% 1.92/1.22  tff(c_4, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.92/1.22  tff(c_83, plain, (![A_46]: (k3_xboole_0(k10_relat_1(k1_xboole_0, A_46), k1_xboole_0)=k10_relat_1(k1_xboole_0, A_46))), inference(resolution, [status(thm)], [c_80, c_4])).
% 1.92/1.22  tff(c_85, plain, (![A_46]: (k10_relat_1(k1_xboole_0, A_46)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_83])).
% 1.92/1.22  tff(c_30, plain, (k10_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.92/1.22  tff(c_89, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_30])).
% 1.92/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.22  
% 1.92/1.22  Inference rules
% 1.92/1.22  ----------------------
% 1.93/1.22  #Ref     : 0
% 1.93/1.22  #Sup     : 14
% 1.93/1.22  #Fact    : 0
% 1.93/1.22  #Define  : 0
% 1.93/1.22  #Split   : 0
% 1.93/1.22  #Chain   : 0
% 1.93/1.22  #Close   : 0
% 1.93/1.22  
% 1.93/1.22  Ordering : KBO
% 1.93/1.22  
% 1.93/1.22  Simplification rules
% 1.93/1.22  ----------------------
% 1.93/1.22  #Subsume      : 0
% 1.93/1.22  #Demod        : 4
% 1.93/1.22  #Tautology    : 10
% 1.93/1.22  #SimpNegUnit  : 0
% 1.93/1.22  #BackRed      : 2
% 1.93/1.22  
% 1.93/1.22  #Partial instantiations: 0
% 1.93/1.22  #Strategies tried      : 1
% 1.93/1.22  
% 1.93/1.22  Timing (in seconds)
% 1.93/1.22  ----------------------
% 1.93/1.23  Preprocessing        : 0.32
% 1.93/1.23  Parsing              : 0.18
% 1.93/1.23  CNF conversion       : 0.02
% 1.93/1.23  Main loop            : 0.09
% 1.93/1.23  Inferencing          : 0.03
% 1.93/1.23  Reduction            : 0.03
% 1.93/1.23  Demodulation         : 0.02
% 1.93/1.23  BG Simplification    : 0.01
% 1.93/1.23  Subsumption          : 0.01
% 1.93/1.23  Abstraction          : 0.01
% 1.93/1.23  MUC search           : 0.00
% 1.93/1.23  Cooper               : 0.00
% 1.93/1.23  Total                : 0.43
% 1.93/1.23  Index Insertion      : 0.00
% 1.93/1.23  Index Deletion       : 0.00
% 1.93/1.23  Index Matching       : 0.00
% 1.93/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
