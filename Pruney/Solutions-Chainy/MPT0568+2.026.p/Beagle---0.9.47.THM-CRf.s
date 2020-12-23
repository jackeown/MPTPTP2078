%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:24 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   40 (  45 expanded)
%              Number of leaves         :   23 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   39 (  49 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_50,axiom,(
    ! [A,B,C,D] : v1_relat_1(k2_tarski(k4_tarski(A,B),k4_tarski(C,D))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).

tff(f_57,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_38,plain,(
    ! [B_24,A_25] :
      ( v1_relat_1(B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(A_25))
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_42,plain,(
    ! [A_4] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_38])).

tff(c_43,plain,(
    ! [A_4] : ~ v1_relat_1(A_4) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13,D_14] : v1_relat_1(k2_tarski(k4_tarski(A_11,B_12),k4_tarski(C_13,D_14))) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_56,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_16])).

tff(c_57,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_81,plain,(
    ! [B_31,A_32] :
      ( r1_tarski(k10_relat_1(B_31,A_32),k1_relat_1(B_31))
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_86,plain,(
    ! [A_32] :
      ( r1_tarski(k10_relat_1(k1_xboole_0,A_32),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_81])).

tff(c_94,plain,(
    ! [A_36] : r1_tarski(k10_relat_1(k1_xboole_0,A_36),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_86])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_58,plain,(
    ! [B_28,A_29] :
      ( B_28 = A_29
      | ~ r1_tarski(B_28,A_29)
      | ~ r1_tarski(A_29,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_67,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_58])).

tff(c_100,plain,(
    ! [A_36] : k10_relat_1(k1_xboole_0,A_36) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_94,c_67])).

tff(c_24,plain,(
    k10_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:07:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.18  
% 1.74/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.18  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.74/1.18  
% 1.74/1.18  %Foreground sorts:
% 1.74/1.18  
% 1.74/1.18  
% 1.74/1.18  %Background operators:
% 1.74/1.18  
% 1.74/1.18  
% 1.74/1.18  %Foreground operators:
% 1.74/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.74/1.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.74/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.74/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.74/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.74/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.74/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.74/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.74/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.18  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.74/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.74/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.74/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.74/1.18  
% 1.74/1.19  tff(f_35, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 1.74/1.19  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.74/1.19  tff(f_50, axiom, (![A, B, C, D]: v1_relat_1(k2_tarski(k4_tarski(A, B), k4_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_relat_1)).
% 1.74/1.19  tff(f_57, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.74/1.19  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 1.74/1.19  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.74/1.19  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.74/1.19  tff(f_60, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 1.74/1.19  tff(c_10, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.74/1.19  tff(c_38, plain, (![B_24, A_25]: (v1_relat_1(B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(A_25)) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.74/1.19  tff(c_42, plain, (![A_4]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_4))), inference(resolution, [status(thm)], [c_10, c_38])).
% 1.74/1.19  tff(c_43, plain, (![A_4]: (~v1_relat_1(A_4))), inference(splitLeft, [status(thm)], [c_42])).
% 1.74/1.19  tff(c_16, plain, (![A_11, B_12, C_13, D_14]: (v1_relat_1(k2_tarski(k4_tarski(A_11, B_12), k4_tarski(C_13, D_14))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.74/1.19  tff(c_56, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43, c_16])).
% 1.74/1.19  tff(c_57, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_42])).
% 1.74/1.19  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.74/1.19  tff(c_81, plain, (![B_31, A_32]: (r1_tarski(k10_relat_1(B_31, A_32), k1_relat_1(B_31)) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.74/1.19  tff(c_86, plain, (![A_32]: (r1_tarski(k10_relat_1(k1_xboole_0, A_32), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_81])).
% 1.74/1.19  tff(c_94, plain, (![A_36]: (r1_tarski(k10_relat_1(k1_xboole_0, A_36), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_86])).
% 1.74/1.19  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.74/1.19  tff(c_58, plain, (![B_28, A_29]: (B_28=A_29 | ~r1_tarski(B_28, A_29) | ~r1_tarski(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.74/1.19  tff(c_67, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_58])).
% 1.74/1.19  tff(c_100, plain, (![A_36]: (k10_relat_1(k1_xboole_0, A_36)=k1_xboole_0)), inference(resolution, [status(thm)], [c_94, c_67])).
% 1.74/1.19  tff(c_24, plain, (k10_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.74/1.19  tff(c_108, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_24])).
% 1.74/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.19  
% 1.74/1.19  Inference rules
% 1.74/1.19  ----------------------
% 1.74/1.19  #Ref     : 0
% 1.74/1.19  #Sup     : 16
% 1.74/1.19  #Fact    : 0
% 1.74/1.19  #Define  : 0
% 1.74/1.19  #Split   : 1
% 1.74/1.19  #Chain   : 0
% 1.74/1.19  #Close   : 0
% 1.74/1.19  
% 1.74/1.19  Ordering : KBO
% 1.74/1.19  
% 1.74/1.19  Simplification rules
% 1.74/1.19  ----------------------
% 1.74/1.19  #Subsume      : 1
% 1.74/1.19  #Demod        : 8
% 1.74/1.19  #Tautology    : 10
% 1.74/1.19  #SimpNegUnit  : 2
% 1.74/1.19  #BackRed      : 3
% 1.74/1.19  
% 1.74/1.19  #Partial instantiations: 0
% 1.74/1.19  #Strategies tried      : 1
% 1.74/1.19  
% 1.74/1.19  Timing (in seconds)
% 1.74/1.19  ----------------------
% 1.74/1.20  Preprocessing        : 0.28
% 1.74/1.20  Parsing              : 0.15
% 1.74/1.20  CNF conversion       : 0.02
% 1.74/1.20  Main loop            : 0.14
% 1.74/1.20  Inferencing          : 0.05
% 1.74/1.20  Reduction            : 0.04
% 1.74/1.20  Demodulation         : 0.03
% 1.74/1.20  BG Simplification    : 0.01
% 1.74/1.20  Subsumption          : 0.02
% 1.74/1.20  Abstraction          : 0.01
% 1.74/1.20  MUC search           : 0.00
% 1.74/1.20  Cooper               : 0.00
% 1.74/1.20  Total                : 0.45
% 1.74/1.20  Index Insertion      : 0.00
% 1.74/1.20  Index Deletion       : 0.00
% 1.74/1.20  Index Matching       : 0.00
% 1.74/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
