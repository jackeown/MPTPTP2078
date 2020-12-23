%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:23 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   36 (  42 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   31 (  43 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_relat_1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0

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

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_53,negated_conjecture,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_48,axiom,(
    ! [A,B,C,D] : v1_relat_1(k2_tarski(k4_tarski(A,B),k4_tarski(C,D))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).

tff(f_51,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(c_18,plain,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    ! [B_16,A_17] :
      ( v1_relat_1(B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_17))
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_41,plain,(
    ! [A_2] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_37])).

tff(c_42,plain,(
    ! [A_2] : ~ v1_relat_1(A_2) ),
    inference(splitLeft,[status(thm)],[c_41])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12,D_13] : v1_relat_1(k2_tarski(k4_tarski(A_10,B_11),k4_tarski(C_12,D_13))) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_45,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_12])).

tff(c_46,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_41])).

tff(c_16,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_48,plain,(
    ! [A_23] :
      ( k2_xboole_0(k1_relat_1(A_23),k2_relat_1(A_23)) = k3_relat_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_57,plain,
    ( k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0) = k3_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_48])).

tff(c_64,plain,(
    k3_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_16,c_2,c_57])).

tff(c_66,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_64])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:21:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.11  
% 1.67/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.11  %$ r2_hidden > m1_subset_1 > v1_relat_1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0
% 1.67/1.11  
% 1.67/1.11  %Foreground sorts:
% 1.67/1.11  
% 1.67/1.11  
% 1.67/1.11  %Background operators:
% 1.67/1.11  
% 1.67/1.11  
% 1.67/1.11  %Foreground operators:
% 1.67/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.67/1.11  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.67/1.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.67/1.11  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.67/1.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.67/1.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.67/1.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.67/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.67/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.67/1.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.67/1.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.67/1.11  
% 1.67/1.12  tff(f_53, negated_conjecture, ~(k3_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_relat_1)).
% 1.67/1.12  tff(f_29, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 1.67/1.12  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.67/1.12  tff(f_48, axiom, (![A, B, C, D]: v1_relat_1(k2_tarski(k4_tarski(A, B), k4_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_relat_1)).
% 1.67/1.12  tff(f_51, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.67/1.12  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 1.67/1.12  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 1.67/1.12  tff(c_18, plain, (k3_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.67/1.12  tff(c_4, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.67/1.12  tff(c_37, plain, (![B_16, A_17]: (v1_relat_1(B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_17)) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.67/1.12  tff(c_41, plain, (![A_2]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_2))), inference(resolution, [status(thm)], [c_4, c_37])).
% 1.67/1.12  tff(c_42, plain, (![A_2]: (~v1_relat_1(A_2))), inference(splitLeft, [status(thm)], [c_41])).
% 1.67/1.12  tff(c_12, plain, (![A_10, B_11, C_12, D_13]: (v1_relat_1(k2_tarski(k4_tarski(A_10, B_11), k4_tarski(C_12, D_13))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.67/1.12  tff(c_45, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_12])).
% 1.67/1.12  tff(c_46, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_41])).
% 1.67/1.12  tff(c_16, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.67/1.12  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.67/1.12  tff(c_14, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.67/1.12  tff(c_48, plain, (![A_23]: (k2_xboole_0(k1_relat_1(A_23), k2_relat_1(A_23))=k3_relat_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.67/1.12  tff(c_57, plain, (k2_xboole_0(k1_relat_1(k1_xboole_0), k1_xboole_0)=k3_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_48])).
% 1.67/1.12  tff(c_64, plain, (k3_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_16, c_2, c_57])).
% 1.67/1.12  tff(c_66, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_64])).
% 1.67/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.12  
% 1.67/1.12  Inference rules
% 1.67/1.12  ----------------------
% 1.67/1.12  #Ref     : 0
% 1.67/1.12  #Sup     : 11
% 1.67/1.12  #Fact    : 0
% 1.67/1.12  #Define  : 0
% 1.67/1.12  #Split   : 1
% 1.67/1.12  #Chain   : 0
% 1.67/1.12  #Close   : 0
% 1.67/1.12  
% 1.67/1.12  Ordering : KBO
% 1.67/1.12  
% 1.67/1.12  Simplification rules
% 1.67/1.12  ----------------------
% 1.67/1.12  #Subsume      : 1
% 1.67/1.12  #Demod        : 3
% 1.67/1.12  #Tautology    : 8
% 1.67/1.12  #SimpNegUnit  : 3
% 1.67/1.12  #BackRed      : 0
% 1.67/1.12  
% 1.67/1.12  #Partial instantiations: 0
% 1.67/1.12  #Strategies tried      : 1
% 1.67/1.12  
% 1.67/1.12  Timing (in seconds)
% 1.67/1.12  ----------------------
% 1.67/1.12  Preprocessing        : 0.26
% 1.67/1.12  Parsing              : 0.15
% 1.67/1.12  CNF conversion       : 0.01
% 1.67/1.12  Main loop            : 0.10
% 1.67/1.12  Inferencing          : 0.04
% 1.67/1.12  Reduction            : 0.04
% 1.67/1.12  Demodulation         : 0.02
% 1.67/1.12  BG Simplification    : 0.01
% 1.67/1.12  Subsumption          : 0.01
% 1.67/1.12  Abstraction          : 0.00
% 1.67/1.12  MUC search           : 0.00
% 1.67/1.12  Cooper               : 0.00
% 1.67/1.12  Total                : 0.39
% 1.67/1.12  Index Insertion      : 0.00
% 1.67/1.12  Index Deletion       : 0.00
% 1.67/1.12  Index Matching       : 0.00
% 1.67/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
