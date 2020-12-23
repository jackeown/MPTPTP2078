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
% DateTime   : Thu Dec  3 09:59:23 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   36 (  42 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   33 (  45 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_53,negated_conjecture,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_relat_1)).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_51,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_38,plain,(
    ! [B_16,A_17] :
      ( v1_relat_1(B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_17))
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_42,plain,(
    ! [A_2] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_38])).

tff(c_43,plain,(
    ! [A_2] : ~ v1_relat_1(A_2) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_12,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_46,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_12])).

tff(c_47,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_18,plain,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_48,plain,(
    ! [A_18] :
      ( k2_xboole_0(k1_relat_1(A_18),k2_relat_1(A_18)) = k3_relat_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_60,plain,
    ( k2_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0)) = k3_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_48])).

tff(c_65,plain,
    ( k3_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14,c_60])).

tff(c_66,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_65])).

tff(c_68,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_66])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:11:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.13  
% 1.76/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.13  %$ r2_hidden > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0
% 1.76/1.13  
% 1.76/1.13  %Foreground sorts:
% 1.76/1.13  
% 1.76/1.13  
% 1.76/1.13  %Background operators:
% 1.76/1.13  
% 1.76/1.13  
% 1.76/1.13  %Foreground operators:
% 1.76/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.76/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.76/1.13  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.76/1.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.76/1.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.76/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.76/1.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.76/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.76/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.76/1.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.76/1.13  
% 1.76/1.14  tff(f_29, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 1.76/1.14  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.76/1.14  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.76/1.14  tff(f_53, negated_conjecture, ~(k3_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_relat_1)).
% 1.76/1.14  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 1.76/1.14  tff(f_51, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.76/1.14  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 1.76/1.14  tff(c_4, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.76/1.14  tff(c_38, plain, (![B_16, A_17]: (v1_relat_1(B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_17)) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.76/1.14  tff(c_42, plain, (![A_2]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_2))), inference(resolution, [status(thm)], [c_4, c_38])).
% 1.76/1.14  tff(c_43, plain, (![A_2]: (~v1_relat_1(A_2))), inference(splitLeft, [status(thm)], [c_42])).
% 1.76/1.14  tff(c_12, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.76/1.14  tff(c_46, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43, c_12])).
% 1.76/1.14  tff(c_47, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_42])).
% 1.76/1.14  tff(c_18, plain, (k3_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.76/1.14  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.76/1.14  tff(c_14, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.76/1.14  tff(c_16, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.76/1.14  tff(c_48, plain, (![A_18]: (k2_xboole_0(k1_relat_1(A_18), k2_relat_1(A_18))=k3_relat_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.76/1.14  tff(c_60, plain, (k2_xboole_0(k1_xboole_0, k2_relat_1(k1_xboole_0))=k3_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_48])).
% 1.76/1.14  tff(c_65, plain, (k3_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14, c_60])).
% 1.76/1.14  tff(c_66, plain, (~v1_relat_1(k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_18, c_65])).
% 1.76/1.14  tff(c_68, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_47, c_66])).
% 1.76/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.14  
% 1.76/1.14  Inference rules
% 1.76/1.14  ----------------------
% 1.76/1.14  #Ref     : 0
% 1.76/1.14  #Sup     : 11
% 1.76/1.14  #Fact    : 0
% 1.76/1.14  #Define  : 0
% 1.76/1.14  #Split   : 1
% 1.76/1.14  #Chain   : 0
% 1.76/1.14  #Close   : 0
% 1.76/1.14  
% 1.76/1.14  Ordering : KBO
% 1.76/1.14  
% 1.76/1.14  Simplification rules
% 1.76/1.14  ----------------------
% 1.76/1.14  #Subsume      : 1
% 1.76/1.14  #Demod        : 5
% 1.76/1.14  #Tautology    : 8
% 1.76/1.14  #SimpNegUnit  : 4
% 1.76/1.14  #BackRed      : 1
% 1.76/1.14  
% 1.76/1.14  #Partial instantiations: 0
% 1.76/1.14  #Strategies tried      : 1
% 1.76/1.14  
% 1.76/1.14  Timing (in seconds)
% 1.76/1.14  ----------------------
% 1.76/1.14  Preprocessing        : 0.27
% 1.76/1.14  Parsing              : 0.16
% 1.76/1.14  CNF conversion       : 0.01
% 1.76/1.14  Main loop            : 0.11
% 1.76/1.14  Inferencing          : 0.04
% 1.76/1.14  Reduction            : 0.04
% 1.76/1.14  Demodulation         : 0.03
% 1.76/1.14  BG Simplification    : 0.01
% 1.76/1.14  Subsumption          : 0.01
% 1.76/1.14  Abstraction          : 0.00
% 1.76/1.14  MUC search           : 0.00
% 1.76/1.14  Cooper               : 0.00
% 1.76/1.14  Total                : 0.40
% 1.76/1.15  Index Insertion      : 0.00
% 1.76/1.15  Index Deletion       : 0.00
% 1.76/1.15  Index Matching       : 0.00
% 1.76/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
