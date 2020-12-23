%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:37 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   36 (  41 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   30 (  40 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_42,axiom,(
    ! [A,B,C,D] : v1_relat_1(k2_tarski(k4_tarski(A,B),k4_tarski(C,D))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_relat_1)).

tff(f_51,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_44,axiom,(
    ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_2,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_35,plain,(
    ! [B_17,A_18] :
      ( v1_relat_1(B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_18))
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_39,plain,(
    ! [A_1] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_35])).

tff(c_40,plain,(
    ! [A_1] : ~ v1_relat_1(A_1) ),
    inference(splitLeft,[status(thm)],[c_39])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10,D_11] : v1_relat_1(k2_tarski(k4_tarski(A_8,B_9),k4_tarski(C_10,D_11))) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_43,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_8])).

tff(c_44,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_39])).

tff(c_14,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [A_12] : k7_relat_1(k1_xboole_0,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_46,plain,(
    ! [B_24,A_25] :
      ( k2_relat_1(k7_relat_1(B_24,A_25)) = k9_relat_1(B_24,A_25)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_55,plain,(
    ! [A_12] :
      ( k9_relat_1(k1_xboole_0,A_12) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_46])).

tff(c_59,plain,(
    ! [A_12] : k9_relat_1(k1_xboole_0,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_14,c_55])).

tff(c_18,plain,(
    k9_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_62,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:04:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.18  
% 1.61/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.18  %$ r2_hidden > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.61/1.18  
% 1.61/1.18  %Foreground sorts:
% 1.61/1.18  
% 1.61/1.18  
% 1.61/1.18  %Background operators:
% 1.61/1.18  
% 1.61/1.18  
% 1.61/1.18  %Foreground operators:
% 1.61/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.61/1.18  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.61/1.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.61/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.61/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.61/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.61/1.18  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.61/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.61/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.61/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.61/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.61/1.18  
% 1.78/1.19  tff(f_27, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 1.78/1.19  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.78/1.19  tff(f_42, axiom, (![A, B, C, D]: v1_relat_1(k2_tarski(k4_tarski(A, B), k4_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_relat_1)).
% 1.78/1.19  tff(f_51, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.78/1.19  tff(f_44, axiom, (![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 1.78/1.19  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.78/1.19  tff(f_54, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.78/1.19  tff(c_2, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.78/1.19  tff(c_35, plain, (![B_17, A_18]: (v1_relat_1(B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(A_18)) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.78/1.19  tff(c_39, plain, (![A_1]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_1))), inference(resolution, [status(thm)], [c_2, c_35])).
% 1.78/1.19  tff(c_40, plain, (![A_1]: (~v1_relat_1(A_1))), inference(splitLeft, [status(thm)], [c_39])).
% 1.78/1.19  tff(c_8, plain, (![A_8, B_9, C_10, D_11]: (v1_relat_1(k2_tarski(k4_tarski(A_8, B_9), k4_tarski(C_10, D_11))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.78/1.19  tff(c_43, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_8])).
% 1.78/1.19  tff(c_44, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_39])).
% 1.78/1.19  tff(c_14, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.78/1.19  tff(c_10, plain, (![A_12]: (k7_relat_1(k1_xboole_0, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.78/1.19  tff(c_46, plain, (![B_24, A_25]: (k2_relat_1(k7_relat_1(B_24, A_25))=k9_relat_1(B_24, A_25) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.78/1.19  tff(c_55, plain, (![A_12]: (k9_relat_1(k1_xboole_0, A_12)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_46])).
% 1.78/1.19  tff(c_59, plain, (![A_12]: (k9_relat_1(k1_xboole_0, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_14, c_55])).
% 1.78/1.19  tff(c_18, plain, (k9_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.78/1.19  tff(c_62, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_18])).
% 1.78/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.19  
% 1.78/1.19  Inference rules
% 1.78/1.19  ----------------------
% 1.78/1.19  #Ref     : 0
% 1.78/1.19  #Sup     : 10
% 1.78/1.19  #Fact    : 0
% 1.78/1.19  #Define  : 0
% 1.78/1.19  #Split   : 1
% 1.78/1.19  #Chain   : 0
% 1.78/1.19  #Close   : 0
% 1.78/1.19  
% 1.78/1.19  Ordering : KBO
% 1.78/1.19  
% 1.78/1.19  Simplification rules
% 1.78/1.19  ----------------------
% 1.78/1.19  #Subsume      : 1
% 1.78/1.19  #Demod        : 3
% 1.78/1.19  #Tautology    : 8
% 1.78/1.19  #SimpNegUnit  : 2
% 1.78/1.19  #BackRed      : 1
% 1.78/1.19  
% 1.78/1.19  #Partial instantiations: 0
% 1.78/1.19  #Strategies tried      : 1
% 1.78/1.19  
% 1.78/1.19  Timing (in seconds)
% 1.78/1.19  ----------------------
% 1.78/1.19  Preprocessing        : 0.28
% 1.78/1.19  Parsing              : 0.16
% 1.78/1.19  CNF conversion       : 0.02
% 1.78/1.19  Main loop            : 0.10
% 1.78/1.19  Inferencing          : 0.04
% 1.78/1.19  Reduction            : 0.03
% 1.78/1.19  Demodulation         : 0.02
% 1.78/1.19  BG Simplification    : 0.01
% 1.78/1.19  Subsumption          : 0.01
% 1.78/1.19  Abstraction          : 0.00
% 1.78/1.19  MUC search           : 0.00
% 1.78/1.19  Cooper               : 0.00
% 1.78/1.19  Total                : 0.41
% 1.78/1.19  Index Insertion      : 0.00
% 1.78/1.19  Index Deletion       : 0.00
% 1.78/1.19  Index Matching       : 0.00
% 1.78/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
