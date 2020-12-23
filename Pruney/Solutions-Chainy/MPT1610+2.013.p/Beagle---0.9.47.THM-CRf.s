%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:31 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   39 (  41 expanded)
%              Number of leaves         :   23 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   41 (  43 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k2_yellow_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_36,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_48,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_57,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k1_xboole_0,A)
       => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A] : k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow_1)).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8,plain,(
    ! [A_6] : ~ v1_xboole_0(k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_16,plain,(
    ! [A_11] : k9_setfam_1(A_11) = k1_zfmisc_1(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_20,plain,(
    ! [A_13] : k2_yellow_1(k9_setfam_1(A_13)) = k3_yellow_1(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_23,plain,(
    ! [A_13] : k2_yellow_1(k1_zfmisc_1(A_13)) = k3_yellow_1(A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_20])).

tff(c_61,plain,(
    ! [A_27] :
      ( k3_yellow_0(k2_yellow_1(A_27)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,A_27)
      | v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_70,plain,(
    ! [A_13] :
      ( k3_yellow_0(k3_yellow_1(A_13)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(A_13))
      | v1_xboole_0(k1_zfmisc_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23,c_61])).

tff(c_74,plain,(
    ! [A_28] :
      ( k3_yellow_0(k3_yellow_1(A_28)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(A_28)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_70])).

tff(c_77,plain,(
    ! [A_28] :
      ( k3_yellow_0(k3_yellow_1(A_28)) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_28))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_28)) ) ),
    inference(resolution,[status(thm)],[c_10,c_74])).

tff(c_81,plain,(
    ! [A_29] :
      ( k3_yellow_0(k3_yellow_1(A_29)) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_29)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_77])).

tff(c_85,plain,(
    ! [B_10] :
      ( k3_yellow_0(k3_yellow_1(B_10)) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,B_10) ) ),
    inference(resolution,[status(thm)],[c_14,c_81])).

tff(c_88,plain,(
    ! [B_10] : k3_yellow_0(k3_yellow_1(B_10)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_85])).

tff(c_22,plain,(
    k3_yellow_0(k3_yellow_1('#skF_2')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_93,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:42:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.18  
% 1.61/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.18  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k2_yellow_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2
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
% 1.61/1.18  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 1.61/1.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.61/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.61/1.18  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 1.61/1.18  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 1.61/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.61/1.18  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 1.61/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.61/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.61/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.61/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.61/1.18  
% 1.81/1.19  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.81/1.19  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.81/1.19  tff(f_36, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.81/1.19  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 1.81/1.19  tff(f_48, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 1.81/1.19  tff(f_57, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 1.81/1.19  tff(f_55, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow_1)).
% 1.81/1.19  tff(f_60, negated_conjecture, ~(![A]: (k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_yellow_1)).
% 1.81/1.19  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.81/1.19  tff(c_14, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.81/1.19  tff(c_8, plain, (![A_6]: (~v1_xboole_0(k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.81/1.19  tff(c_10, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.81/1.19  tff(c_16, plain, (![A_11]: (k9_setfam_1(A_11)=k1_zfmisc_1(A_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.81/1.19  tff(c_20, plain, (![A_13]: (k2_yellow_1(k9_setfam_1(A_13))=k3_yellow_1(A_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.81/1.19  tff(c_23, plain, (![A_13]: (k2_yellow_1(k1_zfmisc_1(A_13))=k3_yellow_1(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_20])).
% 1.81/1.19  tff(c_61, plain, (![A_27]: (k3_yellow_0(k2_yellow_1(A_27))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, A_27) | v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.81/1.19  tff(c_70, plain, (![A_13]: (k3_yellow_0(k3_yellow_1(A_13))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, k1_zfmisc_1(A_13)) | v1_xboole_0(k1_zfmisc_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_23, c_61])).
% 1.81/1.19  tff(c_74, plain, (![A_28]: (k3_yellow_0(k3_yellow_1(A_28))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, k1_zfmisc_1(A_28)))), inference(negUnitSimplification, [status(thm)], [c_8, c_70])).
% 1.81/1.19  tff(c_77, plain, (![A_28]: (k3_yellow_0(k3_yellow_1(A_28))=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_28)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_28)))), inference(resolution, [status(thm)], [c_10, c_74])).
% 1.81/1.19  tff(c_81, plain, (![A_29]: (k3_yellow_0(k3_yellow_1(A_29))=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_29)))), inference(negUnitSimplification, [status(thm)], [c_8, c_77])).
% 1.81/1.19  tff(c_85, plain, (![B_10]: (k3_yellow_0(k3_yellow_1(B_10))=k1_xboole_0 | ~r1_tarski(k1_xboole_0, B_10))), inference(resolution, [status(thm)], [c_14, c_81])).
% 1.81/1.19  tff(c_88, plain, (![B_10]: (k3_yellow_0(k3_yellow_1(B_10))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_85])).
% 1.81/1.19  tff(c_22, plain, (k3_yellow_0(k3_yellow_1('#skF_2'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.81/1.19  tff(c_93, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_22])).
% 1.81/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.19  
% 1.81/1.19  Inference rules
% 1.81/1.19  ----------------------
% 1.81/1.19  #Ref     : 0
% 1.81/1.19  #Sup     : 12
% 1.81/1.19  #Fact    : 0
% 1.81/1.19  #Define  : 0
% 1.81/1.19  #Split   : 0
% 1.81/1.19  #Chain   : 0
% 1.81/1.19  #Close   : 0
% 1.81/1.19  
% 1.81/1.19  Ordering : KBO
% 1.81/1.19  
% 1.81/1.19  Simplification rules
% 1.81/1.19  ----------------------
% 1.81/1.19  #Subsume      : 0
% 1.81/1.19  #Demod        : 5
% 1.81/1.19  #Tautology    : 11
% 1.81/1.19  #SimpNegUnit  : 2
% 1.81/1.19  #BackRed      : 1
% 1.81/1.19  
% 1.81/1.19  #Partial instantiations: 0
% 1.81/1.19  #Strategies tried      : 1
% 1.81/1.19  
% 1.81/1.19  Timing (in seconds)
% 1.81/1.19  ----------------------
% 1.81/1.19  Preprocessing        : 0.30
% 1.81/1.19  Parsing              : 0.15
% 1.81/1.19  CNF conversion       : 0.02
% 1.81/1.19  Main loop            : 0.10
% 1.81/1.19  Inferencing          : 0.04
% 1.81/1.19  Reduction            : 0.03
% 1.81/1.19  Demodulation         : 0.02
% 1.81/1.19  BG Simplification    : 0.01
% 1.81/1.19  Subsumption          : 0.01
% 1.81/1.19  Abstraction          : 0.01
% 1.81/1.19  MUC search           : 0.00
% 1.81/1.19  Cooper               : 0.00
% 1.81/1.19  Total                : 0.42
% 1.81/1.19  Index Insertion      : 0.00
% 1.81/1.19  Index Deletion       : 0.00
% 1.81/1.19  Index Matching       : 0.00
% 1.81/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
