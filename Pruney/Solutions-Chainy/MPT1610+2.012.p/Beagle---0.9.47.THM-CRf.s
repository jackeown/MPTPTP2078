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
% DateTime   : Thu Dec  3 10:25:30 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   41 (  44 expanded)
%              Number of leaves         :   23 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   43 (  47 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k2_yellow_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_38,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_43,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_51,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_60,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k1_xboole_0,A)
       => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A] : k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow_1)).

tff(c_8,plain,(
    ! [A_6] : ~ v1_xboole_0(k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10,plain,(
    ! [A_7] : v1_xboole_0('#skF_2'(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26,plain,(
    ! [A_16] :
      ( k1_xboole_0 = A_16
      | ~ v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    ! [A_7] : '#skF_2'(A_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_26])).

tff(c_12,plain,(
    ! [A_7] : m1_subset_1('#skF_2'(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_63,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_12])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( r2_hidden(A_9,B_10)
      | v1_xboole_0(B_10)
      | ~ m1_subset_1(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16,plain,(
    ! [A_11] : k9_setfam_1(A_11) = k1_zfmisc_1(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    ! [A_13] : k2_yellow_1(k9_setfam_1(A_13)) = k3_yellow_1(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_23,plain,(
    ! [A_13] : k2_yellow_1(k1_zfmisc_1(A_13)) = k3_yellow_1(A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_20])).

tff(c_75,plain,(
    ! [A_26] :
      ( k3_yellow_0(k2_yellow_1(A_26)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,A_26)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_84,plain,(
    ! [A_13] :
      ( k3_yellow_0(k3_yellow_1(A_13)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(A_13))
      | v1_xboole_0(k1_zfmisc_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23,c_75])).

tff(c_88,plain,(
    ! [A_27] :
      ( k3_yellow_0(k3_yellow_1(A_27)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(A_27)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_84])).

tff(c_91,plain,(
    ! [A_27] :
      ( k3_yellow_0(k3_yellow_1(A_27)) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_27))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_27)) ) ),
    inference(resolution,[status(thm)],[c_14,c_88])).

tff(c_94,plain,(
    ! [A_27] :
      ( k3_yellow_0(k3_yellow_1(A_27)) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_27)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_91])).

tff(c_95,plain,(
    ! [A_27] : k3_yellow_0(k3_yellow_1(A_27)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_94])).

tff(c_22,plain,(
    k3_yellow_0(k3_yellow_1('#skF_3')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_99,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:43:19 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.11  
% 1.65/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.11  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k2_yellow_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3
% 1.65/1.11  
% 1.65/1.11  %Foreground sorts:
% 1.65/1.11  
% 1.65/1.11  
% 1.65/1.11  %Background operators:
% 1.65/1.11  
% 1.65/1.11  
% 1.65/1.11  %Foreground operators:
% 1.65/1.11  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.65/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.65/1.11  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 1.65/1.11  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.65/1.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.65/1.11  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 1.65/1.11  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 1.65/1.11  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 1.65/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.65/1.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.65/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.65/1.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.65/1.11  
% 1.65/1.12  tff(f_38, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.65/1.12  tff(f_43, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_subset_1)).
% 1.65/1.12  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.65/1.12  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 1.65/1.12  tff(f_51, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 1.65/1.12  tff(f_60, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_yellow_1)).
% 1.65/1.12  tff(f_58, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_yellow_1)).
% 1.65/1.12  tff(f_63, negated_conjecture, ~(![A]: (k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_yellow_1)).
% 1.65/1.12  tff(c_8, plain, (![A_6]: (~v1_xboole_0(k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.65/1.12  tff(c_10, plain, (![A_7]: (v1_xboole_0('#skF_2'(A_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.65/1.12  tff(c_26, plain, (![A_16]: (k1_xboole_0=A_16 | ~v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.65/1.12  tff(c_30, plain, (![A_7]: ('#skF_2'(A_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_26])).
% 1.65/1.12  tff(c_12, plain, (![A_7]: (m1_subset_1('#skF_2'(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.65/1.12  tff(c_63, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_12])).
% 1.65/1.12  tff(c_14, plain, (![A_9, B_10]: (r2_hidden(A_9, B_10) | v1_xboole_0(B_10) | ~m1_subset_1(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.65/1.12  tff(c_16, plain, (![A_11]: (k9_setfam_1(A_11)=k1_zfmisc_1(A_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.65/1.12  tff(c_20, plain, (![A_13]: (k2_yellow_1(k9_setfam_1(A_13))=k3_yellow_1(A_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.65/1.12  tff(c_23, plain, (![A_13]: (k2_yellow_1(k1_zfmisc_1(A_13))=k3_yellow_1(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_20])).
% 1.65/1.12  tff(c_75, plain, (![A_26]: (k3_yellow_0(k2_yellow_1(A_26))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, A_26) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.65/1.12  tff(c_84, plain, (![A_13]: (k3_yellow_0(k3_yellow_1(A_13))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, k1_zfmisc_1(A_13)) | v1_xboole_0(k1_zfmisc_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_23, c_75])).
% 1.65/1.12  tff(c_88, plain, (![A_27]: (k3_yellow_0(k3_yellow_1(A_27))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, k1_zfmisc_1(A_27)))), inference(negUnitSimplification, [status(thm)], [c_8, c_84])).
% 1.65/1.12  tff(c_91, plain, (![A_27]: (k3_yellow_0(k3_yellow_1(A_27))=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_27)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_27)))), inference(resolution, [status(thm)], [c_14, c_88])).
% 1.65/1.12  tff(c_94, plain, (![A_27]: (k3_yellow_0(k3_yellow_1(A_27))=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_91])).
% 1.65/1.12  tff(c_95, plain, (![A_27]: (k3_yellow_0(k3_yellow_1(A_27))=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_8, c_94])).
% 1.65/1.12  tff(c_22, plain, (k3_yellow_0(k3_yellow_1('#skF_3'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.65/1.12  tff(c_99, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95, c_22])).
% 1.65/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.12  
% 1.65/1.12  Inference rules
% 1.65/1.12  ----------------------
% 1.65/1.12  #Ref     : 0
% 1.65/1.12  #Sup     : 14
% 1.65/1.12  #Fact    : 0
% 1.65/1.12  #Define  : 0
% 1.65/1.12  #Split   : 0
% 1.65/1.12  #Chain   : 0
% 1.65/1.12  #Close   : 0
% 1.65/1.12  
% 1.65/1.12  Ordering : KBO
% 1.65/1.12  
% 1.65/1.12  Simplification rules
% 1.65/1.12  ----------------------
% 1.65/1.12  #Subsume      : 0
% 1.65/1.12  #Demod        : 6
% 1.65/1.12  #Tautology    : 12
% 1.65/1.12  #SimpNegUnit  : 2
% 1.65/1.12  #BackRed      : 2
% 1.65/1.12  
% 1.65/1.12  #Partial instantiations: 0
% 1.65/1.12  #Strategies tried      : 1
% 1.65/1.12  
% 1.65/1.12  Timing (in seconds)
% 1.65/1.12  ----------------------
% 1.65/1.13  Preprocessing        : 0.28
% 1.65/1.13  Parsing              : 0.15
% 1.65/1.13  CNF conversion       : 0.02
% 1.65/1.13  Main loop            : 0.10
% 1.65/1.13  Inferencing          : 0.04
% 1.65/1.13  Reduction            : 0.03
% 1.65/1.13  Demodulation         : 0.02
% 1.65/1.13  BG Simplification    : 0.01
% 1.65/1.13  Subsumption          : 0.01
% 1.65/1.13  Abstraction          : 0.01
% 1.65/1.13  MUC search           : 0.00
% 1.65/1.13  Cooper               : 0.00
% 1.65/1.13  Total                : 0.40
% 1.65/1.13  Index Insertion      : 0.00
% 1.65/1.13  Index Deletion       : 0.00
% 1.65/1.13  Index Matching       : 0.00
% 1.65/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
