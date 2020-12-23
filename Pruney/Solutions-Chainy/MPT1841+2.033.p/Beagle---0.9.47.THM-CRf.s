%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:32 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   34 (  51 expanded)
%              Number of leaves         :   17 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   49 (  95 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_28,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( v1_subset_1(B,A)
           => v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tex_2)).

tff(c_16,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [A_1] : ~ v1_xboole_0(k1_tarski(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_10,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( k6_domain_1(A_11,B_12) = k1_tarski(B_12)
      | ~ m1_subset_1(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_21,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_18])).

tff(c_24,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_21])).

tff(c_12,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_25,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_12])).

tff(c_30,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k6_domain_1(A_13,B_14),k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,A_13)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_36,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_30])).

tff(c_39,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_36])).

tff(c_40,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_39])).

tff(c_46,plain,(
    ! [B_15,A_16] :
      ( v1_xboole_0(B_15)
      | ~ v1_subset_1(B_15,A_16)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_16))
      | ~ v1_zfmisc_1(A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_49,plain,
    ( v1_xboole_0(k1_tarski('#skF_2'))
    | ~ v1_subset_1(k1_tarski('#skF_2'),'#skF_1')
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_46])).

tff(c_55,plain,
    ( v1_xboole_0(k1_tarski('#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_25,c_49])).

tff(c_57,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_2,c_55])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:45:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.16  
% 1.78/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.16  %$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1
% 1.78/1.16  
% 1.78/1.16  %Foreground sorts:
% 1.78/1.16  
% 1.78/1.16  
% 1.78/1.16  %Background operators:
% 1.78/1.16  
% 1.78/1.16  
% 1.78/1.16  %Foreground operators:
% 1.78/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.16  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.78/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.78/1.16  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.78/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.78/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.78/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.78/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.16  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.78/1.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.78/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.78/1.16  
% 1.78/1.17  tff(f_66, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 1.78/1.17  tff(f_28, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 1.78/1.17  tff(f_42, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 1.78/1.17  tff(f_35, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 1.78/1.17  tff(f_54, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) => v1_xboole_0(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_tex_2)).
% 1.78/1.17  tff(c_16, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.78/1.17  tff(c_2, plain, (![A_1]: (~v1_xboole_0(k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.78/1.17  tff(c_10, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.78/1.17  tff(c_14, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.78/1.17  tff(c_18, plain, (![A_11, B_12]: (k6_domain_1(A_11, B_12)=k1_tarski(B_12) | ~m1_subset_1(B_12, A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.78/1.17  tff(c_21, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_14, c_18])).
% 1.78/1.17  tff(c_24, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_16, c_21])).
% 1.78/1.17  tff(c_12, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.78/1.17  tff(c_25, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_12])).
% 1.78/1.17  tff(c_30, plain, (![A_13, B_14]: (m1_subset_1(k6_domain_1(A_13, B_14), k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, A_13) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.78/1.17  tff(c_36, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24, c_30])).
% 1.78/1.17  tff(c_39, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_36])).
% 1.78/1.17  tff(c_40, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_16, c_39])).
% 1.78/1.17  tff(c_46, plain, (![B_15, A_16]: (v1_xboole_0(B_15) | ~v1_subset_1(B_15, A_16) | ~m1_subset_1(B_15, k1_zfmisc_1(A_16)) | ~v1_zfmisc_1(A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.78/1.17  tff(c_49, plain, (v1_xboole_0(k1_tarski('#skF_2')) | ~v1_subset_1(k1_tarski('#skF_2'), '#skF_1') | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_46])).
% 1.78/1.17  tff(c_55, plain, (v1_xboole_0(k1_tarski('#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_25, c_49])).
% 1.78/1.17  tff(c_57, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_2, c_55])).
% 1.78/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.17  
% 1.78/1.17  Inference rules
% 1.78/1.17  ----------------------
% 1.78/1.17  #Ref     : 0
% 1.78/1.17  #Sup     : 8
% 1.78/1.17  #Fact    : 0
% 1.78/1.17  #Define  : 0
% 1.78/1.17  #Split   : 1
% 1.78/1.17  #Chain   : 0
% 1.78/1.17  #Close   : 0
% 1.78/1.17  
% 1.78/1.17  Ordering : KBO
% 1.78/1.17  
% 1.78/1.17  Simplification rules
% 1.78/1.17  ----------------------
% 1.78/1.17  #Subsume      : 0
% 1.78/1.17  #Demod        : 4
% 1.78/1.17  #Tautology    : 2
% 1.78/1.17  #SimpNegUnit  : 3
% 1.78/1.17  #BackRed      : 1
% 1.78/1.17  
% 1.78/1.17  #Partial instantiations: 0
% 1.78/1.17  #Strategies tried      : 1
% 1.78/1.17  
% 1.78/1.17  Timing (in seconds)
% 1.78/1.17  ----------------------
% 1.78/1.18  Preprocessing        : 0.30
% 1.78/1.18  Parsing              : 0.17
% 1.78/1.18  CNF conversion       : 0.02
% 1.78/1.18  Main loop            : 0.10
% 1.78/1.18  Inferencing          : 0.04
% 1.78/1.18  Reduction            : 0.03
% 1.78/1.18  Demodulation         : 0.01
% 1.78/1.18  BG Simplification    : 0.01
% 1.78/1.18  Subsumption          : 0.01
% 1.78/1.18  Abstraction          : 0.01
% 1.78/1.18  MUC search           : 0.00
% 1.78/1.18  Cooper               : 0.00
% 1.78/1.18  Total                : 0.43
% 1.78/1.18  Index Insertion      : 0.00
% 1.78/1.18  Index Deletion       : 0.00
% 1.78/1.18  Index Matching       : 0.00
% 1.78/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
