%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:43 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   44 (  61 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :   58 ( 104 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_36,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_4,plain,(
    ! [A_2] : k2_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_35,plain,(
    ! [A_19,B_20] : k2_xboole_0(k1_tarski(A_19),B_20) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_39,plain,(
    ! [A_19] : k1_tarski(A_19) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_35])).

tff(c_24,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_18,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_22,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_51,plain,(
    ! [A_25,B_26] :
      ( k6_domain_1(A_25,B_26) = k1_tarski(B_26)
      | ~ m1_subset_1(B_26,A_25)
      | v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_54,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_51])).

tff(c_57,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_54])).

tff(c_20,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_58,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_20])).

tff(c_63,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(k6_domain_1(A_27,B_28),k1_zfmisc_1(A_27))
      | ~ m1_subset_1(B_28,A_27)
      | v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_72,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_63])).

tff(c_76,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_72])).

tff(c_77,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_76])).

tff(c_88,plain,(
    ! [B_29,A_30] :
      ( ~ v1_subset_1(B_29,A_30)
      | v1_xboole_0(B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_30))
      | ~ v1_zfmisc_1(A_30)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_91,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_2'),'#skF_1')
    | v1_xboole_0(k1_tarski('#skF_2'))
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_77,c_88])).

tff(c_97,plain,
    ( v1_xboole_0(k1_tarski('#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_58,c_91])).

tff(c_98,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_97])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_102,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_98,c_2])).

tff(c_106,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_102])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:59:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.25  
% 1.85/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.25  %$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.85/1.25  
% 1.85/1.25  %Foreground sorts:
% 1.85/1.25  
% 1.85/1.25  
% 1.85/1.25  %Background operators:
% 1.85/1.25  
% 1.85/1.25  
% 1.85/1.25  %Foreground operators:
% 1.85/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.25  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.85/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.85/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.85/1.25  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.85/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.85/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.85/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.85/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.85/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.25  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.85/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.85/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.85/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.85/1.25  
% 1.85/1.26  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 1.85/1.26  tff(f_36, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.85/1.26  tff(f_84, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 1.85/1.26  tff(f_58, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 1.85/1.26  tff(f_51, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 1.85/1.26  tff(f_72, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 1.85/1.26  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.85/1.26  tff(c_4, plain, (![A_2]: (k2_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.85/1.26  tff(c_35, plain, (![A_19, B_20]: (k2_xboole_0(k1_tarski(A_19), B_20)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.85/1.26  tff(c_39, plain, (![A_19]: (k1_tarski(A_19)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_35])).
% 1.85/1.26  tff(c_24, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.85/1.26  tff(c_18, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.85/1.26  tff(c_22, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.85/1.26  tff(c_51, plain, (![A_25, B_26]: (k6_domain_1(A_25, B_26)=k1_tarski(B_26) | ~m1_subset_1(B_26, A_25) | v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.85/1.26  tff(c_54, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_51])).
% 1.85/1.26  tff(c_57, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_24, c_54])).
% 1.85/1.26  tff(c_20, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.85/1.26  tff(c_58, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_20])).
% 1.85/1.26  tff(c_63, plain, (![A_27, B_28]: (m1_subset_1(k6_domain_1(A_27, B_28), k1_zfmisc_1(A_27)) | ~m1_subset_1(B_28, A_27) | v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.85/1.26  tff(c_72, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_57, c_63])).
% 1.85/1.26  tff(c_76, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_72])).
% 1.85/1.26  tff(c_77, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_24, c_76])).
% 1.85/1.26  tff(c_88, plain, (![B_29, A_30]: (~v1_subset_1(B_29, A_30) | v1_xboole_0(B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(A_30)) | ~v1_zfmisc_1(A_30) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.85/1.26  tff(c_91, plain, (~v1_subset_1(k1_tarski('#skF_2'), '#skF_1') | v1_xboole_0(k1_tarski('#skF_2')) | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_77, c_88])).
% 1.85/1.26  tff(c_97, plain, (v1_xboole_0(k1_tarski('#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_58, c_91])).
% 1.85/1.26  tff(c_98, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_24, c_97])).
% 1.85/1.26  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.85/1.26  tff(c_102, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_98, c_2])).
% 1.85/1.26  tff(c_106, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39, c_102])).
% 1.85/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.26  
% 1.85/1.26  Inference rules
% 1.85/1.26  ----------------------
% 1.85/1.26  #Ref     : 0
% 1.85/1.26  #Sup     : 16
% 1.85/1.26  #Fact    : 0
% 1.85/1.26  #Define  : 0
% 1.85/1.26  #Split   : 0
% 1.85/1.26  #Chain   : 0
% 1.85/1.26  #Close   : 0
% 1.85/1.26  
% 1.85/1.26  Ordering : KBO
% 1.85/1.26  
% 1.85/1.26  Simplification rules
% 1.85/1.26  ----------------------
% 1.85/1.26  #Subsume      : 1
% 1.85/1.26  #Demod        : 5
% 1.85/1.26  #Tautology    : 7
% 1.85/1.26  #SimpNegUnit  : 4
% 1.85/1.26  #BackRed      : 1
% 1.85/1.26  
% 1.85/1.26  #Partial instantiations: 0
% 1.85/1.26  #Strategies tried      : 1
% 1.85/1.26  
% 1.85/1.26  Timing (in seconds)
% 1.85/1.26  ----------------------
% 1.91/1.26  Preprocessing        : 0.29
% 1.91/1.26  Parsing              : 0.16
% 1.91/1.26  CNF conversion       : 0.02
% 1.91/1.26  Main loop            : 0.11
% 1.91/1.26  Inferencing          : 0.05
% 1.91/1.26  Reduction            : 0.03
% 1.91/1.26  Demodulation         : 0.02
% 1.91/1.26  BG Simplification    : 0.01
% 1.91/1.26  Subsumption          : 0.02
% 1.91/1.26  Abstraction          : 0.01
% 1.91/1.26  MUC search           : 0.00
% 1.91/1.26  Cooper               : 0.00
% 1.91/1.26  Total                : 0.43
% 1.91/1.27  Index Insertion      : 0.00
% 1.91/1.27  Index Deletion       : 0.00
% 1.91/1.27  Index Matching       : 0.00
% 1.91/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
