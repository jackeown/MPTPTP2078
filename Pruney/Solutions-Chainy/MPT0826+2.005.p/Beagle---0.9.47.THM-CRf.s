%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:14 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   27 (  28 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    4
%              Number of atoms          :   21 (  23 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(c_6,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_5] : k2_relat_1(k6_relat_1(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_5] : k1_relat_1(k6_relat_1(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_44,plain,(
    ! [A_13] :
      ( r1_tarski(A_13,k2_zfmisc_1(k1_relat_1(A_13),k2_relat_1(A_13)))
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_47,plain,(
    ! [A_5] :
      ( r1_tarski(k6_relat_1(A_5),k2_zfmisc_1(A_5,k2_relat_1(k6_relat_1(A_5))))
      | ~ v1_relat_1(k6_relat_1(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_44])).

tff(c_52,plain,(
    ! [A_5] : r1_tarski(k6_relat_1(A_5),k2_zfmisc_1(A_5,A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12,c_47])).

tff(c_35,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ~ m1_subset_1(k6_relat_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_43,plain,(
    ~ r1_tarski(k6_relat_1('#skF_1'),k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_35,c_14])).

tff(c_57,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:11:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.56/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.56/1.09  
% 1.56/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.56/1.10  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1
% 1.56/1.10  
% 1.56/1.10  %Foreground sorts:
% 1.56/1.10  
% 1.56/1.10  
% 1.56/1.10  %Background operators:
% 1.56/1.10  
% 1.56/1.10  
% 1.56/1.10  %Foreground operators:
% 1.56/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.56/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.56/1.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.56/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.56/1.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.56/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.56/1.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.56/1.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.56/1.10  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.56/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.56/1.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.56/1.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.56/1.10  
% 1.56/1.10  tff(f_31, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.56/1.10  tff(f_39, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.56/1.10  tff(f_35, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 1.56/1.10  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.56/1.10  tff(f_42, negated_conjecture, ~(![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 1.56/1.10  tff(c_6, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.56/1.10  tff(c_12, plain, (![A_5]: (k2_relat_1(k6_relat_1(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.56/1.10  tff(c_10, plain, (![A_5]: (k1_relat_1(k6_relat_1(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.56/1.10  tff(c_44, plain, (![A_13]: (r1_tarski(A_13, k2_zfmisc_1(k1_relat_1(A_13), k2_relat_1(A_13))) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.56/1.10  tff(c_47, plain, (![A_5]: (r1_tarski(k6_relat_1(A_5), k2_zfmisc_1(A_5, k2_relat_1(k6_relat_1(A_5)))) | ~v1_relat_1(k6_relat_1(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_44])).
% 1.56/1.10  tff(c_52, plain, (![A_5]: (r1_tarski(k6_relat_1(A_5), k2_zfmisc_1(A_5, A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_12, c_47])).
% 1.56/1.10  tff(c_35, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.56/1.10  tff(c_14, plain, (~m1_subset_1(k6_relat_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.56/1.10  tff(c_43, plain, (~r1_tarski(k6_relat_1('#skF_1'), k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_35, c_14])).
% 1.56/1.10  tff(c_57, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_43])).
% 1.56/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.56/1.10  
% 1.56/1.10  Inference rules
% 1.56/1.10  ----------------------
% 1.56/1.10  #Ref     : 0
% 1.56/1.10  #Sup     : 8
% 1.56/1.10  #Fact    : 0
% 1.56/1.10  #Define  : 0
% 1.56/1.10  #Split   : 0
% 1.56/1.10  #Chain   : 0
% 1.56/1.10  #Close   : 0
% 1.56/1.10  
% 1.56/1.10  Ordering : KBO
% 1.56/1.10  
% 1.56/1.10  Simplification rules
% 1.56/1.10  ----------------------
% 1.56/1.10  #Subsume      : 0
% 1.56/1.10  #Demod        : 5
% 1.56/1.10  #Tautology    : 5
% 1.56/1.10  #SimpNegUnit  : 0
% 1.56/1.10  #BackRed      : 1
% 1.56/1.10  
% 1.56/1.10  #Partial instantiations: 0
% 1.56/1.10  #Strategies tried      : 1
% 1.56/1.10  
% 1.56/1.10  Timing (in seconds)
% 1.56/1.10  ----------------------
% 1.56/1.11  Preprocessing        : 0.24
% 1.56/1.11  Parsing              : 0.14
% 1.56/1.11  CNF conversion       : 0.01
% 1.56/1.11  Main loop            : 0.07
% 1.56/1.11  Inferencing          : 0.03
% 1.56/1.11  Reduction            : 0.02
% 1.56/1.11  Demodulation         : 0.02
% 1.56/1.11  BG Simplification    : 0.01
% 1.56/1.11  Subsumption          : 0.01
% 1.56/1.11  Abstraction          : 0.00
% 1.56/1.11  MUC search           : 0.00
% 1.56/1.11  Cooper               : 0.00
% 1.56/1.11  Total                : 0.35
% 1.56/1.11  Index Insertion      : 0.00
% 1.56/1.11  Index Deletion       : 0.00
% 1.56/1.11  Index Matching       : 0.00
% 1.56/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
