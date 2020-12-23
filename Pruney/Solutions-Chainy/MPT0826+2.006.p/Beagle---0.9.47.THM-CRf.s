%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:14 EST 2020

% Result     : Theorem 1.42s
% Output     : CNFRefutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   17 (  17 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    3
%              Number of atoms          :   10 (  10 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k1_zfmisc_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k6_relat_1(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_34,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(c_6,plain,(
    ! [A_3] : r1_tarski(k6_relat_1(A_3),k2_zfmisc_1(A_3,A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ~ m1_subset_1(k6_relat_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_18,plain,(
    ~ r1_tarski(k6_relat_1('#skF_1'),k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_4,c_8])).

tff(c_22,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:03:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.42/1.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.49/1.03  
% 1.49/1.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.49/1.04  %$ r1_tarski > m1_subset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k1_zfmisc_1 > #skF_1
% 1.49/1.04  
% 1.49/1.04  %Foreground sorts:
% 1.49/1.04  
% 1.49/1.04  
% 1.49/1.04  %Background operators:
% 1.49/1.04  
% 1.49/1.04  
% 1.49/1.04  %Foreground operators:
% 1.49/1.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.49/1.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.49/1.04  tff('#skF_1', type, '#skF_1': $i).
% 1.49/1.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.49/1.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.49/1.04  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.49/1.04  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.49/1.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.49/1.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.49/1.04  
% 1.49/1.05  tff(f_31, axiom, (![A]: r1_tarski(k6_relat_1(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_relset_1)).
% 1.49/1.05  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.49/1.05  tff(f_34, negated_conjecture, ~(![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 1.49/1.05  tff(c_6, plain, (![A_3]: (r1_tarski(k6_relat_1(A_3), k2_zfmisc_1(A_3, A_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.49/1.05  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.49/1.05  tff(c_8, plain, (~m1_subset_1(k6_relat_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.49/1.05  tff(c_18, plain, (~r1_tarski(k6_relat_1('#skF_1'), k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_4, c_8])).
% 1.49/1.05  tff(c_22, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_18])).
% 1.49/1.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.49/1.05  
% 1.49/1.05  Inference rules
% 1.49/1.05  ----------------------
% 1.49/1.05  #Ref     : 0
% 1.49/1.05  #Sup     : 2
% 1.49/1.05  #Fact    : 0
% 1.49/1.05  #Define  : 0
% 1.49/1.05  #Split   : 0
% 1.49/1.05  #Chain   : 0
% 1.49/1.05  #Close   : 0
% 1.49/1.05  
% 1.49/1.05  Ordering : KBO
% 1.49/1.05  
% 1.49/1.05  Simplification rules
% 1.49/1.05  ----------------------
% 1.49/1.05  #Subsume      : 0
% 1.49/1.05  #Demod        : 1
% 1.49/1.05  #Tautology    : 1
% 1.49/1.05  #SimpNegUnit  : 0
% 1.49/1.05  #BackRed      : 0
% 1.49/1.05  
% 1.49/1.05  #Partial instantiations: 0
% 1.49/1.05  #Strategies tried      : 1
% 1.49/1.05  
% 1.49/1.05  Timing (in seconds)
% 1.49/1.05  ----------------------
% 1.49/1.05  Preprocessing        : 0.22
% 1.49/1.05  Parsing              : 0.12
% 1.49/1.05  CNF conversion       : 0.01
% 1.49/1.05  Main loop            : 0.06
% 1.49/1.05  Inferencing          : 0.02
% 1.49/1.05  Reduction            : 0.02
% 1.49/1.05  Demodulation         : 0.01
% 1.49/1.05  BG Simplification    : 0.01
% 1.49/1.05  Subsumption          : 0.01
% 1.49/1.05  Abstraction          : 0.00
% 1.49/1.05  MUC search           : 0.00
% 1.49/1.05  Cooper               : 0.00
% 1.49/1.05  Total                : 0.31
% 1.49/1.05  Index Insertion      : 0.00
% 1.49/1.05  Index Deletion       : 0.00
% 1.49/1.05  Index Matching       : 0.00
% 1.49/1.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
