%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:23 EST 2020

% Result     : Theorem 1.54s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   21 (  23 expanded)
%              Number of leaves         :   12 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   23 (  29 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_finset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_43,negated_conjecture,(
    ~ ! [A,B] :
        ( ( r1_tarski(A,B)
          & v1_finset_1(B) )
       => v1_finset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_finset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_finset_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_finset_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_finset_1)).

tff(c_8,plain,(
    ~ v1_finset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    v1_finset_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_19,plain,(
    ! [B_10,A_11] :
      ( v1_finset_1(B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_11))
      | ~ v1_finset_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_24,plain,(
    ! [A_12,B_13] :
      ( v1_finset_1(A_12)
      | ~ v1_finset_1(B_13)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_4,c_19])).

tff(c_27,plain,
    ( v1_finset_1('#skF_1')
    | ~ v1_finset_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_24])).

tff(c_30,plain,(
    v1_finset_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_27])).

tff(c_32,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:53:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.54/1.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.54/1.07  
% 1.54/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.07  %$ r1_tarski > m1_subset_1 > v1_finset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.65/1.07  
% 1.65/1.07  %Foreground sorts:
% 1.65/1.07  
% 1.65/1.07  
% 1.65/1.07  %Background operators:
% 1.65/1.07  
% 1.65/1.07  
% 1.65/1.07  %Foreground operators:
% 1.65/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.65/1.07  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.07  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.65/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.07  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 1.65/1.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.65/1.07  
% 1.65/1.08  tff(f_43, negated_conjecture, ~(![A, B]: ((r1_tarski(A, B) & v1_finset_1(B)) => v1_finset_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_finset_1)).
% 1.65/1.08  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.65/1.08  tff(f_36, axiom, (![A]: (v1_finset_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_finset_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_finset_1)).
% 1.65/1.08  tff(c_8, plain, (~v1_finset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.65/1.08  tff(c_10, plain, (v1_finset_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.65/1.08  tff(c_12, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.65/1.08  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.65/1.08  tff(c_19, plain, (![B_10, A_11]: (v1_finset_1(B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(A_11)) | ~v1_finset_1(A_11))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.65/1.08  tff(c_24, plain, (![A_12, B_13]: (v1_finset_1(A_12) | ~v1_finset_1(B_13) | ~r1_tarski(A_12, B_13))), inference(resolution, [status(thm)], [c_4, c_19])).
% 1.65/1.08  tff(c_27, plain, (v1_finset_1('#skF_1') | ~v1_finset_1('#skF_2')), inference(resolution, [status(thm)], [c_12, c_24])).
% 1.65/1.08  tff(c_30, plain, (v1_finset_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_27])).
% 1.65/1.08  tff(c_32, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_30])).
% 1.65/1.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.08  
% 1.65/1.08  Inference rules
% 1.65/1.08  ----------------------
% 1.65/1.08  #Ref     : 0
% 1.65/1.08  #Sup     : 3
% 1.65/1.08  #Fact    : 0
% 1.65/1.08  #Define  : 0
% 1.65/1.08  #Split   : 0
% 1.65/1.08  #Chain   : 0
% 1.65/1.08  #Close   : 0
% 1.65/1.08  
% 1.65/1.08  Ordering : KBO
% 1.65/1.08  
% 1.65/1.08  Simplification rules
% 1.65/1.08  ----------------------
% 1.65/1.08  #Subsume      : 0
% 1.65/1.08  #Demod        : 1
% 1.65/1.08  #Tautology    : 1
% 1.65/1.08  #SimpNegUnit  : 1
% 1.65/1.08  #BackRed      : 0
% 1.65/1.08  
% 1.65/1.08  #Partial instantiations: 0
% 1.65/1.08  #Strategies tried      : 1
% 1.65/1.08  
% 1.65/1.08  Timing (in seconds)
% 1.65/1.08  ----------------------
% 1.65/1.08  Preprocessing        : 0.24
% 1.65/1.08  Parsing              : 0.14
% 1.65/1.08  CNF conversion       : 0.02
% 1.65/1.09  Main loop            : 0.08
% 1.65/1.09  Inferencing          : 0.04
% 1.65/1.09  Reduction            : 0.02
% 1.65/1.09  Demodulation         : 0.02
% 1.65/1.09  BG Simplification    : 0.01
% 1.65/1.09  Subsumption          : 0.01
% 1.65/1.09  Abstraction          : 0.00
% 1.65/1.09  MUC search           : 0.00
% 1.65/1.09  Cooper               : 0.00
% 1.65/1.09  Total                : 0.35
% 1.65/1.09  Index Insertion      : 0.00
% 1.65/1.09  Index Deletion       : 0.00
% 1.65/1.09  Index Matching       : 0.00
% 1.65/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
