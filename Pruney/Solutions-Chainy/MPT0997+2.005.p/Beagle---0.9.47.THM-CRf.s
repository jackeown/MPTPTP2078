%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:52 EST 2020

% Result     : Theorem 1.54s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   23 (  24 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    3
%              Number of atoms          :   15 (  21 expanded)
%              Number of equality atoms :    8 (  11 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_funct_2)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(c_6,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_24,plain,(
    ! [A_7,B_8,C_9] :
      ( k7_relset_1(A_7,B_8,C_9,A_7) = k2_relset_1(A_7,B_8,C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') = k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_24])).

tff(c_30,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 21:07:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.54/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.54/1.08  
% 1.54/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.54/1.08  %$ v1_funct_2 > m1_subset_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.54/1.08  
% 1.54/1.08  %Foreground sorts:
% 1.54/1.08  
% 1.54/1.08  
% 1.54/1.08  %Background operators:
% 1.54/1.08  
% 1.54/1.08  
% 1.54/1.08  %Foreground operators:
% 1.54/1.08  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.54/1.08  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.54/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.54/1.08  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.54/1.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.54/1.08  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 1.54/1.08  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.54/1.08  tff('#skF_2', type, '#skF_2': $i).
% 1.54/1.08  tff('#skF_3', type, '#skF_3': $i).
% 1.54/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.54/1.08  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.54/1.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.54/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.54/1.08  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.54/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.54/1.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.54/1.08  
% 1.65/1.09  tff(f_44, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_funct_2)).
% 1.65/1.09  tff(f_31, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 1.65/1.09  tff(c_6, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.65/1.09  tff(c_10, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.65/1.09  tff(c_24, plain, (![A_7, B_8, C_9]: (k7_relset_1(A_7, B_8, C_9, A_7)=k2_relset_1(A_7, B_8, C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.65/1.09  tff(c_26, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_10, c_24])).
% 1.65/1.09  tff(c_30, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6, c_26])).
% 1.65/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.09  
% 1.65/1.09  Inference rules
% 1.65/1.09  ----------------------
% 1.65/1.09  #Ref     : 0
% 1.65/1.09  #Sup     : 4
% 1.65/1.09  #Fact    : 0
% 1.65/1.09  #Define  : 0
% 1.65/1.09  #Split   : 1
% 1.65/1.09  #Chain   : 0
% 1.65/1.09  #Close   : 0
% 1.65/1.09  
% 1.65/1.09  Ordering : KBO
% 1.65/1.09  
% 1.65/1.09  Simplification rules
% 1.65/1.09  ----------------------
% 1.65/1.09  #Subsume      : 0
% 1.65/1.09  #Demod        : 0
% 1.65/1.09  #Tautology    : 2
% 1.65/1.09  #SimpNegUnit  : 1
% 1.65/1.09  #BackRed      : 0
% 1.65/1.09  
% 1.65/1.09  #Partial instantiations: 0
% 1.65/1.09  #Strategies tried      : 1
% 1.65/1.09  
% 1.65/1.09  Timing (in seconds)
% 1.65/1.09  ----------------------
% 1.65/1.09  Preprocessing        : 0.26
% 1.65/1.09  Parsing              : 0.14
% 1.65/1.09  CNF conversion       : 0.01
% 1.65/1.09  Main loop            : 0.06
% 1.65/1.09  Inferencing          : 0.03
% 1.65/1.09  Reduction            : 0.02
% 1.65/1.09  Demodulation         : 0.01
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
