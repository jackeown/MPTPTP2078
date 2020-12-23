%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:31 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   32 (  39 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :    4
%              Number of atoms          :   43 ( 106 expanded)
%              Number of equality atoms :    1 (   8 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_funct_1 > k1_partfun1 > k2_zfmisc_1 > #nlpp > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( B != k1_xboole_0
            & ? [D] :
                ( v1_funct_1(D)
                & v1_funct_2(D,B,A)
                & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
                & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A)) )
            & ~ v2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_2)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
           => ( v2_funct_1(C)
              & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

tff(c_6,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_22,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_20,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_14,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_12,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_10,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_23,plain,(
    ! [C_7,A_8,B_9,D_10] :
      ( v2_funct_1(C_7)
      | ~ r2_relset_1(A_8,A_8,k1_partfun1(A_8,B_9,B_9,A_8,C_7,D_10),k6_partfun1(A_8))
      | ~ m1_subset_1(D_10,k1_zfmisc_1(k2_zfmisc_1(B_9,A_8)))
      | ~ v1_funct_2(D_10,B_9,A_8)
      | ~ v1_funct_1(D_10)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_funct_2(C_7,A_8,B_9)
      | ~ v1_funct_1(C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_26,plain,
    ( v2_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_23])).

tff(c_29,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_14,c_12,c_10,c_26])).

tff(c_31,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.11  
% 1.75/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.11  %$ r2_relset_1 > v1_funct_2 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_funct_1 > k1_partfun1 > k2_zfmisc_1 > #nlpp > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.75/1.11  
% 1.75/1.11  %Foreground sorts:
% 1.75/1.11  
% 1.75/1.11  
% 1.75/1.11  %Background operators:
% 1.75/1.11  
% 1.75/1.11  
% 1.75/1.11  %Foreground operators:
% 1.75/1.11  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.75/1.11  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.75/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.11  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 1.75/1.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.75/1.11  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.75/1.11  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.75/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.75/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.75/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.75/1.11  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 1.75/1.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.75/1.11  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 1.75/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.75/1.11  tff('#skF_4', type, '#skF_4': $i).
% 1.75/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.75/1.11  
% 1.75/1.12  tff(f_67, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~((~(B = k1_xboole_0) & (?[D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))))) & ~v2_funct_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_funct_2)).
% 1.75/1.12  tff(f_44, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 1.75/1.12  tff(c_6, plain, (~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.75/1.12  tff(c_22, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.75/1.12  tff(c_20, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.75/1.12  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.75/1.12  tff(c_14, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.75/1.12  tff(c_12, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.75/1.12  tff(c_10, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.75/1.12  tff(c_8, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.75/1.12  tff(c_23, plain, (![C_7, A_8, B_9, D_10]: (v2_funct_1(C_7) | ~r2_relset_1(A_8, A_8, k1_partfun1(A_8, B_9, B_9, A_8, C_7, D_10), k6_partfun1(A_8)) | ~m1_subset_1(D_10, k1_zfmisc_1(k2_zfmisc_1(B_9, A_8))) | ~v1_funct_2(D_10, B_9, A_8) | ~v1_funct_1(D_10) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))) | ~v1_funct_2(C_7, A_8, B_9) | ~v1_funct_1(C_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.75/1.12  tff(c_26, plain, (v2_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_23])).
% 1.75/1.12  tff(c_29, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_18, c_14, c_12, c_10, c_26])).
% 1.75/1.12  tff(c_31, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6, c_29])).
% 1.75/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.12  
% 1.75/1.12  Inference rules
% 1.75/1.12  ----------------------
% 1.75/1.12  #Ref     : 0
% 1.75/1.12  #Sup     : 1
% 1.75/1.12  #Fact    : 0
% 1.75/1.12  #Define  : 0
% 1.75/1.12  #Split   : 0
% 1.75/1.12  #Chain   : 0
% 1.75/1.12  #Close   : 0
% 1.75/1.12  
% 1.75/1.12  Ordering : KBO
% 1.75/1.12  
% 1.75/1.12  Simplification rules
% 1.75/1.12  ----------------------
% 1.75/1.12  #Subsume      : 0
% 1.75/1.12  #Demod        : 6
% 1.75/1.12  #Tautology    : 0
% 1.75/1.12  #SimpNegUnit  : 1
% 1.75/1.12  #BackRed      : 0
% 1.75/1.12  
% 1.75/1.12  #Partial instantiations: 0
% 1.75/1.12  #Strategies tried      : 1
% 1.75/1.12  
% 1.75/1.12  Timing (in seconds)
% 1.75/1.12  ----------------------
% 1.75/1.12  Preprocessing        : 0.29
% 1.75/1.12  Parsing              : 0.15
% 1.75/1.12  CNF conversion       : 0.02
% 1.75/1.12  Main loop            : 0.08
% 1.75/1.12  Inferencing          : 0.04
% 1.75/1.12  Reduction            : 0.03
% 1.75/1.12  Demodulation         : 0.02
% 1.75/1.12  BG Simplification    : 0.01
% 1.75/1.12  Subsumption          : 0.01
% 1.75/1.12  Abstraction          : 0.00
% 1.75/1.12  MUC search           : 0.00
% 1.75/1.12  Cooper               : 0.00
% 1.75/1.12  Total                : 0.39
% 1.75/1.12  Index Insertion      : 0.00
% 1.75/1.12  Index Deletion       : 0.00
% 1.75/1.13  Index Matching       : 0.00
% 1.75/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
