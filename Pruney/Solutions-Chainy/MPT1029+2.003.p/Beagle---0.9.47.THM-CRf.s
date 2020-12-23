%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:48 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   43 (  79 expanded)
%              Number of leaves         :   18 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   65 ( 224 expanded)
%              Number of equality atoms :   11 (  61 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(c_10,plain,(
    ~ v1_partfun1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_12,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_12])).

tff(c_22,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_34,plain,(
    ! [C_14,A_15,B_16] :
      ( v1_partfun1(C_14,A_15)
      | ~ v1_funct_2(C_14,A_15,B_16)
      | ~ v1_funct_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16)))
      | v1_xboole_0(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_37,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_34])).

tff(c_40,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_16,c_37])).

tff(c_41,plain,(
    v1_xboole_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_40])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_44,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_41,c_2])).

tff(c_48,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_44])).

tff(c_49,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_50,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_56,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_50])).

tff(c_63,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_20])).

tff(c_64,plain,(
    ! [C_18,A_19,B_20] :
      ( v1_partfun1(C_18,A_19)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20)))
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_67,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_63,c_64])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_67])).

tff(c_61,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_16])).

tff(c_71,plain,(
    ! [C_21,A_22,B_23] :
      ( v1_partfun1(C_21,A_22)
      | ~ v1_funct_2(C_21,A_22,B_23)
      | ~ v1_funct_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | v1_xboole_0(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_74,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_63,c_71])).

tff(c_77,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_61,c_74])).

tff(c_79,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_10,c_77])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n013.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 12:41:09 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.18/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.11  
% 1.74/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.11  %$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.74/1.11  
% 1.74/1.11  %Foreground sorts:
% 1.74/1.11  
% 1.74/1.11  
% 1.74/1.11  %Background operators:
% 1.74/1.11  
% 1.74/1.11  
% 1.74/1.11  %Foreground operators:
% 1.74/1.11  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.74/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.74/1.11  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.74/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.74/1.11  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 1.74/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.74/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.74/1.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.74/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.74/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.74/1.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.74/1.11  
% 1.74/1.13  tff(f_68, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 1.74/1.13  tff(f_50, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 1.74/1.13  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.74/1.13  tff(f_36, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 1.74/1.13  tff(c_10, plain, (~v1_partfun1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.74/1.13  tff(c_12, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.74/1.13  tff(c_26, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_12])).
% 1.74/1.13  tff(c_22, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.74/1.13  tff(c_16, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.74/1.13  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.74/1.13  tff(c_34, plain, (![C_14, A_15, B_16]: (v1_partfun1(C_14, A_15) | ~v1_funct_2(C_14, A_15, B_16) | ~v1_funct_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))) | v1_xboole_0(B_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.74/1.13  tff(c_37, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_20, c_34])).
% 1.74/1.13  tff(c_40, plain, (v1_partfun1('#skF_3', '#skF_1') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_16, c_37])).
% 1.74/1.13  tff(c_41, plain, (v1_xboole_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_10, c_40])).
% 1.74/1.13  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.74/1.13  tff(c_44, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_41, c_2])).
% 1.74/1.13  tff(c_48, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_44])).
% 1.74/1.13  tff(c_49, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_12])).
% 1.74/1.13  tff(c_50, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_12])).
% 1.74/1.13  tff(c_56, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_49, c_50])).
% 1.74/1.13  tff(c_63, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_20])).
% 1.74/1.13  tff(c_64, plain, (![C_18, A_19, B_20]: (v1_partfun1(C_18, A_19) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.74/1.13  tff(c_67, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_63, c_64])).
% 1.74/1.13  tff(c_70, plain, (~v1_xboole_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_10, c_67])).
% 1.74/1.13  tff(c_61, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_16])).
% 1.74/1.13  tff(c_71, plain, (![C_21, A_22, B_23]: (v1_partfun1(C_21, A_22) | ~v1_funct_2(C_21, A_22, B_23) | ~v1_funct_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | v1_xboole_0(B_23))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.74/1.13  tff(c_74, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_63, c_71])).
% 1.74/1.13  tff(c_77, plain, (v1_partfun1('#skF_3', '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_61, c_74])).
% 1.74/1.13  tff(c_79, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_10, c_77])).
% 1.74/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.13  
% 1.74/1.13  Inference rules
% 1.74/1.13  ----------------------
% 1.74/1.13  #Ref     : 0
% 1.74/1.13  #Sup     : 9
% 1.74/1.13  #Fact    : 0
% 1.74/1.13  #Define  : 0
% 1.74/1.13  #Split   : 1
% 1.74/1.13  #Chain   : 0
% 1.74/1.13  #Close   : 0
% 1.74/1.13  
% 1.74/1.13  Ordering : KBO
% 1.74/1.13  
% 1.74/1.13  Simplification rules
% 1.74/1.13  ----------------------
% 1.74/1.13  #Subsume      : 0
% 1.74/1.13  #Demod        : 10
% 1.74/1.13  #Tautology    : 7
% 1.74/1.13  #SimpNegUnit  : 5
% 1.74/1.13  #BackRed      : 1
% 1.74/1.13  
% 1.74/1.13  #Partial instantiations: 0
% 1.74/1.13  #Strategies tried      : 1
% 1.74/1.13  
% 1.74/1.13  Timing (in seconds)
% 1.74/1.13  ----------------------
% 1.74/1.13  Preprocessing        : 0.29
% 1.74/1.13  Parsing              : 0.16
% 1.74/1.13  CNF conversion       : 0.02
% 1.74/1.13  Main loop            : 0.10
% 1.74/1.13  Inferencing          : 0.04
% 1.74/1.13  Reduction            : 0.03
% 1.74/1.13  Demodulation         : 0.02
% 1.74/1.13  BG Simplification    : 0.01
% 1.74/1.13  Subsumption          : 0.01
% 1.74/1.13  Abstraction          : 0.00
% 1.74/1.13  MUC search           : 0.00
% 1.74/1.13  Cooper               : 0.00
% 1.74/1.13  Total                : 0.42
% 1.74/1.13  Index Insertion      : 0.00
% 1.74/1.13  Index Deletion       : 0.00
% 1.74/1.13  Index Matching       : 0.00
% 1.74/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
