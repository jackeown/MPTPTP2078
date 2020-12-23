%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:34 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   26 (  68 expanded)
%              Number of leaves         :   14 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   36 ( 170 expanded)
%              Number of equality atoms :   19 (  82 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(c_14,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_25,plain,(
    ! [B_11,A_12,C_13] :
      ( k1_xboole_0 = B_11
      | k1_relset_1(A_12,B_11,C_13) = A_12
      | ~ v1_funct_2(C_13,A_12,B_11)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_12,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_28,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_25])).

tff(c_31,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_28])).

tff(c_32,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_31])).

tff(c_10,plain,(
    ! [B_2,C_3] :
      ( k1_relset_1(k1_xboole_0,B_2,C_3) = k1_xboole_0
      | ~ v1_funct_2(C_3,k1_xboole_0,B_2)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_57,plain,(
    ! [B_19,C_20] :
      ( k1_relset_1('#skF_1',B_19,C_20) = '#skF_1'
      | ~ v1_funct_2(C_20,'#skF_1',B_19)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_19))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_32,c_32,c_10])).

tff(c_60,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_57])).

tff(c_63,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_60])).

tff(c_65,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:48:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.32  
% 1.77/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.32  %$ v1_funct_2 > m1_subset_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.77/1.32  
% 1.77/1.32  %Foreground sorts:
% 1.77/1.32  
% 1.77/1.32  
% 1.77/1.32  %Background operators:
% 1.77/1.32  
% 1.77/1.32  
% 1.77/1.32  %Foreground operators:
% 1.77/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.77/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.77/1.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.77/1.32  tff('#skF_2', type, '#skF_2': $i).
% 1.77/1.32  tff('#skF_1', type, '#skF_1': $i).
% 1.77/1.32  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.77/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.77/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.77/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.77/1.32  
% 1.94/1.33  tff(f_52, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 1.94/1.33  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 1.94/1.33  tff(c_14, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.94/1.33  tff(c_18, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.94/1.33  tff(c_16, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.94/1.33  tff(c_25, plain, (![B_11, A_12, C_13]: (k1_xboole_0=B_11 | k1_relset_1(A_12, B_11, C_13)=A_12 | ~v1_funct_2(C_13, A_12, B_11) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_12, B_11))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.94/1.33  tff(c_28, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_16, c_25])).
% 1.94/1.33  tff(c_31, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_28])).
% 1.94/1.33  tff(c_32, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_14, c_31])).
% 1.94/1.33  tff(c_10, plain, (![B_2, C_3]: (k1_relset_1(k1_xboole_0, B_2, C_3)=k1_xboole_0 | ~v1_funct_2(C_3, k1_xboole_0, B_2) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_2))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.94/1.33  tff(c_57, plain, (![B_19, C_20]: (k1_relset_1('#skF_1', B_19, C_20)='#skF_1' | ~v1_funct_2(C_20, '#skF_1', B_19) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_19))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_32, c_32, c_10])).
% 1.94/1.33  tff(c_60, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_16, c_57])).
% 1.94/1.33  tff(c_63, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_60])).
% 1.94/1.33  tff(c_65, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_63])).
% 1.94/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.33  
% 1.94/1.33  Inference rules
% 1.94/1.33  ----------------------
% 1.94/1.33  #Ref     : 0
% 1.94/1.33  #Sup     : 6
% 1.94/1.33  #Fact    : 0
% 1.94/1.33  #Define  : 0
% 1.94/1.33  #Split   : 0
% 1.94/1.33  #Chain   : 0
% 1.94/1.33  #Close   : 0
% 1.94/1.33  
% 1.94/1.33  Ordering : KBO
% 1.94/1.33  
% 1.94/1.33  Simplification rules
% 1.94/1.33  ----------------------
% 1.94/1.33  #Subsume      : 1
% 1.94/1.33  #Demod        : 22
% 1.94/1.33  #Tautology    : 3
% 1.94/1.33  #SimpNegUnit  : 2
% 1.94/1.33  #BackRed      : 5
% 1.94/1.33  
% 1.94/1.33  #Partial instantiations: 0
% 1.94/1.33  #Strategies tried      : 1
% 1.94/1.33  
% 1.94/1.33  Timing (in seconds)
% 1.94/1.33  ----------------------
% 1.94/1.33  Preprocessing        : 0.37
% 1.94/1.33  Parsing              : 0.23
% 1.94/1.33  CNF conversion       : 0.02
% 1.94/1.33  Main loop            : 0.10
% 1.94/1.33  Inferencing          : 0.04
% 1.94/1.33  Reduction            : 0.03
% 1.94/1.33  Demodulation         : 0.02
% 1.94/1.33  BG Simplification    : 0.01
% 1.94/1.33  Subsumption          : 0.02
% 1.94/1.33  Abstraction          : 0.00
% 1.94/1.33  MUC search           : 0.00
% 1.94/1.33  Cooper               : 0.00
% 1.94/1.33  Total                : 0.50
% 1.94/1.33  Index Insertion      : 0.00
% 1.94/1.33  Index Deletion       : 0.00
% 1.94/1.33  Index Matching       : 0.00
% 1.94/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
