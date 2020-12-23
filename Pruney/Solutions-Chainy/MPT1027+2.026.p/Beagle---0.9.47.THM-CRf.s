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
% DateTime   : Thu Dec  3 10:16:45 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   57 (1450 expanded)
%              Number of leaves         :   19 ( 479 expanded)
%              Depth                    :   13
%              Number of atoms          :   84 (3377 expanded)
%              Number of equality atoms :   30 ( 703 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_59,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_43,plain,(
    ! [C_13,B_14,A_15] :
      ( v1_xboole_0(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(B_14,A_15)))
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_47,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_43])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_47])).

tff(c_26,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_28,plain,(
    ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_20])).

tff(c_22,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_53,plain,(
    ! [B_23,C_24,A_25] :
      ( k1_xboole_0 = B_23
      | v1_funct_2(C_24,A_25,B_23)
      | k1_relset_1(A_25,B_23,C_24) != A_25
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_25,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_56,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2')
    | k1_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_24,c_53])).

tff(c_59,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_56])).

tff(c_60,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_59])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_74,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2])).

tff(c_76,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_74])).

tff(c_77,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_47])).

tff(c_33,plain,(
    ! [B_10,A_11] :
      ( ~ v1_xboole_0(B_10)
      | B_10 = A_11
      | ~ v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_36,plain,(
    ! [A_11] :
      ( k1_xboole_0 = A_11
      | ~ v1_xboole_0(A_11) ) ),
    inference(resolution,[status(thm)],[c_2,c_33])).

tff(c_84,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_77,c_36])).

tff(c_78,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_47])).

tff(c_91,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_78,c_36])).

tff(c_100,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_91])).

tff(c_104,plain,(
    ~ v1_funct_2('#skF_3','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_28])).

tff(c_102,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_24])).

tff(c_8,plain,(
    ! [A_7] :
      ( v1_funct_2(k1_xboole_0,A_7,k1_xboole_0)
      | k1_xboole_0 = A_7
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_7,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_117,plain,(
    ! [A_7] :
      ( v1_funct_2('#skF_3',A_7,'#skF_3')
      | A_7 = '#skF_3'
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_7,'#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_84,c_84,c_84,c_84,c_8])).

tff(c_125,plain,
    ( v1_funct_2('#skF_3','#skF_1','#skF_3')
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_102,c_117])).

tff(c_131,plain,(
    '#skF_3' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_125])).

tff(c_138,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_131,c_104])).

tff(c_103,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_22])).

tff(c_136,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_131,c_103])).

tff(c_135,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_131,c_102])).

tff(c_141,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_84])).

tff(c_12,plain,(
    ! [C_9,B_8] :
      ( v1_funct_2(C_9,k1_xboole_0,B_8)
      | k1_relset_1(k1_xboole_0,B_8,C_9) != k1_xboole_0
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_182,plain,(
    ! [C_34,B_35] :
      ( v1_funct_2(C_34,'#skF_1',B_35)
      | k1_relset_1('#skF_1',B_35,C_34) != '#skF_1'
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_35))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_141,c_141,c_141,c_12])).

tff(c_185,plain,
    ( v1_funct_2('#skF_1','#skF_1','#skF_1')
    | k1_relset_1('#skF_1','#skF_1','#skF_1') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_135,c_182])).

tff(c_188,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_185])).

tff(c_190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_188])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:23:06 EST 2020
% 0.21/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.19  
% 1.90/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.19  %$ v1_funct_2 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.90/1.19  
% 1.90/1.19  %Foreground sorts:
% 1.90/1.19  
% 1.90/1.19  
% 1.90/1.19  %Background operators:
% 1.90/1.19  
% 1.90/1.19  
% 1.90/1.19  %Foreground operators:
% 1.90/1.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.90/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.90/1.19  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.90/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.90/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.90/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.90/1.19  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.90/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.90/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.90/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.90/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.90/1.19  
% 1.90/1.20  tff(f_72, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_funct_2)).
% 1.90/1.20  tff(f_41, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 1.90/1.20  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 1.90/1.20  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.90/1.20  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 1.90/1.20  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.90/1.20  tff(c_43, plain, (![C_13, B_14, A_15]: (v1_xboole_0(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(B_14, A_15))) | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.90/1.20  tff(c_47, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_24, c_43])).
% 1.90/1.20  tff(c_48, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_47])).
% 1.90/1.20  tff(c_26, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.90/1.20  tff(c_20, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.90/1.20  tff(c_28, plain, (~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_20])).
% 1.90/1.20  tff(c_22, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.90/1.20  tff(c_53, plain, (![B_23, C_24, A_25]: (k1_xboole_0=B_23 | v1_funct_2(C_24, A_25, B_23) | k1_relset_1(A_25, B_23, C_24)!=A_25 | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_25, B_23))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.90/1.20  tff(c_56, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_24, c_53])).
% 1.90/1.20  tff(c_59, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_56])).
% 1.90/1.20  tff(c_60, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_28, c_59])).
% 1.90/1.20  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.90/1.20  tff(c_74, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2])).
% 1.90/1.20  tff(c_76, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_74])).
% 1.90/1.20  tff(c_77, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_47])).
% 1.90/1.20  tff(c_33, plain, (![B_10, A_11]: (~v1_xboole_0(B_10) | B_10=A_11 | ~v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.90/1.20  tff(c_36, plain, (![A_11]: (k1_xboole_0=A_11 | ~v1_xboole_0(A_11))), inference(resolution, [status(thm)], [c_2, c_33])).
% 1.90/1.20  tff(c_84, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_77, c_36])).
% 1.90/1.20  tff(c_78, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_47])).
% 1.90/1.20  tff(c_91, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_78, c_36])).
% 1.90/1.20  tff(c_100, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_91])).
% 1.90/1.20  tff(c_104, plain, (~v1_funct_2('#skF_3', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_28])).
% 1.90/1.20  tff(c_102, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_24])).
% 1.90/1.20  tff(c_8, plain, (![A_7]: (v1_funct_2(k1_xboole_0, A_7, k1_xboole_0) | k1_xboole_0=A_7 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_7, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.90/1.20  tff(c_117, plain, (![A_7]: (v1_funct_2('#skF_3', A_7, '#skF_3') | A_7='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_7, '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_84, c_84, c_84, c_84, c_8])).
% 1.90/1.20  tff(c_125, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_3') | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_102, c_117])).
% 1.90/1.20  tff(c_131, plain, ('#skF_3'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_104, c_125])).
% 1.90/1.20  tff(c_138, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_131, c_104])).
% 1.90/1.20  tff(c_103, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_22])).
% 1.90/1.20  tff(c_136, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_131, c_131, c_103])).
% 1.90/1.20  tff(c_135, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_131, c_102])).
% 1.90/1.20  tff(c_141, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_131, c_84])).
% 1.90/1.20  tff(c_12, plain, (![C_9, B_8]: (v1_funct_2(C_9, k1_xboole_0, B_8) | k1_relset_1(k1_xboole_0, B_8, C_9)!=k1_xboole_0 | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_8))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.90/1.20  tff(c_182, plain, (![C_34, B_35]: (v1_funct_2(C_34, '#skF_1', B_35) | k1_relset_1('#skF_1', B_35, C_34)!='#skF_1' | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_35))))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_141, c_141, c_141, c_12])).
% 1.90/1.20  tff(c_185, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1') | k1_relset_1('#skF_1', '#skF_1', '#skF_1')!='#skF_1'), inference(resolution, [status(thm)], [c_135, c_182])).
% 1.90/1.20  tff(c_188, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_185])).
% 1.90/1.20  tff(c_190, plain, $false, inference(negUnitSimplification, [status(thm)], [c_138, c_188])).
% 1.90/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.20  
% 1.90/1.20  Inference rules
% 1.90/1.20  ----------------------
% 1.90/1.20  #Ref     : 0
% 1.90/1.20  #Sup     : 33
% 1.90/1.20  #Fact    : 0
% 1.90/1.20  #Define  : 0
% 1.90/1.20  #Split   : 1
% 1.90/1.20  #Chain   : 0
% 1.90/1.20  #Close   : 0
% 1.90/1.20  
% 1.90/1.20  Ordering : KBO
% 1.90/1.20  
% 1.90/1.20  Simplification rules
% 1.90/1.20  ----------------------
% 1.90/1.20  #Subsume      : 5
% 1.90/1.20  #Demod        : 69
% 1.90/1.20  #Tautology    : 23
% 1.90/1.20  #SimpNegUnit  : 4
% 1.90/1.20  #BackRed      : 23
% 1.90/1.20  
% 1.90/1.20  #Partial instantiations: 0
% 1.90/1.20  #Strategies tried      : 1
% 1.90/1.20  
% 1.90/1.20  Timing (in seconds)
% 1.90/1.20  ----------------------
% 1.90/1.21  Preprocessing        : 0.28
% 1.90/1.21  Parsing              : 0.15
% 1.90/1.21  CNF conversion       : 0.02
% 1.90/1.21  Main loop            : 0.17
% 1.90/1.21  Inferencing          : 0.05
% 1.90/1.21  Reduction            : 0.05
% 1.90/1.21  Demodulation         : 0.04
% 1.90/1.21  BG Simplification    : 0.01
% 1.90/1.21  Subsumption          : 0.03
% 1.90/1.21  Abstraction          : 0.01
% 1.90/1.21  MUC search           : 0.00
% 1.90/1.21  Cooper               : 0.00
% 1.90/1.21  Total                : 0.48
% 1.90/1.21  Index Insertion      : 0.00
% 1.90/1.21  Index Deletion       : 0.00
% 1.90/1.21  Index Matching       : 0.00
% 1.90/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
