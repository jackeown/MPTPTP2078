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

% Result     : Theorem 1.82s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 173 expanded)
%              Number of leaves         :   26 (  66 expanded)
%              Depth                    :    9
%              Number of atoms          :   94 ( 399 expanded)
%              Number of equality atoms :   53 ( 232 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_funct_2)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_63,axiom,(
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

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_69,plain,(
    ! [A_31,B_32,C_33,D_34] :
      ( k7_relset_1(A_31,B_32,C_33,D_34) = k9_relat_1(C_33,D_34)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_72,plain,(
    ! [D_34] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_34) = k9_relat_1('#skF_3',D_34) ),
    inference(resolution,[status(thm)],[c_28,c_69])).

tff(c_48,plain,(
    ! [A_22,B_23,C_24] :
      ( k2_relset_1(A_22,B_23,C_24) = k2_relat_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_52,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_48])).

tff(c_24,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_53,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_24])).

tff(c_73,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_53])).

tff(c_43,plain,(
    ! [C_19,A_20,B_21] :
      ( v1_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_47,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_43])).

tff(c_26,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_33,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_30,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_59,plain,(
    ! [A_26,B_27,C_28] :
      ( k1_relset_1(A_26,B_27,C_28) = k1_relat_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_63,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_59])).

tff(c_85,plain,(
    ! [B_40,A_41,C_42] :
      ( k1_xboole_0 = B_40
      | k1_relset_1(A_41,B_40,C_42) = A_41
      | ~ v1_funct_2(C_42,A_41,B_40)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_41,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_88,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_85])).

tff(c_91,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_63,c_88])).

tff(c_92,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_91])).

tff(c_2,plain,(
    ! [A_1] :
      ( k9_relat_1(A_1,k1_relat_1(A_1)) = k2_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_97,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_2])).

tff(c_101,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_97])).

tff(c_103,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_101])).

tff(c_104,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_105,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_110,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_105])).

tff(c_116,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_28])).

tff(c_153,plain,(
    ! [A_54,B_55,C_56,D_57] :
      ( k7_relset_1(A_54,B_55,C_56,D_57) = k9_relat_1(C_56,D_57)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_156,plain,(
    ! [D_57] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_57) = k9_relat_1('#skF_3',D_57) ),
    inference(resolution,[status(thm)],[c_116,c_153])).

tff(c_132,plain,(
    ! [A_47,B_48,C_49] :
      ( k2_relset_1(A_47,B_48,C_49) = k2_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_136,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_116,c_132])).

tff(c_122,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_110,c_24])).

tff(c_137,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_122])).

tff(c_157,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_137])).

tff(c_117,plain,(
    ! [C_43,A_44,B_45] :
      ( v1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_121,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_116,c_117])).

tff(c_111,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_30])).

tff(c_144,plain,(
    ! [A_51,B_52,C_53] :
      ( k1_relset_1(A_51,B_52,C_53) = k1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_148,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_116,c_144])).

tff(c_20,plain,(
    ! [B_16,C_17] :
      ( k1_relset_1(k1_xboole_0,B_16,C_17) = k1_xboole_0
      | ~ v1_funct_2(C_17,k1_xboole_0,B_16)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_184,plain,(
    ! [B_63,C_64] :
      ( k1_relset_1('#skF_1',B_63,C_64) = '#skF_1'
      | ~ v1_funct_2(C_64,'#skF_1',B_63)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_63))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_104,c_104,c_104,c_20])).

tff(c_187,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_116,c_184])).

tff(c_190,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_148,c_187])).

tff(c_195,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_2])).

tff(c_199,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_195])).

tff(c_201,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_157,c_199])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:38:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.24  
% 2.02/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.24  %$ v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.02/1.24  
% 2.02/1.24  %Foreground sorts:
% 2.02/1.24  
% 2.02/1.24  
% 2.02/1.24  %Background operators:
% 2.02/1.24  
% 2.02/1.24  
% 2.02/1.24  %Foreground operators:
% 2.02/1.24  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.02/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.02/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.02/1.24  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.02/1.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.02/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.24  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.02/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.24  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.02/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.02/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.02/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.02/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.02/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.02/1.24  
% 2.02/1.25  tff(f_76, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_funct_2)).
% 2.02/1.25  tff(f_45, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.02/1.25  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.02/1.25  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.02/1.25  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.02/1.25  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.02/1.25  tff(f_29, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.02/1.25  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.02/1.25  tff(c_69, plain, (![A_31, B_32, C_33, D_34]: (k7_relset_1(A_31, B_32, C_33, D_34)=k9_relat_1(C_33, D_34) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.02/1.25  tff(c_72, plain, (![D_34]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_34)=k9_relat_1('#skF_3', D_34))), inference(resolution, [status(thm)], [c_28, c_69])).
% 2.02/1.25  tff(c_48, plain, (![A_22, B_23, C_24]: (k2_relset_1(A_22, B_23, C_24)=k2_relat_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.02/1.25  tff(c_52, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_48])).
% 2.02/1.25  tff(c_24, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.02/1.25  tff(c_53, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_24])).
% 2.02/1.25  tff(c_73, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_53])).
% 2.02/1.25  tff(c_43, plain, (![C_19, A_20, B_21]: (v1_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.02/1.25  tff(c_47, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_43])).
% 2.02/1.25  tff(c_26, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.02/1.25  tff(c_33, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_26])).
% 2.02/1.25  tff(c_30, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.02/1.25  tff(c_59, plain, (![A_26, B_27, C_28]: (k1_relset_1(A_26, B_27, C_28)=k1_relat_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.02/1.25  tff(c_63, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_59])).
% 2.02/1.25  tff(c_85, plain, (![B_40, A_41, C_42]: (k1_xboole_0=B_40 | k1_relset_1(A_41, B_40, C_42)=A_41 | ~v1_funct_2(C_42, A_41, B_40) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_41, B_40))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.02/1.25  tff(c_88, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_85])).
% 2.02/1.25  tff(c_91, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_63, c_88])).
% 2.02/1.25  tff(c_92, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_33, c_91])).
% 2.02/1.25  tff(c_2, plain, (![A_1]: (k9_relat_1(A_1, k1_relat_1(A_1))=k2_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.02/1.25  tff(c_97, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_92, c_2])).
% 2.02/1.25  tff(c_101, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_97])).
% 2.02/1.25  tff(c_103, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_101])).
% 2.02/1.25  tff(c_104, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_26])).
% 2.02/1.25  tff(c_105, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_26])).
% 2.02/1.25  tff(c_110, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_105])).
% 2.02/1.25  tff(c_116, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_28])).
% 2.02/1.25  tff(c_153, plain, (![A_54, B_55, C_56, D_57]: (k7_relset_1(A_54, B_55, C_56, D_57)=k9_relat_1(C_56, D_57) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.02/1.25  tff(c_156, plain, (![D_57]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_57)=k9_relat_1('#skF_3', D_57))), inference(resolution, [status(thm)], [c_116, c_153])).
% 2.02/1.25  tff(c_132, plain, (![A_47, B_48, C_49]: (k2_relset_1(A_47, B_48, C_49)=k2_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.02/1.25  tff(c_136, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_116, c_132])).
% 2.02/1.25  tff(c_122, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_110, c_24])).
% 2.02/1.25  tff(c_137, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_122])).
% 2.02/1.25  tff(c_157, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_137])).
% 2.02/1.25  tff(c_117, plain, (![C_43, A_44, B_45]: (v1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.02/1.25  tff(c_121, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_116, c_117])).
% 2.02/1.25  tff(c_111, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_30])).
% 2.02/1.25  tff(c_144, plain, (![A_51, B_52, C_53]: (k1_relset_1(A_51, B_52, C_53)=k1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.02/1.25  tff(c_148, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_116, c_144])).
% 2.02/1.25  tff(c_20, plain, (![B_16, C_17]: (k1_relset_1(k1_xboole_0, B_16, C_17)=k1_xboole_0 | ~v1_funct_2(C_17, k1_xboole_0, B_16) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_16))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.02/1.25  tff(c_184, plain, (![B_63, C_64]: (k1_relset_1('#skF_1', B_63, C_64)='#skF_1' | ~v1_funct_2(C_64, '#skF_1', B_63) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_63))))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_104, c_104, c_104, c_20])).
% 2.02/1.25  tff(c_187, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_116, c_184])).
% 2.02/1.25  tff(c_190, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_111, c_148, c_187])).
% 2.02/1.25  tff(c_195, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_190, c_2])).
% 2.02/1.25  tff(c_199, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_195])).
% 2.02/1.25  tff(c_201, plain, $false, inference(negUnitSimplification, [status(thm)], [c_157, c_199])).
% 2.02/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.25  
% 2.02/1.25  Inference rules
% 2.02/1.25  ----------------------
% 2.02/1.25  #Ref     : 0
% 2.02/1.25  #Sup     : 38
% 2.02/1.25  #Fact    : 0
% 2.02/1.26  #Define  : 0
% 2.02/1.26  #Split   : 1
% 2.02/1.26  #Chain   : 0
% 2.02/1.26  #Close   : 0
% 2.02/1.26  
% 2.02/1.26  Ordering : KBO
% 2.02/1.26  
% 2.02/1.26  Simplification rules
% 2.02/1.26  ----------------------
% 2.02/1.26  #Subsume      : 0
% 2.02/1.26  #Demod        : 37
% 2.02/1.26  #Tautology    : 24
% 2.02/1.26  #SimpNegUnit  : 3
% 2.02/1.26  #BackRed      : 7
% 2.02/1.26  
% 2.02/1.26  #Partial instantiations: 0
% 2.02/1.26  #Strategies tried      : 1
% 2.02/1.26  
% 2.02/1.26  Timing (in seconds)
% 2.02/1.26  ----------------------
% 2.02/1.26  Preprocessing        : 0.29
% 2.02/1.26  Parsing              : 0.15
% 2.02/1.26  CNF conversion       : 0.02
% 2.02/1.26  Main loop            : 0.17
% 2.02/1.26  Inferencing          : 0.06
% 2.02/1.26  Reduction            : 0.05
% 2.02/1.26  Demodulation         : 0.04
% 2.02/1.26  BG Simplification    : 0.01
% 2.02/1.26  Subsumption          : 0.02
% 2.02/1.26  Abstraction          : 0.01
% 2.02/1.26  MUC search           : 0.00
% 2.02/1.26  Cooper               : 0.00
% 2.02/1.26  Total                : 0.49
% 2.02/1.26  Index Insertion      : 0.00
% 2.02/1.26  Index Deletion       : 0.00
% 2.02/1.26  Index Matching       : 0.00
% 2.02/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
