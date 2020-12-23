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
% DateTime   : Thu Dec  3 10:13:58 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 192 expanded)
%              Number of leaves         :   28 (  73 expanded)
%              Depth                    :    9
%              Number of atoms          :  103 ( 445 expanded)
%              Number of equality atoms :   59 ( 259 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => k8_relset_1(A,B,C,k7_relset_1(A,B,C,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_2)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_69,axiom,(
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

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_38,plain,(
    ! [C_21,A_22,B_23] :
      ( v1_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_42,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_38])).

tff(c_2,plain,(
    ! [A_1] :
      ( k10_relat_1(A_1,k2_relat_1(A_1)) = k1_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    ! [A_26,B_27,C_28] :
      ( k2_relset_1(A_26,B_27,C_28) = k2_relat_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_57,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_53])).

tff(c_97,plain,(
    ! [A_46,B_47,C_48] :
      ( k7_relset_1(A_46,B_47,C_48,A_46) = k2_relset_1(A_46,B_47,C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_99,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') = k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_97])).

tff(c_101,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_99])).

tff(c_71,plain,(
    ! [A_32,B_33,C_34,D_35] :
      ( k8_relset_1(A_32,B_33,C_34,D_35) = k10_relat_1(C_34,D_35)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_74,plain,(
    ! [D_35] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_35) = k10_relat_1('#skF_3',D_35) ),
    inference(resolution,[status(thm)],[c_32,c_71])).

tff(c_28,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3',k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_76,plain,(
    k10_relat_1('#skF_3',k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_28])).

tff(c_102,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_76])).

tff(c_109,plain,
    ( k1_relat_1('#skF_3') != '#skF_1'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_102])).

tff(c_111,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_109])).

tff(c_30,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_37,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_34,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_62,plain,(
    ! [A_29,B_30,C_31] :
      ( k1_relset_1(A_29,B_30,C_31) = k1_relat_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_66,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_62])).

tff(c_119,plain,(
    ! [B_52,A_53,C_54] :
      ( k1_xboole_0 = B_52
      | k1_relset_1(A_53,B_52,C_54) = A_53
      | ~ v1_funct_2(C_54,A_53,B_52)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_53,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_122,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_119])).

tff(c_125,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_66,c_122])).

tff(c_127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_37,c_125])).

tff(c_128,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_129,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_134,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_129])).

tff(c_135,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_32])).

tff(c_141,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_145,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_135,c_141])).

tff(c_136,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_34])).

tff(c_156,plain,(
    ! [A_59,B_60,C_61] :
      ( k1_relset_1(A_59,B_60,C_61) = k1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_160,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_135,c_156])).

tff(c_24,plain,(
    ! [B_19,C_20] :
      ( k1_relset_1(k1_xboole_0,B_19,C_20) = k1_xboole_0
      | ~ v1_funct_2(C_20,k1_xboole_0,B_19)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_216,plain,(
    ! [B_78,C_79] :
      ( k1_relset_1('#skF_1',B_78,C_79) = '#skF_1'
      | ~ v1_funct_2(C_79,'#skF_1',B_78)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_78))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_128,c_128,c_128,c_24])).

tff(c_219,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_135,c_216])).

tff(c_222,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_160,c_219])).

tff(c_167,plain,(
    ! [A_63,B_64,C_65] :
      ( k2_relset_1(A_63,B_64,C_65) = k2_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_171,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_135,c_167])).

tff(c_237,plain,(
    ! [A_80,B_81,C_82] :
      ( k7_relset_1(A_80,B_81,C_82,A_80) = k2_relset_1(A_80,B_81,C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_239,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_1') = k2_relset_1('#skF_1','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_135,c_237])).

tff(c_241,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_239])).

tff(c_185,plain,(
    ! [A_68,B_69,C_70,D_71] :
      ( k8_relset_1(A_68,B_69,C_70,D_71) = k10_relat_1(C_70,D_71)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_188,plain,(
    ! [D_71] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_71) = k10_relat_1('#skF_3',D_71) ),
    inference(resolution,[status(thm)],[c_135,c_185])).

tff(c_155,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_134,c_28])).

tff(c_189,plain,(
    k10_relat_1('#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_155])).

tff(c_242,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_189])).

tff(c_258,plain,
    ( k1_relat_1('#skF_3') != '#skF_1'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_242])).

tff(c_261,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_222,c_258])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n003.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 20:33:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.24  
% 2.18/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.24  %$ v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.18/1.24  
% 2.18/1.24  %Foreground sorts:
% 2.18/1.24  
% 2.18/1.24  
% 2.18/1.24  %Background operators:
% 2.18/1.24  
% 2.18/1.24  
% 2.18/1.24  %Foreground operators:
% 2.18/1.24  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.18/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.18/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.24  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.18/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.18/1.24  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.18/1.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.18/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.24  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.18/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.24  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.18/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.18/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.18/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.18/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.24  
% 2.18/1.26  tff(f_82, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, k7_relset_1(A, B, C, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_funct_2)).
% 2.18/1.26  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.18/1.26  tff(f_29, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.18/1.26  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.18/1.26  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 2.18/1.26  tff(f_45, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.18/1.26  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.18/1.26  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.18/1.26  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.18/1.26  tff(c_38, plain, (![C_21, A_22, B_23]: (v1_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.18/1.26  tff(c_42, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_38])).
% 2.18/1.26  tff(c_2, plain, (![A_1]: (k10_relat_1(A_1, k2_relat_1(A_1))=k1_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.18/1.26  tff(c_53, plain, (![A_26, B_27, C_28]: (k2_relset_1(A_26, B_27, C_28)=k2_relat_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.18/1.26  tff(c_57, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_53])).
% 2.18/1.26  tff(c_97, plain, (![A_46, B_47, C_48]: (k7_relset_1(A_46, B_47, C_48, A_46)=k2_relset_1(A_46, B_47, C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.18/1.26  tff(c_99, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_97])).
% 2.18/1.26  tff(c_101, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_99])).
% 2.18/1.26  tff(c_71, plain, (![A_32, B_33, C_34, D_35]: (k8_relset_1(A_32, B_33, C_34, D_35)=k10_relat_1(C_34, D_35) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.18/1.26  tff(c_74, plain, (![D_35]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_35)=k10_relat_1('#skF_3', D_35))), inference(resolution, [status(thm)], [c_32, c_71])).
% 2.18/1.26  tff(c_28, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.18/1.26  tff(c_76, plain, (k10_relat_1('#skF_3', k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_28])).
% 2.18/1.26  tff(c_102, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_101, c_76])).
% 2.18/1.26  tff(c_109, plain, (k1_relat_1('#skF_3')!='#skF_1' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2, c_102])).
% 2.18/1.26  tff(c_111, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_109])).
% 2.18/1.26  tff(c_30, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.18/1.26  tff(c_37, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_30])).
% 2.18/1.26  tff(c_34, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.18/1.26  tff(c_62, plain, (![A_29, B_30, C_31]: (k1_relset_1(A_29, B_30, C_31)=k1_relat_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.18/1.26  tff(c_66, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_62])).
% 2.18/1.26  tff(c_119, plain, (![B_52, A_53, C_54]: (k1_xboole_0=B_52 | k1_relset_1(A_53, B_52, C_54)=A_53 | ~v1_funct_2(C_54, A_53, B_52) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_53, B_52))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.18/1.26  tff(c_122, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_119])).
% 2.18/1.26  tff(c_125, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_66, c_122])).
% 2.18/1.26  tff(c_127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111, c_37, c_125])).
% 2.18/1.26  tff(c_128, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_30])).
% 2.18/1.26  tff(c_129, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_30])).
% 2.18/1.26  tff(c_134, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_128, c_129])).
% 2.18/1.26  tff(c_135, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_32])).
% 2.18/1.26  tff(c_141, plain, (![C_55, A_56, B_57]: (v1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.18/1.26  tff(c_145, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_135, c_141])).
% 2.18/1.26  tff(c_136, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_34])).
% 2.18/1.26  tff(c_156, plain, (![A_59, B_60, C_61]: (k1_relset_1(A_59, B_60, C_61)=k1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.18/1.26  tff(c_160, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_135, c_156])).
% 2.18/1.26  tff(c_24, plain, (![B_19, C_20]: (k1_relset_1(k1_xboole_0, B_19, C_20)=k1_xboole_0 | ~v1_funct_2(C_20, k1_xboole_0, B_19) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_19))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.18/1.26  tff(c_216, plain, (![B_78, C_79]: (k1_relset_1('#skF_1', B_78, C_79)='#skF_1' | ~v1_funct_2(C_79, '#skF_1', B_78) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_78))))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_128, c_128, c_128, c_24])).
% 2.18/1.26  tff(c_219, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_135, c_216])).
% 2.18/1.26  tff(c_222, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_136, c_160, c_219])).
% 2.18/1.26  tff(c_167, plain, (![A_63, B_64, C_65]: (k2_relset_1(A_63, B_64, C_65)=k2_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.18/1.26  tff(c_171, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_135, c_167])).
% 2.18/1.26  tff(c_237, plain, (![A_80, B_81, C_82]: (k7_relset_1(A_80, B_81, C_82, A_80)=k2_relset_1(A_80, B_81, C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.18/1.26  tff(c_239, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1')=k2_relset_1('#skF_1', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_135, c_237])).
% 2.18/1.26  tff(c_241, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_239])).
% 2.18/1.26  tff(c_185, plain, (![A_68, B_69, C_70, D_71]: (k8_relset_1(A_68, B_69, C_70, D_71)=k10_relat_1(C_70, D_71) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.18/1.26  tff(c_188, plain, (![D_71]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_71)=k10_relat_1('#skF_3', D_71))), inference(resolution, [status(thm)], [c_135, c_185])).
% 2.18/1.26  tff(c_155, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_134, c_134, c_28])).
% 2.18/1.26  tff(c_189, plain, (k10_relat_1('#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_188, c_155])).
% 2.18/1.26  tff(c_242, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_241, c_189])).
% 2.18/1.26  tff(c_258, plain, (k1_relat_1('#skF_3')!='#skF_1' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2, c_242])).
% 2.18/1.26  tff(c_261, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_145, c_222, c_258])).
% 2.18/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.26  
% 2.18/1.26  Inference rules
% 2.18/1.26  ----------------------
% 2.18/1.26  #Ref     : 0
% 2.18/1.26  #Sup     : 54
% 2.18/1.26  #Fact    : 0
% 2.18/1.26  #Define  : 0
% 2.18/1.26  #Split   : 1
% 2.18/1.26  #Chain   : 0
% 2.18/1.26  #Close   : 0
% 2.18/1.26  
% 2.18/1.26  Ordering : KBO
% 2.18/1.26  
% 2.18/1.26  Simplification rules
% 2.18/1.26  ----------------------
% 2.18/1.26  #Subsume      : 0
% 2.18/1.26  #Demod        : 49
% 2.18/1.26  #Tautology    : 38
% 2.18/1.26  #SimpNegUnit  : 2
% 2.18/1.26  #BackRed      : 8
% 2.18/1.26  
% 2.18/1.26  #Partial instantiations: 0
% 2.18/1.26  #Strategies tried      : 1
% 2.18/1.26  
% 2.18/1.26  Timing (in seconds)
% 2.18/1.26  ----------------------
% 2.18/1.26  Preprocessing        : 0.32
% 2.34/1.26  Parsing              : 0.17
% 2.34/1.26  CNF conversion       : 0.02
% 2.34/1.26  Main loop            : 0.19
% 2.34/1.27  Inferencing          : 0.07
% 2.34/1.27  Reduction            : 0.06
% 2.34/1.27  Demodulation         : 0.04
% 2.34/1.27  BG Simplification    : 0.01
% 2.34/1.27  Subsumption          : 0.03
% 2.34/1.27  Abstraction          : 0.01
% 2.34/1.27  MUC search           : 0.00
% 2.34/1.27  Cooper               : 0.00
% 2.34/1.27  Total                : 0.55
% 2.34/1.27  Index Insertion      : 0.00
% 2.34/1.27  Index Deletion       : 0.00
% 2.34/1.27  Index Matching       : 0.00
% 2.34/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
