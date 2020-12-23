%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:54 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 213 expanded)
%              Number of leaves         :   32 (  81 expanded)
%              Depth                    :   11
%              Number of atoms          :  131 ( 492 expanded)
%              Number of equality atoms :   59 ( 260 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k1_relset_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_79,axiom,(
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

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_45,plain,(
    ! [C_26,A_27,B_28] :
      ( v1_relat_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_49,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_45])).

tff(c_69,plain,(
    ! [C_34,B_35,A_36] :
      ( v5_relat_1(C_34,B_35)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_36,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_73,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_69])).

tff(c_60,plain,(
    ! [B_32,A_33] :
      ( r1_tarski(k2_relat_1(B_32),A_33)
      | ~ v5_relat_1(B_32,A_33)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_88,plain,(
    ! [B_42,A_43] :
      ( k3_xboole_0(k2_relat_1(B_42),A_43) = k2_relat_1(B_42)
      | ~ v5_relat_1(B_42,A_43)
      | ~ v1_relat_1(B_42) ) ),
    inference(resolution,[status(thm)],[c_60,c_2])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( k10_relat_1(B_6,k3_xboole_0(k2_relat_1(B_6),A_5)) = k10_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_126,plain,(
    ! [B_57,A_58] :
      ( k10_relat_1(B_57,k2_relat_1(B_57)) = k10_relat_1(B_57,A_58)
      | ~ v1_relat_1(B_57)
      | ~ v5_relat_1(B_57,A_58)
      | ~ v1_relat_1(B_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_8])).

tff(c_128,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_73,c_126])).

tff(c_131,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_128])).

tff(c_10,plain,(
    ! [A_7] :
      ( k10_relat_1(A_7,k2_relat_1(A_7)) = k1_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_135,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_10])).

tff(c_142,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_135])).

tff(c_110,plain,(
    ! [A_48,B_49,C_50,D_51] :
      ( k8_relset_1(A_48,B_49,C_50,D_51) = k10_relat_1(C_50,D_51)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_113,plain,(
    ! [D_51] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_51) = k10_relat_1('#skF_3',D_51) ),
    inference(resolution,[status(thm)],[c_38,c_110])).

tff(c_34,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_114,plain,(
    k10_relat_1('#skF_3','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_34])).

tff(c_147,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_114])).

tff(c_36,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_43,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_40,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_100,plain,(
    ! [A_44,B_45,C_46] :
      ( k1_relset_1(A_44,B_45,C_46) = k1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_104,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_100])).

tff(c_170,plain,(
    ! [B_61,A_62,C_63] :
      ( k1_xboole_0 = B_61
      | k1_relset_1(A_62,B_61,C_63) = A_62
      | ~ v1_funct_2(C_63,A_62,B_61)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_62,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_173,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_170])).

tff(c_176,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_104,c_173])).

tff(c_178,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_43,c_176])).

tff(c_179,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_180,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_185,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_180])).

tff(c_191,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_38])).

tff(c_203,plain,(
    ! [C_67,A_68,B_69] :
      ( v1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_207,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_191,c_203])).

tff(c_208,plain,(
    ! [C_70,B_71,A_72] :
      ( v5_relat_1(C_70,B_71)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_72,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_212,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_191,c_208])).

tff(c_213,plain,(
    ! [B_73,A_74] :
      ( r1_tarski(k2_relat_1(B_73),A_74)
      | ~ v5_relat_1(B_73,A_74)
      | ~ v1_relat_1(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_237,plain,(
    ! [B_82,A_83] :
      ( k3_xboole_0(k2_relat_1(B_82),A_83) = k2_relat_1(B_82)
      | ~ v5_relat_1(B_82,A_83)
      | ~ v1_relat_1(B_82) ) ),
    inference(resolution,[status(thm)],[c_213,c_2])).

tff(c_283,plain,(
    ! [B_95,A_96] :
      ( k10_relat_1(B_95,k2_relat_1(B_95)) = k10_relat_1(B_95,A_96)
      | ~ v1_relat_1(B_95)
      | ~ v5_relat_1(B_95,A_96)
      | ~ v1_relat_1(B_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_8])).

tff(c_285,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_212,c_283])).

tff(c_288,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_285])).

tff(c_292,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_10])).

tff(c_299,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_292])).

tff(c_260,plain,(
    ! [A_88,B_89,C_90,D_91] :
      ( k8_relset_1(A_88,B_89,C_90,D_91) = k10_relat_1(C_90,D_91)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_263,plain,(
    ! [D_91] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_91) = k10_relat_1('#skF_3',D_91) ),
    inference(resolution,[status(thm)],[c_191,c_260])).

tff(c_192,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_185,c_34])).

tff(c_273,plain,(
    k10_relat_1('#skF_3','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_192])).

tff(c_304,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_273])).

tff(c_186,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_40])).

tff(c_251,plain,(
    ! [A_85,B_86,C_87] :
      ( k1_relset_1(A_85,B_86,C_87) = k1_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_255,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_191,c_251])).

tff(c_30,plain,(
    ! [B_22,C_23] :
      ( k1_relset_1(k1_xboole_0,B_22,C_23) = k1_xboole_0
      | ~ v1_funct_2(C_23,k1_xboole_0,B_22)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_334,plain,(
    ! [B_99,C_100] :
      ( k1_relset_1('#skF_1',B_99,C_100) = '#skF_1'
      | ~ v1_funct_2(C_100,'#skF_1',B_99)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_99))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_179,c_179,c_179,c_30])).

tff(c_337,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_191,c_334])).

tff(c_340,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_255,c_337])).

tff(c_342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_304,c_340])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:46:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.33  
% 2.31/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.33  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k1_relset_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.31/1.33  
% 2.31/1.33  %Foreground sorts:
% 2.31/1.33  
% 2.31/1.33  
% 2.31/1.33  %Background operators:
% 2.31/1.33  
% 2.31/1.33  
% 2.31/1.33  %Foreground operators:
% 2.31/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.31/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.33  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.31/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.31/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.31/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.31/1.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.31/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.31/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.31/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.31/1.33  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.31/1.33  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.31/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.31/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.33  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.31/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.31/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.31/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.33  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.31/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.31/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.31/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.31/1.33  
% 2.31/1.35  tff(f_92, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_2)).
% 2.31/1.35  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.31/1.35  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.31/1.35  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.31/1.35  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.31/1.35  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 2.31/1.35  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.31/1.35  tff(f_61, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.31/1.35  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.31/1.35  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.31/1.35  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.31/1.35  tff(c_45, plain, (![C_26, A_27, B_28]: (v1_relat_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.31/1.35  tff(c_49, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_45])).
% 2.31/1.35  tff(c_69, plain, (![C_34, B_35, A_36]: (v5_relat_1(C_34, B_35) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_36, B_35))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.31/1.35  tff(c_73, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_69])).
% 2.31/1.35  tff(c_60, plain, (![B_32, A_33]: (r1_tarski(k2_relat_1(B_32), A_33) | ~v5_relat_1(B_32, A_33) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.31/1.35  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.31/1.35  tff(c_88, plain, (![B_42, A_43]: (k3_xboole_0(k2_relat_1(B_42), A_43)=k2_relat_1(B_42) | ~v5_relat_1(B_42, A_43) | ~v1_relat_1(B_42))), inference(resolution, [status(thm)], [c_60, c_2])).
% 2.31/1.35  tff(c_8, plain, (![B_6, A_5]: (k10_relat_1(B_6, k3_xboole_0(k2_relat_1(B_6), A_5))=k10_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.31/1.35  tff(c_126, plain, (![B_57, A_58]: (k10_relat_1(B_57, k2_relat_1(B_57))=k10_relat_1(B_57, A_58) | ~v1_relat_1(B_57) | ~v5_relat_1(B_57, A_58) | ~v1_relat_1(B_57))), inference(superposition, [status(thm), theory('equality')], [c_88, c_8])).
% 2.31/1.35  tff(c_128, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_73, c_126])).
% 2.31/1.35  tff(c_131, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_49, c_128])).
% 2.31/1.35  tff(c_10, plain, (![A_7]: (k10_relat_1(A_7, k2_relat_1(A_7))=k1_relat_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.31/1.35  tff(c_135, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_131, c_10])).
% 2.31/1.35  tff(c_142, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_49, c_135])).
% 2.31/1.35  tff(c_110, plain, (![A_48, B_49, C_50, D_51]: (k8_relset_1(A_48, B_49, C_50, D_51)=k10_relat_1(C_50, D_51) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.31/1.35  tff(c_113, plain, (![D_51]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_51)=k10_relat_1('#skF_3', D_51))), inference(resolution, [status(thm)], [c_38, c_110])).
% 2.31/1.35  tff(c_34, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.31/1.35  tff(c_114, plain, (k10_relat_1('#skF_3', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_113, c_34])).
% 2.31/1.35  tff(c_147, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_142, c_114])).
% 2.31/1.35  tff(c_36, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.31/1.35  tff(c_43, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_36])).
% 2.31/1.35  tff(c_40, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.31/1.35  tff(c_100, plain, (![A_44, B_45, C_46]: (k1_relset_1(A_44, B_45, C_46)=k1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.31/1.35  tff(c_104, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_100])).
% 2.31/1.35  tff(c_170, plain, (![B_61, A_62, C_63]: (k1_xboole_0=B_61 | k1_relset_1(A_62, B_61, C_63)=A_62 | ~v1_funct_2(C_63, A_62, B_61) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_62, B_61))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.31/1.35  tff(c_173, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_170])).
% 2.31/1.35  tff(c_176, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_104, c_173])).
% 2.31/1.35  tff(c_178, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_43, c_176])).
% 2.31/1.35  tff(c_179, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_36])).
% 2.31/1.35  tff(c_180, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_36])).
% 2.31/1.35  tff(c_185, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_179, c_180])).
% 2.31/1.35  tff(c_191, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_38])).
% 2.31/1.35  tff(c_203, plain, (![C_67, A_68, B_69]: (v1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.31/1.35  tff(c_207, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_191, c_203])).
% 2.31/1.35  tff(c_208, plain, (![C_70, B_71, A_72]: (v5_relat_1(C_70, B_71) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_72, B_71))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.31/1.35  tff(c_212, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_191, c_208])).
% 2.31/1.35  tff(c_213, plain, (![B_73, A_74]: (r1_tarski(k2_relat_1(B_73), A_74) | ~v5_relat_1(B_73, A_74) | ~v1_relat_1(B_73))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.31/1.35  tff(c_237, plain, (![B_82, A_83]: (k3_xboole_0(k2_relat_1(B_82), A_83)=k2_relat_1(B_82) | ~v5_relat_1(B_82, A_83) | ~v1_relat_1(B_82))), inference(resolution, [status(thm)], [c_213, c_2])).
% 2.31/1.35  tff(c_283, plain, (![B_95, A_96]: (k10_relat_1(B_95, k2_relat_1(B_95))=k10_relat_1(B_95, A_96) | ~v1_relat_1(B_95) | ~v5_relat_1(B_95, A_96) | ~v1_relat_1(B_95))), inference(superposition, [status(thm), theory('equality')], [c_237, c_8])).
% 2.31/1.35  tff(c_285, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_212, c_283])).
% 2.31/1.35  tff(c_288, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_207, c_285])).
% 2.31/1.35  tff(c_292, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_288, c_10])).
% 2.31/1.35  tff(c_299, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_207, c_292])).
% 2.31/1.35  tff(c_260, plain, (![A_88, B_89, C_90, D_91]: (k8_relset_1(A_88, B_89, C_90, D_91)=k10_relat_1(C_90, D_91) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.31/1.35  tff(c_263, plain, (![D_91]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_91)=k10_relat_1('#skF_3', D_91))), inference(resolution, [status(thm)], [c_191, c_260])).
% 2.31/1.35  tff(c_192, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_185, c_185, c_34])).
% 2.31/1.35  tff(c_273, plain, (k10_relat_1('#skF_3', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_263, c_192])).
% 2.31/1.35  tff(c_304, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_299, c_273])).
% 2.31/1.35  tff(c_186, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_185, c_40])).
% 2.31/1.35  tff(c_251, plain, (![A_85, B_86, C_87]: (k1_relset_1(A_85, B_86, C_87)=k1_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.31/1.35  tff(c_255, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_191, c_251])).
% 2.31/1.35  tff(c_30, plain, (![B_22, C_23]: (k1_relset_1(k1_xboole_0, B_22, C_23)=k1_xboole_0 | ~v1_funct_2(C_23, k1_xboole_0, B_22) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_22))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.31/1.35  tff(c_334, plain, (![B_99, C_100]: (k1_relset_1('#skF_1', B_99, C_100)='#skF_1' | ~v1_funct_2(C_100, '#skF_1', B_99) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_99))))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_179, c_179, c_179, c_30])).
% 2.31/1.35  tff(c_337, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_191, c_334])).
% 2.31/1.35  tff(c_340, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_186, c_255, c_337])).
% 2.31/1.35  tff(c_342, plain, $false, inference(negUnitSimplification, [status(thm)], [c_304, c_340])).
% 2.31/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.35  
% 2.31/1.35  Inference rules
% 2.31/1.35  ----------------------
% 2.31/1.35  #Ref     : 0
% 2.31/1.35  #Sup     : 66
% 2.31/1.35  #Fact    : 0
% 2.31/1.35  #Define  : 0
% 2.31/1.35  #Split   : 1
% 2.31/1.35  #Chain   : 0
% 2.31/1.35  #Close   : 0
% 2.31/1.35  
% 2.31/1.35  Ordering : KBO
% 2.31/1.35  
% 2.31/1.35  Simplification rules
% 2.31/1.35  ----------------------
% 2.31/1.35  #Subsume      : 1
% 2.31/1.35  #Demod        : 47
% 2.31/1.35  #Tautology    : 45
% 2.31/1.35  #SimpNegUnit  : 2
% 2.31/1.35  #BackRed      : 7
% 2.31/1.35  
% 2.31/1.35  #Partial instantiations: 0
% 2.31/1.35  #Strategies tried      : 1
% 2.31/1.35  
% 2.31/1.35  Timing (in seconds)
% 2.31/1.35  ----------------------
% 2.31/1.35  Preprocessing        : 0.33
% 2.31/1.35  Parsing              : 0.18
% 2.31/1.35  CNF conversion       : 0.02
% 2.31/1.35  Main loop            : 0.21
% 2.31/1.35  Inferencing          : 0.08
% 2.31/1.35  Reduction            : 0.06
% 2.31/1.35  Demodulation         : 0.04
% 2.31/1.35  BG Simplification    : 0.01
% 2.31/1.35  Subsumption          : 0.03
% 2.31/1.35  Abstraction          : 0.01
% 2.31/1.35  MUC search           : 0.00
% 2.31/1.35  Cooper               : 0.00
% 2.31/1.36  Total                : 0.57
% 2.31/1.36  Index Insertion      : 0.00
% 2.31/1.36  Index Deletion       : 0.00
% 2.31/1.36  Index Matching       : 0.00
% 2.31/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
