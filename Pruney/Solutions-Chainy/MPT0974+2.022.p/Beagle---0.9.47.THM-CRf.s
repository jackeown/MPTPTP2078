%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:44 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 266 expanded)
%              Number of leaves         :   34 ( 107 expanded)
%              Depth                    :   15
%              Number of atoms          :  171 ( 829 expanded)
%              Number of equality atoms :   71 ( 300 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,B,C)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ( ( k2_relset_1(A,B,D) = B
                & k2_relset_1(B,C,E) = C )
             => ( C = k1_xboole_0
                | k2_relset_1(A,C,k1_partfun1(A,B,B,C,D,E)) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_funct_2)).

tff(f_104,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k2_relat_1(A) = k2_relat_1(B)
               => k2_relat_1(k5_relat_1(A,C)) = k2_relat_1(k5_relat_1(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_relat_1)).

tff(f_64,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_82,axiom,(
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

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_50,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_514,plain,(
    ! [C_92,F_91,B_88,D_87,E_89,A_90] :
      ( k1_partfun1(A_90,B_88,C_92,D_87,E_89,F_91) = k5_relat_1(E_89,F_91)
      | ~ m1_subset_1(F_91,k1_zfmisc_1(k2_zfmisc_1(C_92,D_87)))
      | ~ v1_funct_1(F_91)
      | ~ m1_subset_1(E_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_88)))
      | ~ v1_funct_1(E_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_518,plain,(
    ! [A_90,B_88,E_89] :
      ( k1_partfun1(A_90,B_88,'#skF_2','#skF_3',E_89,'#skF_5') = k5_relat_1(E_89,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_88)))
      | ~ v1_funct_1(E_89) ) ),
    inference(resolution,[status(thm)],[c_46,c_514])).

tff(c_895,plain,(
    ! [A_111,B_112,E_113] :
      ( k1_partfun1(A_111,B_112,'#skF_2','#skF_3',E_113,'#skF_5') = k5_relat_1(E_113,'#skF_5')
      | ~ m1_subset_1(E_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112)))
      | ~ v1_funct_1(E_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_518])).

tff(c_907,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_895])).

tff(c_915,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_907])).

tff(c_38,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1014,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_915,c_38])).

tff(c_44,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_129,plain,(
    ! [A_49,B_50,C_51] :
      ( k2_relset_1(A_49,B_50,C_51) = k2_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_138,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_129])).

tff(c_144,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_138])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_97,plain,(
    ! [B_44,A_45] :
      ( v1_relat_1(B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_106,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_97])).

tff(c_115,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_106])).

tff(c_103,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_97])).

tff(c_112,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_103])).

tff(c_6,plain,(
    ! [B_10,C_12,A_6] :
      ( k2_relat_1(k5_relat_1(B_10,C_12)) = k2_relat_1(k5_relat_1(A_6,C_12))
      | k2_relat_1(B_10) != k2_relat_1(A_6)
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_18,plain,(
    ! [A_21] : m1_subset_1(k6_relat_1(A_21),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_100,plain,(
    ! [A_21] :
      ( v1_relat_1(k6_relat_1(A_21))
      | ~ v1_relat_1(k2_zfmisc_1(A_21,A_21)) ) ),
    inference(resolution,[status(thm)],[c_18,c_97])).

tff(c_109,plain,(
    ! [A_21] : v1_relat_1(k6_relat_1(A_21)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_100])).

tff(c_10,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_42,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_135,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_129])).

tff(c_142,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_135])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_48,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_162,plain,(
    ! [A_53,B_54,C_55] :
      ( k1_relset_1(A_53,B_54,C_55) = k1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_174,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_162])).

tff(c_234,plain,(
    ! [B_67,A_68,C_69] :
      ( k1_xboole_0 = B_67
      | k1_relset_1(A_68,B_67,C_69) = A_68
      | ~ v1_funct_2(C_69,A_68,B_67)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_68,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_240,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_234])).

tff(c_248,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_174,c_240])).

tff(c_249,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_248])).

tff(c_12,plain,(
    ! [A_14] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_14)),A_14) = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_257,plain,
    ( k5_relat_1(k6_relat_1('#skF_2'),'#skF_5') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_12])).

tff(c_261,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_257])).

tff(c_290,plain,(
    ! [B_70,C_71,A_72] :
      ( k2_relat_1(k5_relat_1(B_70,C_71)) = k2_relat_1(k5_relat_1(A_72,C_71))
      | k2_relat_1(B_70) != k2_relat_1(A_72)
      | ~ v1_relat_1(C_71)
      | ~ v1_relat_1(B_70)
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_323,plain,(
    ! [A_72] :
      ( k2_relat_1(k5_relat_1(A_72,'#skF_5')) = k2_relat_1('#skF_5')
      | k2_relat_1(k6_relat_1('#skF_2')) != k2_relat_1(A_72)
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1(k6_relat_1('#skF_2'))
      | ~ v1_relat_1(A_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_290])).

tff(c_355,plain,(
    ! [A_73] :
      ( k2_relat_1(k5_relat_1(A_73,'#skF_5')) = '#skF_3'
      | k2_relat_1(A_73) != '#skF_2'
      | ~ v1_relat_1(A_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_112,c_10,c_142,c_323])).

tff(c_375,plain,(
    ! [A_6,B_10] :
      ( k2_relat_1(k5_relat_1(A_6,'#skF_5')) = '#skF_3'
      | k2_relat_1(B_10) != '#skF_2'
      | ~ v1_relat_1(B_10)
      | k2_relat_1(B_10) != k2_relat_1(A_6)
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_355])).

tff(c_624,plain,(
    ! [A_99,B_100] :
      ( k2_relat_1(k5_relat_1(A_99,'#skF_5')) = '#skF_3'
      | k2_relat_1(B_100) != '#skF_2'
      | k2_relat_1(B_100) != k2_relat_1(A_99)
      | ~ v1_relat_1(B_100)
      | ~ v1_relat_1(A_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_375])).

tff(c_652,plain,(
    ! [B_100] :
      ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3'
      | k2_relat_1(B_100) != '#skF_2'
      | k2_relat_1(B_100) != '#skF_2'
      | ~ v1_relat_1(B_100)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_624])).

tff(c_664,plain,(
    ! [B_100] :
      ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3'
      | k2_relat_1(B_100) != '#skF_2'
      | ~ v1_relat_1(B_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_652])).

tff(c_674,plain,(
    ! [B_101] :
      ( k2_relat_1(B_101) != '#skF_2'
      | ~ v1_relat_1(B_101) ) ),
    inference(splitLeft,[status(thm)],[c_664])).

tff(c_680,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_115,c_674])).

tff(c_692,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_680])).

tff(c_693,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_664])).

tff(c_32,plain,(
    ! [A_25,F_30,E_29,C_27,D_28,B_26] :
      ( m1_subset_1(k1_partfun1(A_25,B_26,C_27,D_28,E_29,F_30),k1_zfmisc_1(k2_zfmisc_1(A_25,D_28)))
      | ~ m1_subset_1(F_30,k1_zfmisc_1(k2_zfmisc_1(C_27,D_28)))
      | ~ v1_funct_1(F_30)
      | ~ m1_subset_1(E_29,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_1(E_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1018,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_915,c_32])).

tff(c_1022,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_46,c_1018])).

tff(c_16,plain,(
    ! [A_18,B_19,C_20] :
      ( k2_relset_1(A_18,B_19,C_20) = k2_relat_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1051,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1022,c_16])).

tff(c_1081,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_693,c_1051])).

tff(c_1083,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1014,c_1081])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:39:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.50  
% 3.31/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.51  %$ v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.31/1.51  
% 3.31/1.51  %Foreground sorts:
% 3.31/1.51  
% 3.31/1.51  
% 3.31/1.51  %Background operators:
% 3.31/1.51  
% 3.31/1.51  
% 3.31/1.51  %Foreground operators:
% 3.31/1.51  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.31/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.31/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.31/1.51  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.31/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.31/1.51  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.31/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.31/1.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.31/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.31/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.31/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.31/1.51  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.31/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.31/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.31/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.31/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.31/1.51  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.31/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.31/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.31/1.51  
% 3.31/1.52  tff(f_126, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, B, D) = B) & (k2_relset_1(B, C, E) = C)) => ((C = k1_xboole_0) | (k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_funct_2)).
% 3.31/1.52  tff(f_104, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.31/1.52  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.31/1.52  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.31/1.52  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.31/1.52  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k2_relat_1(A) = k2_relat_1(B)) => (k2_relat_1(k5_relat_1(A, C)) = k2_relat_1(k5_relat_1(B, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t199_relat_1)).
% 3.31/1.52  tff(f_64, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 3.31/1.52  tff(f_50, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.31/1.52  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.31/1.52  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.31/1.52  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 3.31/1.52  tff(f_94, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.31/1.52  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.31/1.52  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.31/1.52  tff(c_50, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.31/1.52  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.31/1.52  tff(c_514, plain, (![C_92, F_91, B_88, D_87, E_89, A_90]: (k1_partfun1(A_90, B_88, C_92, D_87, E_89, F_91)=k5_relat_1(E_89, F_91) | ~m1_subset_1(F_91, k1_zfmisc_1(k2_zfmisc_1(C_92, D_87))) | ~v1_funct_1(F_91) | ~m1_subset_1(E_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_88))) | ~v1_funct_1(E_89))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.31/1.52  tff(c_518, plain, (![A_90, B_88, E_89]: (k1_partfun1(A_90, B_88, '#skF_2', '#skF_3', E_89, '#skF_5')=k5_relat_1(E_89, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_88))) | ~v1_funct_1(E_89))), inference(resolution, [status(thm)], [c_46, c_514])).
% 3.31/1.52  tff(c_895, plain, (![A_111, B_112, E_113]: (k1_partfun1(A_111, B_112, '#skF_2', '#skF_3', E_113, '#skF_5')=k5_relat_1(E_113, '#skF_5') | ~m1_subset_1(E_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))) | ~v1_funct_1(E_113))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_518])).
% 3.31/1.52  tff(c_907, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_895])).
% 3.31/1.52  tff(c_915, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_907])).
% 3.31/1.52  tff(c_38, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.31/1.52  tff(c_1014, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_915, c_38])).
% 3.31/1.52  tff(c_44, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.31/1.52  tff(c_129, plain, (![A_49, B_50, C_51]: (k2_relset_1(A_49, B_50, C_51)=k2_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.31/1.52  tff(c_138, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_129])).
% 3.31/1.52  tff(c_144, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_138])).
% 3.31/1.52  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.31/1.52  tff(c_97, plain, (![B_44, A_45]: (v1_relat_1(B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.31/1.52  tff(c_106, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_97])).
% 3.31/1.52  tff(c_115, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_106])).
% 3.31/1.52  tff(c_103, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_46, c_97])).
% 3.31/1.52  tff(c_112, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_103])).
% 3.31/1.52  tff(c_6, plain, (![B_10, C_12, A_6]: (k2_relat_1(k5_relat_1(B_10, C_12))=k2_relat_1(k5_relat_1(A_6, C_12)) | k2_relat_1(B_10)!=k2_relat_1(A_6) | ~v1_relat_1(C_12) | ~v1_relat_1(B_10) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.31/1.52  tff(c_18, plain, (![A_21]: (m1_subset_1(k6_relat_1(A_21), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.31/1.52  tff(c_100, plain, (![A_21]: (v1_relat_1(k6_relat_1(A_21)) | ~v1_relat_1(k2_zfmisc_1(A_21, A_21)))), inference(resolution, [status(thm)], [c_18, c_97])).
% 3.31/1.52  tff(c_109, plain, (![A_21]: (v1_relat_1(k6_relat_1(A_21)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_100])).
% 3.31/1.52  tff(c_10, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.31/1.52  tff(c_42, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.31/1.52  tff(c_135, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_129])).
% 3.31/1.52  tff(c_142, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_135])).
% 3.31/1.52  tff(c_40, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.31/1.52  tff(c_48, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.31/1.52  tff(c_162, plain, (![A_53, B_54, C_55]: (k1_relset_1(A_53, B_54, C_55)=k1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.31/1.52  tff(c_174, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_162])).
% 3.31/1.52  tff(c_234, plain, (![B_67, A_68, C_69]: (k1_xboole_0=B_67 | k1_relset_1(A_68, B_67, C_69)=A_68 | ~v1_funct_2(C_69, A_68, B_67) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_68, B_67))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.31/1.52  tff(c_240, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_234])).
% 3.31/1.52  tff(c_248, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_174, c_240])).
% 3.31/1.52  tff(c_249, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_40, c_248])).
% 3.31/1.52  tff(c_12, plain, (![A_14]: (k5_relat_1(k6_relat_1(k1_relat_1(A_14)), A_14)=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.31/1.52  tff(c_257, plain, (k5_relat_1(k6_relat_1('#skF_2'), '#skF_5')='#skF_5' | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_249, c_12])).
% 3.31/1.52  tff(c_261, plain, (k5_relat_1(k6_relat_1('#skF_2'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_257])).
% 3.31/1.52  tff(c_290, plain, (![B_70, C_71, A_72]: (k2_relat_1(k5_relat_1(B_70, C_71))=k2_relat_1(k5_relat_1(A_72, C_71)) | k2_relat_1(B_70)!=k2_relat_1(A_72) | ~v1_relat_1(C_71) | ~v1_relat_1(B_70) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.31/1.52  tff(c_323, plain, (![A_72]: (k2_relat_1(k5_relat_1(A_72, '#skF_5'))=k2_relat_1('#skF_5') | k2_relat_1(k6_relat_1('#skF_2'))!=k2_relat_1(A_72) | ~v1_relat_1('#skF_5') | ~v1_relat_1(k6_relat_1('#skF_2')) | ~v1_relat_1(A_72))), inference(superposition, [status(thm), theory('equality')], [c_261, c_290])).
% 3.31/1.52  tff(c_355, plain, (![A_73]: (k2_relat_1(k5_relat_1(A_73, '#skF_5'))='#skF_3' | k2_relat_1(A_73)!='#skF_2' | ~v1_relat_1(A_73))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_112, c_10, c_142, c_323])).
% 3.31/1.52  tff(c_375, plain, (![A_6, B_10]: (k2_relat_1(k5_relat_1(A_6, '#skF_5'))='#skF_3' | k2_relat_1(B_10)!='#skF_2' | ~v1_relat_1(B_10) | k2_relat_1(B_10)!=k2_relat_1(A_6) | ~v1_relat_1('#skF_5') | ~v1_relat_1(B_10) | ~v1_relat_1(A_6))), inference(superposition, [status(thm), theory('equality')], [c_6, c_355])).
% 3.31/1.52  tff(c_624, plain, (![A_99, B_100]: (k2_relat_1(k5_relat_1(A_99, '#skF_5'))='#skF_3' | k2_relat_1(B_100)!='#skF_2' | k2_relat_1(B_100)!=k2_relat_1(A_99) | ~v1_relat_1(B_100) | ~v1_relat_1(A_99))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_375])).
% 3.31/1.52  tff(c_652, plain, (![B_100]: (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3' | k2_relat_1(B_100)!='#skF_2' | k2_relat_1(B_100)!='#skF_2' | ~v1_relat_1(B_100) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_144, c_624])).
% 3.31/1.52  tff(c_664, plain, (![B_100]: (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3' | k2_relat_1(B_100)!='#skF_2' | ~v1_relat_1(B_100))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_652])).
% 3.31/1.52  tff(c_674, plain, (![B_101]: (k2_relat_1(B_101)!='#skF_2' | ~v1_relat_1(B_101))), inference(splitLeft, [status(thm)], [c_664])).
% 3.31/1.52  tff(c_680, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(resolution, [status(thm)], [c_115, c_674])).
% 3.31/1.52  tff(c_692, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_144, c_680])).
% 3.31/1.52  tff(c_693, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(splitRight, [status(thm)], [c_664])).
% 3.31/1.52  tff(c_32, plain, (![A_25, F_30, E_29, C_27, D_28, B_26]: (m1_subset_1(k1_partfun1(A_25, B_26, C_27, D_28, E_29, F_30), k1_zfmisc_1(k2_zfmisc_1(A_25, D_28))) | ~m1_subset_1(F_30, k1_zfmisc_1(k2_zfmisc_1(C_27, D_28))) | ~v1_funct_1(F_30) | ~m1_subset_1(E_29, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_1(E_29))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.31/1.52  tff(c_1018, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_915, c_32])).
% 3.31/1.52  tff(c_1022, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_46, c_1018])).
% 3.31/1.52  tff(c_16, plain, (![A_18, B_19, C_20]: (k2_relset_1(A_18, B_19, C_20)=k2_relat_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.31/1.52  tff(c_1051, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_1022, c_16])).
% 3.31/1.52  tff(c_1081, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_693, c_1051])).
% 3.31/1.52  tff(c_1083, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1014, c_1081])).
% 3.31/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.52  
% 3.31/1.52  Inference rules
% 3.31/1.52  ----------------------
% 3.31/1.52  #Ref     : 3
% 3.31/1.52  #Sup     : 230
% 3.31/1.52  #Fact    : 0
% 3.31/1.52  #Define  : 0
% 3.31/1.52  #Split   : 3
% 3.31/1.52  #Chain   : 0
% 3.31/1.52  #Close   : 0
% 3.31/1.52  
% 3.31/1.52  Ordering : KBO
% 3.31/1.52  
% 3.31/1.52  Simplification rules
% 3.31/1.52  ----------------------
% 3.31/1.52  #Subsume      : 19
% 3.31/1.52  #Demod        : 237
% 3.31/1.52  #Tautology    : 84
% 3.31/1.52  #SimpNegUnit  : 7
% 3.31/1.52  #BackRed      : 5
% 3.31/1.52  
% 3.31/1.52  #Partial instantiations: 0
% 3.31/1.52  #Strategies tried      : 1
% 3.31/1.52  
% 3.31/1.52  Timing (in seconds)
% 3.31/1.52  ----------------------
% 3.31/1.53  Preprocessing        : 0.33
% 3.31/1.53  Parsing              : 0.18
% 3.31/1.53  CNF conversion       : 0.02
% 3.31/1.53  Main loop            : 0.41
% 3.31/1.53  Inferencing          : 0.14
% 3.31/1.53  Reduction            : 0.14
% 3.31/1.53  Demodulation         : 0.11
% 3.31/1.53  BG Simplification    : 0.02
% 3.31/1.53  Subsumption          : 0.07
% 3.31/1.53  Abstraction          : 0.02
% 3.31/1.53  MUC search           : 0.00
% 3.31/1.53  Cooper               : 0.00
% 3.31/1.53  Total                : 0.78
% 3.31/1.53  Index Insertion      : 0.00
% 3.31/1.53  Index Deletion       : 0.00
% 3.31/1.53  Index Matching       : 0.00
% 3.31/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
