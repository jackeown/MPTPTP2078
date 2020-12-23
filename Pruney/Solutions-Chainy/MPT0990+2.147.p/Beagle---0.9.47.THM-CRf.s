%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:18 EST 2020

% Result     : Theorem 12.71s
% Output     : CNFRefutation 12.71s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 891 expanded)
%              Number of leaves         :   56 ( 337 expanded)
%              Depth                    :   19
%              Number of atoms          :  330 (2698 expanded)
%              Number of equality atoms :  112 ( 950 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_243,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( ( k2_relset_1(A,B,C) = B
                & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
                & v2_funct_1(C) )
             => ( A = k1_xboole_0
                | B = k1_xboole_0
                | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_49,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_32,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_132,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_148,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_166,axiom,(
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

tff(f_190,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_142,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_140,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_128,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_178,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_207,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
           => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_124,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

tff(f_107,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_97,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_188,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_88,plain,(
    k2_funct_1('#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_12,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_100,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_224,plain,(
    ! [B_83,A_84] :
      ( v1_relat_1(B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_84))
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_230,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_100,c_224])).

tff(c_239,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_230])).

tff(c_6,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_124,plain,(
    ! [A_69] :
      ( k1_xboole_0 = A_69
      | ~ v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_132,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_124])).

tff(c_92,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_142,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_92])).

tff(c_102,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_538,plain,(
    ! [A_109,B_110,C_111,D_112] :
      ( k8_relset_1(A_109,B_110,C_111,D_112) = k10_relat_1(C_111,D_112)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_555,plain,(
    ! [D_112] : k8_relset_1('#skF_3','#skF_2','#skF_5',D_112) = k10_relat_1('#skF_5',D_112) ),
    inference(resolution,[status(thm)],[c_100,c_538])).

tff(c_704,plain,(
    ! [A_132,B_133,C_134] :
      ( k8_relset_1(A_132,B_133,C_134,B_133) = k1_relset_1(A_132,B_133,C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_714,plain,(
    k8_relset_1('#skF_3','#skF_2','#skF_5','#skF_2') = k1_relset_1('#skF_3','#skF_2','#skF_5') ),
    inference(resolution,[status(thm)],[c_100,c_704])).

tff(c_725,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_5') = k10_relat_1('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_555,c_714])).

tff(c_70,plain,(
    ! [B_44,A_43,C_45] :
      ( k1_xboole_0 = B_44
      | k1_relset_1(A_43,B_44,C_45) = A_43
      | ~ v1_funct_2(C_45,A_43,B_44)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_938,plain,(
    ! [B_143,A_144,C_145] :
      ( B_143 = '#skF_1'
      | k1_relset_1(A_144,B_143,C_145) = A_144
      | ~ v1_funct_2(C_145,A_144,B_143)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_144,B_143))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_70])).

tff(c_953,plain,
    ( '#skF_2' = '#skF_1'
    | k1_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_100,c_938])).

tff(c_969,plain,
    ( '#skF_2' = '#skF_1'
    | k10_relat_1('#skF_5','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_725,c_953])).

tff(c_970,plain,(
    k10_relat_1('#skF_5','#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_969])).

tff(c_104,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_110,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_108,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_106,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_78,plain,(
    ! [A_58] : k6_relat_1(A_58) = k6_partfun1(A_58) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_54,plain,(
    ! [A_39] : m1_subset_1(k6_relat_1(A_39),k1_zfmisc_1(k2_zfmisc_1(A_39,A_39))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_111,plain,(
    ! [A_39] : m1_subset_1(k6_partfun1(A_39),k1_zfmisc_1(k2_zfmisc_1(A_39,A_39))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_54])).

tff(c_330,plain,(
    ! [A_92,B_93,D_94] :
      ( r2_relset_1(A_92,B_93,D_94,D_94)
      | ~ m1_subset_1(D_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_337,plain,(
    ! [A_39] : r2_relset_1(A_39,A_39,k6_partfun1(A_39),k6_partfun1(A_39)) ),
    inference(resolution,[status(thm)],[c_111,c_330])).

tff(c_386,plain,(
    ! [A_100,B_101,C_102] :
      ( k2_relset_1(A_100,B_101,C_102) = k2_relat_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_407,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_100,c_386])).

tff(c_2508,plain,(
    ! [C_193,F_190,A_194,B_189,E_192,D_191] :
      ( m1_subset_1(k1_partfun1(A_194,B_189,C_193,D_191,E_192,F_190),k1_zfmisc_1(k2_zfmisc_1(A_194,D_191)))
      | ~ m1_subset_1(F_190,k1_zfmisc_1(k2_zfmisc_1(C_193,D_191)))
      | ~ v1_funct_1(F_190)
      | ~ m1_subset_1(E_192,k1_zfmisc_1(k2_zfmisc_1(A_194,B_189)))
      | ~ v1_funct_1(E_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_96,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_1330,plain,(
    ! [D_151,C_152,A_153,B_154] :
      ( D_151 = C_152
      | ~ r2_relset_1(A_153,B_154,C_152,D_151)
      | ~ m1_subset_1(D_151,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154)))
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1342,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_96,c_1330])).

tff(c_1363,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_1342])).

tff(c_1425,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1363])).

tff(c_2521,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2508,c_1425])).

tff(c_2561,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_106,c_104,c_100,c_2521])).

tff(c_2562,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1363])).

tff(c_4086,plain,(
    ! [A_243,B_244,C_245,D_246] :
      ( k2_relset_1(A_243,B_244,C_245) = B_244
      | ~ r2_relset_1(B_244,B_244,k1_partfun1(B_244,A_243,A_243,B_244,D_246,C_245),k6_partfun1(B_244))
      | ~ m1_subset_1(D_246,k1_zfmisc_1(k2_zfmisc_1(B_244,A_243)))
      | ~ v1_funct_2(D_246,B_244,A_243)
      | ~ v1_funct_1(D_246)
      | ~ m1_subset_1(C_245,k1_zfmisc_1(k2_zfmisc_1(A_243,B_244)))
      | ~ v1_funct_2(C_245,A_243,B_244)
      | ~ v1_funct_1(C_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_4092,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2562,c_4086])).

tff(c_4097,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_100,c_110,c_108,c_106,c_337,c_407,c_4092])).

tff(c_14,plain,(
    ! [A_9] :
      ( k10_relat_1(A_9,k2_relat_1(A_9)) = k1_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4127,plain,
    ( k10_relat_1('#skF_5','#skF_2') = k1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4097,c_14])).

tff(c_4150,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_970,c_4127])).

tff(c_18,plain,(
    ! [A_17] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_17)),A_17) = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_120,plain,(
    ! [A_17] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_17)),A_17) = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_18])).

tff(c_4181,plain,
    ( k5_relat_1(k6_partfun1('#skF_3'),'#skF_5') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4150,c_120])).

tff(c_4201,plain,(
    k5_relat_1(k6_partfun1('#skF_3'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_4181])).

tff(c_233,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_106,c_224])).

tff(c_242,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_233])).

tff(c_94,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_24,plain,(
    ! [A_19] :
      ( v1_relat_1(k2_funct_1(A_19))
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_30,plain,(
    ! [A_21] : v1_relat_1(k6_relat_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_116,plain,(
    ! [A_21] : v1_relat_1(k6_partfun1(A_21)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_30])).

tff(c_28,plain,(
    ! [A_20] : v1_funct_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_117,plain,(
    ! [A_20] : v1_funct_1(k6_partfun1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_28])).

tff(c_32,plain,(
    ! [A_21] : v2_funct_1(k6_relat_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_115,plain,(
    ! [A_21] : v2_funct_1(k6_partfun1(A_21)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_32])).

tff(c_44,plain,(
    ! [A_27] : k2_funct_1(k6_relat_1(A_27)) = k6_relat_1(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_112,plain,(
    ! [A_27] : k2_funct_1(k6_partfun1(A_27)) = k6_partfun1(A_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_78,c_44])).

tff(c_40,plain,(
    ! [A_23] :
      ( k5_relat_1(A_23,k2_funct_1(A_23)) = k6_relat_1(k1_relat_1(A_23))
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_481,plain,(
    ! [A_105] :
      ( k5_relat_1(A_105,k2_funct_1(A_105)) = k6_partfun1(k1_relat_1(A_105))
      | ~ v2_funct_1(A_105)
      | ~ v1_funct_1(A_105)
      | ~ v1_relat_1(A_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_40])).

tff(c_490,plain,(
    ! [A_27] :
      ( k5_relat_1(k6_partfun1(A_27),k6_partfun1(A_27)) = k6_partfun1(k1_relat_1(k6_partfun1(A_27)))
      | ~ v2_funct_1(k6_partfun1(A_27))
      | ~ v1_funct_1(k6_partfun1(A_27))
      | ~ v1_relat_1(k6_partfun1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_481])).

tff(c_494,plain,(
    ! [A_27] : k5_relat_1(k6_partfun1(A_27),k6_partfun1(A_27)) = k6_partfun1(k1_relat_1(k6_partfun1(A_27))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_117,c_115,c_490])).

tff(c_90,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_141,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_90])).

tff(c_98,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_401,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_106,c_386])).

tff(c_409,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_401])).

tff(c_424,plain,
    ( k10_relat_1('#skF_4','#skF_3') = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_14])).

tff(c_437,plain,(
    k10_relat_1('#skF_4','#skF_3') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_424])).

tff(c_556,plain,(
    ! [D_112] : k8_relset_1('#skF_2','#skF_3','#skF_4',D_112) = k10_relat_1('#skF_4',D_112) ),
    inference(resolution,[status(thm)],[c_106,c_538])).

tff(c_716,plain,(
    k8_relset_1('#skF_2','#skF_3','#skF_4','#skF_3') = k1_relset_1('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_106,c_704])).

tff(c_727,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_556,c_716])).

tff(c_956,plain,
    ( '#skF_3' = '#skF_1'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_106,c_938])).

tff(c_973,plain,
    ( '#skF_3' = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_727,c_956])).

tff(c_974,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_973])).

tff(c_113,plain,(
    ! [A_23] :
      ( k5_relat_1(A_23,k2_funct_1(A_23)) = k6_partfun1(k1_relat_1(A_23))
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_40])).

tff(c_1008,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_974,c_120])).

tff(c_1022,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_1008])).

tff(c_16,plain,(
    ! [A_10,B_14,C_16] :
      ( k5_relat_1(k5_relat_1(A_10,B_14),C_16) = k5_relat_1(A_10,k5_relat_1(B_14,C_16))
      | ~ v1_relat_1(C_16)
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1044,plain,(
    ! [C_16] :
      ( k5_relat_1(k6_partfun1('#skF_2'),k5_relat_1('#skF_4',C_16)) = k5_relat_1('#skF_4',C_16)
      | ~ v1_relat_1(C_16)
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(k6_partfun1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1022,c_16])).

tff(c_1085,plain,(
    ! [C_149] :
      ( k5_relat_1(k6_partfun1('#skF_2'),k5_relat_1('#skF_4',C_149)) = k5_relat_1('#skF_4',C_149)
      | ~ v1_relat_1(C_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_242,c_1044])).

tff(c_1110,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k6_partfun1(k1_relat_1('#skF_4'))) = k5_relat_1('#skF_4',k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_1085])).

tff(c_1127,plain,
    ( k6_partfun1(k1_relat_1(k6_partfun1('#skF_2'))) = k5_relat_1('#skF_4',k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_110,c_94,c_494,c_974,c_1110])).

tff(c_1132,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1127])).

tff(c_1160,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_1132])).

tff(c_1164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_110,c_1160])).

tff(c_1166,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1127])).

tff(c_307,plain,(
    ! [A_91] :
      ( k2_relat_1(k2_funct_1(A_91)) = k1_relat_1(A_91)
      | ~ v2_funct_1(A_91)
      | ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_20,plain,(
    ! [A_18] :
      ( k5_relat_1(A_18,k6_relat_1(k2_relat_1(A_18))) = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_119,plain,(
    ! [A_18] :
      ( k5_relat_1(A_18,k6_partfun1(k2_relat_1(A_18))) = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_20])).

tff(c_5019,plain,(
    ! [A_266] :
      ( k5_relat_1(k2_funct_1(A_266),k6_partfun1(k1_relat_1(A_266))) = k2_funct_1(A_266)
      | ~ v1_relat_1(k2_funct_1(A_266))
      | ~ v2_funct_1(A_266)
      | ~ v1_funct_1(A_266)
      | ~ v1_relat_1(A_266) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_119])).

tff(c_5057,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),k6_partfun1('#skF_2')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_974,c_5019])).

tff(c_5080,plain,(
    k5_relat_1(k2_funct_1('#skF_4'),k6_partfun1('#skF_2')) = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_110,c_94,c_1166,c_5057])).

tff(c_3611,plain,(
    ! [D_223,B_220,C_224,E_221,F_222,A_219] :
      ( k1_partfun1(A_219,B_220,C_224,D_223,E_221,F_222) = k5_relat_1(E_221,F_222)
      | ~ m1_subset_1(F_222,k1_zfmisc_1(k2_zfmisc_1(C_224,D_223)))
      | ~ v1_funct_1(F_222)
      | ~ m1_subset_1(E_221,k1_zfmisc_1(k2_zfmisc_1(A_219,B_220)))
      | ~ v1_funct_1(E_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_3619,plain,(
    ! [A_219,B_220,E_221] :
      ( k1_partfun1(A_219,B_220,'#skF_3','#skF_2',E_221,'#skF_5') = k5_relat_1(E_221,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_221,k1_zfmisc_1(k2_zfmisc_1(A_219,B_220)))
      | ~ v1_funct_1(E_221) ) ),
    inference(resolution,[status(thm)],[c_100,c_3611])).

tff(c_3962,plain,(
    ! [A_240,B_241,E_242] :
      ( k1_partfun1(A_240,B_241,'#skF_3','#skF_2',E_242,'#skF_5') = k5_relat_1(E_242,'#skF_5')
      | ~ m1_subset_1(E_242,k1_zfmisc_1(k2_zfmisc_1(A_240,B_241)))
      | ~ v1_funct_1(E_242) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_3619])).

tff(c_3980,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_106,c_3962])).

tff(c_3994,plain,(
    k5_relat_1('#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_2562,c_3980])).

tff(c_38,plain,(
    ! [A_23] :
      ( k5_relat_1(k2_funct_1(A_23),A_23) = k6_relat_1(k2_relat_1(A_23))
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_114,plain,(
    ! [A_23] :
      ( k5_relat_1(k2_funct_1(A_23),A_23) = k6_partfun1(k2_relat_1(A_23))
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_38])).

tff(c_750,plain,(
    ! [A_136,B_137,C_138] :
      ( k5_relat_1(k5_relat_1(A_136,B_137),C_138) = k5_relat_1(A_136,k5_relat_1(B_137,C_138))
      | ~ v1_relat_1(C_138)
      | ~ v1_relat_1(B_137)
      | ~ v1_relat_1(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8636,plain,(
    ! [A_306,C_307] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_306)),C_307) = k5_relat_1(k2_funct_1(A_306),k5_relat_1(A_306,C_307))
      | ~ v1_relat_1(C_307)
      | ~ v1_relat_1(A_306)
      | ~ v1_relat_1(k2_funct_1(A_306))
      | ~ v2_funct_1(A_306)
      | ~ v1_funct_1(A_306)
      | ~ v1_relat_1(A_306) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_750])).

tff(c_8890,plain,(
    ! [C_307] :
      ( k5_relat_1(k2_funct_1('#skF_4'),k5_relat_1('#skF_4',C_307)) = k5_relat_1(k6_partfun1('#skF_3'),C_307)
      | ~ v1_relat_1(C_307)
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(k2_funct_1('#skF_4'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_8636])).

tff(c_16725,plain,(
    ! [C_439] :
      ( k5_relat_1(k2_funct_1('#skF_4'),k5_relat_1('#skF_4',C_439)) = k5_relat_1(k6_partfun1('#skF_3'),C_439)
      | ~ v1_relat_1(C_439) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_110,c_94,c_1166,c_242,c_8890])).

tff(c_16803,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),k6_partfun1('#skF_2')) = k5_relat_1(k6_partfun1('#skF_3'),'#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3994,c_16725])).

tff(c_16874,plain,(
    k2_funct_1('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_4201,c_5080,c_16803])).

tff(c_16876,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_16874])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:30:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.71/5.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.71/5.25  
% 12.71/5.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.71/5.25  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 12.71/5.25  
% 12.71/5.25  %Foreground sorts:
% 12.71/5.25  
% 12.71/5.25  
% 12.71/5.25  %Background operators:
% 12.71/5.25  
% 12.71/5.25  
% 12.71/5.25  %Foreground operators:
% 12.71/5.25  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 12.71/5.25  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 12.71/5.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.71/5.25  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 12.71/5.25  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 12.71/5.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.71/5.25  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 12.71/5.25  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 12.71/5.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.71/5.25  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 12.71/5.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.71/5.25  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 12.71/5.25  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.71/5.25  tff('#skF_5', type, '#skF_5': $i).
% 12.71/5.25  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.71/5.25  tff('#skF_2', type, '#skF_2': $i).
% 12.71/5.25  tff('#skF_3', type, '#skF_3': $i).
% 12.71/5.25  tff('#skF_1', type, '#skF_1': $i).
% 12.71/5.25  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 12.71/5.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.71/5.25  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 12.71/5.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.71/5.25  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 12.71/5.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.71/5.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.71/5.25  tff('#skF_4', type, '#skF_4': $i).
% 12.71/5.25  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 12.71/5.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.71/5.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.71/5.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.71/5.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.71/5.25  
% 12.71/5.27  tff(f_243, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 12.71/5.27  tff(f_49, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 12.71/5.27  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 12.71/5.27  tff(f_32, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 12.71/5.27  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 12.71/5.27  tff(f_132, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 12.71/5.27  tff(f_148, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 12.71/5.27  tff(f_166, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 12.71/5.27  tff(f_190, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 12.71/5.27  tff(f_142, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 12.71/5.27  tff(f_140, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 12.71/5.27  tff(f_128, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 12.71/5.27  tff(f_178, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 12.71/5.27  tff(f_207, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 12.71/5.27  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 12.71/5.27  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 12.71/5.27  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 12.71/5.27  tff(f_87, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 12.71/5.27  tff(f_83, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 12.71/5.27  tff(f_124, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 12.71/5.27  tff(f_107, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 12.71/5.27  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 12.71/5.27  tff(f_97, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 12.71/5.27  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 12.71/5.27  tff(f_188, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 12.71/5.27  tff(c_88, plain, (k2_funct_1('#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_243])).
% 12.71/5.27  tff(c_12, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.71/5.27  tff(c_100, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_243])).
% 12.71/5.27  tff(c_224, plain, (![B_83, A_84]: (v1_relat_1(B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(A_84)) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.71/5.27  tff(c_230, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_100, c_224])).
% 12.71/5.27  tff(c_239, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_230])).
% 12.71/5.27  tff(c_6, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.71/5.27  tff(c_124, plain, (![A_69]: (k1_xboole_0=A_69 | ~v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_30])).
% 12.71/5.27  tff(c_132, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_6, c_124])).
% 12.71/5.27  tff(c_92, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_243])).
% 12.71/5.27  tff(c_142, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_92])).
% 12.71/5.27  tff(c_102, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_243])).
% 12.71/5.27  tff(c_538, plain, (![A_109, B_110, C_111, D_112]: (k8_relset_1(A_109, B_110, C_111, D_112)=k10_relat_1(C_111, D_112) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 12.71/5.27  tff(c_555, plain, (![D_112]: (k8_relset_1('#skF_3', '#skF_2', '#skF_5', D_112)=k10_relat_1('#skF_5', D_112))), inference(resolution, [status(thm)], [c_100, c_538])).
% 12.71/5.27  tff(c_704, plain, (![A_132, B_133, C_134]: (k8_relset_1(A_132, B_133, C_134, B_133)=k1_relset_1(A_132, B_133, C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 12.71/5.27  tff(c_714, plain, (k8_relset_1('#skF_3', '#skF_2', '#skF_5', '#skF_2')=k1_relset_1('#skF_3', '#skF_2', '#skF_5')), inference(resolution, [status(thm)], [c_100, c_704])).
% 12.71/5.27  tff(c_725, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_5')=k10_relat_1('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_555, c_714])).
% 12.71/5.27  tff(c_70, plain, (![B_44, A_43, C_45]: (k1_xboole_0=B_44 | k1_relset_1(A_43, B_44, C_45)=A_43 | ~v1_funct_2(C_45, A_43, B_44) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_166])).
% 12.71/5.27  tff(c_938, plain, (![B_143, A_144, C_145]: (B_143='#skF_1' | k1_relset_1(A_144, B_143, C_145)=A_144 | ~v1_funct_2(C_145, A_144, B_143) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_144, B_143))))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_70])).
% 12.71/5.27  tff(c_953, plain, ('#skF_2'='#skF_1' | k1_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_100, c_938])).
% 12.71/5.27  tff(c_969, plain, ('#skF_2'='#skF_1' | k10_relat_1('#skF_5', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_725, c_953])).
% 12.71/5.27  tff(c_970, plain, (k10_relat_1('#skF_5', '#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_142, c_969])).
% 12.71/5.27  tff(c_104, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_243])).
% 12.71/5.27  tff(c_110, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_243])).
% 12.71/5.27  tff(c_108, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_243])).
% 12.71/5.27  tff(c_106, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_243])).
% 12.71/5.27  tff(c_78, plain, (![A_58]: (k6_relat_1(A_58)=k6_partfun1(A_58))), inference(cnfTransformation, [status(thm)], [f_190])).
% 12.71/5.27  tff(c_54, plain, (![A_39]: (m1_subset_1(k6_relat_1(A_39), k1_zfmisc_1(k2_zfmisc_1(A_39, A_39))))), inference(cnfTransformation, [status(thm)], [f_142])).
% 12.71/5.27  tff(c_111, plain, (![A_39]: (m1_subset_1(k6_partfun1(A_39), k1_zfmisc_1(k2_zfmisc_1(A_39, A_39))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_54])).
% 12.71/5.27  tff(c_330, plain, (![A_92, B_93, D_94]: (r2_relset_1(A_92, B_93, D_94, D_94) | ~m1_subset_1(D_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 12.71/5.27  tff(c_337, plain, (![A_39]: (r2_relset_1(A_39, A_39, k6_partfun1(A_39), k6_partfun1(A_39)))), inference(resolution, [status(thm)], [c_111, c_330])).
% 12.71/5.27  tff(c_386, plain, (![A_100, B_101, C_102]: (k2_relset_1(A_100, B_101, C_102)=k2_relat_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 12.71/5.27  tff(c_407, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_100, c_386])).
% 12.71/5.27  tff(c_2508, plain, (![C_193, F_190, A_194, B_189, E_192, D_191]: (m1_subset_1(k1_partfun1(A_194, B_189, C_193, D_191, E_192, F_190), k1_zfmisc_1(k2_zfmisc_1(A_194, D_191))) | ~m1_subset_1(F_190, k1_zfmisc_1(k2_zfmisc_1(C_193, D_191))) | ~v1_funct_1(F_190) | ~m1_subset_1(E_192, k1_zfmisc_1(k2_zfmisc_1(A_194, B_189))) | ~v1_funct_1(E_192))), inference(cnfTransformation, [status(thm)], [f_178])).
% 12.71/5.27  tff(c_96, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_243])).
% 12.71/5.27  tff(c_1330, plain, (![D_151, C_152, A_153, B_154]: (D_151=C_152 | ~r2_relset_1(A_153, B_154, C_152, D_151) | ~m1_subset_1(D_151, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 12.71/5.27  tff(c_1342, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_96, c_1330])).
% 12.71/5.27  tff(c_1363, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_1342])).
% 12.71/5.27  tff(c_1425, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1363])).
% 12.71/5.27  tff(c_2521, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_2508, c_1425])).
% 12.71/5.27  tff(c_2561, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_106, c_104, c_100, c_2521])).
% 12.71/5.27  tff(c_2562, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_1363])).
% 12.71/5.27  tff(c_4086, plain, (![A_243, B_244, C_245, D_246]: (k2_relset_1(A_243, B_244, C_245)=B_244 | ~r2_relset_1(B_244, B_244, k1_partfun1(B_244, A_243, A_243, B_244, D_246, C_245), k6_partfun1(B_244)) | ~m1_subset_1(D_246, k1_zfmisc_1(k2_zfmisc_1(B_244, A_243))) | ~v1_funct_2(D_246, B_244, A_243) | ~v1_funct_1(D_246) | ~m1_subset_1(C_245, k1_zfmisc_1(k2_zfmisc_1(A_243, B_244))) | ~v1_funct_2(C_245, A_243, B_244) | ~v1_funct_1(C_245))), inference(cnfTransformation, [status(thm)], [f_207])).
% 12.71/5.27  tff(c_4092, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2562, c_4086])).
% 12.71/5.27  tff(c_4097, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_100, c_110, c_108, c_106, c_337, c_407, c_4092])).
% 12.71/5.27  tff(c_14, plain, (![A_9]: (k10_relat_1(A_9, k2_relat_1(A_9))=k1_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.71/5.27  tff(c_4127, plain, (k10_relat_1('#skF_5', '#skF_2')=k1_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4097, c_14])).
% 12.71/5.27  tff(c_4150, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_239, c_970, c_4127])).
% 12.71/5.27  tff(c_18, plain, (![A_17]: (k5_relat_1(k6_relat_1(k1_relat_1(A_17)), A_17)=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 12.71/5.27  tff(c_120, plain, (![A_17]: (k5_relat_1(k6_partfun1(k1_relat_1(A_17)), A_17)=A_17 | ~v1_relat_1(A_17))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_18])).
% 12.71/5.27  tff(c_4181, plain, (k5_relat_1(k6_partfun1('#skF_3'), '#skF_5')='#skF_5' | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4150, c_120])).
% 12.71/5.27  tff(c_4201, plain, (k5_relat_1(k6_partfun1('#skF_3'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_239, c_4181])).
% 12.71/5.27  tff(c_233, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_106, c_224])).
% 12.71/5.27  tff(c_242, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_233])).
% 12.71/5.27  tff(c_94, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_243])).
% 12.71/5.27  tff(c_24, plain, (![A_19]: (v1_relat_1(k2_funct_1(A_19)) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.71/5.27  tff(c_30, plain, (![A_21]: (v1_relat_1(k6_relat_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 12.71/5.27  tff(c_116, plain, (![A_21]: (v1_relat_1(k6_partfun1(A_21)))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_30])).
% 12.71/5.27  tff(c_28, plain, (![A_20]: (v1_funct_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 12.71/5.27  tff(c_117, plain, (![A_20]: (v1_funct_1(k6_partfun1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_28])).
% 12.71/5.27  tff(c_32, plain, (![A_21]: (v2_funct_1(k6_relat_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 12.71/5.27  tff(c_115, plain, (![A_21]: (v2_funct_1(k6_partfun1(A_21)))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_32])).
% 12.71/5.27  tff(c_44, plain, (![A_27]: (k2_funct_1(k6_relat_1(A_27))=k6_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_124])).
% 12.71/5.27  tff(c_112, plain, (![A_27]: (k2_funct_1(k6_partfun1(A_27))=k6_partfun1(A_27))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_78, c_44])).
% 12.71/5.27  tff(c_40, plain, (![A_23]: (k5_relat_1(A_23, k2_funct_1(A_23))=k6_relat_1(k1_relat_1(A_23)) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_107])).
% 12.71/5.27  tff(c_481, plain, (![A_105]: (k5_relat_1(A_105, k2_funct_1(A_105))=k6_partfun1(k1_relat_1(A_105)) | ~v2_funct_1(A_105) | ~v1_funct_1(A_105) | ~v1_relat_1(A_105))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_40])).
% 12.71/5.27  tff(c_490, plain, (![A_27]: (k5_relat_1(k6_partfun1(A_27), k6_partfun1(A_27))=k6_partfun1(k1_relat_1(k6_partfun1(A_27))) | ~v2_funct_1(k6_partfun1(A_27)) | ~v1_funct_1(k6_partfun1(A_27)) | ~v1_relat_1(k6_partfun1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_112, c_481])).
% 12.71/5.27  tff(c_494, plain, (![A_27]: (k5_relat_1(k6_partfun1(A_27), k6_partfun1(A_27))=k6_partfun1(k1_relat_1(k6_partfun1(A_27))))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_117, c_115, c_490])).
% 12.71/5.27  tff(c_90, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_243])).
% 12.71/5.27  tff(c_141, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_90])).
% 12.71/5.27  tff(c_98, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_243])).
% 12.71/5.27  tff(c_401, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_106, c_386])).
% 12.71/5.27  tff(c_409, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_401])).
% 12.71/5.27  tff(c_424, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_409, c_14])).
% 12.71/5.27  tff(c_437, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_242, c_424])).
% 12.71/5.27  tff(c_556, plain, (![D_112]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', D_112)=k10_relat_1('#skF_4', D_112))), inference(resolution, [status(thm)], [c_106, c_538])).
% 12.71/5.27  tff(c_716, plain, (k8_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_3')=k1_relset_1('#skF_2', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_106, c_704])).
% 12.71/5.27  tff(c_727, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_437, c_556, c_716])).
% 12.71/5.27  tff(c_956, plain, ('#skF_3'='#skF_1' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_106, c_938])).
% 12.71/5.27  tff(c_973, plain, ('#skF_3'='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_727, c_956])).
% 12.71/5.27  tff(c_974, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_141, c_973])).
% 12.71/5.27  tff(c_113, plain, (![A_23]: (k5_relat_1(A_23, k2_funct_1(A_23))=k6_partfun1(k1_relat_1(A_23)) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_40])).
% 12.71/5.27  tff(c_1008, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_974, c_120])).
% 12.71/5.27  tff(c_1022, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_242, c_1008])).
% 12.71/5.27  tff(c_16, plain, (![A_10, B_14, C_16]: (k5_relat_1(k5_relat_1(A_10, B_14), C_16)=k5_relat_1(A_10, k5_relat_1(B_14, C_16)) | ~v1_relat_1(C_16) | ~v1_relat_1(B_14) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.71/5.27  tff(c_1044, plain, (![C_16]: (k5_relat_1(k6_partfun1('#skF_2'), k5_relat_1('#skF_4', C_16))=k5_relat_1('#skF_4', C_16) | ~v1_relat_1(C_16) | ~v1_relat_1('#skF_4') | ~v1_relat_1(k6_partfun1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1022, c_16])).
% 12.71/5.27  tff(c_1085, plain, (![C_149]: (k5_relat_1(k6_partfun1('#skF_2'), k5_relat_1('#skF_4', C_149))=k5_relat_1('#skF_4', C_149) | ~v1_relat_1(C_149))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_242, c_1044])).
% 12.71/5.27  tff(c_1110, plain, (k5_relat_1(k6_partfun1('#skF_2'), k6_partfun1(k1_relat_1('#skF_4')))=k5_relat_1('#skF_4', k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_113, c_1085])).
% 12.71/5.27  tff(c_1127, plain, (k6_partfun1(k1_relat_1(k6_partfun1('#skF_2')))=k5_relat_1('#skF_4', k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_242, c_110, c_94, c_494, c_974, c_1110])).
% 12.71/5.27  tff(c_1132, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_1127])).
% 12.71/5.27  tff(c_1160, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_1132])).
% 12.71/5.27  tff(c_1164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_242, c_110, c_1160])).
% 12.71/5.27  tff(c_1166, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_1127])).
% 12.71/5.27  tff(c_307, plain, (![A_91]: (k2_relat_1(k2_funct_1(A_91))=k1_relat_1(A_91) | ~v2_funct_1(A_91) | ~v1_funct_1(A_91) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.71/5.27  tff(c_20, plain, (![A_18]: (k5_relat_1(A_18, k6_relat_1(k2_relat_1(A_18)))=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.71/5.27  tff(c_119, plain, (![A_18]: (k5_relat_1(A_18, k6_partfun1(k2_relat_1(A_18)))=A_18 | ~v1_relat_1(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_20])).
% 12.71/5.27  tff(c_5019, plain, (![A_266]: (k5_relat_1(k2_funct_1(A_266), k6_partfun1(k1_relat_1(A_266)))=k2_funct_1(A_266) | ~v1_relat_1(k2_funct_1(A_266)) | ~v2_funct_1(A_266) | ~v1_funct_1(A_266) | ~v1_relat_1(A_266))), inference(superposition, [status(thm), theory('equality')], [c_307, c_119])).
% 12.71/5.27  tff(c_5057, plain, (k5_relat_1(k2_funct_1('#skF_4'), k6_partfun1('#skF_2'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_974, c_5019])).
% 12.71/5.27  tff(c_5080, plain, (k5_relat_1(k2_funct_1('#skF_4'), k6_partfun1('#skF_2'))=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_242, c_110, c_94, c_1166, c_5057])).
% 12.71/5.27  tff(c_3611, plain, (![D_223, B_220, C_224, E_221, F_222, A_219]: (k1_partfun1(A_219, B_220, C_224, D_223, E_221, F_222)=k5_relat_1(E_221, F_222) | ~m1_subset_1(F_222, k1_zfmisc_1(k2_zfmisc_1(C_224, D_223))) | ~v1_funct_1(F_222) | ~m1_subset_1(E_221, k1_zfmisc_1(k2_zfmisc_1(A_219, B_220))) | ~v1_funct_1(E_221))), inference(cnfTransformation, [status(thm)], [f_188])).
% 12.71/5.27  tff(c_3619, plain, (![A_219, B_220, E_221]: (k1_partfun1(A_219, B_220, '#skF_3', '#skF_2', E_221, '#skF_5')=k5_relat_1(E_221, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_221, k1_zfmisc_1(k2_zfmisc_1(A_219, B_220))) | ~v1_funct_1(E_221))), inference(resolution, [status(thm)], [c_100, c_3611])).
% 12.71/5.27  tff(c_3962, plain, (![A_240, B_241, E_242]: (k1_partfun1(A_240, B_241, '#skF_3', '#skF_2', E_242, '#skF_5')=k5_relat_1(E_242, '#skF_5') | ~m1_subset_1(E_242, k1_zfmisc_1(k2_zfmisc_1(A_240, B_241))) | ~v1_funct_1(E_242))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_3619])).
% 12.71/5.27  tff(c_3980, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_106, c_3962])).
% 12.71/5.27  tff(c_3994, plain, (k5_relat_1('#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_2562, c_3980])).
% 12.71/5.27  tff(c_38, plain, (![A_23]: (k5_relat_1(k2_funct_1(A_23), A_23)=k6_relat_1(k2_relat_1(A_23)) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_107])).
% 12.71/5.27  tff(c_114, plain, (![A_23]: (k5_relat_1(k2_funct_1(A_23), A_23)=k6_partfun1(k2_relat_1(A_23)) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_38])).
% 12.71/5.27  tff(c_750, plain, (![A_136, B_137, C_138]: (k5_relat_1(k5_relat_1(A_136, B_137), C_138)=k5_relat_1(A_136, k5_relat_1(B_137, C_138)) | ~v1_relat_1(C_138) | ~v1_relat_1(B_137) | ~v1_relat_1(A_136))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.71/5.27  tff(c_8636, plain, (![A_306, C_307]: (k5_relat_1(k6_partfun1(k2_relat_1(A_306)), C_307)=k5_relat_1(k2_funct_1(A_306), k5_relat_1(A_306, C_307)) | ~v1_relat_1(C_307) | ~v1_relat_1(A_306) | ~v1_relat_1(k2_funct_1(A_306)) | ~v2_funct_1(A_306) | ~v1_funct_1(A_306) | ~v1_relat_1(A_306))), inference(superposition, [status(thm), theory('equality')], [c_114, c_750])).
% 12.71/5.27  tff(c_8890, plain, (![C_307]: (k5_relat_1(k2_funct_1('#skF_4'), k5_relat_1('#skF_4', C_307))=k5_relat_1(k6_partfun1('#skF_3'), C_307) | ~v1_relat_1(C_307) | ~v1_relat_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_409, c_8636])).
% 12.71/5.27  tff(c_16725, plain, (![C_439]: (k5_relat_1(k2_funct_1('#skF_4'), k5_relat_1('#skF_4', C_439))=k5_relat_1(k6_partfun1('#skF_3'), C_439) | ~v1_relat_1(C_439))), inference(demodulation, [status(thm), theory('equality')], [c_242, c_110, c_94, c_1166, c_242, c_8890])).
% 12.71/5.27  tff(c_16803, plain, (k5_relat_1(k2_funct_1('#skF_4'), k6_partfun1('#skF_2'))=k5_relat_1(k6_partfun1('#skF_3'), '#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3994, c_16725])).
% 12.71/5.27  tff(c_16874, plain, (k2_funct_1('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_239, c_4201, c_5080, c_16803])).
% 12.71/5.27  tff(c_16876, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_16874])).
% 12.71/5.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.71/5.27  
% 12.71/5.27  Inference rules
% 12.71/5.27  ----------------------
% 12.71/5.27  #Ref     : 0
% 12.71/5.27  #Sup     : 3755
% 12.71/5.27  #Fact    : 0
% 12.71/5.28  #Define  : 0
% 12.71/5.28  #Split   : 18
% 12.71/5.28  #Chain   : 0
% 12.71/5.28  #Close   : 0
% 12.71/5.28  
% 12.71/5.28  Ordering : KBO
% 12.71/5.28  
% 12.71/5.28  Simplification rules
% 12.71/5.28  ----------------------
% 12.71/5.28  #Subsume      : 63
% 12.71/5.28  #Demod        : 7562
% 12.71/5.28  #Tautology    : 1503
% 12.71/5.28  #SimpNegUnit  : 41
% 12.71/5.28  #BackRed      : 56
% 12.71/5.28  
% 12.71/5.28  #Partial instantiations: 0
% 12.71/5.28  #Strategies tried      : 1
% 12.71/5.28  
% 12.71/5.28  Timing (in seconds)
% 12.71/5.28  ----------------------
% 12.71/5.28  Preprocessing        : 0.41
% 12.71/5.28  Parsing              : 0.23
% 12.71/5.28  CNF conversion       : 0.03
% 12.71/5.28  Main loop            : 4.05
% 12.71/5.28  Inferencing          : 0.84
% 12.71/5.28  Reduction            : 2.30
% 12.71/5.28  Demodulation         : 2.02
% 12.71/5.28  BG Simplification    : 0.10
% 12.71/5.28  Subsumption          : 0.63
% 12.71/5.28  Abstraction          : 0.14
% 12.71/5.28  MUC search           : 0.00
% 12.71/5.28  Cooper               : 0.00
% 12.71/5.28  Total                : 4.51
% 12.71/5.28  Index Insertion      : 0.00
% 12.71/5.28  Index Deletion       : 0.00
% 12.71/5.28  Index Matching       : 0.00
% 12.71/5.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
