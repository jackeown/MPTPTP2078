%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:08 EST 2020

% Result     : Theorem 5.18s
% Output     : CNFRefutation 5.18s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 281 expanded)
%              Number of leaves         :   40 ( 117 expanded)
%              Depth                    :    9
%              Number of atoms          :  201 ( 810 expanded)
%              Number of equality atoms :   35 (  80 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_148,negated_conjecture,(
    ~ ! [A,B,C] :
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

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_89,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_36,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_87,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_67,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_128,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_106,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_122,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_xboole_0(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64)))
      | ~ v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_134,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_122])).

tff(c_136,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_40,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_67,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_54,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_52,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_46,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_32,plain,(
    ! [A_30] : k6_relat_1(A_30) = k6_partfun1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6,plain,(
    ! [A_3] : v2_funct_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_56,plain,(
    ! [A_3] : v2_funct_1(k6_partfun1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_6])).

tff(c_28,plain,(
    ! [A_24,B_25,F_29,D_27,C_26,E_28] :
      ( m1_subset_1(k1_partfun1(A_24,B_25,C_26,D_27,E_28,F_29),k1_zfmisc_1(k2_zfmisc_1(A_24,D_27)))
      | ~ m1_subset_1(F_29,k1_zfmisc_1(k2_zfmisc_1(C_26,D_27)))
      | ~ v1_funct_1(F_29)
      | ~ m1_subset_1(E_28,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25)))
      | ~ v1_funct_1(E_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_22,plain,(
    ! [A_21] : m1_subset_1(k6_relat_1(A_21),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_55,plain,(
    ! [A_21] : m1_subset_1(k6_partfun1(A_21),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_22])).

tff(c_42,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_334,plain,(
    ! [D_78,C_79,A_80,B_81] :
      ( D_78 = C_79
      | ~ r2_relset_1(A_80,B_81,C_79,D_78)
      | ~ m1_subset_1(D_78,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81)))
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_342,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_42,c_334])).

tff(c_357,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_342])).

tff(c_1029,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_357])).

tff(c_1456,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_1029])).

tff(c_1460,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_48,c_44,c_1456])).

tff(c_1461,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_357])).

tff(c_1556,plain,(
    ! [B_144,A_141,D_143,C_145,E_142] :
      ( k1_xboole_0 = C_145
      | v2_funct_1(D_143)
      | ~ v2_funct_1(k1_partfun1(A_141,B_144,B_144,C_145,D_143,E_142))
      | ~ m1_subset_1(E_142,k1_zfmisc_1(k2_zfmisc_1(B_144,C_145)))
      | ~ v1_funct_2(E_142,B_144,C_145)
      | ~ v1_funct_1(E_142)
      | ~ m1_subset_1(D_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_144)))
      | ~ v1_funct_2(D_143,A_141,B_144)
      | ~ v1_funct_1(D_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1558,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1461,c_1556])).

tff(c_1560,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_44,c_56,c_1558])).

tff(c_1561,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_1560])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1587,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1561,c_2])).

tff(c_1589,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_1587])).

tff(c_1591,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_68,plain,(
    ! [B_45,A_46] :
      ( ~ v1_xboole_0(B_45)
      | B_45 = A_46
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_71,plain,(
    ! [A_46] :
      ( k1_xboole_0 = A_46
      | ~ v1_xboole_0(A_46) ) ),
    inference(resolution,[status(thm)],[c_2,c_68])).

tff(c_1604,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1591,c_71])).

tff(c_1590,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_1597,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1590,c_71])).

tff(c_1613,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1604,c_1597])).

tff(c_1624,plain,(
    ~ v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1613,c_67])).

tff(c_1680,plain,(
    ! [A_149] :
      ( v1_xboole_0(k6_partfun1(A_149))
      | ~ v1_xboole_0(A_149) ) ),
    inference(resolution,[status(thm)],[c_55,c_122])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1605,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_1591,c_4])).

tff(c_1688,plain,(
    ! [A_150] :
      ( k6_partfun1(A_150) = '#skF_1'
      | ~ v1_xboole_0(A_150) ) ),
    inference(resolution,[status(thm)],[c_1680,c_1605])).

tff(c_1696,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1591,c_1688])).

tff(c_1723,plain,(
    v2_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1696,c_56])).

tff(c_1731,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1624,c_1723])).

tff(c_1732,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1745,plain,(
    ! [C_158,A_159,B_160] :
      ( v1_relat_1(C_158)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1757,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_1745])).

tff(c_1758,plain,(
    ! [C_161,B_162,A_163] :
      ( v5_relat_1(C_161,B_162)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_163,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1770,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_1758])).

tff(c_1820,plain,(
    ! [A_176,B_177,D_178] :
      ( r2_relset_1(A_176,B_177,D_178,D_178)
      | ~ m1_subset_1(D_178,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1827,plain,(
    ! [A_21] : r2_relset_1(A_21,A_21,k6_partfun1(A_21),k6_partfun1(A_21)) ),
    inference(resolution,[status(thm)],[c_55,c_1820])).

tff(c_1943,plain,(
    ! [A_182,B_183,C_184] :
      ( k2_relset_1(A_182,B_183,C_184) = k2_relat_1(C_184)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_182,B_183))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1959,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_1943])).

tff(c_1995,plain,(
    ! [D_187,C_188,A_189,B_190] :
      ( D_187 = C_188
      | ~ r2_relset_1(A_189,B_190,C_188,D_187)
      | ~ m1_subset_1(D_187,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190)))
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2003,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_42,c_1995])).

tff(c_2018,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_2003])).

tff(c_2044,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2018])).

tff(c_2755,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_2044])).

tff(c_2759,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_48,c_44,c_2755])).

tff(c_2760,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2018])).

tff(c_4331,plain,(
    ! [A_297,B_298,C_299,D_300] :
      ( k2_relset_1(A_297,B_298,C_299) = B_298
      | ~ r2_relset_1(B_298,B_298,k1_partfun1(B_298,A_297,A_297,B_298,D_300,C_299),k6_partfun1(B_298))
      | ~ m1_subset_1(D_300,k1_zfmisc_1(k2_zfmisc_1(B_298,A_297)))
      | ~ v1_funct_2(D_300,B_298,A_297)
      | ~ v1_funct_1(D_300)
      | ~ m1_subset_1(C_299,k1_zfmisc_1(k2_zfmisc_1(A_297,B_298)))
      | ~ v1_funct_2(C_299,A_297,B_298)
      | ~ v1_funct_1(C_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_4349,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2760,c_4331])).

tff(c_4357,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_54,c_52,c_50,c_1827,c_1959,c_4349])).

tff(c_24,plain,(
    ! [B_23] :
      ( v2_funct_2(B_23,k2_relat_1(B_23))
      | ~ v5_relat_1(B_23,k2_relat_1(B_23))
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4362,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4357,c_24])).

tff(c_4366,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1757,c_1770,c_4357,c_4362])).

tff(c_4368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1732,c_4366])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n004.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 18:41:08 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.18/1.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.18/1.94  
% 5.18/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.18/1.95  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.18/1.95  
% 5.18/1.95  %Foreground sorts:
% 5.18/1.95  
% 5.18/1.95  
% 5.18/1.95  %Background operators:
% 5.18/1.95  
% 5.18/1.95  
% 5.18/1.95  %Foreground operators:
% 5.18/1.95  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.18/1.95  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.18/1.95  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.18/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.18/1.95  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.18/1.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.18/1.95  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.18/1.95  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.18/1.95  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.18/1.95  tff('#skF_2', type, '#skF_2': $i).
% 5.18/1.95  tff('#skF_3', type, '#skF_3': $i).
% 5.18/1.95  tff('#skF_1', type, '#skF_1': $i).
% 5.18/1.95  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.18/1.95  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.18/1.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.18/1.95  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.18/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.18/1.95  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.18/1.95  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.18/1.95  tff('#skF_4', type, '#skF_4': $i).
% 5.18/1.95  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.18/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.18/1.95  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.18/1.95  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.18/1.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.18/1.95  
% 5.18/1.96  tff(f_148, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 5.18/1.96  tff(f_53, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 5.18/1.96  tff(f_89, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.18/1.96  tff(f_36, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 5.18/1.96  tff(f_87, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.18/1.96  tff(f_67, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 5.18/1.96  tff(f_65, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.18/1.96  tff(f_128, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 5.18/1.96  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.18/1.96  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 5.18/1.96  tff(f_40, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.18/1.96  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.18/1.96  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.18/1.96  tff(f_106, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 5.18/1.96  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 5.18/1.96  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.18/1.96  tff(c_122, plain, (![C_62, A_63, B_64]: (v1_xboole_0(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))) | ~v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.18/1.96  tff(c_134, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_122])).
% 5.18/1.96  tff(c_136, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_134])).
% 5.18/1.96  tff(c_40, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.18/1.96  tff(c_67, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_40])).
% 5.18/1.96  tff(c_54, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.18/1.96  tff(c_52, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.18/1.96  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.18/1.96  tff(c_46, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.18/1.96  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.18/1.96  tff(c_32, plain, (![A_30]: (k6_relat_1(A_30)=k6_partfun1(A_30))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.18/1.96  tff(c_6, plain, (![A_3]: (v2_funct_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.18/1.96  tff(c_56, plain, (![A_3]: (v2_funct_1(k6_partfun1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_6])).
% 5.18/1.96  tff(c_28, plain, (![A_24, B_25, F_29, D_27, C_26, E_28]: (m1_subset_1(k1_partfun1(A_24, B_25, C_26, D_27, E_28, F_29), k1_zfmisc_1(k2_zfmisc_1(A_24, D_27))) | ~m1_subset_1(F_29, k1_zfmisc_1(k2_zfmisc_1(C_26, D_27))) | ~v1_funct_1(F_29) | ~m1_subset_1(E_28, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))) | ~v1_funct_1(E_28))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.18/1.96  tff(c_22, plain, (![A_21]: (m1_subset_1(k6_relat_1(A_21), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.18/1.96  tff(c_55, plain, (![A_21]: (m1_subset_1(k6_partfun1(A_21), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_22])).
% 5.18/1.96  tff(c_42, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.18/1.96  tff(c_334, plain, (![D_78, C_79, A_80, B_81]: (D_78=C_79 | ~r2_relset_1(A_80, B_81, C_79, D_78) | ~m1_subset_1(D_78, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.18/1.96  tff(c_342, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_42, c_334])).
% 5.18/1.96  tff(c_357, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_342])).
% 5.18/1.96  tff(c_1029, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_357])).
% 5.18/1.96  tff(c_1456, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_1029])).
% 5.18/1.96  tff(c_1460, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_48, c_44, c_1456])).
% 5.18/1.96  tff(c_1461, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_357])).
% 5.18/1.96  tff(c_1556, plain, (![B_144, A_141, D_143, C_145, E_142]: (k1_xboole_0=C_145 | v2_funct_1(D_143) | ~v2_funct_1(k1_partfun1(A_141, B_144, B_144, C_145, D_143, E_142)) | ~m1_subset_1(E_142, k1_zfmisc_1(k2_zfmisc_1(B_144, C_145))) | ~v1_funct_2(E_142, B_144, C_145) | ~v1_funct_1(E_142) | ~m1_subset_1(D_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_144))) | ~v1_funct_2(D_143, A_141, B_144) | ~v1_funct_1(D_143))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.18/1.96  tff(c_1558, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1461, c_1556])).
% 5.18/1.96  tff(c_1560, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_44, c_56, c_1558])).
% 5.18/1.96  tff(c_1561, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_67, c_1560])).
% 5.18/1.96  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.18/1.96  tff(c_1587, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1561, c_2])).
% 5.18/1.96  tff(c_1589, plain, $false, inference(negUnitSimplification, [status(thm)], [c_136, c_1587])).
% 5.18/1.96  tff(c_1591, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_134])).
% 5.18/1.96  tff(c_68, plain, (![B_45, A_46]: (~v1_xboole_0(B_45) | B_45=A_46 | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.18/1.96  tff(c_71, plain, (![A_46]: (k1_xboole_0=A_46 | ~v1_xboole_0(A_46))), inference(resolution, [status(thm)], [c_2, c_68])).
% 5.18/1.96  tff(c_1604, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_1591, c_71])).
% 5.18/1.96  tff(c_1590, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_134])).
% 5.18/1.96  tff(c_1597, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1590, c_71])).
% 5.18/1.96  tff(c_1613, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1604, c_1597])).
% 5.18/1.96  tff(c_1624, plain, (~v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1613, c_67])).
% 5.18/1.96  tff(c_1680, plain, (![A_149]: (v1_xboole_0(k6_partfun1(A_149)) | ~v1_xboole_0(A_149))), inference(resolution, [status(thm)], [c_55, c_122])).
% 5.18/1.96  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.18/1.96  tff(c_1605, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_1591, c_4])).
% 5.18/1.96  tff(c_1688, plain, (![A_150]: (k6_partfun1(A_150)='#skF_1' | ~v1_xboole_0(A_150))), inference(resolution, [status(thm)], [c_1680, c_1605])).
% 5.18/1.96  tff(c_1696, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_1591, c_1688])).
% 5.18/1.96  tff(c_1723, plain, (v2_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1696, c_56])).
% 5.18/1.96  tff(c_1731, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1624, c_1723])).
% 5.18/1.96  tff(c_1732, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_40])).
% 5.18/1.96  tff(c_1745, plain, (![C_158, A_159, B_160]: (v1_relat_1(C_158) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.18/1.96  tff(c_1757, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_1745])).
% 5.18/1.96  tff(c_1758, plain, (![C_161, B_162, A_163]: (v5_relat_1(C_161, B_162) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_163, B_162))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.18/1.96  tff(c_1770, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_1758])).
% 5.18/1.96  tff(c_1820, plain, (![A_176, B_177, D_178]: (r2_relset_1(A_176, B_177, D_178, D_178) | ~m1_subset_1(D_178, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.18/1.96  tff(c_1827, plain, (![A_21]: (r2_relset_1(A_21, A_21, k6_partfun1(A_21), k6_partfun1(A_21)))), inference(resolution, [status(thm)], [c_55, c_1820])).
% 5.18/1.96  tff(c_1943, plain, (![A_182, B_183, C_184]: (k2_relset_1(A_182, B_183, C_184)=k2_relat_1(C_184) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.18/1.96  tff(c_1959, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_1943])).
% 5.18/1.96  tff(c_1995, plain, (![D_187, C_188, A_189, B_190]: (D_187=C_188 | ~r2_relset_1(A_189, B_190, C_188, D_187) | ~m1_subset_1(D_187, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.18/1.96  tff(c_2003, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_42, c_1995])).
% 5.18/1.96  tff(c_2018, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_2003])).
% 5.18/1.96  tff(c_2044, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2018])).
% 5.18/1.96  tff(c_2755, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_2044])).
% 5.18/1.96  tff(c_2759, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_48, c_44, c_2755])).
% 5.18/1.96  tff(c_2760, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2018])).
% 5.18/1.96  tff(c_4331, plain, (![A_297, B_298, C_299, D_300]: (k2_relset_1(A_297, B_298, C_299)=B_298 | ~r2_relset_1(B_298, B_298, k1_partfun1(B_298, A_297, A_297, B_298, D_300, C_299), k6_partfun1(B_298)) | ~m1_subset_1(D_300, k1_zfmisc_1(k2_zfmisc_1(B_298, A_297))) | ~v1_funct_2(D_300, B_298, A_297) | ~v1_funct_1(D_300) | ~m1_subset_1(C_299, k1_zfmisc_1(k2_zfmisc_1(A_297, B_298))) | ~v1_funct_2(C_299, A_297, B_298) | ~v1_funct_1(C_299))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.18/1.96  tff(c_4349, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2760, c_4331])).
% 5.18/1.96  tff(c_4357, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_54, c_52, c_50, c_1827, c_1959, c_4349])).
% 5.18/1.96  tff(c_24, plain, (![B_23]: (v2_funct_2(B_23, k2_relat_1(B_23)) | ~v5_relat_1(B_23, k2_relat_1(B_23)) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.18/1.96  tff(c_4362, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4357, c_24])).
% 5.18/1.96  tff(c_4366, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1757, c_1770, c_4357, c_4362])).
% 5.18/1.96  tff(c_4368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1732, c_4366])).
% 5.18/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.18/1.96  
% 5.18/1.96  Inference rules
% 5.18/1.96  ----------------------
% 5.18/1.96  #Ref     : 0
% 5.18/1.96  #Sup     : 1159
% 5.18/1.96  #Fact    : 0
% 5.18/1.96  #Define  : 0
% 5.18/1.96  #Split   : 19
% 5.18/1.96  #Chain   : 0
% 5.18/1.96  #Close   : 0
% 5.18/1.96  
% 5.18/1.96  Ordering : KBO
% 5.18/1.96  
% 5.18/1.96  Simplification rules
% 5.18/1.96  ----------------------
% 5.18/1.96  #Subsume      : 270
% 5.18/1.96  #Demod        : 645
% 5.18/1.96  #Tautology    : 263
% 5.18/1.96  #SimpNegUnit  : 4
% 5.18/1.96  #BackRed      : 42
% 5.18/1.96  
% 5.18/1.96  #Partial instantiations: 0
% 5.18/1.96  #Strategies tried      : 1
% 5.18/1.96  
% 5.18/1.96  Timing (in seconds)
% 5.18/1.96  ----------------------
% 5.18/1.97  Preprocessing        : 0.34
% 5.18/1.97  Parsing              : 0.18
% 5.18/1.97  CNF conversion       : 0.02
% 5.18/1.97  Main loop            : 0.87
% 5.18/1.97  Inferencing          : 0.28
% 5.18/1.97  Reduction            : 0.29
% 5.18/1.97  Demodulation         : 0.21
% 5.18/1.97  BG Simplification    : 0.03
% 5.18/1.97  Subsumption          : 0.20
% 5.18/1.97  Abstraction          : 0.04
% 5.18/1.97  MUC search           : 0.00
% 5.18/1.97  Cooper               : 0.00
% 5.18/1.97  Total                : 1.25
% 5.18/1.97  Index Insertion      : 0.00
% 5.18/1.97  Index Deletion       : 0.00
% 5.18/1.97  Index Matching       : 0.00
% 5.18/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
