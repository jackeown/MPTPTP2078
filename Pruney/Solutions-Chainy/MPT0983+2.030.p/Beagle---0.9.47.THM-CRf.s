%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:05 EST 2020

% Result     : Theorem 4.80s
% Output     : CNFRefutation 5.11s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 507 expanded)
%              Number of leaves         :   41 ( 193 expanded)
%              Depth                    :   10
%              Number of atoms          :  226 (1469 expanded)
%              Number of equality atoms :   50 ( 189 expanded)
%              Maximal formula depth    :   15 (   3 average)
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

tff(f_150,negated_conjecture,(
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

tff(f_91,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_45,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_89,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_69,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_130,axiom,(
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

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_108,axiom,(
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

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_46,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_94,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_60,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_58,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_54,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_52,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_38,plain,(
    ! [A_30] : k6_relat_1(A_30) = k6_partfun1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_14,plain,(
    ! [A_7] : v2_funct_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_62,plain,(
    ! [A_7] : v2_funct_1(k6_partfun1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_14])).

tff(c_34,plain,(
    ! [A_24,B_25,F_29,D_27,C_26,E_28] :
      ( m1_subset_1(k1_partfun1(A_24,B_25,C_26,D_27,E_28,F_29),k1_zfmisc_1(k2_zfmisc_1(A_24,D_27)))
      | ~ m1_subset_1(F_29,k1_zfmisc_1(k2_zfmisc_1(C_26,D_27)))
      | ~ v1_funct_1(F_29)
      | ~ m1_subset_1(E_28,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25)))
      | ~ v1_funct_1(E_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_28,plain,(
    ! [A_21] : m1_subset_1(k6_relat_1(A_21),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_61,plain,(
    ! [A_21] : m1_subset_1(k6_partfun1(A_21),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_28])).

tff(c_48,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_898,plain,(
    ! [D_179,C_180,A_181,B_182] :
      ( D_179 = C_180
      | ~ r2_relset_1(A_181,B_182,C_180,D_179)
      | ~ m1_subset_1(D_179,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182)))
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_908,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_48,c_898])).

tff(c_927,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_908])).

tff(c_1405,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_927])).

tff(c_1409,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_1405])).

tff(c_1413,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_54,c_50,c_1409])).

tff(c_1414,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_927])).

tff(c_44,plain,(
    ! [D_39,A_36,E_41,C_38,B_37] :
      ( k1_xboole_0 = C_38
      | v2_funct_1(D_39)
      | ~ v2_funct_1(k1_partfun1(A_36,B_37,B_37,C_38,D_39,E_41))
      | ~ m1_subset_1(E_41,k1_zfmisc_1(k2_zfmisc_1(B_37,C_38)))
      | ~ v1_funct_2(E_41,B_37,C_38)
      | ~ v1_funct_1(E_41)
      | ~ m1_subset_1(D_39,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_2(D_39,A_36,B_37)
      | ~ v1_funct_1(D_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1422,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1414,c_44])).

tff(c_1429,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_52,c_50,c_62,c_1422])).

tff(c_1430,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_1429])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1468,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1430,c_2])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1466,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1430,c_1430,c_8])).

tff(c_149,plain,(
    ! [B_56,A_57] :
      ( v1_xboole_0(B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57))
      | ~ v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_166,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_50,c_149])).

tff(c_200,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_1582,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1466,c_200])).

tff(c_1586,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1468,c_1582])).

tff(c_1587,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_1592,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1587,c_4])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1603,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_4',B_3) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1592,c_1592,c_10])).

tff(c_1604,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1592,c_1592,c_8])).

tff(c_1588,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_1596,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1588,c_4])).

tff(c_1626,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1592,c_1596])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( k1_xboole_0 = B_3
      | k1_xboole_0 = A_2
      | k2_zfmisc_1(A_2,B_3) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1809,plain,(
    ! [B_334,A_335] :
      ( B_334 = '#skF_4'
      | A_335 = '#skF_4'
      | k2_zfmisc_1(A_335,B_334) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1592,c_1592,c_1592,c_6])).

tff(c_1823,plain,
    ( '#skF_1' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1626,c_1809])).

tff(c_1824,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1823])).

tff(c_167,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_56,c_149])).

tff(c_187,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_1830,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1824,c_187])).

tff(c_1838,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1587,c_1604,c_1830])).

tff(c_1839,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1823])).

tff(c_1865,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1839,c_187])).

tff(c_1873,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1587,c_1603,c_1865])).

tff(c_1874,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_1879,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1874,c_4])).

tff(c_104,plain,(
    ! [A_48] : m1_subset_1(k6_partfun1(A_48),k1_zfmisc_1(k2_zfmisc_1(A_48,A_48))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_28])).

tff(c_108,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_104])).

tff(c_152,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_108,c_149])).

tff(c_164,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_152])).

tff(c_171,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_164,c_4])).

tff(c_182,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_62])).

tff(c_1895,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1879,c_182])).

tff(c_1896,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_1895])).

tff(c_1897,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1965,plain,(
    ! [C_344,A_345,B_346] :
      ( v1_relat_1(C_344)
      | ~ m1_subset_1(C_344,k1_zfmisc_1(k2_zfmisc_1(A_345,B_346))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1981,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1965])).

tff(c_1999,plain,(
    ! [C_349,B_350,A_351] :
      ( v5_relat_1(C_349,B_350)
      | ~ m1_subset_1(C_349,k1_zfmisc_1(k2_zfmisc_1(A_351,B_350))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2017,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_1999])).

tff(c_2117,plain,(
    ! [A_367,B_368,D_369] :
      ( r2_relset_1(A_367,B_368,D_369,D_369)
      | ~ m1_subset_1(D_369,k1_zfmisc_1(k2_zfmisc_1(A_367,B_368))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2128,plain,(
    ! [A_21] : r2_relset_1(A_21,A_21,k6_partfun1(A_21),k6_partfun1(A_21)) ),
    inference(resolution,[status(thm)],[c_61,c_2117])).

tff(c_2146,plain,(
    ! [A_374,B_375,C_376] :
      ( k2_relset_1(A_374,B_375,C_376) = k2_relat_1(C_376)
      | ~ m1_subset_1(C_376,k1_zfmisc_1(k2_zfmisc_1(A_374,B_375))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2164,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_2146])).

tff(c_2293,plain,(
    ! [C_401,A_405,E_403,B_402,F_404,D_406] :
      ( m1_subset_1(k1_partfun1(A_405,B_402,C_401,D_406,E_403,F_404),k1_zfmisc_1(k2_zfmisc_1(A_405,D_406)))
      | ~ m1_subset_1(F_404,k1_zfmisc_1(k2_zfmisc_1(C_401,D_406)))
      | ~ v1_funct_1(F_404)
      | ~ m1_subset_1(E_403,k1_zfmisc_1(k2_zfmisc_1(A_405,B_402)))
      | ~ v1_funct_1(E_403) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2202,plain,(
    ! [D_382,C_383,A_384,B_385] :
      ( D_382 = C_383
      | ~ r2_relset_1(A_384,B_385,C_383,D_382)
      | ~ m1_subset_1(D_382,k1_zfmisc_1(k2_zfmisc_1(A_384,B_385)))
      | ~ m1_subset_1(C_383,k1_zfmisc_1(k2_zfmisc_1(A_384,B_385))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2212,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_48,c_2202])).

tff(c_2231,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_2212])).

tff(c_2247,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2231])).

tff(c_2298,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2293,c_2247])).

tff(c_2326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_54,c_50,c_2298])).

tff(c_2327,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2231])).

tff(c_2654,plain,(
    ! [A_489,B_490,C_491,D_492] :
      ( k2_relset_1(A_489,B_490,C_491) = B_490
      | ~ r2_relset_1(B_490,B_490,k1_partfun1(B_490,A_489,A_489,B_490,D_492,C_491),k6_partfun1(B_490))
      | ~ m1_subset_1(D_492,k1_zfmisc_1(k2_zfmisc_1(B_490,A_489)))
      | ~ v1_funct_2(D_492,B_490,A_489)
      | ~ v1_funct_1(D_492)
      | ~ m1_subset_1(C_491,k1_zfmisc_1(k2_zfmisc_1(A_489,B_490)))
      | ~ v1_funct_2(C_491,A_489,B_490)
      | ~ v1_funct_1(C_491) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2657,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2327,c_2654])).

tff(c_2662,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_60,c_58,c_56,c_2128,c_2164,c_2657])).

tff(c_30,plain,(
    ! [B_23] :
      ( v2_funct_2(B_23,k2_relat_1(B_23))
      | ~ v5_relat_1(B_23,k2_relat_1(B_23))
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2668,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2662,c_30])).

tff(c_2672,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1981,c_2017,c_2662,c_2668])).

tff(c_2674,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1897,c_2672])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:20:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.80/1.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.80/1.90  
% 4.80/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.80/1.90  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.80/1.90  
% 4.80/1.90  %Foreground sorts:
% 4.80/1.90  
% 4.80/1.90  
% 4.80/1.90  %Background operators:
% 4.80/1.90  
% 4.80/1.90  
% 4.80/1.90  %Foreground operators:
% 4.80/1.90  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.80/1.90  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.80/1.90  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.80/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.80/1.90  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.80/1.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.80/1.90  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.80/1.90  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.80/1.90  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.80/1.90  tff('#skF_2', type, '#skF_2': $i).
% 4.80/1.90  tff('#skF_3', type, '#skF_3': $i).
% 4.80/1.90  tff('#skF_1', type, '#skF_1': $i).
% 4.80/1.90  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.80/1.90  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.80/1.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.80/1.90  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.80/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.80/1.90  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.80/1.90  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.80/1.90  tff('#skF_4', type, '#skF_4': $i).
% 4.80/1.90  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.80/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.80/1.90  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.80/1.90  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.80/1.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.80/1.90  
% 5.11/1.92  tff(f_150, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 5.11/1.92  tff(f_91, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.11/1.92  tff(f_45, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 5.11/1.92  tff(f_89, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.11/1.92  tff(f_69, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 5.11/1.92  tff(f_67, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.11/1.92  tff(f_130, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 5.11/1.92  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.11/1.92  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.11/1.92  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 5.11/1.92  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.11/1.92  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.11/1.92  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.11/1.92  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.11/1.92  tff(f_108, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 5.11/1.92  tff(f_77, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 5.11/1.92  tff(c_46, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.11/1.92  tff(c_94, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_46])).
% 5.11/1.92  tff(c_60, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.11/1.92  tff(c_58, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.11/1.92  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.11/1.92  tff(c_54, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.11/1.92  tff(c_52, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.11/1.92  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.11/1.92  tff(c_38, plain, (![A_30]: (k6_relat_1(A_30)=k6_partfun1(A_30))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.11/1.92  tff(c_14, plain, (![A_7]: (v2_funct_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.11/1.92  tff(c_62, plain, (![A_7]: (v2_funct_1(k6_partfun1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_14])).
% 5.11/1.92  tff(c_34, plain, (![A_24, B_25, F_29, D_27, C_26, E_28]: (m1_subset_1(k1_partfun1(A_24, B_25, C_26, D_27, E_28, F_29), k1_zfmisc_1(k2_zfmisc_1(A_24, D_27))) | ~m1_subset_1(F_29, k1_zfmisc_1(k2_zfmisc_1(C_26, D_27))) | ~v1_funct_1(F_29) | ~m1_subset_1(E_28, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))) | ~v1_funct_1(E_28))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.11/1.92  tff(c_28, plain, (![A_21]: (m1_subset_1(k6_relat_1(A_21), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.11/1.92  tff(c_61, plain, (![A_21]: (m1_subset_1(k6_partfun1(A_21), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_28])).
% 5.11/1.92  tff(c_48, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.11/1.92  tff(c_898, plain, (![D_179, C_180, A_181, B_182]: (D_179=C_180 | ~r2_relset_1(A_181, B_182, C_180, D_179) | ~m1_subset_1(D_179, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.11/1.92  tff(c_908, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_48, c_898])).
% 5.11/1.92  tff(c_927, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_908])).
% 5.11/1.92  tff(c_1405, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_927])).
% 5.11/1.92  tff(c_1409, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_1405])).
% 5.11/1.92  tff(c_1413, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_54, c_50, c_1409])).
% 5.11/1.92  tff(c_1414, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_927])).
% 5.11/1.92  tff(c_44, plain, (![D_39, A_36, E_41, C_38, B_37]: (k1_xboole_0=C_38 | v2_funct_1(D_39) | ~v2_funct_1(k1_partfun1(A_36, B_37, B_37, C_38, D_39, E_41)) | ~m1_subset_1(E_41, k1_zfmisc_1(k2_zfmisc_1(B_37, C_38))) | ~v1_funct_2(E_41, B_37, C_38) | ~v1_funct_1(E_41) | ~m1_subset_1(D_39, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_2(D_39, A_36, B_37) | ~v1_funct_1(D_39))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.11/1.92  tff(c_1422, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1414, c_44])).
% 5.11/1.92  tff(c_1429, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_52, c_50, c_62, c_1422])).
% 5.11/1.92  tff(c_1430, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_94, c_1429])).
% 5.11/1.92  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.11/1.92  tff(c_1468, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1430, c_2])).
% 5.11/1.92  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.11/1.92  tff(c_1466, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1430, c_1430, c_8])).
% 5.11/1.92  tff(c_149, plain, (![B_56, A_57]: (v1_xboole_0(B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)) | ~v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.11/1.92  tff(c_166, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_50, c_149])).
% 5.11/1.92  tff(c_200, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_166])).
% 5.11/1.92  tff(c_1582, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1466, c_200])).
% 5.11/1.92  tff(c_1586, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1468, c_1582])).
% 5.11/1.92  tff(c_1587, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_166])).
% 5.11/1.92  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 5.11/1.92  tff(c_1592, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1587, c_4])).
% 5.11/1.92  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.11/1.92  tff(c_1603, plain, (![B_3]: (k2_zfmisc_1('#skF_4', B_3)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1592, c_1592, c_10])).
% 5.11/1.92  tff(c_1604, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1592, c_1592, c_8])).
% 5.11/1.92  tff(c_1588, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_166])).
% 5.11/1.92  tff(c_1596, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_1588, c_4])).
% 5.11/1.92  tff(c_1626, plain, (k2_zfmisc_1('#skF_2', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1592, c_1596])).
% 5.11/1.92  tff(c_6, plain, (![B_3, A_2]: (k1_xboole_0=B_3 | k1_xboole_0=A_2 | k2_zfmisc_1(A_2, B_3)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.11/1.92  tff(c_1809, plain, (![B_334, A_335]: (B_334='#skF_4' | A_335='#skF_4' | k2_zfmisc_1(A_335, B_334)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1592, c_1592, c_1592, c_6])).
% 5.11/1.92  tff(c_1823, plain, ('#skF_1'='#skF_4' | '#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1626, c_1809])).
% 5.11/1.92  tff(c_1824, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_1823])).
% 5.11/1.92  tff(c_167, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_56, c_149])).
% 5.11/1.92  tff(c_187, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_167])).
% 5.11/1.92  tff(c_1830, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1824, c_187])).
% 5.11/1.92  tff(c_1838, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1587, c_1604, c_1830])).
% 5.11/1.92  tff(c_1839, plain, ('#skF_1'='#skF_4'), inference(splitRight, [status(thm)], [c_1823])).
% 5.11/1.92  tff(c_1865, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1839, c_187])).
% 5.11/1.92  tff(c_1873, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1587, c_1603, c_1865])).
% 5.11/1.92  tff(c_1874, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_167])).
% 5.11/1.92  tff(c_1879, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1874, c_4])).
% 5.11/1.92  tff(c_104, plain, (![A_48]: (m1_subset_1(k6_partfun1(A_48), k1_zfmisc_1(k2_zfmisc_1(A_48, A_48))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_28])).
% 5.11/1.92  tff(c_108, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_104])).
% 5.11/1.92  tff(c_152, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_108, c_149])).
% 5.11/1.92  tff(c_164, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_152])).
% 5.11/1.92  tff(c_171, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_164, c_4])).
% 5.11/1.92  tff(c_182, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_171, c_62])).
% 5.11/1.92  tff(c_1895, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1879, c_182])).
% 5.11/1.92  tff(c_1896, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_1895])).
% 5.11/1.92  tff(c_1897, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 5.11/1.92  tff(c_1965, plain, (![C_344, A_345, B_346]: (v1_relat_1(C_344) | ~m1_subset_1(C_344, k1_zfmisc_1(k2_zfmisc_1(A_345, B_346))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.11/1.92  tff(c_1981, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_1965])).
% 5.11/1.92  tff(c_1999, plain, (![C_349, B_350, A_351]: (v5_relat_1(C_349, B_350) | ~m1_subset_1(C_349, k1_zfmisc_1(k2_zfmisc_1(A_351, B_350))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.11/1.92  tff(c_2017, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_1999])).
% 5.11/1.92  tff(c_2117, plain, (![A_367, B_368, D_369]: (r2_relset_1(A_367, B_368, D_369, D_369) | ~m1_subset_1(D_369, k1_zfmisc_1(k2_zfmisc_1(A_367, B_368))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.11/1.92  tff(c_2128, plain, (![A_21]: (r2_relset_1(A_21, A_21, k6_partfun1(A_21), k6_partfun1(A_21)))), inference(resolution, [status(thm)], [c_61, c_2117])).
% 5.11/1.92  tff(c_2146, plain, (![A_374, B_375, C_376]: (k2_relset_1(A_374, B_375, C_376)=k2_relat_1(C_376) | ~m1_subset_1(C_376, k1_zfmisc_1(k2_zfmisc_1(A_374, B_375))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.11/1.92  tff(c_2164, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_2146])).
% 5.11/1.92  tff(c_2293, plain, (![C_401, A_405, E_403, B_402, F_404, D_406]: (m1_subset_1(k1_partfun1(A_405, B_402, C_401, D_406, E_403, F_404), k1_zfmisc_1(k2_zfmisc_1(A_405, D_406))) | ~m1_subset_1(F_404, k1_zfmisc_1(k2_zfmisc_1(C_401, D_406))) | ~v1_funct_1(F_404) | ~m1_subset_1(E_403, k1_zfmisc_1(k2_zfmisc_1(A_405, B_402))) | ~v1_funct_1(E_403))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.11/1.92  tff(c_2202, plain, (![D_382, C_383, A_384, B_385]: (D_382=C_383 | ~r2_relset_1(A_384, B_385, C_383, D_382) | ~m1_subset_1(D_382, k1_zfmisc_1(k2_zfmisc_1(A_384, B_385))) | ~m1_subset_1(C_383, k1_zfmisc_1(k2_zfmisc_1(A_384, B_385))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.11/1.92  tff(c_2212, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_48, c_2202])).
% 5.11/1.92  tff(c_2231, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_2212])).
% 5.11/1.92  tff(c_2247, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2231])).
% 5.11/1.92  tff(c_2298, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2293, c_2247])).
% 5.11/1.92  tff(c_2326, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_54, c_50, c_2298])).
% 5.11/1.92  tff(c_2327, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2231])).
% 5.11/1.92  tff(c_2654, plain, (![A_489, B_490, C_491, D_492]: (k2_relset_1(A_489, B_490, C_491)=B_490 | ~r2_relset_1(B_490, B_490, k1_partfun1(B_490, A_489, A_489, B_490, D_492, C_491), k6_partfun1(B_490)) | ~m1_subset_1(D_492, k1_zfmisc_1(k2_zfmisc_1(B_490, A_489))) | ~v1_funct_2(D_492, B_490, A_489) | ~v1_funct_1(D_492) | ~m1_subset_1(C_491, k1_zfmisc_1(k2_zfmisc_1(A_489, B_490))) | ~v1_funct_2(C_491, A_489, B_490) | ~v1_funct_1(C_491))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.11/1.92  tff(c_2657, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2327, c_2654])).
% 5.11/1.92  tff(c_2662, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_60, c_58, c_56, c_2128, c_2164, c_2657])).
% 5.11/1.92  tff(c_30, plain, (![B_23]: (v2_funct_2(B_23, k2_relat_1(B_23)) | ~v5_relat_1(B_23, k2_relat_1(B_23)) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.11/1.92  tff(c_2668, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2662, c_30])).
% 5.11/1.92  tff(c_2672, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1981, c_2017, c_2662, c_2668])).
% 5.11/1.92  tff(c_2674, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1897, c_2672])).
% 5.11/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.11/1.92  
% 5.11/1.92  Inference rules
% 5.11/1.92  ----------------------
% 5.11/1.92  #Ref     : 0
% 5.11/1.92  #Sup     : 553
% 5.11/1.92  #Fact    : 0
% 5.11/1.92  #Define  : 0
% 5.11/1.92  #Split   : 18
% 5.11/1.92  #Chain   : 0
% 5.11/1.92  #Close   : 0
% 5.11/1.92  
% 5.11/1.92  Ordering : KBO
% 5.11/1.92  
% 5.11/1.92  Simplification rules
% 5.11/1.92  ----------------------
% 5.11/1.92  #Subsume      : 51
% 5.11/1.92  #Demod        : 716
% 5.11/1.92  #Tautology    : 208
% 5.11/1.92  #SimpNegUnit  : 9
% 5.11/1.92  #BackRed      : 200
% 5.11/1.92  
% 5.11/1.92  #Partial instantiations: 0
% 5.11/1.92  #Strategies tried      : 1
% 5.11/1.92  
% 5.11/1.92  Timing (in seconds)
% 5.11/1.92  ----------------------
% 5.11/1.93  Preprocessing        : 0.33
% 5.11/1.93  Parsing              : 0.17
% 5.11/1.93  CNF conversion       : 0.02
% 5.11/1.93  Main loop            : 0.79
% 5.11/1.93  Inferencing          : 0.27
% 5.11/1.93  Reduction            : 0.28
% 5.11/1.93  Demodulation         : 0.20
% 5.11/1.93  BG Simplification    : 0.03
% 5.11/1.93  Subsumption          : 0.14
% 5.11/1.93  Abstraction          : 0.03
% 5.11/1.93  MUC search           : 0.00
% 5.11/1.93  Cooper               : 0.00
% 5.11/1.93  Total                : 1.16
% 5.11/1.93  Index Insertion      : 0.00
% 5.11/1.93  Index Deletion       : 0.00
% 5.11/1.93  Index Matching       : 0.00
% 5.11/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
