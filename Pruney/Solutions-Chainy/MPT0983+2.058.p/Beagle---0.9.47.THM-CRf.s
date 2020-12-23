%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:09 EST 2020

% Result     : Theorem 4.63s
% Output     : CNFRefutation 4.74s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 322 expanded)
%              Number of leaves         :   42 ( 130 expanded)
%              Depth                    :   11
%              Number of atoms          :  211 ( 906 expanded)
%              Number of equality atoms :   42 ( 104 expanded)
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

tff(f_151,negated_conjecture,(
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

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_92,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_39,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_90,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_70,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_131,axiom,(
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

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_37,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_109,axiom,(
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

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_223,plain,(
    ! [C_65,B_66,A_67] :
      ( v1_xboole_0(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(B_66,A_67)))
      | ~ v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_241,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_223])).

tff(c_245,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_241])).

tff(c_48,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_122,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_62,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_60,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_54,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_40,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_14,plain,(
    ! [A_4] : v2_funct_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_64,plain,(
    ! [A_4] : v2_funct_1(k6_partfun1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_14])).

tff(c_36,plain,(
    ! [A_25,F_30,E_29,C_27,D_28,B_26] :
      ( m1_subset_1(k1_partfun1(A_25,B_26,C_27,D_28,E_29,F_30),k1_zfmisc_1(k2_zfmisc_1(A_25,D_28)))
      | ~ m1_subset_1(F_30,k1_zfmisc_1(k2_zfmisc_1(C_27,D_28)))
      | ~ v1_funct_1(F_30)
      | ~ m1_subset_1(E_29,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_1(E_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_30,plain,(
    ! [A_22] : m1_subset_1(k6_relat_1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_63,plain,(
    ! [A_22] : m1_subset_1(k6_partfun1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_30])).

tff(c_50,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_431,plain,(
    ! [D_87,C_88,A_89,B_90] :
      ( D_87 = C_88
      | ~ r2_relset_1(A_89,B_90,C_88,D_87)
      | ~ m1_subset_1(D_87,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90)))
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_439,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_50,c_431])).

tff(c_454,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_439])).

tff(c_684,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_454])).

tff(c_863,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_684])).

tff(c_867,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_56,c_52,c_863])).

tff(c_868,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_454])).

tff(c_1023,plain,(
    ! [E_149,D_148,B_147,A_146,C_150] :
      ( k1_xboole_0 = C_150
      | v2_funct_1(D_148)
      | ~ v2_funct_1(k1_partfun1(A_146,B_147,B_147,C_150,D_148,E_149))
      | ~ m1_subset_1(E_149,k1_zfmisc_1(k2_zfmisc_1(B_147,C_150)))
      | ~ v1_funct_2(E_149,B_147,C_150)
      | ~ v1_funct_1(E_149)
      | ~ m1_subset_1(D_148,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147)))
      | ~ v1_funct_2(D_148,A_146,B_147)
      | ~ v1_funct_1(D_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1025,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_868,c_1023])).

tff(c_1027,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_54,c_52,c_64,c_1025])).

tff(c_1028,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_1027])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1063,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1028,c_2])).

tff(c_1065,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_245,c_1063])).

tff(c_1066,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_241])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_1071,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1066,c_4])).

tff(c_100,plain,(
    ! [A_48] : k6_relat_1(A_48) = k6_partfun1(A_48) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_12,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_106,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_12])).

tff(c_117,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_64])).

tff(c_1082,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1071,c_117])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1084,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_4',B_3) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1071,c_1071,c_10])).

tff(c_1067,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_241])).

tff(c_1075,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1067,c_4])).

tff(c_1095,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1071,c_1075])).

tff(c_1100,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1095,c_58])).

tff(c_1249,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1084,c_1100])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_238,plain,(
    ! [C_65] :
      ( v1_xboole_0(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_223])).

tff(c_243,plain,(
    ! [C_65] :
      ( v1_xboole_0(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_238])).

tff(c_1242,plain,(
    ! [C_65] :
      ( v1_xboole_0(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1071,c_243])).

tff(c_1256,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1249,c_1242])).

tff(c_1086,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1071,c_4])).

tff(c_1266,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1256,c_1086])).

tff(c_1273,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1266,c_122])).

tff(c_1281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1082,c_1273])).

tff(c_1282,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1301,plain,(
    ! [C_163,A_164,B_165] :
      ( v1_relat_1(C_163)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1317,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_1301])).

tff(c_1332,plain,(
    ! [C_169,B_170,A_171] :
      ( v5_relat_1(C_169,B_170)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_171,B_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1350,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_1332])).

tff(c_1434,plain,(
    ! [A_185,B_186,D_187] :
      ( r2_relset_1(A_185,B_186,D_187,D_187)
      | ~ m1_subset_1(D_187,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1445,plain,(
    ! [A_22] : r2_relset_1(A_22,A_22,k6_partfun1(A_22),k6_partfun1(A_22)) ),
    inference(resolution,[status(thm)],[c_63,c_1434])).

tff(c_1526,plain,(
    ! [A_192,B_193,C_194] :
      ( k2_relset_1(A_192,B_193,C_194) = k2_relat_1(C_194)
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(A_192,B_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1544,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_1526])).

tff(c_1584,plain,(
    ! [D_197,C_198,A_199,B_200] :
      ( D_197 = C_198
      | ~ r2_relset_1(A_199,B_200,C_198,D_197)
      | ~ m1_subset_1(D_197,k1_zfmisc_1(k2_zfmisc_1(A_199,B_200)))
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(A_199,B_200))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1592,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_50,c_1584])).

tff(c_1607,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_1592])).

tff(c_1619,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1607])).

tff(c_1898,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_1619])).

tff(c_1902,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_56,c_52,c_1898])).

tff(c_1903,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1607])).

tff(c_2425,plain,(
    ! [A_301,B_302,C_303,D_304] :
      ( k2_relset_1(A_301,B_302,C_303) = B_302
      | ~ r2_relset_1(B_302,B_302,k1_partfun1(B_302,A_301,A_301,B_302,D_304,C_303),k6_partfun1(B_302))
      | ~ m1_subset_1(D_304,k1_zfmisc_1(k2_zfmisc_1(B_302,A_301)))
      | ~ v1_funct_2(D_304,B_302,A_301)
      | ~ v1_funct_1(D_304)
      | ~ m1_subset_1(C_303,k1_zfmisc_1(k2_zfmisc_1(A_301,B_302)))
      | ~ v1_funct_2(C_303,A_301,B_302)
      | ~ v1_funct_1(C_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2428,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1903,c_2425])).

tff(c_2436,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_62,c_60,c_58,c_1445,c_1544,c_2428])).

tff(c_32,plain,(
    ! [B_24] :
      ( v2_funct_2(B_24,k2_relat_1(B_24))
      | ~ v5_relat_1(B_24,k2_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2442,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2436,c_32])).

tff(c_2446,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1317,c_1350,c_2436,c_2442])).

tff(c_2448,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1282,c_2446])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:37:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.63/1.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.83  
% 4.63/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.84  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.63/1.84  
% 4.63/1.84  %Foreground sorts:
% 4.63/1.84  
% 4.63/1.84  
% 4.63/1.84  %Background operators:
% 4.63/1.84  
% 4.63/1.84  
% 4.63/1.84  %Foreground operators:
% 4.63/1.84  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.63/1.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.63/1.84  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.63/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.63/1.84  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.63/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.63/1.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.63/1.84  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.63/1.84  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.63/1.84  tff('#skF_2', type, '#skF_2': $i).
% 4.63/1.84  tff('#skF_3', type, '#skF_3': $i).
% 4.63/1.84  tff('#skF_1', type, '#skF_1': $i).
% 4.63/1.84  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.63/1.84  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.63/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.63/1.84  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.63/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.63/1.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.63/1.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.63/1.84  tff('#skF_4', type, '#skF_4': $i).
% 4.63/1.84  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.63/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.63/1.84  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.63/1.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.63/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.63/1.84  
% 4.74/1.86  tff(f_151, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 4.74/1.86  tff(f_56, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 4.74/1.86  tff(f_92, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.74/1.86  tff(f_39, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 4.74/1.86  tff(f_90, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.74/1.86  tff(f_70, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 4.74/1.86  tff(f_68, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.74/1.86  tff(f_131, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 4.74/1.86  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.74/1.86  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.74/1.86  tff(f_37, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 4.74/1.86  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.74/1.86  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.74/1.86  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.74/1.86  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.74/1.86  tff(f_109, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 4.74/1.86  tff(f_78, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 4.74/1.86  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.74/1.86  tff(c_223, plain, (![C_65, B_66, A_67]: (v1_xboole_0(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(B_66, A_67))) | ~v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.74/1.86  tff(c_241, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_223])).
% 4.74/1.86  tff(c_245, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_241])).
% 4.74/1.86  tff(c_48, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.74/1.86  tff(c_122, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_48])).
% 4.74/1.86  tff(c_62, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.74/1.86  tff(c_60, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.74/1.86  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.74/1.86  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.74/1.86  tff(c_54, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.74/1.86  tff(c_40, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.74/1.86  tff(c_14, plain, (![A_4]: (v2_funct_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.74/1.86  tff(c_64, plain, (![A_4]: (v2_funct_1(k6_partfun1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_14])).
% 4.74/1.86  tff(c_36, plain, (![A_25, F_30, E_29, C_27, D_28, B_26]: (m1_subset_1(k1_partfun1(A_25, B_26, C_27, D_28, E_29, F_30), k1_zfmisc_1(k2_zfmisc_1(A_25, D_28))) | ~m1_subset_1(F_30, k1_zfmisc_1(k2_zfmisc_1(C_27, D_28))) | ~v1_funct_1(F_30) | ~m1_subset_1(E_29, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_1(E_29))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.74/1.86  tff(c_30, plain, (![A_22]: (m1_subset_1(k6_relat_1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.74/1.86  tff(c_63, plain, (![A_22]: (m1_subset_1(k6_partfun1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_30])).
% 4.74/1.86  tff(c_50, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.74/1.86  tff(c_431, plain, (![D_87, C_88, A_89, B_90]: (D_87=C_88 | ~r2_relset_1(A_89, B_90, C_88, D_87) | ~m1_subset_1(D_87, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.74/1.86  tff(c_439, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_50, c_431])).
% 4.74/1.86  tff(c_454, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_439])).
% 4.74/1.86  tff(c_684, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_454])).
% 4.74/1.86  tff(c_863, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_684])).
% 4.74/1.86  tff(c_867, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_56, c_52, c_863])).
% 4.74/1.86  tff(c_868, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_454])).
% 4.74/1.86  tff(c_1023, plain, (![E_149, D_148, B_147, A_146, C_150]: (k1_xboole_0=C_150 | v2_funct_1(D_148) | ~v2_funct_1(k1_partfun1(A_146, B_147, B_147, C_150, D_148, E_149)) | ~m1_subset_1(E_149, k1_zfmisc_1(k2_zfmisc_1(B_147, C_150))) | ~v1_funct_2(E_149, B_147, C_150) | ~v1_funct_1(E_149) | ~m1_subset_1(D_148, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))) | ~v1_funct_2(D_148, A_146, B_147) | ~v1_funct_1(D_148))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.74/1.86  tff(c_1025, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_868, c_1023])).
% 4.74/1.86  tff(c_1027, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_54, c_52, c_64, c_1025])).
% 4.74/1.86  tff(c_1028, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_122, c_1027])).
% 4.74/1.86  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.74/1.86  tff(c_1063, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1028, c_2])).
% 4.74/1.86  tff(c_1065, plain, $false, inference(negUnitSimplification, [status(thm)], [c_245, c_1063])).
% 4.74/1.86  tff(c_1066, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_241])).
% 4.74/1.86  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.74/1.86  tff(c_1071, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1066, c_4])).
% 4.74/1.86  tff(c_100, plain, (![A_48]: (k6_relat_1(A_48)=k6_partfun1(A_48))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.74/1.86  tff(c_12, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.74/1.86  tff(c_106, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_100, c_12])).
% 4.74/1.86  tff(c_117, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_106, c_64])).
% 4.74/1.86  tff(c_1082, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1071, c_117])).
% 4.74/1.86  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.74/1.86  tff(c_1084, plain, (![B_3]: (k2_zfmisc_1('#skF_4', B_3)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1071, c_1071, c_10])).
% 4.74/1.86  tff(c_1067, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_241])).
% 4.74/1.86  tff(c_1075, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_1067, c_4])).
% 4.74/1.86  tff(c_1095, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1071, c_1075])).
% 4.74/1.86  tff(c_1100, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1095, c_58])).
% 4.74/1.86  tff(c_1249, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1084, c_1100])).
% 4.74/1.86  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.74/1.86  tff(c_238, plain, (![C_65]: (v1_xboole_0(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_223])).
% 4.74/1.86  tff(c_243, plain, (![C_65]: (v1_xboole_0(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_238])).
% 4.74/1.86  tff(c_1242, plain, (![C_65]: (v1_xboole_0(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1071, c_243])).
% 4.74/1.86  tff(c_1256, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_1249, c_1242])).
% 4.74/1.86  tff(c_1086, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1071, c_4])).
% 4.74/1.86  tff(c_1266, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_1256, c_1086])).
% 4.74/1.86  tff(c_1273, plain, (~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1266, c_122])).
% 4.74/1.86  tff(c_1281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1082, c_1273])).
% 4.74/1.86  tff(c_1282, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 4.74/1.86  tff(c_1301, plain, (![C_163, A_164, B_165]: (v1_relat_1(C_163) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.74/1.86  tff(c_1317, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_1301])).
% 4.74/1.86  tff(c_1332, plain, (![C_169, B_170, A_171]: (v5_relat_1(C_169, B_170) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_171, B_170))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.74/1.86  tff(c_1350, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_52, c_1332])).
% 4.74/1.86  tff(c_1434, plain, (![A_185, B_186, D_187]: (r2_relset_1(A_185, B_186, D_187, D_187) | ~m1_subset_1(D_187, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.74/1.86  tff(c_1445, plain, (![A_22]: (r2_relset_1(A_22, A_22, k6_partfun1(A_22), k6_partfun1(A_22)))), inference(resolution, [status(thm)], [c_63, c_1434])).
% 4.74/1.86  tff(c_1526, plain, (![A_192, B_193, C_194]: (k2_relset_1(A_192, B_193, C_194)=k2_relat_1(C_194) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(A_192, B_193))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.74/1.86  tff(c_1544, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_1526])).
% 4.74/1.86  tff(c_1584, plain, (![D_197, C_198, A_199, B_200]: (D_197=C_198 | ~r2_relset_1(A_199, B_200, C_198, D_197) | ~m1_subset_1(D_197, k1_zfmisc_1(k2_zfmisc_1(A_199, B_200))) | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(A_199, B_200))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.74/1.86  tff(c_1592, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_50, c_1584])).
% 4.74/1.86  tff(c_1607, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_1592])).
% 4.74/1.86  tff(c_1619, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1607])).
% 4.74/1.86  tff(c_1898, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_1619])).
% 4.74/1.86  tff(c_1902, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_56, c_52, c_1898])).
% 4.74/1.86  tff(c_1903, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1607])).
% 4.74/1.86  tff(c_2425, plain, (![A_301, B_302, C_303, D_304]: (k2_relset_1(A_301, B_302, C_303)=B_302 | ~r2_relset_1(B_302, B_302, k1_partfun1(B_302, A_301, A_301, B_302, D_304, C_303), k6_partfun1(B_302)) | ~m1_subset_1(D_304, k1_zfmisc_1(k2_zfmisc_1(B_302, A_301))) | ~v1_funct_2(D_304, B_302, A_301) | ~v1_funct_1(D_304) | ~m1_subset_1(C_303, k1_zfmisc_1(k2_zfmisc_1(A_301, B_302))) | ~v1_funct_2(C_303, A_301, B_302) | ~v1_funct_1(C_303))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.74/1.86  tff(c_2428, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1903, c_2425])).
% 4.74/1.86  tff(c_2436, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_62, c_60, c_58, c_1445, c_1544, c_2428])).
% 4.74/1.86  tff(c_32, plain, (![B_24]: (v2_funct_2(B_24, k2_relat_1(B_24)) | ~v5_relat_1(B_24, k2_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.74/1.86  tff(c_2442, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2436, c_32])).
% 4.74/1.86  tff(c_2446, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1317, c_1350, c_2436, c_2442])).
% 4.74/1.86  tff(c_2448, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1282, c_2446])).
% 4.74/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.74/1.86  
% 4.74/1.86  Inference rules
% 4.74/1.86  ----------------------
% 4.74/1.86  #Ref     : 0
% 4.74/1.86  #Sup     : 537
% 4.74/1.86  #Fact    : 0
% 4.74/1.86  #Define  : 0
% 4.74/1.86  #Split   : 13
% 4.74/1.86  #Chain   : 0
% 4.74/1.86  #Close   : 0
% 4.74/1.86  
% 4.74/1.86  Ordering : KBO
% 4.74/1.86  
% 4.74/1.86  Simplification rules
% 4.74/1.86  ----------------------
% 4.74/1.86  #Subsume      : 39
% 4.74/1.86  #Demod        : 558
% 4.74/1.86  #Tautology    : 269
% 4.74/1.86  #SimpNegUnit  : 3
% 4.74/1.86  #BackRed      : 68
% 4.74/1.86  
% 4.74/1.86  #Partial instantiations: 0
% 4.74/1.86  #Strategies tried      : 1
% 4.74/1.86  
% 4.74/1.86  Timing (in seconds)
% 4.74/1.86  ----------------------
% 4.74/1.86  Preprocessing        : 0.37
% 4.74/1.86  Parsing              : 0.20
% 4.74/1.86  CNF conversion       : 0.03
% 4.74/1.86  Main loop            : 0.71
% 4.74/1.86  Inferencing          : 0.26
% 4.74/1.86  Reduction            : 0.25
% 4.74/1.86  Demodulation         : 0.18
% 4.74/1.86  BG Simplification    : 0.03
% 4.74/1.86  Subsumption          : 0.11
% 4.74/1.86  Abstraction          : 0.03
% 4.74/1.86  MUC search           : 0.00
% 4.74/1.86  Cooper               : 0.00
% 4.74/1.86  Total                : 1.13
% 4.74/1.86  Index Insertion      : 0.00
% 4.74/1.86  Index Deletion       : 0.00
% 4.74/1.86  Index Matching       : 0.00
% 4.74/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
