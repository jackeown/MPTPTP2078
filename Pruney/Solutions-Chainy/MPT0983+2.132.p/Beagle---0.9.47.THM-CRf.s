%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:20 EST 2020

% Result     : Theorem 4.55s
% Output     : CNFRefutation 4.55s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 543 expanded)
%              Number of leaves         :   43 ( 205 expanded)
%              Depth                    :   10
%              Number of atoms          :  230 (1546 expanded)
%              Number of equality atoms :   54 ( 200 expanded)
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

tff(f_160,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_101,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_59,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_99,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_79,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_140,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_57,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_56,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_118,axiom,(
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

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_50,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_123,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_62,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_56,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_42,plain,(
    ! [A_33] : k6_relat_1(A_33) = k6_partfun1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_20,plain,(
    ! [A_13] : v2_funct_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_66,plain,(
    ! [A_13] : v2_funct_1(k6_partfun1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_20])).

tff(c_38,plain,(
    ! [C_29,D_30,B_28,F_32,A_27,E_31] :
      ( m1_subset_1(k1_partfun1(A_27,B_28,C_29,D_30,E_31,F_32),k1_zfmisc_1(k2_zfmisc_1(A_27,D_30)))
      | ~ m1_subset_1(F_32,k1_zfmisc_1(k2_zfmisc_1(C_29,D_30)))
      | ~ v1_funct_1(F_32)
      | ~ m1_subset_1(E_31,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_funct_1(E_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_32,plain,(
    ! [A_24] : m1_subset_1(k6_relat_1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_65,plain,(
    ! [A_24] : m1_subset_1(k6_partfun1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_32])).

tff(c_52,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_371,plain,(
    ! [D_89,C_90,A_91,B_92] :
      ( D_89 = C_90
      | ~ r2_relset_1(A_91,B_92,C_90,D_89)
      | ~ m1_subset_1(D_89,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_377,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_52,c_371])).

tff(c_388,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_377])).

tff(c_726,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_388])).

tff(c_729,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_726])).

tff(c_733,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_58,c_54,c_729])).

tff(c_734,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_388])).

tff(c_755,plain,(
    ! [C_160,B_159,D_161,E_158,A_157] :
      ( k1_xboole_0 = C_160
      | v2_funct_1(D_161)
      | ~ v2_funct_1(k1_partfun1(A_157,B_159,B_159,C_160,D_161,E_158))
      | ~ m1_subset_1(E_158,k1_zfmisc_1(k2_zfmisc_1(B_159,C_160)))
      | ~ v1_funct_2(E_158,B_159,C_160)
      | ~ v1_funct_1(E_158)
      | ~ m1_subset_1(D_161,k1_zfmisc_1(k2_zfmisc_1(A_157,B_159)))
      | ~ v1_funct_2(D_161,A_157,B_159)
      | ~ v1_funct_1(D_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_757,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_734,c_755])).

tff(c_759,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_58,c_56,c_54,c_66,c_757])).

tff(c_760,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_759])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_790,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_760,c_2])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_788,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_760,c_760,c_8])).

tff(c_151,plain,(
    ! [B_56,A_57] :
      ( v1_xboole_0(B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57))
      | ~ v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_169,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_54,c_151])).

tff(c_172,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_883,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_788,c_172])).

tff(c_887,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_883])).

tff(c_888,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_125,plain,(
    ! [B_52,A_53] :
      ( ~ v1_xboole_0(B_52)
      | B_52 = A_53
      | ~ v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_128,plain,(
    ! [A_53] :
      ( k1_xboole_0 = A_53
      | ~ v1_xboole_0(A_53) ) ),
    inference(resolution,[status(thm)],[c_2,c_125])).

tff(c_895,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_888,c_128])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_902,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_895,c_895,c_10])).

tff(c_903,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_895,c_895,c_8])).

tff(c_889,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_938,plain,(
    ! [A_174] :
      ( A_174 = '#skF_4'
      | ~ v1_xboole_0(A_174) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_895,c_128])).

tff(c_945,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_889,c_938])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_911,plain,(
    ! [B_4,A_3] :
      ( B_4 = '#skF_4'
      | A_3 = '#skF_4'
      | k2_zfmisc_1(A_3,B_4) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_895,c_895,c_895,c_6])).

tff(c_1002,plain,
    ( '#skF_1' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_945,c_911])).

tff(c_1071,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1002])).

tff(c_168,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_151])).

tff(c_171,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_168])).

tff(c_1074,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1071,c_171])).

tff(c_1081,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_888,c_903,c_1074])).

tff(c_1082,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1002])).

tff(c_1087,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1082,c_171])).

tff(c_1095,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_888,c_902,c_1087])).

tff(c_1096,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_1103,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1096,c_128])).

tff(c_102,plain,(
    ! [A_51] : k6_relat_1(A_51) = k6_partfun1(A_51) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_18,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_108,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_18])).

tff(c_119,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_66])).

tff(c_1107,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1103,c_119])).

tff(c_1115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_1107])).

tff(c_1116,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_16,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1180,plain,(
    ! [B_191,A_192] :
      ( v1_relat_1(B_191)
      | ~ m1_subset_1(B_191,k1_zfmisc_1(A_192))
      | ~ v1_relat_1(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1192,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_54,c_1180])).

tff(c_1204,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1192])).

tff(c_1220,plain,(
    ! [C_196,B_197,A_198] :
      ( v5_relat_1(C_196,B_197)
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(A_198,B_197))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1238,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_1220])).

tff(c_1324,plain,(
    ! [A_215,B_216,D_217] :
      ( r2_relset_1(A_215,B_216,D_217,D_217)
      | ~ m1_subset_1(D_217,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1335,plain,(
    ! [A_24] : r2_relset_1(A_24,A_24,k6_partfun1(A_24),k6_partfun1(A_24)) ),
    inference(resolution,[status(thm)],[c_65,c_1324])).

tff(c_1353,plain,(
    ! [A_220,B_221,C_222] :
      ( k2_relset_1(A_220,B_221,C_222) = k2_relat_1(C_222)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(A_220,B_221))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1371,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_1353])).

tff(c_1381,plain,(
    ! [D_223,C_224,A_225,B_226] :
      ( D_223 = C_224
      | ~ r2_relset_1(A_225,B_226,C_224,D_223)
      | ~ m1_subset_1(D_223,k1_zfmisc_1(k2_zfmisc_1(A_225,B_226)))
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1(A_225,B_226))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1391,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_52,c_1381])).

tff(c_1410,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_1391])).

tff(c_1674,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1410])).

tff(c_1678,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_1674])).

tff(c_1682,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_58,c_54,c_1678])).

tff(c_1683,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1410])).

tff(c_1812,plain,(
    ! [A_329,B_330,C_331,D_332] :
      ( k2_relset_1(A_329,B_330,C_331) = B_330
      | ~ r2_relset_1(B_330,B_330,k1_partfun1(B_330,A_329,A_329,B_330,D_332,C_331),k6_partfun1(B_330))
      | ~ m1_subset_1(D_332,k1_zfmisc_1(k2_zfmisc_1(B_330,A_329)))
      | ~ v1_funct_2(D_332,B_330,A_329)
      | ~ v1_funct_1(D_332)
      | ~ m1_subset_1(C_331,k1_zfmisc_1(k2_zfmisc_1(A_329,B_330)))
      | ~ v1_funct_2(C_331,A_329,B_330)
      | ~ v1_funct_1(C_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1815,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1683,c_1812])).

tff(c_1820,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_64,c_62,c_60,c_1335,c_1371,c_1815])).

tff(c_34,plain,(
    ! [B_26] :
      ( v2_funct_2(B_26,k2_relat_1(B_26))
      | ~ v5_relat_1(B_26,k2_relat_1(B_26))
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1826,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1820,c_34])).

tff(c_1830,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1204,c_1238,c_1820,c_1826])).

tff(c_1832,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1116,c_1830])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n008.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 12:51:45 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.55/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/1.88  
% 4.55/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/1.89  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.55/1.89  
% 4.55/1.89  %Foreground sorts:
% 4.55/1.89  
% 4.55/1.89  
% 4.55/1.89  %Background operators:
% 4.55/1.89  
% 4.55/1.89  
% 4.55/1.89  %Foreground operators:
% 4.55/1.89  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.55/1.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.55/1.89  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.55/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.55/1.89  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.55/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.55/1.89  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.55/1.89  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.55/1.89  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.55/1.89  tff('#skF_2', type, '#skF_2': $i).
% 4.55/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.55/1.89  tff('#skF_1', type, '#skF_1': $i).
% 4.55/1.89  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.55/1.89  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.55/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.55/1.89  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.55/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.55/1.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.55/1.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.55/1.89  tff('#skF_4', type, '#skF_4': $i).
% 4.55/1.89  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.55/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.55/1.89  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.55/1.89  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.55/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.55/1.89  
% 4.55/1.91  tff(f_160, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 4.55/1.91  tff(f_101, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.55/1.91  tff(f_59, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 4.55/1.91  tff(f_99, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.55/1.91  tff(f_79, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 4.55/1.91  tff(f_77, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.55/1.91  tff(f_140, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 4.55/1.91  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.55/1.91  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.55/1.91  tff(f_47, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 4.55/1.91  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 4.55/1.91  tff(f_57, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 4.55/1.91  tff(f_56, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.55/1.91  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.55/1.91  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.55/1.91  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.55/1.91  tff(f_118, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 4.55/1.91  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 4.55/1.91  tff(c_50, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.55/1.91  tff(c_123, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_50])).
% 4.55/1.91  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.55/1.91  tff(c_62, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.55/1.91  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.55/1.91  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.55/1.91  tff(c_56, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.55/1.91  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.55/1.91  tff(c_42, plain, (![A_33]: (k6_relat_1(A_33)=k6_partfun1(A_33))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.55/1.91  tff(c_20, plain, (![A_13]: (v2_funct_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.55/1.91  tff(c_66, plain, (![A_13]: (v2_funct_1(k6_partfun1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_20])).
% 4.55/1.91  tff(c_38, plain, (![C_29, D_30, B_28, F_32, A_27, E_31]: (m1_subset_1(k1_partfun1(A_27, B_28, C_29, D_30, E_31, F_32), k1_zfmisc_1(k2_zfmisc_1(A_27, D_30))) | ~m1_subset_1(F_32, k1_zfmisc_1(k2_zfmisc_1(C_29, D_30))) | ~v1_funct_1(F_32) | ~m1_subset_1(E_31, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~v1_funct_1(E_31))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.55/1.91  tff(c_32, plain, (![A_24]: (m1_subset_1(k6_relat_1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.55/1.91  tff(c_65, plain, (![A_24]: (m1_subset_1(k6_partfun1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_32])).
% 4.55/1.91  tff(c_52, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.55/1.91  tff(c_371, plain, (![D_89, C_90, A_91, B_92]: (D_89=C_90 | ~r2_relset_1(A_91, B_92, C_90, D_89) | ~m1_subset_1(D_89, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.55/1.91  tff(c_377, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_52, c_371])).
% 4.55/1.91  tff(c_388, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_377])).
% 4.55/1.91  tff(c_726, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_388])).
% 4.55/1.91  tff(c_729, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_726])).
% 4.55/1.91  tff(c_733, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_58, c_54, c_729])).
% 4.55/1.91  tff(c_734, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_388])).
% 4.55/1.91  tff(c_755, plain, (![C_160, B_159, D_161, E_158, A_157]: (k1_xboole_0=C_160 | v2_funct_1(D_161) | ~v2_funct_1(k1_partfun1(A_157, B_159, B_159, C_160, D_161, E_158)) | ~m1_subset_1(E_158, k1_zfmisc_1(k2_zfmisc_1(B_159, C_160))) | ~v1_funct_2(E_158, B_159, C_160) | ~v1_funct_1(E_158) | ~m1_subset_1(D_161, k1_zfmisc_1(k2_zfmisc_1(A_157, B_159))) | ~v1_funct_2(D_161, A_157, B_159) | ~v1_funct_1(D_161))), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.55/1.91  tff(c_757, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_734, c_755])).
% 4.55/1.91  tff(c_759, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_56, c_54, c_66, c_757])).
% 4.55/1.91  tff(c_760, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_123, c_759])).
% 4.55/1.91  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.55/1.91  tff(c_790, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_760, c_2])).
% 4.55/1.91  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.55/1.91  tff(c_788, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_760, c_760, c_8])).
% 4.55/1.91  tff(c_151, plain, (![B_56, A_57]: (v1_xboole_0(B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)) | ~v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.55/1.91  tff(c_169, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_54, c_151])).
% 4.55/1.91  tff(c_172, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_169])).
% 4.55/1.91  tff(c_883, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_788, c_172])).
% 4.55/1.91  tff(c_887, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_790, c_883])).
% 4.55/1.91  tff(c_888, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_169])).
% 4.55/1.91  tff(c_125, plain, (![B_52, A_53]: (~v1_xboole_0(B_52) | B_52=A_53 | ~v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.55/1.91  tff(c_128, plain, (![A_53]: (k1_xboole_0=A_53 | ~v1_xboole_0(A_53))), inference(resolution, [status(thm)], [c_2, c_125])).
% 4.55/1.91  tff(c_895, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_888, c_128])).
% 4.55/1.91  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.55/1.91  tff(c_902, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_895, c_895, c_10])).
% 4.55/1.91  tff(c_903, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_895, c_895, c_8])).
% 4.55/1.91  tff(c_889, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_169])).
% 4.55/1.91  tff(c_938, plain, (![A_174]: (A_174='#skF_4' | ~v1_xboole_0(A_174))), inference(demodulation, [status(thm), theory('equality')], [c_895, c_128])).
% 4.55/1.91  tff(c_945, plain, (k2_zfmisc_1('#skF_2', '#skF_1')='#skF_4'), inference(resolution, [status(thm)], [c_889, c_938])).
% 4.55/1.91  tff(c_6, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.55/1.91  tff(c_911, plain, (![B_4, A_3]: (B_4='#skF_4' | A_3='#skF_4' | k2_zfmisc_1(A_3, B_4)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_895, c_895, c_895, c_6])).
% 4.55/1.91  tff(c_1002, plain, ('#skF_1'='#skF_4' | '#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_945, c_911])).
% 4.55/1.91  tff(c_1071, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_1002])).
% 4.55/1.91  tff(c_168, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_151])).
% 4.55/1.91  tff(c_171, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_168])).
% 4.55/1.91  tff(c_1074, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1071, c_171])).
% 4.55/1.91  tff(c_1081, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_888, c_903, c_1074])).
% 4.55/1.91  tff(c_1082, plain, ('#skF_1'='#skF_4'), inference(splitRight, [status(thm)], [c_1002])).
% 4.55/1.91  tff(c_1087, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1082, c_171])).
% 4.55/1.91  tff(c_1095, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_888, c_902, c_1087])).
% 4.55/1.91  tff(c_1096, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_168])).
% 4.55/1.91  tff(c_1103, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1096, c_128])).
% 4.55/1.91  tff(c_102, plain, (![A_51]: (k6_relat_1(A_51)=k6_partfun1(A_51))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.55/1.91  tff(c_18, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.55/1.91  tff(c_108, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_102, c_18])).
% 4.55/1.91  tff(c_119, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_108, c_66])).
% 4.55/1.91  tff(c_1107, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1103, c_119])).
% 4.55/1.91  tff(c_1115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_123, c_1107])).
% 4.55/1.91  tff(c_1116, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 4.55/1.91  tff(c_16, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.55/1.91  tff(c_1180, plain, (![B_191, A_192]: (v1_relat_1(B_191) | ~m1_subset_1(B_191, k1_zfmisc_1(A_192)) | ~v1_relat_1(A_192))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.55/1.91  tff(c_1192, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_54, c_1180])).
% 4.55/1.91  tff(c_1204, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1192])).
% 4.55/1.91  tff(c_1220, plain, (![C_196, B_197, A_198]: (v5_relat_1(C_196, B_197) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(A_198, B_197))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.55/1.91  tff(c_1238, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_54, c_1220])).
% 4.55/1.91  tff(c_1324, plain, (![A_215, B_216, D_217]: (r2_relset_1(A_215, B_216, D_217, D_217) | ~m1_subset_1(D_217, k1_zfmisc_1(k2_zfmisc_1(A_215, B_216))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.55/1.91  tff(c_1335, plain, (![A_24]: (r2_relset_1(A_24, A_24, k6_partfun1(A_24), k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_65, c_1324])).
% 4.55/1.91  tff(c_1353, plain, (![A_220, B_221, C_222]: (k2_relset_1(A_220, B_221, C_222)=k2_relat_1(C_222) | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(A_220, B_221))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.55/1.91  tff(c_1371, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_1353])).
% 4.55/1.91  tff(c_1381, plain, (![D_223, C_224, A_225, B_226]: (D_223=C_224 | ~r2_relset_1(A_225, B_226, C_224, D_223) | ~m1_subset_1(D_223, k1_zfmisc_1(k2_zfmisc_1(A_225, B_226))) | ~m1_subset_1(C_224, k1_zfmisc_1(k2_zfmisc_1(A_225, B_226))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.55/1.91  tff(c_1391, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_52, c_1381])).
% 4.55/1.91  tff(c_1410, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_1391])).
% 4.55/1.91  tff(c_1674, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1410])).
% 4.55/1.91  tff(c_1678, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_1674])).
% 4.55/1.91  tff(c_1682, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_58, c_54, c_1678])).
% 4.55/1.91  tff(c_1683, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1410])).
% 4.55/1.91  tff(c_1812, plain, (![A_329, B_330, C_331, D_332]: (k2_relset_1(A_329, B_330, C_331)=B_330 | ~r2_relset_1(B_330, B_330, k1_partfun1(B_330, A_329, A_329, B_330, D_332, C_331), k6_partfun1(B_330)) | ~m1_subset_1(D_332, k1_zfmisc_1(k2_zfmisc_1(B_330, A_329))) | ~v1_funct_2(D_332, B_330, A_329) | ~v1_funct_1(D_332) | ~m1_subset_1(C_331, k1_zfmisc_1(k2_zfmisc_1(A_329, B_330))) | ~v1_funct_2(C_331, A_329, B_330) | ~v1_funct_1(C_331))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.55/1.91  tff(c_1815, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1683, c_1812])).
% 4.55/1.91  tff(c_1820, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_64, c_62, c_60, c_1335, c_1371, c_1815])).
% 4.55/1.91  tff(c_34, plain, (![B_26]: (v2_funct_2(B_26, k2_relat_1(B_26)) | ~v5_relat_1(B_26, k2_relat_1(B_26)) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.55/1.91  tff(c_1826, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1820, c_34])).
% 4.55/1.91  tff(c_1830, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1204, c_1238, c_1820, c_1826])).
% 4.55/1.91  tff(c_1832, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1116, c_1830])).
% 4.55/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/1.91  
% 4.55/1.91  Inference rules
% 4.55/1.91  ----------------------
% 4.55/1.91  #Ref     : 0
% 4.55/1.91  #Sup     : 376
% 4.55/1.91  #Fact    : 0
% 4.55/1.91  #Define  : 0
% 4.55/1.91  #Split   : 14
% 4.55/1.91  #Chain   : 0
% 4.55/1.91  #Close   : 0
% 4.55/1.91  
% 4.55/1.91  Ordering : KBO
% 4.55/1.91  
% 4.55/1.91  Simplification rules
% 4.55/1.91  ----------------------
% 4.55/1.91  #Subsume      : 33
% 4.55/1.91  #Demod        : 449
% 4.55/1.91  #Tautology    : 158
% 4.55/1.91  #SimpNegUnit  : 5
% 4.55/1.91  #BackRed      : 107
% 4.55/1.91  
% 4.55/1.91  #Partial instantiations: 0
% 4.55/1.91  #Strategies tried      : 1
% 4.55/1.91  
% 4.55/1.91  Timing (in seconds)
% 4.55/1.91  ----------------------
% 4.55/1.91  Preprocessing        : 0.36
% 4.55/1.91  Parsing              : 0.20
% 4.55/1.91  CNF conversion       : 0.02
% 4.55/1.91  Main loop            : 0.70
% 4.55/1.92  Inferencing          : 0.24
% 4.55/1.92  Reduction            : 0.26
% 4.55/1.92  Demodulation         : 0.19
% 4.55/1.92  BG Simplification    : 0.03
% 4.55/1.92  Subsumption          : 0.11
% 4.55/1.92  Abstraction          : 0.03
% 4.55/1.92  MUC search           : 0.00
% 4.55/1.92  Cooper               : 0.00
% 4.55/1.92  Total                : 1.11
% 4.55/1.92  Index Insertion      : 0.00
% 4.55/1.92  Index Deletion       : 0.00
% 4.55/1.92  Index Matching       : 0.00
% 4.55/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
