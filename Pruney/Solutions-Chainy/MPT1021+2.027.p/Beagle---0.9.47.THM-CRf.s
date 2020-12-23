%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:03 EST 2020

% Result     : Theorem 11.87s
% Output     : CNFRefutation 12.13s
% Verified   : 
% Statistics : Number of formulae       :  185 (1944 expanded)
%              Number of leaves         :   48 ( 770 expanded)
%              Depth                    :   14
%              Number of atoms          :  379 (6694 expanded)
%              Number of equality atoms :   91 ( 757 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_184,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_161,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_85,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_123,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_159,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_139,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_149,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_115,axiom,(
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

tff(f_171,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_50,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_86,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_18692,plain,(
    ! [C_1004,A_1005,B_1006] :
      ( v1_relat_1(C_1004)
      | ~ m1_subset_1(C_1004,k1_zfmisc_1(k2_zfmisc_1(A_1005,B_1006))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_18713,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_86,c_18692])).

tff(c_92,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_88,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_19599,plain,(
    ! [C_1133,A_1134,B_1135] :
      ( v2_funct_1(C_1133)
      | ~ v3_funct_2(C_1133,A_1134,B_1135)
      | ~ v1_funct_1(C_1133)
      | ~ m1_subset_1(C_1133,k1_zfmisc_1(k2_zfmisc_1(A_1134,B_1135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_19615,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_86,c_19599])).

tff(c_19634,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_19615])).

tff(c_76,plain,(
    ! [A_43] : k6_relat_1(A_43) = k6_partfun1(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_40,plain,(
    ! [A_24] : m1_subset_1(k6_relat_1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_93,plain,(
    ! [A_24] : m1_subset_1(k6_partfun1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_40])).

tff(c_18912,plain,(
    ! [A_1042,B_1043,D_1044] :
      ( r2_relset_1(A_1042,B_1043,D_1044,D_1044)
      | ~ m1_subset_1(D_1044,k1_zfmisc_1(k2_zfmisc_1(A_1042,B_1043))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_18927,plain,(
    ! [A_24] : r2_relset_1(A_24,A_24,k6_partfun1(A_24),k6_partfun1(A_24)) ),
    inference(resolution,[status(thm)],[c_93,c_18912])).

tff(c_18801,plain,(
    ! [C_1020,B_1021,A_1022] :
      ( v5_relat_1(C_1020,B_1021)
      | ~ m1_subset_1(C_1020,k1_zfmisc_1(k2_zfmisc_1(A_1022,B_1021))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_18824,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_86,c_18801])).

tff(c_19003,plain,(
    ! [B_1061,A_1062] :
      ( k2_relat_1(B_1061) = A_1062
      | ~ v2_funct_2(B_1061,A_1062)
      | ~ v5_relat_1(B_1061,A_1062)
      | ~ v1_relat_1(B_1061) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_19015,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18824,c_19003])).

tff(c_19025,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18713,c_19015])).

tff(c_19032,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_19025])).

tff(c_19267,plain,(
    ! [C_1097,B_1098,A_1099] :
      ( v2_funct_2(C_1097,B_1098)
      | ~ v3_funct_2(C_1097,A_1099,B_1098)
      | ~ v1_funct_1(C_1097)
      | ~ m1_subset_1(C_1097,k1_zfmisc_1(k2_zfmisc_1(A_1099,B_1098))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_19280,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_86,c_19267])).

tff(c_19296,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_19280])).

tff(c_19298,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19032,c_19296])).

tff(c_19299,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_19025])).

tff(c_24,plain,(
    ! [A_10] :
      ( k5_relat_1(k2_funct_1(A_10),A_10) = k6_relat_1(k2_relat_1(A_10))
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_95,plain,(
    ! [A_10] :
      ( k5_relat_1(k2_funct_1(A_10),A_10) = k6_partfun1(k2_relat_1(A_10))
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_24])).

tff(c_90,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_20357,plain,(
    ! [A_1209,B_1210] :
      ( k2_funct_2(A_1209,B_1210) = k2_funct_1(B_1210)
      | ~ m1_subset_1(B_1210,k1_zfmisc_1(k2_zfmisc_1(A_1209,A_1209)))
      | ~ v3_funct_2(B_1210,A_1209,A_1209)
      | ~ v1_funct_2(B_1210,A_1209,A_1209)
      | ~ v1_funct_1(B_1210) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_20367,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_86,c_20357])).

tff(c_20384,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_20367])).

tff(c_20265,plain,(
    ! [A_1202,B_1203] :
      ( v1_funct_1(k2_funct_2(A_1202,B_1203))
      | ~ m1_subset_1(B_1203,k1_zfmisc_1(k2_zfmisc_1(A_1202,A_1202)))
      | ~ v3_funct_2(B_1203,A_1202,A_1202)
      | ~ v1_funct_2(B_1203,A_1202,A_1202)
      | ~ v1_funct_1(B_1203) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_20275,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_86,c_20265])).

tff(c_20292,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_20275])).

tff(c_20386,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20384,c_20292])).

tff(c_64,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(k2_funct_2(A_33,B_34),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33)))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(k2_zfmisc_1(A_33,A_33)))
      | ~ v3_funct_2(B_34,A_33,A_33)
      | ~ v1_funct_2(B_34,A_33,A_33)
      | ~ v1_funct_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_20656,plain,(
    ! [A_1224,B_1229,C_1226,D_1228,E_1227,F_1225] :
      ( k1_partfun1(A_1224,B_1229,C_1226,D_1228,E_1227,F_1225) = k5_relat_1(E_1227,F_1225)
      | ~ m1_subset_1(F_1225,k1_zfmisc_1(k2_zfmisc_1(C_1226,D_1228)))
      | ~ v1_funct_1(F_1225)
      | ~ m1_subset_1(E_1227,k1_zfmisc_1(k2_zfmisc_1(A_1224,B_1229)))
      | ~ v1_funct_1(E_1227) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_20669,plain,(
    ! [A_1224,B_1229,E_1227] :
      ( k1_partfun1(A_1224,B_1229,'#skF_1','#skF_1',E_1227,'#skF_2') = k5_relat_1(E_1227,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_1227,k1_zfmisc_1(k2_zfmisc_1(A_1224,B_1229)))
      | ~ v1_funct_1(E_1227) ) ),
    inference(resolution,[status(thm)],[c_86,c_20656])).

tff(c_20745,plain,(
    ! [A_1230,B_1231,E_1232] :
      ( k1_partfun1(A_1230,B_1231,'#skF_1','#skF_1',E_1232,'#skF_2') = k5_relat_1(E_1232,'#skF_2')
      | ~ m1_subset_1(E_1232,k1_zfmisc_1(k2_zfmisc_1(A_1230,B_1231)))
      | ~ v1_funct_1(E_1232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_20669])).

tff(c_21591,plain,(
    ! [A_1249,B_1250] :
      ( k1_partfun1(A_1249,A_1249,'#skF_1','#skF_1',k2_funct_2(A_1249,B_1250),'#skF_2') = k5_relat_1(k2_funct_2(A_1249,B_1250),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_1249,B_1250))
      | ~ m1_subset_1(B_1250,k1_zfmisc_1(k2_zfmisc_1(A_1249,A_1249)))
      | ~ v3_funct_2(B_1250,A_1249,A_1249)
      | ~ v1_funct_2(B_1250,A_1249,A_1249)
      | ~ v1_funct_1(B_1250) ) ),
    inference(resolution,[status(thm)],[c_64,c_20745])).

tff(c_21606,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_86,c_21591])).

tff(c_21630,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_20386,c_20384,c_20384,c_20384,c_21606])).

tff(c_214,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_235,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_86,c_214])).

tff(c_6906,plain,(
    ! [C_481,A_482,B_483] :
      ( v2_funct_1(C_481)
      | ~ v3_funct_2(C_481,A_482,B_483)
      | ~ v1_funct_1(C_481)
      | ~ m1_subset_1(C_481,k1_zfmisc_1(k2_zfmisc_1(A_482,B_483))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6922,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_86,c_6906])).

tff(c_6941,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_6922])).

tff(c_6279,plain,(
    ! [A_400,B_401,D_402] :
      ( r2_relset_1(A_400,B_401,D_402,D_402)
      | ~ m1_subset_1(D_402,k1_zfmisc_1(k2_zfmisc_1(A_400,B_401))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6294,plain,(
    ! [A_24] : r2_relset_1(A_24,A_24,k6_partfun1(A_24),k6_partfun1(A_24)) ),
    inference(resolution,[status(thm)],[c_93,c_6279])).

tff(c_6641,plain,(
    ! [A_450,B_451,C_452] :
      ( k1_relset_1(A_450,B_451,C_452) = k1_relat_1(C_452)
      | ~ m1_subset_1(C_452,k1_zfmisc_1(k2_zfmisc_1(A_450,B_451))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6664,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_86,c_6641])).

tff(c_12951,plain,(
    ! [B_762,A_763,C_764] :
      ( k1_xboole_0 = B_762
      | k1_relset_1(A_763,B_762,C_764) = A_763
      | ~ v1_funct_2(C_764,A_763,B_762)
      | ~ m1_subset_1(C_764,k1_zfmisc_1(k2_zfmisc_1(A_763,B_762))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_12967,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_86,c_12951])).

tff(c_12987,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_6664,c_12967])).

tff(c_12991,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_12987])).

tff(c_26,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k2_funct_1(A_10)) = k6_relat_1(k1_relat_1(A_10))
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_94,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k2_funct_1(A_10)) = k6_partfun1(k1_relat_1(A_10))
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_26])).

tff(c_13431,plain,(
    ! [A_808,B_809] :
      ( k2_funct_2(A_808,B_809) = k2_funct_1(B_809)
      | ~ m1_subset_1(B_809,k1_zfmisc_1(k2_zfmisc_1(A_808,A_808)))
      | ~ v3_funct_2(B_809,A_808,A_808)
      | ~ v1_funct_2(B_809,A_808,A_808)
      | ~ v1_funct_1(B_809) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_13441,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_86,c_13431])).

tff(c_13458,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_13441])).

tff(c_13638,plain,(
    ! [A_827,B_828] :
      ( m1_subset_1(k2_funct_2(A_827,B_828),k1_zfmisc_1(k2_zfmisc_1(A_827,A_827)))
      | ~ m1_subset_1(B_828,k1_zfmisc_1(k2_zfmisc_1(A_827,A_827)))
      | ~ v3_funct_2(B_828,A_827,A_827)
      | ~ v1_funct_2(B_828,A_827,A_827)
      | ~ v1_funct_1(B_828) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_13682,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_13458,c_13638])).

tff(c_13707,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_86,c_13682])).

tff(c_28,plain,(
    ! [C_13,A_11,B_12] :
      ( v1_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_13779,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_13707,c_28])).

tff(c_13398,plain,(
    ! [A_802,B_803] :
      ( v1_funct_1(k2_funct_2(A_802,B_803))
      | ~ m1_subset_1(B_803,k1_zfmisc_1(k2_zfmisc_1(A_802,A_802)))
      | ~ v3_funct_2(B_803,A_802,A_802)
      | ~ v1_funct_2(B_803,A_802,A_802)
      | ~ v1_funct_1(B_803) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_13408,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_86,c_13398])).

tff(c_13425,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_13408])).

tff(c_13462,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13458,c_13425])).

tff(c_13544,plain,(
    ! [A_819,B_820] :
      ( v3_funct_2(k2_funct_2(A_819,B_820),A_819,A_819)
      | ~ m1_subset_1(B_820,k1_zfmisc_1(k2_zfmisc_1(A_819,A_819)))
      | ~ v3_funct_2(B_820,A_819,A_819)
      | ~ v1_funct_2(B_820,A_819,A_819)
      | ~ v1_funct_1(B_820) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_13551,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_86,c_13544])).

tff(c_13565,plain,(
    v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_13458,c_13551])).

tff(c_42,plain,(
    ! [C_27,B_26,A_25] :
      ( v2_funct_2(C_27,B_26)
      | ~ v3_funct_2(C_27,A_25,B_26)
      | ~ v1_funct_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_13728,plain,
    ( v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_13707,c_42])).

tff(c_13770,plain,(
    v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13462,c_13565,c_13728])).

tff(c_30,plain,(
    ! [C_16,B_15,A_14] :
      ( v5_relat_1(C_16,B_15)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_13777,plain,(
    v5_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_13707,c_30])).

tff(c_62,plain,(
    ! [B_32,A_31] :
      ( k2_relat_1(B_32) = A_31
      | ~ v2_funct_2(B_32,A_31)
      | ~ v5_relat_1(B_32,A_31)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_13783,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_13777,c_62])).

tff(c_13786,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13779,c_13783])).

tff(c_14018,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13770,c_13786])).

tff(c_34,plain,(
    ! [A_17,B_18,C_19] :
      ( k1_relset_1(A_17,B_18,C_19) = k1_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_13774,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_2')) = k1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_13707,c_34])).

tff(c_13470,plain,(
    ! [A_812,B_813] :
      ( v1_funct_2(k2_funct_2(A_812,B_813),A_812,A_812)
      | ~ m1_subset_1(B_813,k1_zfmisc_1(k2_zfmisc_1(A_812,A_812)))
      | ~ v3_funct_2(B_813,A_812,A_812)
      | ~ v1_funct_2(B_813,A_812,A_812)
      | ~ v1_funct_1(B_813) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_13477,plain,
    ( v1_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_86,c_13470])).

tff(c_13491,plain,(
    v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_13458,c_13477])).

tff(c_58,plain,(
    ! [B_29,A_28,C_30] :
      ( k1_xboole_0 = B_29
      | k1_relset_1(A_28,B_29,C_30) = A_28
      | ~ v1_funct_2(C_30,A_28,B_29)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_13725,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_13707,c_58])).

tff(c_13767,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13491,c_13725])).

tff(c_13927,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13774,c_13767])).

tff(c_13928,plain,(
    k1_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_13927])).

tff(c_78,plain,(
    ! [A_44] :
      ( m1_subset_1(A_44,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_44),k2_relat_1(A_44))))
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_13833,plain,(
    ! [F_830,E_832,C_831,B_834,D_833,A_829] :
      ( k1_partfun1(A_829,B_834,C_831,D_833,E_832,F_830) = k5_relat_1(E_832,F_830)
      | ~ m1_subset_1(F_830,k1_zfmisc_1(k2_zfmisc_1(C_831,D_833)))
      | ~ v1_funct_1(F_830)
      | ~ m1_subset_1(E_832,k1_zfmisc_1(k2_zfmisc_1(A_829,B_834)))
      | ~ v1_funct_1(E_832) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_17227,plain,(
    ! [A_958,B_959,A_960,E_961] :
      ( k1_partfun1(A_958,B_959,k1_relat_1(A_960),k2_relat_1(A_960),E_961,A_960) = k5_relat_1(E_961,A_960)
      | ~ m1_subset_1(E_961,k1_zfmisc_1(k2_zfmisc_1(A_958,B_959)))
      | ~ v1_funct_1(E_961)
      | ~ v1_funct_1(A_960)
      | ~ v1_relat_1(A_960) ) ),
    inference(resolution,[status(thm)],[c_78,c_13833])).

tff(c_17252,plain,(
    ! [A_960] :
      ( k1_partfun1('#skF_1','#skF_1',k1_relat_1(A_960),k2_relat_1(A_960),'#skF_2',A_960) = k5_relat_1('#skF_2',A_960)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_funct_1(A_960)
      | ~ v1_relat_1(A_960) ) ),
    inference(resolution,[status(thm)],[c_86,c_17227])).

tff(c_17291,plain,(
    ! [A_962] :
      ( k1_partfun1('#skF_1','#skF_1',k1_relat_1(A_962),k2_relat_1(A_962),'#skF_2',A_962) = k5_relat_1('#skF_2',A_962)
      | ~ v1_funct_1(A_962)
      | ~ v1_relat_1(A_962) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_17252])).

tff(c_17335,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1',k2_relat_1(k2_funct_1('#skF_2')),'#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13928,c_17291])).

tff(c_17375,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13779,c_13462,c_14018,c_17335])).

tff(c_84,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_198,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_13463,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13458,c_198])).

tff(c_17384,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17375,c_13463])).

tff(c_17391,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_17384])).

tff(c_17394,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_92,c_6941,c_6294,c_12991,c_17391])).

tff(c_17395,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_13927])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_17460,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17395,c_17395,c_20])).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_17455,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_1',B_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17395,c_17395,c_8])).

tff(c_174,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,B_55)
      | ~ m1_subset_1(A_54,k1_zfmisc_1(B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_189,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_86,c_174])).

tff(c_17754,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17455,c_189])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18081,plain,(
    ! [A_981] :
      ( A_981 = '#skF_1'
      | ~ r1_tarski(A_981,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17395,c_17395,c_2])).

tff(c_18093,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_17754,c_18081])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_13780,plain,(
    r1_tarski(k2_funct_1('#skF_2'),k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_13707,c_12])).

tff(c_17751,plain,(
    r1_tarski(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17455,c_13780])).

tff(c_18092,plain,(
    k2_funct_1('#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_17751,c_18081])).

tff(c_18149,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18093,c_18092])).

tff(c_17396,plain,(
    k1_relat_1(k2_funct_1('#skF_2')) != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_13927])).

tff(c_18101,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18093,c_17396])).

tff(c_18186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17460,c_18149,c_18101])).

tff(c_18187,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_12987])).

tff(c_18229,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18187,c_18187,c_20])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18225,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18187,c_18187,c_6])).

tff(c_18413,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18225,c_189])).

tff(c_18639,plain,(
    ! [A_1002] :
      ( A_1002 = '#skF_1'
      | ~ r1_tarski(A_1002,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18187,c_18187,c_2])).

tff(c_18647,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_18413,c_18639])).

tff(c_18188,plain,(
    k1_relat_1('#skF_2') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_12987])).

tff(c_18654,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18647,c_18188])).

tff(c_18674,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18229,c_18654])).

tff(c_18675,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_20389,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20384,c_18675])).

tff(c_21715,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21630,c_20389])).

tff(c_21722,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_21715])).

tff(c_21725,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18713,c_92,c_19634,c_18927,c_19299,c_21722])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:53:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.87/4.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.06/4.79  
% 12.06/4.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.06/4.79  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 12.06/4.79  
% 12.06/4.79  %Foreground sorts:
% 12.06/4.79  
% 12.06/4.79  
% 12.06/4.79  %Background operators:
% 12.06/4.79  
% 12.06/4.79  
% 12.06/4.79  %Foreground operators:
% 12.06/4.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.06/4.79  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 12.06/4.79  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 12.06/4.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.06/4.79  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 12.06/4.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.06/4.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.06/4.79  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 12.06/4.79  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 12.06/4.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.06/4.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.06/4.79  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.06/4.79  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.06/4.79  tff('#skF_2', type, '#skF_2': $i).
% 12.06/4.79  tff('#skF_1', type, '#skF_1': $i).
% 12.06/4.79  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 12.06/4.79  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 12.06/4.79  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 12.06/4.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.06/4.79  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 12.06/4.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.06/4.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.06/4.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.06/4.79  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 12.06/4.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.06/4.79  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 12.06/4.79  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 12.06/4.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.06/4.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.06/4.79  
% 12.13/4.82  tff(f_184, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 12.13/4.82  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 12.13/4.82  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 12.13/4.82  tff(f_161, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 12.13/4.82  tff(f_85, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 12.13/4.82  tff(f_83, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 12.13/4.82  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 12.13/4.82  tff(f_123, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 12.13/4.82  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 12.13/4.82  tff(f_159, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 12.13/4.82  tff(f_139, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 12.13/4.82  tff(f_149, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 12.13/4.82  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 12.13/4.82  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 12.13/4.82  tff(f_171, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 12.13/4.82  tff(f_50, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 12.13/4.82  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 12.13/4.82  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 12.13/4.82  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 12.13/4.82  tff(c_86, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_184])).
% 12.13/4.82  tff(c_18692, plain, (![C_1004, A_1005, B_1006]: (v1_relat_1(C_1004) | ~m1_subset_1(C_1004, k1_zfmisc_1(k2_zfmisc_1(A_1005, B_1006))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.13/4.82  tff(c_18713, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_86, c_18692])).
% 12.13/4.82  tff(c_92, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_184])).
% 12.13/4.82  tff(c_88, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_184])).
% 12.13/4.82  tff(c_19599, plain, (![C_1133, A_1134, B_1135]: (v2_funct_1(C_1133) | ~v3_funct_2(C_1133, A_1134, B_1135) | ~v1_funct_1(C_1133) | ~m1_subset_1(C_1133, k1_zfmisc_1(k2_zfmisc_1(A_1134, B_1135))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.13/4.82  tff(c_19615, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_86, c_19599])).
% 12.13/4.82  tff(c_19634, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_19615])).
% 12.13/4.82  tff(c_76, plain, (![A_43]: (k6_relat_1(A_43)=k6_partfun1(A_43))), inference(cnfTransformation, [status(thm)], [f_161])).
% 12.13/4.82  tff(c_40, plain, (![A_24]: (m1_subset_1(k6_relat_1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.13/4.82  tff(c_93, plain, (![A_24]: (m1_subset_1(k6_partfun1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_40])).
% 12.13/4.82  tff(c_18912, plain, (![A_1042, B_1043, D_1044]: (r2_relset_1(A_1042, B_1043, D_1044, D_1044) | ~m1_subset_1(D_1044, k1_zfmisc_1(k2_zfmisc_1(A_1042, B_1043))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 12.13/4.82  tff(c_18927, plain, (![A_24]: (r2_relset_1(A_24, A_24, k6_partfun1(A_24), k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_93, c_18912])).
% 12.13/4.82  tff(c_18801, plain, (![C_1020, B_1021, A_1022]: (v5_relat_1(C_1020, B_1021) | ~m1_subset_1(C_1020, k1_zfmisc_1(k2_zfmisc_1(A_1022, B_1021))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.13/4.82  tff(c_18824, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_86, c_18801])).
% 12.13/4.82  tff(c_19003, plain, (![B_1061, A_1062]: (k2_relat_1(B_1061)=A_1062 | ~v2_funct_2(B_1061, A_1062) | ~v5_relat_1(B_1061, A_1062) | ~v1_relat_1(B_1061))), inference(cnfTransformation, [status(thm)], [f_123])).
% 12.13/4.82  tff(c_19015, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_18824, c_19003])).
% 12.13/4.82  tff(c_19025, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18713, c_19015])).
% 12.13/4.82  tff(c_19032, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_19025])).
% 12.13/4.82  tff(c_19267, plain, (![C_1097, B_1098, A_1099]: (v2_funct_2(C_1097, B_1098) | ~v3_funct_2(C_1097, A_1099, B_1098) | ~v1_funct_1(C_1097) | ~m1_subset_1(C_1097, k1_zfmisc_1(k2_zfmisc_1(A_1099, B_1098))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.13/4.82  tff(c_19280, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_86, c_19267])).
% 12.13/4.82  tff(c_19296, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_19280])).
% 12.13/4.82  tff(c_19298, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19032, c_19296])).
% 12.13/4.82  tff(c_19299, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_19025])).
% 12.13/4.82  tff(c_24, plain, (![A_10]: (k5_relat_1(k2_funct_1(A_10), A_10)=k6_relat_1(k2_relat_1(A_10)) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_61])).
% 12.13/4.82  tff(c_95, plain, (![A_10]: (k5_relat_1(k2_funct_1(A_10), A_10)=k6_partfun1(k2_relat_1(A_10)) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_24])).
% 12.13/4.82  tff(c_90, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_184])).
% 12.13/4.82  tff(c_20357, plain, (![A_1209, B_1210]: (k2_funct_2(A_1209, B_1210)=k2_funct_1(B_1210) | ~m1_subset_1(B_1210, k1_zfmisc_1(k2_zfmisc_1(A_1209, A_1209))) | ~v3_funct_2(B_1210, A_1209, A_1209) | ~v1_funct_2(B_1210, A_1209, A_1209) | ~v1_funct_1(B_1210))), inference(cnfTransformation, [status(thm)], [f_159])).
% 12.13/4.82  tff(c_20367, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_86, c_20357])).
% 12.13/4.82  tff(c_20384, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_20367])).
% 12.13/4.82  tff(c_20265, plain, (![A_1202, B_1203]: (v1_funct_1(k2_funct_2(A_1202, B_1203)) | ~m1_subset_1(B_1203, k1_zfmisc_1(k2_zfmisc_1(A_1202, A_1202))) | ~v3_funct_2(B_1203, A_1202, A_1202) | ~v1_funct_2(B_1203, A_1202, A_1202) | ~v1_funct_1(B_1203))), inference(cnfTransformation, [status(thm)], [f_139])).
% 12.13/4.82  tff(c_20275, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_86, c_20265])).
% 12.13/4.82  tff(c_20292, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_20275])).
% 12.13/4.82  tff(c_20386, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20384, c_20292])).
% 12.13/4.82  tff(c_64, plain, (![A_33, B_34]: (m1_subset_1(k2_funct_2(A_33, B_34), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))) | ~m1_subset_1(B_34, k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))) | ~v3_funct_2(B_34, A_33, A_33) | ~v1_funct_2(B_34, A_33, A_33) | ~v1_funct_1(B_34))), inference(cnfTransformation, [status(thm)], [f_139])).
% 12.13/4.82  tff(c_20656, plain, (![A_1224, B_1229, C_1226, D_1228, E_1227, F_1225]: (k1_partfun1(A_1224, B_1229, C_1226, D_1228, E_1227, F_1225)=k5_relat_1(E_1227, F_1225) | ~m1_subset_1(F_1225, k1_zfmisc_1(k2_zfmisc_1(C_1226, D_1228))) | ~v1_funct_1(F_1225) | ~m1_subset_1(E_1227, k1_zfmisc_1(k2_zfmisc_1(A_1224, B_1229))) | ~v1_funct_1(E_1227))), inference(cnfTransformation, [status(thm)], [f_149])).
% 12.13/4.82  tff(c_20669, plain, (![A_1224, B_1229, E_1227]: (k1_partfun1(A_1224, B_1229, '#skF_1', '#skF_1', E_1227, '#skF_2')=k5_relat_1(E_1227, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_1227, k1_zfmisc_1(k2_zfmisc_1(A_1224, B_1229))) | ~v1_funct_1(E_1227))), inference(resolution, [status(thm)], [c_86, c_20656])).
% 12.13/4.82  tff(c_20745, plain, (![A_1230, B_1231, E_1232]: (k1_partfun1(A_1230, B_1231, '#skF_1', '#skF_1', E_1232, '#skF_2')=k5_relat_1(E_1232, '#skF_2') | ~m1_subset_1(E_1232, k1_zfmisc_1(k2_zfmisc_1(A_1230, B_1231))) | ~v1_funct_1(E_1232))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_20669])).
% 12.13/4.82  tff(c_21591, plain, (![A_1249, B_1250]: (k1_partfun1(A_1249, A_1249, '#skF_1', '#skF_1', k2_funct_2(A_1249, B_1250), '#skF_2')=k5_relat_1(k2_funct_2(A_1249, B_1250), '#skF_2') | ~v1_funct_1(k2_funct_2(A_1249, B_1250)) | ~m1_subset_1(B_1250, k1_zfmisc_1(k2_zfmisc_1(A_1249, A_1249))) | ~v3_funct_2(B_1250, A_1249, A_1249) | ~v1_funct_2(B_1250, A_1249, A_1249) | ~v1_funct_1(B_1250))), inference(resolution, [status(thm)], [c_64, c_20745])).
% 12.13/4.82  tff(c_21606, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_86, c_21591])).
% 12.13/4.82  tff(c_21630, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_20386, c_20384, c_20384, c_20384, c_21606])).
% 12.13/4.82  tff(c_214, plain, (![C_58, A_59, B_60]: (v1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.13/4.82  tff(c_235, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_86, c_214])).
% 12.13/4.82  tff(c_6906, plain, (![C_481, A_482, B_483]: (v2_funct_1(C_481) | ~v3_funct_2(C_481, A_482, B_483) | ~v1_funct_1(C_481) | ~m1_subset_1(C_481, k1_zfmisc_1(k2_zfmisc_1(A_482, B_483))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.13/4.82  tff(c_6922, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_86, c_6906])).
% 12.13/4.82  tff(c_6941, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_6922])).
% 12.13/4.82  tff(c_6279, plain, (![A_400, B_401, D_402]: (r2_relset_1(A_400, B_401, D_402, D_402) | ~m1_subset_1(D_402, k1_zfmisc_1(k2_zfmisc_1(A_400, B_401))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 12.13/4.82  tff(c_6294, plain, (![A_24]: (r2_relset_1(A_24, A_24, k6_partfun1(A_24), k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_93, c_6279])).
% 12.13/4.82  tff(c_6641, plain, (![A_450, B_451, C_452]: (k1_relset_1(A_450, B_451, C_452)=k1_relat_1(C_452) | ~m1_subset_1(C_452, k1_zfmisc_1(k2_zfmisc_1(A_450, B_451))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.13/4.82  tff(c_6664, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_86, c_6641])).
% 12.13/4.82  tff(c_12951, plain, (![B_762, A_763, C_764]: (k1_xboole_0=B_762 | k1_relset_1(A_763, B_762, C_764)=A_763 | ~v1_funct_2(C_764, A_763, B_762) | ~m1_subset_1(C_764, k1_zfmisc_1(k2_zfmisc_1(A_763, B_762))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 12.13/4.82  tff(c_12967, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_86, c_12951])).
% 12.13/4.82  tff(c_12987, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_6664, c_12967])).
% 12.13/4.82  tff(c_12991, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_12987])).
% 12.13/4.82  tff(c_26, plain, (![A_10]: (k5_relat_1(A_10, k2_funct_1(A_10))=k6_relat_1(k1_relat_1(A_10)) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_61])).
% 12.13/4.82  tff(c_94, plain, (![A_10]: (k5_relat_1(A_10, k2_funct_1(A_10))=k6_partfun1(k1_relat_1(A_10)) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_26])).
% 12.13/4.82  tff(c_13431, plain, (![A_808, B_809]: (k2_funct_2(A_808, B_809)=k2_funct_1(B_809) | ~m1_subset_1(B_809, k1_zfmisc_1(k2_zfmisc_1(A_808, A_808))) | ~v3_funct_2(B_809, A_808, A_808) | ~v1_funct_2(B_809, A_808, A_808) | ~v1_funct_1(B_809))), inference(cnfTransformation, [status(thm)], [f_159])).
% 12.13/4.82  tff(c_13441, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_86, c_13431])).
% 12.13/4.82  tff(c_13458, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_13441])).
% 12.13/4.82  tff(c_13638, plain, (![A_827, B_828]: (m1_subset_1(k2_funct_2(A_827, B_828), k1_zfmisc_1(k2_zfmisc_1(A_827, A_827))) | ~m1_subset_1(B_828, k1_zfmisc_1(k2_zfmisc_1(A_827, A_827))) | ~v3_funct_2(B_828, A_827, A_827) | ~v1_funct_2(B_828, A_827, A_827) | ~v1_funct_1(B_828))), inference(cnfTransformation, [status(thm)], [f_139])).
% 12.13/4.82  tff(c_13682, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_13458, c_13638])).
% 12.13/4.82  tff(c_13707, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_86, c_13682])).
% 12.13/4.82  tff(c_28, plain, (![C_13, A_11, B_12]: (v1_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.13/4.82  tff(c_13779, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_13707, c_28])).
% 12.13/4.82  tff(c_13398, plain, (![A_802, B_803]: (v1_funct_1(k2_funct_2(A_802, B_803)) | ~m1_subset_1(B_803, k1_zfmisc_1(k2_zfmisc_1(A_802, A_802))) | ~v3_funct_2(B_803, A_802, A_802) | ~v1_funct_2(B_803, A_802, A_802) | ~v1_funct_1(B_803))), inference(cnfTransformation, [status(thm)], [f_139])).
% 12.13/4.82  tff(c_13408, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_86, c_13398])).
% 12.13/4.82  tff(c_13425, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_13408])).
% 12.13/4.82  tff(c_13462, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_13458, c_13425])).
% 12.13/4.82  tff(c_13544, plain, (![A_819, B_820]: (v3_funct_2(k2_funct_2(A_819, B_820), A_819, A_819) | ~m1_subset_1(B_820, k1_zfmisc_1(k2_zfmisc_1(A_819, A_819))) | ~v3_funct_2(B_820, A_819, A_819) | ~v1_funct_2(B_820, A_819, A_819) | ~v1_funct_1(B_820))), inference(cnfTransformation, [status(thm)], [f_139])).
% 12.13/4.82  tff(c_13551, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_86, c_13544])).
% 12.13/4.82  tff(c_13565, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_13458, c_13551])).
% 12.13/4.82  tff(c_42, plain, (![C_27, B_26, A_25]: (v2_funct_2(C_27, B_26) | ~v3_funct_2(C_27, A_25, B_26) | ~v1_funct_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.13/4.82  tff(c_13728, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_13707, c_42])).
% 12.13/4.82  tff(c_13770, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13462, c_13565, c_13728])).
% 12.13/4.82  tff(c_30, plain, (![C_16, B_15, A_14]: (v5_relat_1(C_16, B_15) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.13/4.82  tff(c_13777, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_13707, c_30])).
% 12.13/4.82  tff(c_62, plain, (![B_32, A_31]: (k2_relat_1(B_32)=A_31 | ~v2_funct_2(B_32, A_31) | ~v5_relat_1(B_32, A_31) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_123])).
% 12.13/4.82  tff(c_13783, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_13777, c_62])).
% 12.13/4.82  tff(c_13786, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13779, c_13783])).
% 12.13/4.82  tff(c_14018, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13770, c_13786])).
% 12.13/4.82  tff(c_34, plain, (![A_17, B_18, C_19]: (k1_relset_1(A_17, B_18, C_19)=k1_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.13/4.82  tff(c_13774, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_2'))=k1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_13707, c_34])).
% 12.13/4.82  tff(c_13470, plain, (![A_812, B_813]: (v1_funct_2(k2_funct_2(A_812, B_813), A_812, A_812) | ~m1_subset_1(B_813, k1_zfmisc_1(k2_zfmisc_1(A_812, A_812))) | ~v3_funct_2(B_813, A_812, A_812) | ~v1_funct_2(B_813, A_812, A_812) | ~v1_funct_1(B_813))), inference(cnfTransformation, [status(thm)], [f_139])).
% 12.13/4.82  tff(c_13477, plain, (v1_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_86, c_13470])).
% 12.13/4.82  tff(c_13491, plain, (v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_13458, c_13477])).
% 12.13/4.82  tff(c_58, plain, (![B_29, A_28, C_30]: (k1_xboole_0=B_29 | k1_relset_1(A_28, B_29, C_30)=A_28 | ~v1_funct_2(C_30, A_28, B_29) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 12.13/4.82  tff(c_13725, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_2'))='#skF_1' | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_13707, c_58])).
% 12.13/4.82  tff(c_13767, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13491, c_13725])).
% 12.13/4.82  tff(c_13927, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13774, c_13767])).
% 12.13/4.82  tff(c_13928, plain, (k1_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(splitLeft, [status(thm)], [c_13927])).
% 12.13/4.82  tff(c_78, plain, (![A_44]: (m1_subset_1(A_44, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_44), k2_relat_1(A_44)))) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_171])).
% 12.13/4.82  tff(c_13833, plain, (![F_830, E_832, C_831, B_834, D_833, A_829]: (k1_partfun1(A_829, B_834, C_831, D_833, E_832, F_830)=k5_relat_1(E_832, F_830) | ~m1_subset_1(F_830, k1_zfmisc_1(k2_zfmisc_1(C_831, D_833))) | ~v1_funct_1(F_830) | ~m1_subset_1(E_832, k1_zfmisc_1(k2_zfmisc_1(A_829, B_834))) | ~v1_funct_1(E_832))), inference(cnfTransformation, [status(thm)], [f_149])).
% 12.13/4.82  tff(c_17227, plain, (![A_958, B_959, A_960, E_961]: (k1_partfun1(A_958, B_959, k1_relat_1(A_960), k2_relat_1(A_960), E_961, A_960)=k5_relat_1(E_961, A_960) | ~m1_subset_1(E_961, k1_zfmisc_1(k2_zfmisc_1(A_958, B_959))) | ~v1_funct_1(E_961) | ~v1_funct_1(A_960) | ~v1_relat_1(A_960))), inference(resolution, [status(thm)], [c_78, c_13833])).
% 12.13/4.82  tff(c_17252, plain, (![A_960]: (k1_partfun1('#skF_1', '#skF_1', k1_relat_1(A_960), k2_relat_1(A_960), '#skF_2', A_960)=k5_relat_1('#skF_2', A_960) | ~v1_funct_1('#skF_2') | ~v1_funct_1(A_960) | ~v1_relat_1(A_960))), inference(resolution, [status(thm)], [c_86, c_17227])).
% 12.13/4.82  tff(c_17291, plain, (![A_962]: (k1_partfun1('#skF_1', '#skF_1', k1_relat_1(A_962), k2_relat_1(A_962), '#skF_2', A_962)=k5_relat_1('#skF_2', A_962) | ~v1_funct_1(A_962) | ~v1_relat_1(A_962))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_17252])).
% 12.13/4.82  tff(c_17335, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', k2_relat_1(k2_funct_1('#skF_2')), '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_13928, c_17291])).
% 12.13/4.82  tff(c_17375, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_13779, c_13462, c_14018, c_17335])).
% 12.13/4.82  tff(c_84, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_184])).
% 12.13/4.82  tff(c_198, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_84])).
% 12.13/4.82  tff(c_13463, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_13458, c_198])).
% 12.13/4.82  tff(c_17384, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_17375, c_13463])).
% 12.13/4.82  tff(c_17391, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_94, c_17384])).
% 12.13/4.82  tff(c_17394, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_235, c_92, c_6941, c_6294, c_12991, c_17391])).
% 12.13/4.82  tff(c_17395, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_13927])).
% 12.13/4.82  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.13/4.82  tff(c_17460, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_17395, c_17395, c_20])).
% 12.13/4.82  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.13/4.82  tff(c_17455, plain, (![B_3]: (k2_zfmisc_1('#skF_1', B_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_17395, c_17395, c_8])).
% 12.13/4.82  tff(c_174, plain, (![A_54, B_55]: (r1_tarski(A_54, B_55) | ~m1_subset_1(A_54, k1_zfmisc_1(B_55)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.13/4.82  tff(c_189, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_86, c_174])).
% 12.13/4.82  tff(c_17754, plain, (r1_tarski('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_17455, c_189])).
% 12.13/4.82  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.13/4.82  tff(c_18081, plain, (![A_981]: (A_981='#skF_1' | ~r1_tarski(A_981, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_17395, c_17395, c_2])).
% 12.13/4.82  tff(c_18093, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_17754, c_18081])).
% 12.13/4.82  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.13/4.82  tff(c_13780, plain, (r1_tarski(k2_funct_1('#skF_2'), k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_13707, c_12])).
% 12.13/4.82  tff(c_17751, plain, (r1_tarski(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_17455, c_13780])).
% 12.13/4.82  tff(c_18092, plain, (k2_funct_1('#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_17751, c_18081])).
% 12.13/4.82  tff(c_18149, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18093, c_18092])).
% 12.13/4.82  tff(c_17396, plain, (k1_relat_1(k2_funct_1('#skF_2'))!='#skF_1'), inference(splitRight, [status(thm)], [c_13927])).
% 12.13/4.82  tff(c_18101, plain, (k1_relat_1(k2_funct_1('#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18093, c_17396])).
% 12.13/4.82  tff(c_18186, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17460, c_18149, c_18101])).
% 12.13/4.82  tff(c_18187, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_12987])).
% 12.13/4.82  tff(c_18229, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18187, c_18187, c_20])).
% 12.13/4.82  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.13/4.82  tff(c_18225, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18187, c_18187, c_6])).
% 12.13/4.82  tff(c_18413, plain, (r1_tarski('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18225, c_189])).
% 12.13/4.82  tff(c_18639, plain, (![A_1002]: (A_1002='#skF_1' | ~r1_tarski(A_1002, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_18187, c_18187, c_2])).
% 12.13/4.82  tff(c_18647, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_18413, c_18639])).
% 12.13/4.82  tff(c_18188, plain, (k1_relat_1('#skF_2')!='#skF_1'), inference(splitRight, [status(thm)], [c_12987])).
% 12.13/4.82  tff(c_18654, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18647, c_18188])).
% 12.13/4.82  tff(c_18674, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18229, c_18654])).
% 12.13/4.82  tff(c_18675, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_84])).
% 12.13/4.82  tff(c_20389, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20384, c_18675])).
% 12.13/4.82  tff(c_21715, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_21630, c_20389])).
% 12.13/4.82  tff(c_21722, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_95, c_21715])).
% 12.13/4.82  tff(c_21725, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18713, c_92, c_19634, c_18927, c_19299, c_21722])).
% 12.13/4.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.13/4.82  
% 12.13/4.82  Inference rules
% 12.13/4.82  ----------------------
% 12.13/4.82  #Ref     : 0
% 12.13/4.82  #Sup     : 4449
% 12.13/4.82  #Fact    : 0
% 12.13/4.82  #Define  : 0
% 12.13/4.82  #Split   : 42
% 12.13/4.82  #Chain   : 0
% 12.13/4.82  #Close   : 0
% 12.13/4.82  
% 12.13/4.82  Ordering : KBO
% 12.13/4.82  
% 12.13/4.82  Simplification rules
% 12.13/4.82  ----------------------
% 12.13/4.82  #Subsume      : 563
% 12.13/4.82  #Demod        : 7798
% 12.13/4.82  #Tautology    : 2092
% 12.13/4.82  #SimpNegUnit  : 5
% 12.13/4.82  #BackRed      : 671
% 12.13/4.82  
% 12.13/4.82  #Partial instantiations: 0
% 12.13/4.82  #Strategies tried      : 1
% 12.13/4.82  
% 12.13/4.82  Timing (in seconds)
% 12.13/4.82  ----------------------
% 12.13/4.82  Preprocessing        : 0.37
% 12.13/4.82  Parsing              : 0.20
% 12.13/4.82  CNF conversion       : 0.02
% 12.13/4.82  Main loop            : 3.64
% 12.13/4.82  Inferencing          : 1.06
% 12.13/4.82  Reduction            : 1.56
% 12.13/4.82  Demodulation         : 1.22
% 12.13/4.82  BG Simplification    : 0.08
% 12.13/4.82  Subsumption          : 0.67
% 12.13/4.82  Abstraction          : 0.11
% 12.13/4.82  MUC search           : 0.00
% 12.13/4.82  Cooper               : 0.00
% 12.13/4.82  Total                : 4.07
% 12.13/4.82  Index Insertion      : 0.00
% 12.13/4.82  Index Deletion       : 0.00
% 12.13/4.82  Index Matching       : 0.00
% 12.13/4.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
