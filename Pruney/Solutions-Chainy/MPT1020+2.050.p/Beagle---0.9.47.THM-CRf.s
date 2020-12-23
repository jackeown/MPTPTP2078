%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:58 EST 2020

% Result     : Theorem 5.06s
% Output     : CNFRefutation 5.32s
% Verified   : 
% Statistics : Number of formulae       :  183 (3138 expanded)
%              Number of leaves         :   48 (1039 expanded)
%              Depth                    :   17
%              Number of atoms          :  306 (8148 expanded)
%              Number of equality atoms :   84 ( 885 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_184,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & v3_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,C),k6_partfun1(A))
             => r2_relset_1(A,A,C,k2_funct_2(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_62,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_162,axiom,(
    ! [A,B,C] :
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

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_116,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_106,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_118,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_64,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_736,plain,(
    ! [A_136,B_137,D_138] :
      ( r2_relset_1(A_136,B_137,D_138,D_138)
      | ~ m1_subset_1(D_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_749,plain,(
    r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_736])).

tff(c_76,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_74,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_66,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_20,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_162,plain,(
    ! [B_64,A_65] :
      ( v1_relat_1(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65))
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_171,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_70,c_162])).

tff(c_183,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_171])).

tff(c_189,plain,(
    ! [C_67,B_68,A_69] :
      ( v5_relat_1(C_67,B_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_69,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_206,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_189])).

tff(c_325,plain,(
    ! [B_84,A_85] :
      ( k2_relat_1(B_84) = A_85
      | ~ v2_funct_2(B_84,A_85)
      | ~ v5_relat_1(B_84,A_85)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_337,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_206,c_325])).

tff(c_349,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_337])).

tff(c_602,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_349])).

tff(c_72,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_690,plain,(
    ! [C_131,B_132,A_133] :
      ( v2_funct_2(C_131,B_132)
      | ~ v3_funct_2(C_131,A_133,B_132)
      | ~ v1_funct_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_133,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_696,plain,
    ( v2_funct_2('#skF_3','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_690])).

tff(c_709,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_696])).

tff(c_711,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_602,c_709])).

tff(c_712,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_349])).

tff(c_759,plain,(
    ! [A_140,B_141,C_142] :
      ( k2_relset_1(A_140,B_141,C_142) = k2_relat_1(C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_765,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_759])).

tff(c_777,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_712,c_765])).

tff(c_793,plain,(
    ! [C_145,A_146,B_147] :
      ( v2_funct_1(C_145)
      | ~ v3_funct_2(C_145,A_146,B_147)
      | ~ v1_funct_1(C_145)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_799,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_793])).

tff(c_812,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_799])).

tff(c_60,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_1044,plain,(
    ! [C_200,D_201,B_202,A_203] :
      ( k2_funct_1(C_200) = D_201
      | k1_xboole_0 = B_202
      | k1_xboole_0 = A_203
      | ~ v2_funct_1(C_200)
      | ~ r2_relset_1(A_203,A_203,k1_partfun1(A_203,B_202,B_202,A_203,C_200,D_201),k6_partfun1(A_203))
      | k2_relset_1(A_203,B_202,C_200) != B_202
      | ~ m1_subset_1(D_201,k1_zfmisc_1(k2_zfmisc_1(B_202,A_203)))
      | ~ v1_funct_2(D_201,B_202,A_203)
      | ~ v1_funct_1(D_201)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_203,B_202)))
      | ~ v1_funct_2(C_200,A_203,B_202)
      | ~ v1_funct_1(C_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_1050,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_2','#skF_2','#skF_3') != '#skF_2'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1044])).

tff(c_1055,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_68,c_66,c_62,c_777,c_812,c_1050])).

tff(c_1056,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1055])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1090,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1056,c_6])).

tff(c_14,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1088,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_2',B_8) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1056,c_1056,c_14])).

tff(c_208,plain,(
    ! [C_70,B_71,A_72] :
      ( ~ v1_xboole_0(C_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(C_70))
      | ~ r2_hidden(A_72,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_221,plain,(
    ! [A_72] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_2'))
      | ~ r2_hidden(A_72,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_70,c_208])).

tff(c_237,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_1202,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1088,c_237])).

tff(c_1207,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1090,c_1202])).

tff(c_1208,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1055])).

tff(c_959,plain,(
    ! [A_172,B_173] :
      ( k2_funct_2(A_172,B_173) = k2_funct_1(B_173)
      | ~ m1_subset_1(B_173,k1_zfmisc_1(k2_zfmisc_1(A_172,A_172)))
      | ~ v3_funct_2(B_173,A_172,A_172)
      | ~ v1_funct_2(B_173,A_172,A_172)
      | ~ v1_funct_1(B_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_965,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_959])).

tff(c_981,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_965])).

tff(c_58,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4',k2_funct_2('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_985,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_981,c_58])).

tff(c_1210,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1208,c_985])).

tff(c_1214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_749,c_1210])).

tff(c_1216,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_222,plain,(
    ! [A_72] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_2'))
      | ~ r2_hidden(A_72,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_208])).

tff(c_1245,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_222])).

tff(c_1293,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1216,c_1245])).

tff(c_1296,plain,(
    ! [A_212] : ~ r2_hidden(A_212,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_1301,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_1296])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( ~ v1_xboole_0(B_6)
      | B_6 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1356,plain,(
    ! [A_217] :
      ( A_217 = '#skF_4'
      | ~ v1_xboole_0(A_217) ) ),
    inference(resolution,[status(thm)],[c_1301,c_8])).

tff(c_1366,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1216,c_1356])).

tff(c_1521,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1366,c_62])).

tff(c_1217,plain,(
    ! [A_208] : ~ r2_hidden(A_208,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_1222,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_1217])).

tff(c_1369,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1222,c_1356])).

tff(c_131,plain,(
    ! [B_58,A_59] :
      ( ~ v1_xboole_0(B_58)
      | B_58 = A_59
      | ~ v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_134,plain,(
    ! [A_59] :
      ( k1_xboole_0 = A_59
      | ~ v1_xboole_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_6,c_131])).

tff(c_1228,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1222,c_134])).

tff(c_12,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1237,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1228,c_1228,c_12])).

tff(c_1455,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1369,c_1369,c_1237])).

tff(c_1509,plain,(
    ! [A_223,B_224,D_225] :
      ( r2_relset_1(A_223,B_224,D_225,D_225)
      | ~ m1_subset_1(D_225,k1_zfmisc_1(k2_zfmisc_1(A_223,B_224))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2565,plain,(
    ! [A_357,D_358] :
      ( r2_relset_1(A_357,'#skF_4',D_358,D_358)
      | ~ m1_subset_1(D_358,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1455,c_1509])).

tff(c_2568,plain,(
    ! [A_357] : r2_relset_1(A_357,'#skF_4','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_1521,c_2565])).

tff(c_141,plain,(
    ! [A_61] : m1_subset_1(k6_partfun1(A_61),k1_zfmisc_1(k2_zfmisc_1(A_61,A_61))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_145,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_141])).

tff(c_210,plain,(
    ! [A_72] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_72,k6_partfun1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_145,c_208])).

tff(c_224,plain,(
    ! [A_74] : ~ r2_hidden(A_74,k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_210])).

tff(c_229,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_4,c_224])).

tff(c_235,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_229,c_134])).

tff(c_1308,plain,(
    k6_partfun1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1228,c_1228,c_235])).

tff(c_1376,plain,(
    k6_partfun1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1369,c_1369,c_1308])).

tff(c_174,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_162])).

tff(c_186,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_174])).

tff(c_46,plain,(
    ! [A_33] : m1_subset_1(k6_partfun1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_205,plain,(
    ! [A_33] : v5_relat_1(k6_partfun1(A_33),A_33) ),
    inference(resolution,[status(thm)],[c_46,c_189])).

tff(c_1410,plain,(
    v5_relat_1('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1376,c_205])).

tff(c_1432,plain,(
    ! [B_219,A_220] :
      ( k2_relat_1(B_219) = A_220
      | ~ v2_funct_2(B_219,A_220)
      | ~ v5_relat_1(B_219,A_220)
      | ~ v1_relat_1(B_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1435,plain,
    ( k2_relat_1('#skF_4') = '#skF_4'
    | ~ v2_funct_2('#skF_4','#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1410,c_1432])).

tff(c_1444,plain,
    ( k2_relat_1('#skF_4') = '#skF_4'
    | ~ v2_funct_2('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_1435])).

tff(c_1646,plain,(
    ~ v2_funct_2('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1444])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( k1_xboole_0 = B_8
      | k1_xboole_0 = A_7
      | k2_zfmisc_1(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1232,plain,(
    ! [B_8,A_7] :
      ( B_8 = '#skF_3'
      | A_7 = '#skF_3'
      | k2_zfmisc_1(A_7,B_8) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1228,c_1228,c_1228,c_10])).

tff(c_1805,plain,(
    ! [B_255,A_256] :
      ( B_255 = '#skF_4'
      | A_256 = '#skF_4'
      | k2_zfmisc_1(A_256,B_255) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1369,c_1369,c_1369,c_1232])).

tff(c_1815,plain,(
    '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1366,c_1805])).

tff(c_64,plain,(
    v3_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_1829,plain,(
    v3_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1815,c_1815,c_64])).

tff(c_1678,plain,(
    ! [C_236,B_237,A_238] :
      ( v2_funct_2(C_236,B_237)
      | ~ v3_funct_2(C_236,A_238,B_237)
      | ~ v1_funct_1(C_236)
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(A_238,B_237))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1938,plain,(
    ! [A_278] :
      ( v2_funct_2(k6_partfun1(A_278),A_278)
      | ~ v3_funct_2(k6_partfun1(A_278),A_278,A_278)
      | ~ v1_funct_1(k6_partfun1(A_278)) ) ),
    inference(resolution,[status(thm)],[c_46,c_1678])).

tff(c_1941,plain,
    ( v2_funct_2(k6_partfun1('#skF_4'),'#skF_4')
    | ~ v3_funct_2('#skF_4','#skF_4','#skF_4')
    | ~ v1_funct_1(k6_partfun1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1376,c_1938])).

tff(c_1943,plain,(
    v2_funct_2('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1376,c_1829,c_1376,c_1941])).

tff(c_1945,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1646,c_1943])).

tff(c_1947,plain,(
    v2_funct_2('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1444])).

tff(c_2128,plain,(
    ! [B_302,A_303] :
      ( B_302 = '#skF_4'
      | A_303 = '#skF_4'
      | k2_zfmisc_1(A_303,B_302) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1369,c_1369,c_1369,c_1232])).

tff(c_2138,plain,(
    '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1366,c_2128])).

tff(c_207,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_189])).

tff(c_1441,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ v2_funct_2('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_207,c_1432])).

tff(c_1450,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ v2_funct_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_1441])).

tff(c_1629,plain,(
    ~ v2_funct_2('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1450])).

tff(c_2145,plain,(
    ~ v2_funct_2('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2138,c_1629])).

tff(c_2157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1947,c_2145])).

tff(c_2158,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1450])).

tff(c_2192,plain,
    ( '#skF_2' = '#skF_4'
    | ~ v2_funct_2('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2158,c_1444])).

tff(c_2193,plain,(
    ~ v2_funct_2('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2192])).

tff(c_2353,plain,(
    ! [B_330,A_331] :
      ( B_330 = '#skF_4'
      | A_331 = '#skF_4'
      | k2_zfmisc_1(A_331,B_330) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1369,c_1369,c_1369,c_1232])).

tff(c_2363,plain,(
    '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1366,c_2353])).

tff(c_2159,plain,(
    v2_funct_2('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1450])).

tff(c_2372,plain,(
    v2_funct_2('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2363,c_2159])).

tff(c_2383,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2193,c_2372])).

tff(c_2384,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2192])).

tff(c_2412,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2384,c_2384,c_66])).

tff(c_2411,plain,(
    v3_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2384,c_2384,c_64])).

tff(c_50,plain,(
    ! [A_36] : k6_relat_1(A_36) = k6_partfun1(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_22,plain,(
    ! [A_17] : k2_funct_1(k6_relat_1(A_17)) = k6_relat_1(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_77,plain,(
    ! [A_17] : k2_funct_1(k6_partfun1(A_17)) = k6_partfun1(A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_22])).

tff(c_2500,plain,(
    ! [A_349,B_350] :
      ( k2_funct_2(A_349,B_350) = k2_funct_1(B_350)
      | ~ m1_subset_1(B_350,k1_zfmisc_1(k2_zfmisc_1(A_349,A_349)))
      | ~ v3_funct_2(B_350,A_349,A_349)
      | ~ v1_funct_2(B_350,A_349,A_349)
      | ~ v1_funct_1(B_350) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2511,plain,(
    ! [A_33] :
      ( k2_funct_2(A_33,k6_partfun1(A_33)) = k2_funct_1(k6_partfun1(A_33))
      | ~ v3_funct_2(k6_partfun1(A_33),A_33,A_33)
      | ~ v1_funct_2(k6_partfun1(A_33),A_33,A_33)
      | ~ v1_funct_1(k6_partfun1(A_33)) ) ),
    inference(resolution,[status(thm)],[c_46,c_2500])).

tff(c_2699,plain,(
    ! [A_394] :
      ( k2_funct_2(A_394,k6_partfun1(A_394)) = k6_partfun1(A_394)
      | ~ v3_funct_2(k6_partfun1(A_394),A_394,A_394)
      | ~ v1_funct_2(k6_partfun1(A_394),A_394,A_394)
      | ~ v1_funct_1(k6_partfun1(A_394)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_2511])).

tff(c_2702,plain,
    ( k2_funct_2('#skF_4',k6_partfun1('#skF_4')) = k6_partfun1('#skF_4')
    | ~ v3_funct_2('#skF_4','#skF_4','#skF_4')
    | ~ v1_funct_2(k6_partfun1('#skF_4'),'#skF_4','#skF_4')
    | ~ v1_funct_1(k6_partfun1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1376,c_2699])).

tff(c_2704,plain,(
    k2_funct_2('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1376,c_2412,c_1376,c_2411,c_1376,c_1376,c_2702])).

tff(c_1383,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4',k2_funct_2('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1369,c_58])).

tff(c_2408,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4',k2_funct_2('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2384,c_2384,c_2384,c_1383])).

tff(c_2712,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2704,c_2408])).

tff(c_2715,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2568,c_2712])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:19:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.06/1.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.06/1.98  
% 5.06/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.06/1.98  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 5.06/1.98  
% 5.06/1.98  %Foreground sorts:
% 5.06/1.98  
% 5.06/1.98  
% 5.06/1.98  %Background operators:
% 5.06/1.98  
% 5.06/1.98  
% 5.06/1.98  %Foreground operators:
% 5.06/1.98  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.06/1.98  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.06/1.98  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.06/1.98  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.06/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.06/1.98  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.06/1.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.06/1.98  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.06/1.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.06/1.98  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.06/1.98  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.06/1.98  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.32/1.98  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.32/1.98  tff('#skF_2', type, '#skF_2': $i).
% 5.32/1.98  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.32/1.98  tff('#skF_3', type, '#skF_3': $i).
% 5.32/1.98  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.32/1.98  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.32/1.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.32/1.98  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.32/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.32/1.98  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.32/1.98  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.32/1.98  tff('#skF_4', type, '#skF_4': $i).
% 5.32/1.98  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.32/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.32/1.98  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.32/1.98  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.32/1.98  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.32/1.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.32/1.98  
% 5.32/2.00  tff(f_184, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_2)).
% 5.32/2.00  tff(f_82, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.32/2.00  tff(f_62, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.32/2.00  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.32/2.00  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.32/2.00  tff(f_102, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 5.32/2.00  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.32/2.00  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.32/2.00  tff(f_162, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 5.32/2.00  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.32/2.00  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.32/2.00  tff(f_53, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 5.32/2.00  tff(f_116, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.32/2.00  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.32/2.00  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 5.32/2.00  tff(f_106, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.32/2.00  tff(f_118, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.32/2.00  tff(f_64, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 5.32/2.00  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_184])).
% 5.32/2.00  tff(c_736, plain, (![A_136, B_137, D_138]: (r2_relset_1(A_136, B_137, D_138, D_138) | ~m1_subset_1(D_138, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.32/2.00  tff(c_749, plain, (r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_62, c_736])).
% 5.32/2.00  tff(c_76, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_184])).
% 5.32/2.00  tff(c_74, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_184])).
% 5.32/2.00  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_184])).
% 5.32/2.00  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_184])).
% 5.32/2.00  tff(c_66, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_184])).
% 5.32/2.00  tff(c_20, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.32/2.00  tff(c_162, plain, (![B_64, A_65]: (v1_relat_1(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.32/2.00  tff(c_171, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_70, c_162])).
% 5.32/2.00  tff(c_183, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_171])).
% 5.32/2.00  tff(c_189, plain, (![C_67, B_68, A_69]: (v5_relat_1(C_67, B_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_69, B_68))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.32/2.00  tff(c_206, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_189])).
% 5.32/2.00  tff(c_325, plain, (![B_84, A_85]: (k2_relat_1(B_84)=A_85 | ~v2_funct_2(B_84, A_85) | ~v5_relat_1(B_84, A_85) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.32/2.00  tff(c_337, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_206, c_325])).
% 5.32/2.00  tff(c_349, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_183, c_337])).
% 5.32/2.00  tff(c_602, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_349])).
% 5.32/2.00  tff(c_72, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_184])).
% 5.32/2.00  tff(c_690, plain, (![C_131, B_132, A_133]: (v2_funct_2(C_131, B_132) | ~v3_funct_2(C_131, A_133, B_132) | ~v1_funct_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_133, B_132))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.32/2.00  tff(c_696, plain, (v2_funct_2('#skF_3', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_690])).
% 5.32/2.00  tff(c_709, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_696])).
% 5.32/2.00  tff(c_711, plain, $false, inference(negUnitSimplification, [status(thm)], [c_602, c_709])).
% 5.32/2.00  tff(c_712, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_349])).
% 5.32/2.00  tff(c_759, plain, (![A_140, B_141, C_142]: (k2_relset_1(A_140, B_141, C_142)=k2_relat_1(C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.32/2.00  tff(c_765, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_759])).
% 5.32/2.00  tff(c_777, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_712, c_765])).
% 5.32/2.00  tff(c_793, plain, (![C_145, A_146, B_147]: (v2_funct_1(C_145) | ~v3_funct_2(C_145, A_146, B_147) | ~v1_funct_1(C_145) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.32/2.00  tff(c_799, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_793])).
% 5.32/2.00  tff(c_812, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_799])).
% 5.32/2.00  tff(c_60, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_184])).
% 5.32/2.00  tff(c_1044, plain, (![C_200, D_201, B_202, A_203]: (k2_funct_1(C_200)=D_201 | k1_xboole_0=B_202 | k1_xboole_0=A_203 | ~v2_funct_1(C_200) | ~r2_relset_1(A_203, A_203, k1_partfun1(A_203, B_202, B_202, A_203, C_200, D_201), k6_partfun1(A_203)) | k2_relset_1(A_203, B_202, C_200)!=B_202 | ~m1_subset_1(D_201, k1_zfmisc_1(k2_zfmisc_1(B_202, A_203))) | ~v1_funct_2(D_201, B_202, A_203) | ~v1_funct_1(D_201) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_203, B_202))) | ~v1_funct_2(C_200, A_203, B_202) | ~v1_funct_1(C_200))), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.32/2.00  tff(c_1050, plain, (k2_funct_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_2', '#skF_2', '#skF_3')!='#skF_2' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_1044])).
% 5.32/2.00  tff(c_1055, plain, (k2_funct_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_70, c_68, c_66, c_62, c_777, c_812, c_1050])).
% 5.32/2.00  tff(c_1056, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1055])).
% 5.32/2.00  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.32/2.00  tff(c_1090, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1056, c_6])).
% 5.32/2.00  tff(c_14, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.32/2.00  tff(c_1088, plain, (![B_8]: (k2_zfmisc_1('#skF_2', B_8)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1056, c_1056, c_14])).
% 5.32/2.00  tff(c_208, plain, (![C_70, B_71, A_72]: (~v1_xboole_0(C_70) | ~m1_subset_1(B_71, k1_zfmisc_1(C_70)) | ~r2_hidden(A_72, B_71))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.32/2.00  tff(c_221, plain, (![A_72]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_2')) | ~r2_hidden(A_72, '#skF_3'))), inference(resolution, [status(thm)], [c_70, c_208])).
% 5.32/2.00  tff(c_237, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(splitLeft, [status(thm)], [c_221])).
% 5.32/2.00  tff(c_1202, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1088, c_237])).
% 5.32/2.00  tff(c_1207, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1090, c_1202])).
% 5.32/2.00  tff(c_1208, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_1055])).
% 5.32/2.00  tff(c_959, plain, (![A_172, B_173]: (k2_funct_2(A_172, B_173)=k2_funct_1(B_173) | ~m1_subset_1(B_173, k1_zfmisc_1(k2_zfmisc_1(A_172, A_172))) | ~v3_funct_2(B_173, A_172, A_172) | ~v1_funct_2(B_173, A_172, A_172) | ~v1_funct_1(B_173))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.32/2.00  tff(c_965, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_959])).
% 5.32/2.00  tff(c_981, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_965])).
% 5.32/2.00  tff(c_58, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', k2_funct_2('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_184])).
% 5.32/2.00  tff(c_985, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_981, c_58])).
% 5.32/2.00  tff(c_1210, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1208, c_985])).
% 5.32/2.00  tff(c_1214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_749, c_1210])).
% 5.32/2.00  tff(c_1216, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(splitRight, [status(thm)], [c_221])).
% 5.32/2.00  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.32/2.00  tff(c_222, plain, (![A_72]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_2')) | ~r2_hidden(A_72, '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_208])).
% 5.32/2.00  tff(c_1245, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(splitLeft, [status(thm)], [c_222])).
% 5.32/2.00  tff(c_1293, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1216, c_1245])).
% 5.32/2.00  tff(c_1296, plain, (![A_212]: (~r2_hidden(A_212, '#skF_4'))), inference(splitRight, [status(thm)], [c_222])).
% 5.32/2.00  tff(c_1301, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_1296])).
% 5.32/2.00  tff(c_8, plain, (![B_6, A_5]: (~v1_xboole_0(B_6) | B_6=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.32/2.00  tff(c_1356, plain, (![A_217]: (A_217='#skF_4' | ~v1_xboole_0(A_217))), inference(resolution, [status(thm)], [c_1301, c_8])).
% 5.32/2.00  tff(c_1366, plain, (k2_zfmisc_1('#skF_2', '#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_1216, c_1356])).
% 5.32/2.00  tff(c_1521, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1366, c_62])).
% 5.32/2.00  tff(c_1217, plain, (![A_208]: (~r2_hidden(A_208, '#skF_3'))), inference(splitRight, [status(thm)], [c_221])).
% 5.32/2.00  tff(c_1222, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_4, c_1217])).
% 5.32/2.00  tff(c_1369, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_1222, c_1356])).
% 5.32/2.00  tff(c_131, plain, (![B_58, A_59]: (~v1_xboole_0(B_58) | B_58=A_59 | ~v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.32/2.00  tff(c_134, plain, (![A_59]: (k1_xboole_0=A_59 | ~v1_xboole_0(A_59))), inference(resolution, [status(thm)], [c_6, c_131])).
% 5.32/2.00  tff(c_1228, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1222, c_134])).
% 5.32/2.00  tff(c_12, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.32/2.00  tff(c_1237, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1228, c_1228, c_12])).
% 5.32/2.00  tff(c_1455, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1369, c_1369, c_1237])).
% 5.32/2.00  tff(c_1509, plain, (![A_223, B_224, D_225]: (r2_relset_1(A_223, B_224, D_225, D_225) | ~m1_subset_1(D_225, k1_zfmisc_1(k2_zfmisc_1(A_223, B_224))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.32/2.00  tff(c_2565, plain, (![A_357, D_358]: (r2_relset_1(A_357, '#skF_4', D_358, D_358) | ~m1_subset_1(D_358, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1455, c_1509])).
% 5.32/2.00  tff(c_2568, plain, (![A_357]: (r2_relset_1(A_357, '#skF_4', '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_1521, c_2565])).
% 5.32/2.00  tff(c_141, plain, (![A_61]: (m1_subset_1(k6_partfun1(A_61), k1_zfmisc_1(k2_zfmisc_1(A_61, A_61))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.32/2.00  tff(c_145, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_141])).
% 5.32/2.00  tff(c_210, plain, (![A_72]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_72, k6_partfun1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_145, c_208])).
% 5.32/2.00  tff(c_224, plain, (![A_74]: (~r2_hidden(A_74, k6_partfun1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_210])).
% 5.32/2.00  tff(c_229, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_224])).
% 5.32/2.00  tff(c_235, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_229, c_134])).
% 5.32/2.00  tff(c_1308, plain, (k6_partfun1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1228, c_1228, c_235])).
% 5.32/2.00  tff(c_1376, plain, (k6_partfun1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1369, c_1369, c_1308])).
% 5.32/2.00  tff(c_174, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_62, c_162])).
% 5.32/2.00  tff(c_186, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_174])).
% 5.32/2.00  tff(c_46, plain, (![A_33]: (m1_subset_1(k6_partfun1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.32/2.00  tff(c_205, plain, (![A_33]: (v5_relat_1(k6_partfun1(A_33), A_33))), inference(resolution, [status(thm)], [c_46, c_189])).
% 5.32/2.00  tff(c_1410, plain, (v5_relat_1('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1376, c_205])).
% 5.32/2.00  tff(c_1432, plain, (![B_219, A_220]: (k2_relat_1(B_219)=A_220 | ~v2_funct_2(B_219, A_220) | ~v5_relat_1(B_219, A_220) | ~v1_relat_1(B_219))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.32/2.00  tff(c_1435, plain, (k2_relat_1('#skF_4')='#skF_4' | ~v2_funct_2('#skF_4', '#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1410, c_1432])).
% 5.32/2.00  tff(c_1444, plain, (k2_relat_1('#skF_4')='#skF_4' | ~v2_funct_2('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_186, c_1435])).
% 5.32/2.00  tff(c_1646, plain, (~v2_funct_2('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_1444])).
% 5.32/2.00  tff(c_10, plain, (![B_8, A_7]: (k1_xboole_0=B_8 | k1_xboole_0=A_7 | k2_zfmisc_1(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.32/2.00  tff(c_1232, plain, (![B_8, A_7]: (B_8='#skF_3' | A_7='#skF_3' | k2_zfmisc_1(A_7, B_8)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1228, c_1228, c_1228, c_10])).
% 5.32/2.00  tff(c_1805, plain, (![B_255, A_256]: (B_255='#skF_4' | A_256='#skF_4' | k2_zfmisc_1(A_256, B_255)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1369, c_1369, c_1369, c_1232])).
% 5.32/2.00  tff(c_1815, plain, ('#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1366, c_1805])).
% 5.32/2.00  tff(c_64, plain, (v3_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_184])).
% 5.32/2.00  tff(c_1829, plain, (v3_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1815, c_1815, c_64])).
% 5.32/2.00  tff(c_1678, plain, (![C_236, B_237, A_238]: (v2_funct_2(C_236, B_237) | ~v3_funct_2(C_236, A_238, B_237) | ~v1_funct_1(C_236) | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(A_238, B_237))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.32/2.00  tff(c_1938, plain, (![A_278]: (v2_funct_2(k6_partfun1(A_278), A_278) | ~v3_funct_2(k6_partfun1(A_278), A_278, A_278) | ~v1_funct_1(k6_partfun1(A_278)))), inference(resolution, [status(thm)], [c_46, c_1678])).
% 5.32/2.00  tff(c_1941, plain, (v2_funct_2(k6_partfun1('#skF_4'), '#skF_4') | ~v3_funct_2('#skF_4', '#skF_4', '#skF_4') | ~v1_funct_1(k6_partfun1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1376, c_1938])).
% 5.32/2.00  tff(c_1943, plain, (v2_funct_2('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1376, c_1829, c_1376, c_1941])).
% 5.32/2.00  tff(c_1945, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1646, c_1943])).
% 5.32/2.00  tff(c_1947, plain, (v2_funct_2('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_1444])).
% 5.32/2.00  tff(c_2128, plain, (![B_302, A_303]: (B_302='#skF_4' | A_303='#skF_4' | k2_zfmisc_1(A_303, B_302)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1369, c_1369, c_1369, c_1232])).
% 5.32/2.00  tff(c_2138, plain, ('#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1366, c_2128])).
% 5.32/2.00  tff(c_207, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_189])).
% 5.32/2.00  tff(c_1441, plain, (k2_relat_1('#skF_4')='#skF_2' | ~v2_funct_2('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_207, c_1432])).
% 5.32/2.00  tff(c_1450, plain, (k2_relat_1('#skF_4')='#skF_2' | ~v2_funct_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_186, c_1441])).
% 5.32/2.00  tff(c_1629, plain, (~v2_funct_2('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_1450])).
% 5.32/2.00  tff(c_2145, plain, (~v2_funct_2('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2138, c_1629])).
% 5.32/2.00  tff(c_2157, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1947, c_2145])).
% 5.32/2.00  tff(c_2158, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_1450])).
% 5.32/2.00  tff(c_2192, plain, ('#skF_2'='#skF_4' | ~v2_funct_2('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2158, c_1444])).
% 5.32/2.00  tff(c_2193, plain, (~v2_funct_2('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_2192])).
% 5.32/2.00  tff(c_2353, plain, (![B_330, A_331]: (B_330='#skF_4' | A_331='#skF_4' | k2_zfmisc_1(A_331, B_330)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1369, c_1369, c_1369, c_1232])).
% 5.32/2.00  tff(c_2363, plain, ('#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1366, c_2353])).
% 5.32/2.00  tff(c_2159, plain, (v2_funct_2('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_1450])).
% 5.32/2.00  tff(c_2372, plain, (v2_funct_2('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2363, c_2159])).
% 5.32/2.00  tff(c_2383, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2193, c_2372])).
% 5.32/2.00  tff(c_2384, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_2192])).
% 5.32/2.00  tff(c_2412, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2384, c_2384, c_66])).
% 5.32/2.00  tff(c_2411, plain, (v3_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2384, c_2384, c_64])).
% 5.32/2.00  tff(c_50, plain, (![A_36]: (k6_relat_1(A_36)=k6_partfun1(A_36))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.32/2.00  tff(c_22, plain, (![A_17]: (k2_funct_1(k6_relat_1(A_17))=k6_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.32/2.00  tff(c_77, plain, (![A_17]: (k2_funct_1(k6_partfun1(A_17))=k6_partfun1(A_17))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_22])).
% 5.32/2.00  tff(c_2500, plain, (![A_349, B_350]: (k2_funct_2(A_349, B_350)=k2_funct_1(B_350) | ~m1_subset_1(B_350, k1_zfmisc_1(k2_zfmisc_1(A_349, A_349))) | ~v3_funct_2(B_350, A_349, A_349) | ~v1_funct_2(B_350, A_349, A_349) | ~v1_funct_1(B_350))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.32/2.00  tff(c_2511, plain, (![A_33]: (k2_funct_2(A_33, k6_partfun1(A_33))=k2_funct_1(k6_partfun1(A_33)) | ~v3_funct_2(k6_partfun1(A_33), A_33, A_33) | ~v1_funct_2(k6_partfun1(A_33), A_33, A_33) | ~v1_funct_1(k6_partfun1(A_33)))), inference(resolution, [status(thm)], [c_46, c_2500])).
% 5.32/2.00  tff(c_2699, plain, (![A_394]: (k2_funct_2(A_394, k6_partfun1(A_394))=k6_partfun1(A_394) | ~v3_funct_2(k6_partfun1(A_394), A_394, A_394) | ~v1_funct_2(k6_partfun1(A_394), A_394, A_394) | ~v1_funct_1(k6_partfun1(A_394)))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_2511])).
% 5.32/2.00  tff(c_2702, plain, (k2_funct_2('#skF_4', k6_partfun1('#skF_4'))=k6_partfun1('#skF_4') | ~v3_funct_2('#skF_4', '#skF_4', '#skF_4') | ~v1_funct_2(k6_partfun1('#skF_4'), '#skF_4', '#skF_4') | ~v1_funct_1(k6_partfun1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1376, c_2699])).
% 5.32/2.00  tff(c_2704, plain, (k2_funct_2('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1376, c_2412, c_1376, c_2411, c_1376, c_1376, c_2702])).
% 5.32/2.00  tff(c_1383, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', k2_funct_2('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1369, c_58])).
% 5.32/2.00  tff(c_2408, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', k2_funct_2('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2384, c_2384, c_2384, c_1383])).
% 5.32/2.00  tff(c_2712, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2704, c_2408])).
% 5.32/2.00  tff(c_2715, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2568, c_2712])).
% 5.32/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.32/2.00  
% 5.32/2.00  Inference rules
% 5.32/2.00  ----------------------
% 5.32/2.00  #Ref     : 0
% 5.32/2.00  #Sup     : 563
% 5.32/2.00  #Fact    : 0
% 5.32/2.00  #Define  : 0
% 5.32/2.00  #Split   : 13
% 5.32/2.00  #Chain   : 0
% 5.32/2.00  #Close   : 0
% 5.32/2.00  
% 5.32/2.00  Ordering : KBO
% 5.32/2.00  
% 5.32/2.01  Simplification rules
% 5.32/2.01  ----------------------
% 5.32/2.01  #Subsume      : 73
% 5.32/2.01  #Demod        : 795
% 5.32/2.01  #Tautology    : 320
% 5.32/2.01  #SimpNegUnit  : 5
% 5.32/2.01  #BackRed      : 129
% 5.32/2.01  
% 5.32/2.01  #Partial instantiations: 0
% 5.32/2.01  #Strategies tried      : 1
% 5.32/2.01  
% 5.32/2.01  Timing (in seconds)
% 5.32/2.01  ----------------------
% 5.32/2.01  Preprocessing        : 0.39
% 5.32/2.01  Parsing              : 0.21
% 5.32/2.01  CNF conversion       : 0.03
% 5.32/2.01  Main loop            : 0.79
% 5.32/2.01  Inferencing          : 0.29
% 5.32/2.01  Reduction            : 0.28
% 5.32/2.01  Demodulation         : 0.20
% 5.32/2.01  BG Simplification    : 0.03
% 5.32/2.01  Subsumption          : 0.12
% 5.32/2.01  Abstraction          : 0.03
% 5.32/2.01  MUC search           : 0.00
% 5.32/2.01  Cooper               : 0.00
% 5.32/2.01  Total                : 1.24
% 5.32/2.01  Index Insertion      : 0.00
% 5.32/2.01  Index Deletion       : 0.00
% 5.32/2.01  Index Matching       : 0.00
% 5.32/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
