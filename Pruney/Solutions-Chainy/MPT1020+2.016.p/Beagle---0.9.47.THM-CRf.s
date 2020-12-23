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
% DateTime   : Thu Dec  3 10:15:52 EST 2020

% Result     : Theorem 6.39s
% Output     : CNFRefutation 6.58s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 562 expanded)
%              Number of leaves         :   44 ( 206 expanded)
%              Depth                    :   13
%              Number of atoms          :  243 (1678 expanded)
%              Number of equality atoms :   57 ( 185 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_179,negated_conjecture,(
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

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_101,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_97,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_157,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_113,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_36,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_201,plain,(
    ! [A_72,B_73,D_74] :
      ( r2_relset_1(A_72,B_73,D_74,D_74)
      | ~ m1_subset_1(D_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_209,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_201])).

tff(c_142,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_xboole_0(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68)))
      | ~ v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_153,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_142])).

tff(c_155,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_68,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_66,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_62,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_60,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_58,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_100,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_112,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_100])).

tff(c_128,plain,(
    ! [C_62,B_63,A_64] :
      ( v5_relat_1(C_62,B_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_64,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_140,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_128])).

tff(c_215,plain,(
    ! [B_75,A_76] :
      ( k2_relat_1(B_75) = A_76
      | ~ v2_funct_2(B_75,A_76)
      | ~ v5_relat_1(B_75,A_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_224,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_140,c_215])).

tff(c_236,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_224])).

tff(c_240,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_236])).

tff(c_64,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_558,plain,(
    ! [C_98,B_99,A_100] :
      ( v2_funct_2(C_98,B_99)
      | ~ v3_funct_2(C_98,A_100,B_99)
      | ~ v1_funct_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_100,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_570,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_558])).

tff(c_578,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_570])).

tff(c_580,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_578])).

tff(c_581,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_236])).

tff(c_768,plain,(
    ! [A_113,B_114,C_115] :
      ( k2_relset_1(A_113,B_114,C_115) = k2_relat_1(C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_777,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_768])).

tff(c_782,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_777])).

tff(c_38,plain,(
    ! [A_32] : m1_subset_1(k6_partfun1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_208,plain,(
    ! [A_32] : r2_relset_1(A_32,A_32,k6_partfun1(A_32),k6_partfun1(A_32)) ),
    inference(resolution,[status(thm)],[c_38,c_201])).

tff(c_864,plain,(
    ! [C_117,A_118,B_119] :
      ( v2_funct_1(C_117)
      | ~ v3_funct_2(C_117,A_118,B_119)
      | ~ v1_funct_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_876,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_864])).

tff(c_884,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_876])).

tff(c_1584,plain,(
    ! [D_162,B_163,C_166,E_167,F_165,A_164] :
      ( m1_subset_1(k1_partfun1(A_164,B_163,C_166,D_162,E_167,F_165),k1_zfmisc_1(k2_zfmisc_1(A_164,D_162)))
      | ~ m1_subset_1(F_165,k1_zfmisc_1(k2_zfmisc_1(C_166,D_162)))
      | ~ v1_funct_1(F_165)
      | ~ m1_subset_1(E_167,k1_zfmisc_1(k2_zfmisc_1(A_164,B_163)))
      | ~ v1_funct_1(E_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_52,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_947,plain,(
    ! [D_126,C_127,A_128,B_129] :
      ( D_126 = C_127
      | ~ r2_relset_1(A_128,B_129,C_127,D_126)
      | ~ m1_subset_1(D_126,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129)))
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_955,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_52,c_947])).

tff(c_970,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_955])).

tff(c_1015,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_970])).

tff(c_1592,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1584,c_1015])).

tff(c_1625,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_62,c_60,c_54,c_1592])).

tff(c_1626,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_970])).

tff(c_4164,plain,(
    ! [C_238,D_239,B_240,A_241] :
      ( k2_funct_1(C_238) = D_239
      | k1_xboole_0 = B_240
      | k1_xboole_0 = A_241
      | ~ v2_funct_1(C_238)
      | ~ r2_relset_1(A_241,A_241,k1_partfun1(A_241,B_240,B_240,A_241,C_238,D_239),k6_partfun1(A_241))
      | k2_relset_1(A_241,B_240,C_238) != B_240
      | ~ m1_subset_1(D_239,k1_zfmisc_1(k2_zfmisc_1(B_240,A_241)))
      | ~ v1_funct_2(D_239,B_240,A_241)
      | ~ v1_funct_1(D_239)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_241,B_240)))
      | ~ v1_funct_2(C_238,A_241,B_240)
      | ~ v1_funct_1(C_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_4185,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1626,c_4164])).

tff(c_4193,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_62,c_60,c_58,c_54,c_782,c_208,c_884,c_4185])).

tff(c_4195,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4193])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4230,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4195,c_2])).

tff(c_4232,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_4230])).

tff(c_4233,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4193])).

tff(c_1731,plain,(
    ! [A_175,B_176] :
      ( k2_funct_2(A_175,B_176) = k2_funct_1(B_176)
      | ~ m1_subset_1(B_176,k1_zfmisc_1(k2_zfmisc_1(A_175,A_175)))
      | ~ v3_funct_2(B_176,A_175,A_175)
      | ~ v1_funct_2(B_176,A_175,A_175)
      | ~ v1_funct_1(B_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1746,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_1731])).

tff(c_1758,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_1746])).

tff(c_50,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_1763,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1758,c_50])).

tff(c_4261,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4233,c_1763])).

tff(c_4265,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_4261])).

tff(c_4267,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_89,plain,(
    ! [B_50,A_51] :
      ( ~ v1_xboole_0(B_50)
      | B_50 = A_51
      | ~ v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_92,plain,(
    ! [A_51] :
      ( k1_xboole_0 = A_51
      | ~ v1_xboole_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_2,c_89])).

tff(c_4280,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4267,c_92])).

tff(c_4266,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_4273,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4266,c_92])).

tff(c_4289,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4280,c_4273])).

tff(c_4301,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4289,c_54])).

tff(c_18,plain,(
    ! [A_17,B_18,D_20] :
      ( r2_relset_1(A_17,B_18,D_20,D_20)
      | ~ m1_subset_1(D_20,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4429,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_4301,c_18])).

tff(c_4304,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4289,c_60])).

tff(c_4302,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4289,c_58])).

tff(c_56,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_4303,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4289,c_56])).

tff(c_4360,plain,(
    ! [A_247] :
      ( v1_xboole_0(k6_partfun1(A_247))
      | ~ v1_xboole_0(A_247) ) ),
    inference(resolution,[status(thm)],[c_38,c_142])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4274,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4266,c_4])).

tff(c_4315,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4289,c_4274])).

tff(c_4368,plain,(
    ! [A_248] :
      ( k6_partfun1(A_248) = '#skF_1'
      | ~ v1_xboole_0(A_248) ) ),
    inference(resolution,[status(thm)],[c_4360,c_4315])).

tff(c_4376,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4267,c_4368])).

tff(c_42,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_6,plain,(
    ! [A_3] : k2_funct_1(k6_relat_1(A_3)) = k6_relat_1(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_69,plain,(
    ! [A_3] : k2_funct_1(k6_partfun1(A_3)) = k6_partfun1(A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_6])).

tff(c_4394,plain,(
    k6_partfun1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4376,c_69])).

tff(c_4405,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4376,c_4394])).

tff(c_6254,plain,(
    ! [A_330,B_331] :
      ( k2_funct_2(A_330,B_331) = k2_funct_1(B_331)
      | ~ m1_subset_1(B_331,k1_zfmisc_1(k2_zfmisc_1(A_330,A_330)))
      | ~ v3_funct_2(B_331,A_330,A_330)
      | ~ v1_funct_2(B_331,A_330,A_330)
      | ~ v1_funct_1(B_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_6260,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4301,c_6254])).

tff(c_6269,plain,(
    k2_funct_2('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4304,c_4302,c_4303,c_4405,c_6260])).

tff(c_154,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_142])).

tff(c_4311,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4267,c_154])).

tff(c_4316,plain,(
    ! [A_244] :
      ( A_244 = '#skF_1'
      | ~ v1_xboole_0(A_244) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4289,c_4274])).

tff(c_4323,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4311,c_4316])).

tff(c_4300,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4289,c_50])).

tff(c_4953,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4323,c_4300])).

tff(c_6272,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6269,c_4953])).

tff(c_6275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4429,c_6272])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:51:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.39/2.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.58/2.30  
% 6.58/2.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.58/2.30  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.58/2.30  
% 6.58/2.30  %Foreground sorts:
% 6.58/2.30  
% 6.58/2.30  
% 6.58/2.30  %Background operators:
% 6.58/2.30  
% 6.58/2.30  
% 6.58/2.30  %Foreground operators:
% 6.58/2.30  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.58/2.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.58/2.30  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.58/2.30  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.58/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.58/2.30  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.58/2.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.58/2.30  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 6.58/2.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.58/2.30  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.58/2.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.58/2.30  tff('#skF_2', type, '#skF_2': $i).
% 6.58/2.30  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.58/2.30  tff('#skF_3', type, '#skF_3': $i).
% 6.58/2.30  tff('#skF_1', type, '#skF_1': $i).
% 6.58/2.30  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.58/2.30  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.58/2.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.58/2.30  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.58/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.58/2.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.58/2.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.58/2.30  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.58/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.58/2.30  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.58/2.30  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 6.58/2.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.58/2.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.58/2.30  
% 6.58/2.32  tff(f_179, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_2)).
% 6.58/2.32  tff(f_65, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.58/2.32  tff(f_53, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 6.58/2.32  tff(f_40, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.58/2.32  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.58/2.32  tff(f_85, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 6.58/2.32  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 6.58/2.32  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.58/2.32  tff(f_101, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.58/2.32  tff(f_97, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.58/2.32  tff(f_157, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 6.58/2.32  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.58/2.32  tff(f_111, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 6.58/2.32  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 6.58/2.32  tff(f_113, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.58/2.32  tff(f_36, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 6.58/2.32  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 6.58/2.32  tff(c_201, plain, (![A_72, B_73, D_74]: (r2_relset_1(A_72, B_73, D_74, D_74) | ~m1_subset_1(D_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.58/2.32  tff(c_209, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_201])).
% 6.58/2.32  tff(c_142, plain, (![C_66, A_67, B_68]: (v1_xboole_0(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))) | ~v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.58/2.32  tff(c_153, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_54, c_142])).
% 6.58/2.32  tff(c_155, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_153])).
% 6.58/2.32  tff(c_68, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 6.58/2.32  tff(c_66, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 6.58/2.32  tff(c_62, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 6.58/2.32  tff(c_60, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_179])).
% 6.58/2.32  tff(c_58, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 6.58/2.32  tff(c_100, plain, (![C_54, A_55, B_56]: (v1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.58/2.32  tff(c_112, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_62, c_100])).
% 6.58/2.32  tff(c_128, plain, (![C_62, B_63, A_64]: (v5_relat_1(C_62, B_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_64, B_63))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.58/2.32  tff(c_140, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_128])).
% 6.58/2.32  tff(c_215, plain, (![B_75, A_76]: (k2_relat_1(B_75)=A_76 | ~v2_funct_2(B_75, A_76) | ~v5_relat_1(B_75, A_76) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.58/2.32  tff(c_224, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_140, c_215])).
% 6.58/2.32  tff(c_236, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_224])).
% 6.58/2.32  tff(c_240, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_236])).
% 6.58/2.32  tff(c_64, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 6.58/2.32  tff(c_558, plain, (![C_98, B_99, A_100]: (v2_funct_2(C_98, B_99) | ~v3_funct_2(C_98, A_100, B_99) | ~v1_funct_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_100, B_99))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.58/2.32  tff(c_570, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_62, c_558])).
% 6.58/2.32  tff(c_578, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_570])).
% 6.58/2.32  tff(c_580, plain, $false, inference(negUnitSimplification, [status(thm)], [c_240, c_578])).
% 6.58/2.32  tff(c_581, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_236])).
% 6.58/2.32  tff(c_768, plain, (![A_113, B_114, C_115]: (k2_relset_1(A_113, B_114, C_115)=k2_relat_1(C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.58/2.32  tff(c_777, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_62, c_768])).
% 6.58/2.32  tff(c_782, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_581, c_777])).
% 6.58/2.32  tff(c_38, plain, (![A_32]: (m1_subset_1(k6_partfun1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.58/2.32  tff(c_208, plain, (![A_32]: (r2_relset_1(A_32, A_32, k6_partfun1(A_32), k6_partfun1(A_32)))), inference(resolution, [status(thm)], [c_38, c_201])).
% 6.58/2.32  tff(c_864, plain, (![C_117, A_118, B_119]: (v2_funct_1(C_117) | ~v3_funct_2(C_117, A_118, B_119) | ~v1_funct_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.58/2.32  tff(c_876, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_62, c_864])).
% 6.58/2.32  tff(c_884, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_876])).
% 6.58/2.32  tff(c_1584, plain, (![D_162, B_163, C_166, E_167, F_165, A_164]: (m1_subset_1(k1_partfun1(A_164, B_163, C_166, D_162, E_167, F_165), k1_zfmisc_1(k2_zfmisc_1(A_164, D_162))) | ~m1_subset_1(F_165, k1_zfmisc_1(k2_zfmisc_1(C_166, D_162))) | ~v1_funct_1(F_165) | ~m1_subset_1(E_167, k1_zfmisc_1(k2_zfmisc_1(A_164, B_163))) | ~v1_funct_1(E_167))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.58/2.32  tff(c_52, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 6.58/2.32  tff(c_947, plain, (![D_126, C_127, A_128, B_129]: (D_126=C_127 | ~r2_relset_1(A_128, B_129, C_127, D_126) | ~m1_subset_1(D_126, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.58/2.32  tff(c_955, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_52, c_947])).
% 6.58/2.32  tff(c_970, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_955])).
% 6.58/2.32  tff(c_1015, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_970])).
% 6.58/2.32  tff(c_1592, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_1584, c_1015])).
% 6.58/2.32  tff(c_1625, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_62, c_60, c_54, c_1592])).
% 6.58/2.32  tff(c_1626, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_970])).
% 6.58/2.32  tff(c_4164, plain, (![C_238, D_239, B_240, A_241]: (k2_funct_1(C_238)=D_239 | k1_xboole_0=B_240 | k1_xboole_0=A_241 | ~v2_funct_1(C_238) | ~r2_relset_1(A_241, A_241, k1_partfun1(A_241, B_240, B_240, A_241, C_238, D_239), k6_partfun1(A_241)) | k2_relset_1(A_241, B_240, C_238)!=B_240 | ~m1_subset_1(D_239, k1_zfmisc_1(k2_zfmisc_1(B_240, A_241))) | ~v1_funct_2(D_239, B_240, A_241) | ~v1_funct_1(D_239) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_241, B_240))) | ~v1_funct_2(C_238, A_241, B_240) | ~v1_funct_1(C_238))), inference(cnfTransformation, [status(thm)], [f_157])).
% 6.58/2.32  tff(c_4185, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1626, c_4164])).
% 6.58/2.32  tff(c_4193, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_62, c_60, c_58, c_54, c_782, c_208, c_884, c_4185])).
% 6.58/2.32  tff(c_4195, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_4193])).
% 6.58/2.32  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.58/2.32  tff(c_4230, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4195, c_2])).
% 6.58/2.32  tff(c_4232, plain, $false, inference(negUnitSimplification, [status(thm)], [c_155, c_4230])).
% 6.58/2.32  tff(c_4233, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_4193])).
% 6.58/2.32  tff(c_1731, plain, (![A_175, B_176]: (k2_funct_2(A_175, B_176)=k2_funct_1(B_176) | ~m1_subset_1(B_176, k1_zfmisc_1(k2_zfmisc_1(A_175, A_175))) | ~v3_funct_2(B_176, A_175, A_175) | ~v1_funct_2(B_176, A_175, A_175) | ~v1_funct_1(B_176))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.58/2.32  tff(c_1746, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_62, c_1731])).
% 6.58/2.32  tff(c_1758, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_1746])).
% 6.58/2.32  tff(c_50, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 6.58/2.32  tff(c_1763, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1758, c_50])).
% 6.58/2.32  tff(c_4261, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4233, c_1763])).
% 6.58/2.32  tff(c_4265, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_209, c_4261])).
% 6.58/2.32  tff(c_4267, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_153])).
% 6.58/2.32  tff(c_89, plain, (![B_50, A_51]: (~v1_xboole_0(B_50) | B_50=A_51 | ~v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.58/2.32  tff(c_92, plain, (![A_51]: (k1_xboole_0=A_51 | ~v1_xboole_0(A_51))), inference(resolution, [status(thm)], [c_2, c_89])).
% 6.58/2.32  tff(c_4280, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4267, c_92])).
% 6.58/2.32  tff(c_4266, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_153])).
% 6.58/2.32  tff(c_4273, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_4266, c_92])).
% 6.58/2.32  tff(c_4289, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4280, c_4273])).
% 6.58/2.32  tff(c_4301, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4289, c_54])).
% 6.58/2.32  tff(c_18, plain, (![A_17, B_18, D_20]: (r2_relset_1(A_17, B_18, D_20, D_20) | ~m1_subset_1(D_20, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.58/2.32  tff(c_4429, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_4301, c_18])).
% 6.58/2.32  tff(c_4304, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4289, c_60])).
% 6.58/2.32  tff(c_4302, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4289, c_58])).
% 6.58/2.32  tff(c_56, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 6.58/2.32  tff(c_4303, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4289, c_56])).
% 6.58/2.32  tff(c_4360, plain, (![A_247]: (v1_xboole_0(k6_partfun1(A_247)) | ~v1_xboole_0(A_247))), inference(resolution, [status(thm)], [c_38, c_142])).
% 6.58/2.32  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.58/2.32  tff(c_4274, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4266, c_4])).
% 6.58/2.32  tff(c_4315, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_4289, c_4274])).
% 6.58/2.32  tff(c_4368, plain, (![A_248]: (k6_partfun1(A_248)='#skF_1' | ~v1_xboole_0(A_248))), inference(resolution, [status(thm)], [c_4360, c_4315])).
% 6.58/2.32  tff(c_4376, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_4267, c_4368])).
% 6.58/2.32  tff(c_42, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.58/2.32  tff(c_6, plain, (![A_3]: (k2_funct_1(k6_relat_1(A_3))=k6_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.58/2.32  tff(c_69, plain, (![A_3]: (k2_funct_1(k6_partfun1(A_3))=k6_partfun1(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_6])).
% 6.58/2.32  tff(c_4394, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4376, c_69])).
% 6.58/2.32  tff(c_4405, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4376, c_4394])).
% 6.58/2.32  tff(c_6254, plain, (![A_330, B_331]: (k2_funct_2(A_330, B_331)=k2_funct_1(B_331) | ~m1_subset_1(B_331, k1_zfmisc_1(k2_zfmisc_1(A_330, A_330))) | ~v3_funct_2(B_331, A_330, A_330) | ~v1_funct_2(B_331, A_330, A_330) | ~v1_funct_1(B_331))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.58/2.32  tff(c_6260, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_4301, c_6254])).
% 6.58/2.32  tff(c_6269, plain, (k2_funct_2('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4304, c_4302, c_4303, c_4405, c_6260])).
% 6.58/2.32  tff(c_154, plain, (v1_xboole_0('#skF_2') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_62, c_142])).
% 6.58/2.32  tff(c_4311, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4267, c_154])).
% 6.58/2.32  tff(c_4316, plain, (![A_244]: (A_244='#skF_1' | ~v1_xboole_0(A_244))), inference(demodulation, [status(thm), theory('equality')], [c_4289, c_4274])).
% 6.58/2.32  tff(c_4323, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_4311, c_4316])).
% 6.58/2.32  tff(c_4300, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4289, c_50])).
% 6.58/2.32  tff(c_4953, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4323, c_4300])).
% 6.58/2.32  tff(c_6272, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6269, c_4953])).
% 6.58/2.32  tff(c_6275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4429, c_6272])).
% 6.58/2.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.58/2.32  
% 6.58/2.32  Inference rules
% 6.58/2.32  ----------------------
% 6.58/2.32  #Ref     : 0
% 6.58/2.32  #Sup     : 1662
% 6.58/2.32  #Fact    : 0
% 6.58/2.32  #Define  : 0
% 6.58/2.32  #Split   : 16
% 6.58/2.32  #Chain   : 0
% 6.58/2.32  #Close   : 0
% 6.58/2.32  
% 6.58/2.32  Ordering : KBO
% 6.58/2.32  
% 6.58/2.32  Simplification rules
% 6.58/2.32  ----------------------
% 6.58/2.32  #Subsume      : 412
% 6.58/2.32  #Demod        : 1026
% 6.58/2.32  #Tautology    : 461
% 6.58/2.32  #SimpNegUnit  : 8
% 6.58/2.32  #BackRed      : 62
% 6.58/2.32  
% 6.58/2.32  #Partial instantiations: 0
% 6.58/2.32  #Strategies tried      : 1
% 6.58/2.32  
% 6.58/2.32  Timing (in seconds)
% 6.58/2.32  ----------------------
% 6.58/2.33  Preprocessing        : 0.38
% 6.58/2.33  Parsing              : 0.21
% 6.58/2.33  CNF conversion       : 0.02
% 6.58/2.33  Main loop            : 1.11
% 6.58/2.33  Inferencing          : 0.34
% 6.58/2.33  Reduction            : 0.38
% 6.58/2.33  Demodulation         : 0.28
% 6.58/2.33  BG Simplification    : 0.04
% 6.58/2.33  Subsumption          : 0.26
% 6.58/2.33  Abstraction          : 0.05
% 6.58/2.33  MUC search           : 0.00
% 6.58/2.33  Cooper               : 0.00
% 6.58/2.33  Total                : 1.54
% 6.58/2.33  Index Insertion      : 0.00
% 6.58/2.33  Index Deletion       : 0.00
% 6.58/2.33  Index Matching       : 0.00
% 6.58/2.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
