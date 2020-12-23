%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:31 EST 2020

% Result     : Theorem 4.47s
% Output     : CNFRefutation 4.68s
% Verified   : 
% Statistics : Number of formulae       :  216 (1509 expanded)
%              Number of leaves         :   38 ( 500 expanded)
%              Depth                    :   14
%              Number of atoms          :  365 (3580 expanded)
%              Number of equality atoms :  100 ( 706 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_153,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_28,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_47,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_126,axiom,(
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

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_136,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(c_66,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_1853,plain,(
    ! [C_233,B_234,A_235] :
      ( v1_xboole_0(C_233)
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(B_234,A_235)))
      | ~ v1_xboole_0(A_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1875,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_1853])).

tff(c_1876,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1875])).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_103,plain,(
    ! [B_41,A_42] :
      ( ~ v1_xboole_0(B_41)
      | B_41 = A_42
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_113,plain,(
    ! [A_43] :
      ( k1_xboole_0 = A_43
      | ~ v1_xboole_0(A_43) ) ),
    inference(resolution,[status(thm)],[c_2,c_103])).

tff(c_126,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_113])).

tff(c_14,plain,(
    ! [A_5] : v1_xboole_0('#skF_2'(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_123,plain,(
    ! [A_5] : '#skF_2'(A_5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_113])).

tff(c_136,plain,(
    ! [A_5] : '#skF_2'(A_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_123])).

tff(c_16,plain,(
    ! [A_5] : m1_subset_1('#skF_2'(A_5),k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_137,plain,(
    ! [A_5] : m1_subset_1('#skF_1',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_16])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_42,plain,(
    ! [A_33] :
      ( v1_funct_2(k1_xboole_0,A_33,k1_xboole_0)
      | k1_xboole_0 = A_33
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_33,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_73,plain,(
    ! [A_33] :
      ( v1_funct_2(k1_xboole_0,A_33,k1_xboole_0)
      | k1_xboole_0 = A_33
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_42])).

tff(c_1843,plain,(
    ! [A_33] :
      ( v1_funct_2('#skF_1',A_33,'#skF_1')
      | A_33 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_126,c_126,c_126,c_126,c_73])).

tff(c_1824,plain,(
    ! [C_227,A_228,B_229] :
      ( v1_relat_1(C_227)
      | ~ m1_subset_1(C_227,k1_zfmisc_1(k2_zfmisc_1(A_228,B_229))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1841,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_1824])).

tff(c_70,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_64,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_62,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_1966,plain,(
    ! [A_249,B_250,C_251] :
      ( k2_relset_1(A_249,B_250,C_251) = k2_relat_1(C_251)
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_zfmisc_1(A_249,B_250))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1982,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_1966])).

tff(c_1986,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1982])).

tff(c_24,plain,(
    ! [A_8] :
      ( k1_relat_1(k2_funct_1(A_8)) = k2_relat_1(A_8)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_256,plain,(
    ! [C_63,B_64,A_65] :
      ( v1_xboole_0(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(B_64,A_65)))
      | ~ v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_274,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_256])).

tff(c_275,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_274])).

tff(c_186,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_199,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_186])).

tff(c_179,plain,(
    ! [A_50] :
      ( v1_funct_1(k2_funct_1(A_50))
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_60,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_161,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_182,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_179,c_161])).

tff(c_185,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_182])).

tff(c_201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_185])).

tff(c_202,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_204,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_202])).

tff(c_223,plain,(
    ! [C_57,A_58,B_59] :
      ( v1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_236,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_223])).

tff(c_361,plain,(
    ! [A_81,B_82,C_83] :
      ( k2_relset_1(A_81,B_82,C_83) = k2_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_374,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_361])).

tff(c_377,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_374])).

tff(c_20,plain,(
    ! [A_7] :
      ( v1_relat_1(k2_funct_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_203,plain,(
    v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_307,plain,(
    ! [A_72] :
      ( k1_relat_1(k2_funct_1(A_72)) = k2_relat_1(A_72)
      | ~ v2_funct_1(A_72)
      | ~ v1_funct_1(A_72)
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_56,plain,(
    ! [A_36] :
      ( v1_funct_2(A_36,k1_relat_1(A_36),k2_relat_1(A_36))
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_742,plain,(
    ! [A_126] :
      ( v1_funct_2(k2_funct_1(A_126),k2_relat_1(A_126),k2_relat_1(k2_funct_1(A_126)))
      | ~ v1_funct_1(k2_funct_1(A_126))
      | ~ v1_relat_1(k2_funct_1(A_126))
      | ~ v2_funct_1(A_126)
      | ~ v1_funct_1(A_126)
      | ~ v1_relat_1(A_126) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_56])).

tff(c_745,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_742])).

tff(c_753,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_70,c_64,c_203,c_745])).

tff(c_802,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_753])).

tff(c_805,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_802])).

tff(c_809,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_70,c_805])).

tff(c_811,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_753])).

tff(c_68,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_438,plain,(
    ! [A_91,B_92,C_93] :
      ( k1_relset_1(A_91,B_92,C_93) = k1_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_457,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_438])).

tff(c_52,plain,(
    ! [B_34,A_33,C_35] :
      ( k1_xboole_0 = B_34
      | k1_relset_1(A_33,B_34,C_35) = A_33
      | ~ v1_funct_2(C_35,A_33,B_34)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_711,plain,(
    ! [B_123,A_124,C_125] :
      ( B_123 = '#skF_1'
      | k1_relset_1(A_124,B_123,C_125) = A_124
      | ~ v1_funct_2(C_125,A_124,B_123)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_124,B_123))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_52])).

tff(c_730,plain,
    ( '#skF_1' = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_711])).

tff(c_740,plain,
    ( '#skF_1' = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_457,c_730])).

tff(c_741,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_740])).

tff(c_22,plain,(
    ! [A_8] :
      ( k2_relat_1(k2_funct_1(A_8)) = k1_relat_1(A_8)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_406,plain,(
    ! [A_90] :
      ( m1_subset_1(A_90,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_90),k2_relat_1(A_90))))
      | ~ v1_funct_1(A_90)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_900,plain,(
    ! [A_136] :
      ( m1_subset_1(k2_funct_1(A_136),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_136)),k1_relat_1(A_136))))
      | ~ v1_funct_1(k2_funct_1(A_136))
      | ~ v1_relat_1(k2_funct_1(A_136))
      | ~ v2_funct_1(A_136)
      | ~ v1_funct_1(A_136)
      | ~ v1_relat_1(A_136) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_406])).

tff(c_930,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_741,c_900])).

tff(c_947,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_70,c_64,c_811,c_203,c_930])).

tff(c_977,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'),'#skF_3')))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_947])).

tff(c_994,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_70,c_64,c_377,c_977])).

tff(c_996,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_204,c_994])).

tff(c_997,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_740])).

tff(c_1030,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_997,c_4])).

tff(c_1032,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_275,c_1030])).

tff(c_1034,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_274])).

tff(c_112,plain,(
    ! [A_42] :
      ( A_42 = '#skF_1'
      | ~ v1_xboole_0(A_42) ) ),
    inference(resolution,[status(thm)],[c_4,c_103])).

tff(c_1047,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1034,c_112])).

tff(c_1071,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1047,c_137])).

tff(c_235,plain,(
    v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_137,c_223])).

tff(c_1068,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1047,c_235])).

tff(c_1033,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_274])).

tff(c_1040,plain,(
    '#skF_5' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1033,c_112])).

tff(c_1057,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1040,c_70])).

tff(c_1086,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1047,c_1057])).

tff(c_1056,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1040,c_64])).

tff(c_1081,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1047,c_1056])).

tff(c_1052,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1040,c_203])).

tff(c_1100,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1047,c_1052])).

tff(c_1270,plain,(
    ! [A_162,B_163,C_164] :
      ( k2_relset_1(A_162,B_163,C_164) = k2_relat_1(C_164)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1282,plain,(
    ! [A_165,B_166] : k2_relset_1(A_165,B_166,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1071,c_1270])).

tff(c_1054,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1040,c_62])).

tff(c_1158,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1047,c_1054])).

tff(c_1286,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1282,c_1158])).

tff(c_1361,plain,(
    ! [A_182] :
      ( m1_subset_1(A_182,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_182),k2_relat_1(A_182))))
      | ~ v1_funct_1(A_182)
      | ~ v1_relat_1(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_28,plain,(
    ! [C_15,A_12,B_13] :
      ( v1_xboole_0(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13)))
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1397,plain,(
    ! [A_183] :
      ( v1_xboole_0(A_183)
      | ~ v1_xboole_0(k1_relat_1(A_183))
      | ~ v1_funct_1(A_183)
      | ~ v1_relat_1(A_183) ) ),
    inference(resolution,[status(thm)],[c_1361,c_28])).

tff(c_1757,plain,(
    ! [A_221] :
      ( v1_xboole_0(k2_funct_1(A_221))
      | ~ v1_xboole_0(k2_relat_1(A_221))
      | ~ v1_funct_1(k2_funct_1(A_221))
      | ~ v1_relat_1(k2_funct_1(A_221))
      | ~ v2_funct_1(A_221)
      | ~ v1_funct_1(A_221)
      | ~ v1_relat_1(A_221) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1397])).

tff(c_1760,plain,
    ( v1_xboole_0(k2_funct_1('#skF_4'))
    | ~ v1_xboole_0('#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1286,c_1757])).

tff(c_1765,plain,
    ( v1_xboole_0(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1068,c_1086,c_1081,c_1100,c_1034,c_1760])).

tff(c_1766,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1765])).

tff(c_1769,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_1766])).

tff(c_1773,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1068,c_1086,c_1769])).

tff(c_1774,plain,(
    v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1765])).

tff(c_1072,plain,(
    ! [A_42] :
      ( A_42 = '#skF_4'
      | ~ v1_xboole_0(A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1047,c_112])).

tff(c_1781,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1774,c_1072])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_128,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_126,c_12])).

tff(c_1069,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1047,c_1047,c_128])).

tff(c_1051,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1040,c_204])).

tff(c_1163,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1069,c_1047,c_1051])).

tff(c_1785,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1781,c_1163])).

tff(c_1791,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1071,c_1785])).

tff(c_1792,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_1793,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_2051,plain,(
    ! [A_259,B_260,C_261] :
      ( k1_relset_1(A_259,B_260,C_261) = k1_relat_1(C_261)
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k2_zfmisc_1(A_259,B_260))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2072,plain,(
    k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) = k1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1793,c_2051])).

tff(c_48,plain,(
    ! [B_34,C_35,A_33] :
      ( k1_xboole_0 = B_34
      | v1_funct_2(C_35,A_33,B_34)
      | k1_relset_1(A_33,B_34,C_35) != A_33
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2239,plain,(
    ! [B_279,C_280,A_281] :
      ( B_279 = '#skF_1'
      | v1_funct_2(C_280,A_281,B_279)
      | k1_relset_1(A_281,B_279,C_280) != A_281
      | ~ m1_subset_1(C_280,k1_zfmisc_1(k2_zfmisc_1(A_281,B_279))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_48])).

tff(c_2248,plain,
    ( '#skF_3' = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_1793,c_2239])).

tff(c_2267,plain,
    ( '#skF_3' = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2072,c_2248])).

tff(c_2268,plain,
    ( '#skF_3' = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_1792,c_2267])).

tff(c_2274,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2268])).

tff(c_2277,plain,
    ( k2_relat_1('#skF_5') != '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2274])).

tff(c_2280,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1841,c_70,c_64,c_1986,c_2277])).

tff(c_2281,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2268])).

tff(c_1870,plain,
    ( v1_xboole_0(k2_funct_1('#skF_5'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1793,c_1853])).

tff(c_1877,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1870])).

tff(c_2286,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2281,c_1877])).

tff(c_2294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2286])).

tff(c_2295,plain,(
    v1_xboole_0(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1870])).

tff(c_2337,plain,(
    k2_funct_1('#skF_5') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2295,c_112])).

tff(c_2296,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1870])).

tff(c_2302,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2296,c_112])).

tff(c_2306,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2302,c_1792])).

tff(c_2365,plain,(
    ~ v1_funct_2('#skF_1','#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2337,c_2306])).

tff(c_2369,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1843,c_2365])).

tff(c_2386,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2369,c_4])).

tff(c_2388,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1876,c_2386])).

tff(c_2390,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1875])).

tff(c_2426,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2390,c_112])).

tff(c_1840,plain,(
    v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_137,c_1824])).

tff(c_2451,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2426,c_1840])).

tff(c_2389,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1875])).

tff(c_2419,plain,(
    '#skF_5' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2389,c_112])).

tff(c_2438,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2419,c_70])).

tff(c_2446,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2426,c_2438])).

tff(c_2437,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2419,c_64])).

tff(c_2447,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2426,c_2437])).

tff(c_2448,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2426,c_2419])).

tff(c_2391,plain,(
    ! [C_285,A_286,B_287] :
      ( v1_xboole_0(C_285)
      | ~ m1_subset_1(C_285,k1_zfmisc_1(k2_zfmisc_1(A_286,B_287)))
      | ~ v1_xboole_0(A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2408,plain,
    ( v1_xboole_0(k2_funct_1('#skF_5'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1793,c_2391])).

tff(c_2579,plain,(
    v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2390,c_2448,c_2408])).

tff(c_6,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2420,plain,(
    ! [A_1] :
      ( A_1 = '#skF_5'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_2389,c_6])).

tff(c_2495,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2448,c_2420])).

tff(c_2585,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2579,c_2495])).

tff(c_2596,plain,
    ( k2_relat_1('#skF_4') = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2585,c_22])).

tff(c_2606,plain,(
    k2_relat_1('#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2451,c_2446,c_2447,c_2596])).

tff(c_2455,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2426,c_137])).

tff(c_2779,plain,(
    ! [A_321,B_322,C_323] :
      ( k2_relset_1(A_321,B_322,C_323) = k2_relat_1(C_323)
      | ~ m1_subset_1(C_323,k1_zfmisc_1(k2_zfmisc_1(A_321,B_322))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2792,plain,(
    ! [A_321,B_322] : k2_relset_1(A_321,B_322,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2455,c_2779])).

tff(c_2796,plain,(
    ! [A_324,B_325] : k2_relset_1(A_324,B_325,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2606,c_2792])).

tff(c_2435,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2419,c_62])).

tff(c_2640,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2426,c_2435])).

tff(c_2800,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2796,c_2640])).

tff(c_2696,plain,(
    ! [A_307,B_308,C_309] :
      ( k1_relset_1(A_307,B_308,C_309) = k1_relat_1(C_309)
      | ~ m1_subset_1(C_309,k1_zfmisc_1(k2_zfmisc_1(A_307,B_308))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2707,plain,(
    ! [A_307,B_308] : k1_relset_1(A_307,B_308,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2455,c_2696])).

tff(c_2808,plain,(
    ! [A_307,B_308] : k1_relset_1(A_307,B_308,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2800,c_2707])).

tff(c_2458,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2426,c_126])).

tff(c_46,plain,(
    ! [C_35,B_34] :
      ( v1_funct_2(C_35,k1_xboole_0,B_34)
      | k1_relset_1(k1_xboole_0,B_34,C_35) != k1_xboole_0
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_72,plain,(
    ! [C_35,B_34] :
      ( v1_funct_2(C_35,k1_xboole_0,B_34)
      | k1_relset_1(k1_xboole_0,B_34,C_35) != k1_xboole_0
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_46])).

tff(c_2868,plain,(
    ! [C_328,B_329] :
      ( v1_funct_2(C_328,'#skF_4',B_329)
      | k1_relset_1('#skF_4',B_329,C_328) != '#skF_4'
      | ~ m1_subset_1(C_328,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2458,c_2458,c_2458,c_2458,c_72])).

tff(c_2872,plain,(
    ! [B_329] :
      ( v1_funct_2('#skF_4','#skF_4',B_329)
      | k1_relset_1('#skF_4',B_329,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_2455,c_2868])).

tff(c_2881,plain,(
    ! [B_329] : v1_funct_2('#skF_4','#skF_4',B_329) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2808,c_2872])).

tff(c_2432,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2419,c_1792])).

tff(c_2622,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2585,c_2426,c_2432])).

tff(c_2885,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2881,c_2622])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:15:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.47/1.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.60/1.82  
% 4.60/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.60/1.82  %$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4
% 4.60/1.82  
% 4.60/1.82  %Foreground sorts:
% 4.60/1.82  
% 4.60/1.82  
% 4.60/1.82  %Background operators:
% 4.60/1.82  
% 4.60/1.82  
% 4.60/1.82  %Foreground operators:
% 4.60/1.82  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.60/1.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.60/1.82  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.60/1.82  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.60/1.82  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.60/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.60/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.60/1.82  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.60/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.60/1.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.60/1.82  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.60/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.60/1.82  tff('#skF_1', type, '#skF_1': $i).
% 4.60/1.82  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.60/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.60/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.60/1.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.60/1.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.60/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.60/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.60/1.82  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.60/1.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.60/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.60/1.82  
% 4.68/1.87  tff(f_153, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 4.68/1.87  tff(f_83, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 4.68/1.87  tff(f_28, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 4.68/1.87  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.68/1.87  tff(f_36, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 4.68/1.87  tff(f_47, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_subset_1)).
% 4.68/1.87  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.68/1.87  tff(f_126, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.68/1.87  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.68/1.87  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.68/1.87  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 4.68/1.87  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 4.68/1.87  tff(f_136, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 4.68/1.87  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.68/1.87  tff(f_76, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 4.68/1.87  tff(c_66, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.68/1.87  tff(c_1853, plain, (![C_233, B_234, A_235]: (v1_xboole_0(C_233) | ~m1_subset_1(C_233, k1_zfmisc_1(k2_zfmisc_1(B_234, A_235))) | ~v1_xboole_0(A_235))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.68/1.87  tff(c_1875, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_66, c_1853])).
% 4.68/1.87  tff(c_1876, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_1875])).
% 4.68/1.87  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_28])).
% 4.68/1.87  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.68/1.87  tff(c_103, plain, (![B_41, A_42]: (~v1_xboole_0(B_41) | B_41=A_42 | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.68/1.87  tff(c_113, plain, (![A_43]: (k1_xboole_0=A_43 | ~v1_xboole_0(A_43))), inference(resolution, [status(thm)], [c_2, c_103])).
% 4.68/1.87  tff(c_126, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_113])).
% 4.68/1.87  tff(c_14, plain, (![A_5]: (v1_xboole_0('#skF_2'(A_5)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.68/1.87  tff(c_123, plain, (![A_5]: ('#skF_2'(A_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_113])).
% 4.68/1.87  tff(c_136, plain, (![A_5]: ('#skF_2'(A_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_123])).
% 4.68/1.87  tff(c_16, plain, (![A_5]: (m1_subset_1('#skF_2'(A_5), k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.68/1.87  tff(c_137, plain, (![A_5]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_16])).
% 4.68/1.87  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.68/1.87  tff(c_42, plain, (![A_33]: (v1_funct_2(k1_xboole_0, A_33, k1_xboole_0) | k1_xboole_0=A_33 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_33, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.68/1.87  tff(c_73, plain, (![A_33]: (v1_funct_2(k1_xboole_0, A_33, k1_xboole_0) | k1_xboole_0=A_33 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_42])).
% 4.68/1.87  tff(c_1843, plain, (![A_33]: (v1_funct_2('#skF_1', A_33, '#skF_1') | A_33='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_126, c_126, c_126, c_126, c_73])).
% 4.68/1.87  tff(c_1824, plain, (![C_227, A_228, B_229]: (v1_relat_1(C_227) | ~m1_subset_1(C_227, k1_zfmisc_1(k2_zfmisc_1(A_228, B_229))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.68/1.87  tff(c_1841, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_1824])).
% 4.68/1.87  tff(c_70, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.68/1.87  tff(c_64, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.68/1.87  tff(c_62, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.68/1.87  tff(c_1966, plain, (![A_249, B_250, C_251]: (k2_relset_1(A_249, B_250, C_251)=k2_relat_1(C_251) | ~m1_subset_1(C_251, k1_zfmisc_1(k2_zfmisc_1(A_249, B_250))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.68/1.87  tff(c_1982, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_1966])).
% 4.68/1.87  tff(c_1986, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1982])).
% 4.68/1.87  tff(c_24, plain, (![A_8]: (k1_relat_1(k2_funct_1(A_8))=k2_relat_1(A_8) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.68/1.87  tff(c_256, plain, (![C_63, B_64, A_65]: (v1_xboole_0(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(B_64, A_65))) | ~v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.68/1.87  tff(c_274, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_66, c_256])).
% 4.68/1.87  tff(c_275, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_274])).
% 4.68/1.87  tff(c_186, plain, (![C_51, A_52, B_53]: (v1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.68/1.87  tff(c_199, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_186])).
% 4.68/1.87  tff(c_179, plain, (![A_50]: (v1_funct_1(k2_funct_1(A_50)) | ~v1_funct_1(A_50) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.68/1.87  tff(c_60, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.68/1.87  tff(c_161, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_60])).
% 4.68/1.87  tff(c_182, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_179, c_161])).
% 4.68/1.87  tff(c_185, plain, (~v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_182])).
% 4.68/1.87  tff(c_201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_199, c_185])).
% 4.68/1.87  tff(c_202, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_60])).
% 4.68/1.87  tff(c_204, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_202])).
% 4.68/1.87  tff(c_223, plain, (![C_57, A_58, B_59]: (v1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.68/1.87  tff(c_236, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_223])).
% 4.68/1.87  tff(c_361, plain, (![A_81, B_82, C_83]: (k2_relset_1(A_81, B_82, C_83)=k2_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.68/1.87  tff(c_374, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_361])).
% 4.68/1.87  tff(c_377, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_374])).
% 4.68/1.87  tff(c_20, plain, (![A_7]: (v1_relat_1(k2_funct_1(A_7)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.68/1.87  tff(c_203, plain, (v1_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_60])).
% 4.68/1.87  tff(c_307, plain, (![A_72]: (k1_relat_1(k2_funct_1(A_72))=k2_relat_1(A_72) | ~v2_funct_1(A_72) | ~v1_funct_1(A_72) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.68/1.87  tff(c_56, plain, (![A_36]: (v1_funct_2(A_36, k1_relat_1(A_36), k2_relat_1(A_36)) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.68/1.87  tff(c_742, plain, (![A_126]: (v1_funct_2(k2_funct_1(A_126), k2_relat_1(A_126), k2_relat_1(k2_funct_1(A_126))) | ~v1_funct_1(k2_funct_1(A_126)) | ~v1_relat_1(k2_funct_1(A_126)) | ~v2_funct_1(A_126) | ~v1_funct_1(A_126) | ~v1_relat_1(A_126))), inference(superposition, [status(thm), theory('equality')], [c_307, c_56])).
% 4.68/1.87  tff(c_745, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_377, c_742])).
% 4.68/1.87  tff(c_753, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_236, c_70, c_64, c_203, c_745])).
% 4.68/1.87  tff(c_802, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_753])).
% 4.68/1.87  tff(c_805, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_20, c_802])).
% 4.68/1.87  tff(c_809, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_236, c_70, c_805])).
% 4.68/1.87  tff(c_811, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_753])).
% 4.68/1.87  tff(c_68, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.68/1.87  tff(c_438, plain, (![A_91, B_92, C_93]: (k1_relset_1(A_91, B_92, C_93)=k1_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.68/1.87  tff(c_457, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_438])).
% 4.68/1.87  tff(c_52, plain, (![B_34, A_33, C_35]: (k1_xboole_0=B_34 | k1_relset_1(A_33, B_34, C_35)=A_33 | ~v1_funct_2(C_35, A_33, B_34) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.68/1.87  tff(c_711, plain, (![B_123, A_124, C_125]: (B_123='#skF_1' | k1_relset_1(A_124, B_123, C_125)=A_124 | ~v1_funct_2(C_125, A_124, B_123) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_124, B_123))))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_52])).
% 4.68/1.87  tff(c_730, plain, ('#skF_1'='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_66, c_711])).
% 4.68/1.87  tff(c_740, plain, ('#skF_1'='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_457, c_730])).
% 4.68/1.87  tff(c_741, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_740])).
% 4.68/1.87  tff(c_22, plain, (![A_8]: (k2_relat_1(k2_funct_1(A_8))=k1_relat_1(A_8) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.68/1.87  tff(c_406, plain, (![A_90]: (m1_subset_1(A_90, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_90), k2_relat_1(A_90)))) | ~v1_funct_1(A_90) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.68/1.87  tff(c_900, plain, (![A_136]: (m1_subset_1(k2_funct_1(A_136), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_136)), k1_relat_1(A_136)))) | ~v1_funct_1(k2_funct_1(A_136)) | ~v1_relat_1(k2_funct_1(A_136)) | ~v2_funct_1(A_136) | ~v1_funct_1(A_136) | ~v1_relat_1(A_136))), inference(superposition, [status(thm), theory('equality')], [c_22, c_406])).
% 4.68/1.87  tff(c_930, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_741, c_900])).
% 4.68/1.87  tff(c_947, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_236, c_70, c_64, c_811, c_203, c_930])).
% 4.68/1.87  tff(c_977, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'), '#skF_3'))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_24, c_947])).
% 4.68/1.87  tff(c_994, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_236, c_70, c_64, c_377, c_977])).
% 4.68/1.87  tff(c_996, plain, $false, inference(negUnitSimplification, [status(thm)], [c_204, c_994])).
% 4.68/1.87  tff(c_997, plain, ('#skF_1'='#skF_4'), inference(splitRight, [status(thm)], [c_740])).
% 4.68/1.87  tff(c_1030, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_997, c_4])).
% 4.68/1.87  tff(c_1032, plain, $false, inference(negUnitSimplification, [status(thm)], [c_275, c_1030])).
% 4.68/1.87  tff(c_1034, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_274])).
% 4.68/1.87  tff(c_112, plain, (![A_42]: (A_42='#skF_1' | ~v1_xboole_0(A_42))), inference(resolution, [status(thm)], [c_4, c_103])).
% 4.68/1.87  tff(c_1047, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_1034, c_112])).
% 4.68/1.87  tff(c_1071, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_1047, c_137])).
% 4.68/1.87  tff(c_235, plain, (v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_137, c_223])).
% 4.68/1.87  tff(c_1068, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1047, c_235])).
% 4.68/1.87  tff(c_1033, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_274])).
% 4.68/1.87  tff(c_1040, plain, ('#skF_5'='#skF_1'), inference(resolution, [status(thm)], [c_1033, c_112])).
% 4.68/1.87  tff(c_1057, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1040, c_70])).
% 4.68/1.87  tff(c_1086, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1047, c_1057])).
% 4.68/1.87  tff(c_1056, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1040, c_64])).
% 4.68/1.87  tff(c_1081, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1047, c_1056])).
% 4.68/1.87  tff(c_1052, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1040, c_203])).
% 4.68/1.87  tff(c_1100, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1047, c_1052])).
% 4.68/1.87  tff(c_1270, plain, (![A_162, B_163, C_164]: (k2_relset_1(A_162, B_163, C_164)=k2_relat_1(C_164) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.68/1.87  tff(c_1282, plain, (![A_165, B_166]: (k2_relset_1(A_165, B_166, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1071, c_1270])).
% 4.68/1.87  tff(c_1054, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1040, c_62])).
% 4.68/1.87  tff(c_1158, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1047, c_1054])).
% 4.68/1.87  tff(c_1286, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1282, c_1158])).
% 4.68/1.87  tff(c_1361, plain, (![A_182]: (m1_subset_1(A_182, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_182), k2_relat_1(A_182)))) | ~v1_funct_1(A_182) | ~v1_relat_1(A_182))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.68/1.87  tff(c_28, plain, (![C_15, A_12, B_13]: (v1_xboole_0(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))) | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.68/1.87  tff(c_1397, plain, (![A_183]: (v1_xboole_0(A_183) | ~v1_xboole_0(k1_relat_1(A_183)) | ~v1_funct_1(A_183) | ~v1_relat_1(A_183))), inference(resolution, [status(thm)], [c_1361, c_28])).
% 4.68/1.87  tff(c_1757, plain, (![A_221]: (v1_xboole_0(k2_funct_1(A_221)) | ~v1_xboole_0(k2_relat_1(A_221)) | ~v1_funct_1(k2_funct_1(A_221)) | ~v1_relat_1(k2_funct_1(A_221)) | ~v2_funct_1(A_221) | ~v1_funct_1(A_221) | ~v1_relat_1(A_221))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1397])).
% 4.68/1.87  tff(c_1760, plain, (v1_xboole_0(k2_funct_1('#skF_4')) | ~v1_xboole_0('#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1286, c_1757])).
% 4.68/1.87  tff(c_1765, plain, (v1_xboole_0(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1068, c_1086, c_1081, c_1100, c_1034, c_1760])).
% 4.68/1.87  tff(c_1766, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_1765])).
% 4.68/1.87  tff(c_1769, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_1766])).
% 4.68/1.87  tff(c_1773, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1068, c_1086, c_1769])).
% 4.68/1.87  tff(c_1774, plain, (v1_xboole_0(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_1765])).
% 4.68/1.87  tff(c_1072, plain, (![A_42]: (A_42='#skF_4' | ~v1_xboole_0(A_42))), inference(demodulation, [status(thm), theory('equality')], [c_1047, c_112])).
% 4.68/1.87  tff(c_1781, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_1774, c_1072])).
% 4.68/1.87  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.68/1.87  tff(c_128, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_126, c_12])).
% 4.68/1.87  tff(c_1069, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1047, c_1047, c_128])).
% 4.68/1.87  tff(c_1051, plain, (~m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1040, c_204])).
% 4.68/1.87  tff(c_1163, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1069, c_1047, c_1051])).
% 4.68/1.87  tff(c_1785, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1781, c_1163])).
% 4.68/1.87  tff(c_1791, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1071, c_1785])).
% 4.68/1.87  tff(c_1792, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_202])).
% 4.68/1.87  tff(c_1793, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_202])).
% 4.68/1.87  tff(c_2051, plain, (![A_259, B_260, C_261]: (k1_relset_1(A_259, B_260, C_261)=k1_relat_1(C_261) | ~m1_subset_1(C_261, k1_zfmisc_1(k2_zfmisc_1(A_259, B_260))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.68/1.87  tff(c_2072, plain, (k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))=k1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_1793, c_2051])).
% 4.68/1.87  tff(c_48, plain, (![B_34, C_35, A_33]: (k1_xboole_0=B_34 | v1_funct_2(C_35, A_33, B_34) | k1_relset_1(A_33, B_34, C_35)!=A_33 | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.68/1.87  tff(c_2239, plain, (![B_279, C_280, A_281]: (B_279='#skF_1' | v1_funct_2(C_280, A_281, B_279) | k1_relset_1(A_281, B_279, C_280)!=A_281 | ~m1_subset_1(C_280, k1_zfmisc_1(k2_zfmisc_1(A_281, B_279))))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_48])).
% 4.68/1.87  tff(c_2248, plain, ('#skF_3'='#skF_1' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))!='#skF_4'), inference(resolution, [status(thm)], [c_1793, c_2239])).
% 4.68/1.87  tff(c_2267, plain, ('#skF_3'='#skF_1' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2072, c_2248])).
% 4.68/1.87  tff(c_2268, plain, ('#skF_3'='#skF_1' | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_1792, c_2267])).
% 4.68/1.87  tff(c_2274, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_2268])).
% 4.68/1.87  tff(c_2277, plain, (k2_relat_1('#skF_5')!='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_24, c_2274])).
% 4.68/1.87  tff(c_2280, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1841, c_70, c_64, c_1986, c_2277])).
% 4.68/1.87  tff(c_2281, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_2268])).
% 4.68/1.87  tff(c_1870, plain, (v1_xboole_0(k2_funct_1('#skF_5')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_1793, c_1853])).
% 4.68/1.87  tff(c_1877, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_1870])).
% 4.68/1.87  tff(c_2286, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2281, c_1877])).
% 4.68/1.87  tff(c_2294, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_2286])).
% 4.68/1.87  tff(c_2295, plain, (v1_xboole_0(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_1870])).
% 4.68/1.87  tff(c_2337, plain, (k2_funct_1('#skF_5')='#skF_1'), inference(resolution, [status(thm)], [c_2295, c_112])).
% 4.68/1.87  tff(c_2296, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_1870])).
% 4.68/1.87  tff(c_2302, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_2296, c_112])).
% 4.68/1.87  tff(c_2306, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2302, c_1792])).
% 4.68/1.87  tff(c_2365, plain, (~v1_funct_2('#skF_1', '#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2337, c_2306])).
% 4.68/1.87  tff(c_2369, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_1843, c_2365])).
% 4.68/1.87  tff(c_2386, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2369, c_4])).
% 4.68/1.87  tff(c_2388, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1876, c_2386])).
% 4.68/1.87  tff(c_2390, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_1875])).
% 4.68/1.87  tff(c_2426, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_2390, c_112])).
% 4.68/1.87  tff(c_1840, plain, (v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_137, c_1824])).
% 4.68/1.87  tff(c_2451, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2426, c_1840])).
% 4.68/1.87  tff(c_2389, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_1875])).
% 4.68/1.87  tff(c_2419, plain, ('#skF_5'='#skF_1'), inference(resolution, [status(thm)], [c_2389, c_112])).
% 4.68/1.87  tff(c_2438, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2419, c_70])).
% 4.68/1.87  tff(c_2446, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2426, c_2438])).
% 4.68/1.87  tff(c_2437, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2419, c_64])).
% 4.68/1.87  tff(c_2447, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2426, c_2437])).
% 4.68/1.87  tff(c_2448, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2426, c_2419])).
% 4.68/1.87  tff(c_2391, plain, (![C_285, A_286, B_287]: (v1_xboole_0(C_285) | ~m1_subset_1(C_285, k1_zfmisc_1(k2_zfmisc_1(A_286, B_287))) | ~v1_xboole_0(A_286))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.68/1.87  tff(c_2408, plain, (v1_xboole_0(k2_funct_1('#skF_5')) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1793, c_2391])).
% 4.68/1.87  tff(c_2579, plain, (v1_xboole_0(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2390, c_2448, c_2408])).
% 4.68/1.87  tff(c_6, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.68/1.87  tff(c_2420, plain, (![A_1]: (A_1='#skF_5' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_2389, c_6])).
% 4.68/1.87  tff(c_2495, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_2448, c_2420])).
% 4.68/1.87  tff(c_2585, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_2579, c_2495])).
% 4.68/1.87  tff(c_2596, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2585, c_22])).
% 4.68/1.87  tff(c_2606, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2451, c_2446, c_2447, c_2596])).
% 4.68/1.87  tff(c_2455, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_2426, c_137])).
% 4.68/1.87  tff(c_2779, plain, (![A_321, B_322, C_323]: (k2_relset_1(A_321, B_322, C_323)=k2_relat_1(C_323) | ~m1_subset_1(C_323, k1_zfmisc_1(k2_zfmisc_1(A_321, B_322))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.68/1.87  tff(c_2792, plain, (![A_321, B_322]: (k2_relset_1(A_321, B_322, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_2455, c_2779])).
% 4.68/1.87  tff(c_2796, plain, (![A_324, B_325]: (k2_relset_1(A_324, B_325, '#skF_4')=k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2606, c_2792])).
% 4.68/1.87  tff(c_2435, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2419, c_62])).
% 4.68/1.87  tff(c_2640, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2426, c_2435])).
% 4.68/1.87  tff(c_2800, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2796, c_2640])).
% 4.68/1.87  tff(c_2696, plain, (![A_307, B_308, C_309]: (k1_relset_1(A_307, B_308, C_309)=k1_relat_1(C_309) | ~m1_subset_1(C_309, k1_zfmisc_1(k2_zfmisc_1(A_307, B_308))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.68/1.87  tff(c_2707, plain, (![A_307, B_308]: (k1_relset_1(A_307, B_308, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_2455, c_2696])).
% 4.68/1.87  tff(c_2808, plain, (![A_307, B_308]: (k1_relset_1(A_307, B_308, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2800, c_2707])).
% 4.68/1.87  tff(c_2458, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2426, c_126])).
% 4.68/1.87  tff(c_46, plain, (![C_35, B_34]: (v1_funct_2(C_35, k1_xboole_0, B_34) | k1_relset_1(k1_xboole_0, B_34, C_35)!=k1_xboole_0 | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_34))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.68/1.87  tff(c_72, plain, (![C_35, B_34]: (v1_funct_2(C_35, k1_xboole_0, B_34) | k1_relset_1(k1_xboole_0, B_34, C_35)!=k1_xboole_0 | ~m1_subset_1(C_35, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_46])).
% 4.68/1.87  tff(c_2868, plain, (![C_328, B_329]: (v1_funct_2(C_328, '#skF_4', B_329) | k1_relset_1('#skF_4', B_329, C_328)!='#skF_4' | ~m1_subset_1(C_328, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2458, c_2458, c_2458, c_2458, c_72])).
% 4.68/1.87  tff(c_2872, plain, (![B_329]: (v1_funct_2('#skF_4', '#skF_4', B_329) | k1_relset_1('#skF_4', B_329, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_2455, c_2868])).
% 4.68/1.87  tff(c_2881, plain, (![B_329]: (v1_funct_2('#skF_4', '#skF_4', B_329))), inference(demodulation, [status(thm), theory('equality')], [c_2808, c_2872])).
% 4.68/1.87  tff(c_2432, plain, (~v1_funct_2(k2_funct_1('#skF_1'), '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2419, c_1792])).
% 4.68/1.87  tff(c_2622, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2585, c_2426, c_2432])).
% 4.68/1.87  tff(c_2885, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2881, c_2622])).
% 4.68/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.68/1.87  
% 4.68/1.87  Inference rules
% 4.68/1.87  ----------------------
% 4.68/1.87  #Ref     : 0
% 4.68/1.87  #Sup     : 586
% 4.68/1.87  #Fact    : 0
% 4.68/1.87  #Define  : 0
% 4.68/1.87  #Split   : 19
% 4.68/1.87  #Chain   : 0
% 4.68/1.87  #Close   : 0
% 4.68/1.87  
% 4.68/1.87  Ordering : KBO
% 4.68/1.87  
% 4.68/1.87  Simplification rules
% 4.68/1.87  ----------------------
% 4.68/1.87  #Subsume      : 91
% 4.68/1.87  #Demod        : 691
% 4.68/1.87  #Tautology    : 319
% 4.68/1.87  #SimpNegUnit  : 8
% 4.68/1.87  #BackRed      : 140
% 4.68/1.87  
% 4.68/1.87  #Partial instantiations: 0
% 4.68/1.87  #Strategies tried      : 1
% 4.68/1.87  
% 4.68/1.87  Timing (in seconds)
% 4.68/1.87  ----------------------
% 4.68/1.88  Preprocessing        : 0.33
% 4.68/1.88  Parsing              : 0.17
% 4.68/1.88  CNF conversion       : 0.02
% 4.68/1.88  Main loop            : 0.72
% 4.68/1.88  Inferencing          : 0.26
% 4.68/1.88  Reduction            : 0.23
% 4.68/1.88  Demodulation         : 0.16
% 4.68/1.88  BG Simplification    : 0.03
% 4.68/1.88  Subsumption          : 0.12
% 4.68/1.88  Abstraction          : 0.03
% 4.68/1.88  MUC search           : 0.00
% 4.68/1.88  Cooper               : 0.00
% 4.68/1.88  Total                : 1.16
% 4.68/1.88  Index Insertion      : 0.00
% 4.68/1.88  Index Deletion       : 0.00
% 4.68/1.88  Index Matching       : 0.00
% 4.68/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
