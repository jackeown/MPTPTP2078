%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:33 EST 2020

% Result     : Theorem 11.32s
% Output     : CNFRefutation 11.60s
% Verified   : 
% Statistics : Number of formulae       :  267 (2403 expanded)
%              Number of leaves         :   40 ( 783 expanded)
%              Depth                    :   14
%              Number of atoms          :  483 (6111 expanded)
%              Number of equality atoms :  135 (1233 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_166,negated_conjecture,(
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

tff(f_99,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_135,axiom,(
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

tff(f_88,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_149,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_139,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_74,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_278,plain,(
    ! [C_67,B_68,A_69] :
      ( v1_xboole_0(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(B_68,A_69)))
      | ~ v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_296,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_278])).

tff(c_301,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_296])).

tff(c_78,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_20,plain,(
    ! [A_15] :
      ( v1_funct_1(k2_funct_1(A_15))
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_68,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_134,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_137,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_134])).

tff(c_140,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_137])).

tff(c_142,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_148,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_142])).

tff(c_161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_148])).

tff(c_162,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_401,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_165,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_181,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_165])).

tff(c_72,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_76,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1197,plain,(
    ! [A_117,B_118,C_119] :
      ( k1_relset_1(A_117,B_118,C_119) = k1_relat_1(C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1223,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_1197])).

tff(c_1605,plain,(
    ! [B_151,A_152,C_153] :
      ( k1_xboole_0 = B_151
      | k1_relset_1(A_152,B_151,C_153) = A_152
      | ~ v1_funct_2(C_153,A_152,B_151)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_152,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1617,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_1605])).

tff(c_1636,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1223,c_1617])).

tff(c_1640,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1636])).

tff(c_30,plain,(
    ! [A_16] :
      ( k2_relat_1(k2_funct_1(A_16)) = k1_relat_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_22,plain,(
    ! [A_15] :
      ( v1_relat_1(k2_funct_1(A_15))
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_163,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_70,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_924,plain,(
    ! [A_101,B_102,C_103] :
      ( k2_relset_1(A_101,B_102,C_103) = k2_relat_1(C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_933,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_924])).

tff(c_947,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_933])).

tff(c_445,plain,(
    ! [A_88] :
      ( k1_relat_1(k2_funct_1(A_88)) = k2_relat_1(A_88)
      | ~ v2_funct_1(A_88)
      | ~ v1_funct_1(A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_64,plain,(
    ! [A_37] :
      ( v1_funct_2(A_37,k1_relat_1(A_37),k2_relat_1(A_37))
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_5911,plain,(
    ! [A_217] :
      ( v1_funct_2(k2_funct_1(A_217),k2_relat_1(A_217),k2_relat_1(k2_funct_1(A_217)))
      | ~ v1_funct_1(k2_funct_1(A_217))
      | ~ v1_relat_1(k2_funct_1(A_217))
      | ~ v2_funct_1(A_217)
      | ~ v1_funct_1(A_217)
      | ~ v1_relat_1(A_217) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_445,c_64])).

tff(c_5923,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_947,c_5911])).

tff(c_5937,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_78,c_72,c_163,c_5923])).

tff(c_5938,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5937])).

tff(c_5941,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_5938])).

tff(c_5945,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_78,c_5941])).

tff(c_5947,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_5937])).

tff(c_32,plain,(
    ! [A_16] :
      ( k1_relat_1(k2_funct_1(A_16)) = k2_relat_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_690,plain,(
    ! [A_97] :
      ( m1_subset_1(A_97,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_97),k2_relat_1(A_97))))
      | ~ v1_funct_1(A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_7858,plain,(
    ! [A_231] :
      ( m1_subset_1(k2_funct_1(A_231),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_231),k2_relat_1(k2_funct_1(A_231)))))
      | ~ v1_funct_1(k2_funct_1(A_231))
      | ~ v1_relat_1(k2_funct_1(A_231))
      | ~ v2_funct_1(A_231)
      | ~ v1_funct_1(A_231)
      | ~ v1_relat_1(A_231) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_690])).

tff(c_7902,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_947,c_7858])).

tff(c_7928,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_78,c_72,c_5947,c_163,c_7902])).

tff(c_7960,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_4'))))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_7928])).

tff(c_7979,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_78,c_72,c_1640,c_7960])).

tff(c_7981,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_401,c_7979])).

tff(c_7982,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1636])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_8014,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7982,c_2])).

tff(c_8016,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_301,c_8014])).

tff(c_8018,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_36,plain,(
    ! [C_23,B_21,A_20] :
      ( v1_xboole_0(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(B_21,A_20)))
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_8030,plain,
    ( v1_xboole_0(k2_funct_1('#skF_4'))
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_8018,c_36])).

tff(c_8034,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_8030])).

tff(c_8573,plain,(
    ! [A_255,B_256,C_257] :
      ( k2_relset_1(A_255,B_256,C_257) = k2_relat_1(C_257)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_255,B_256))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_8582,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_8573])).

tff(c_8596,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_8582])).

tff(c_8017,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_8773,plain,(
    ! [A_267,B_268,C_269] :
      ( k1_relset_1(A_267,B_268,C_269) = k1_relat_1(C_269)
      | ~ m1_subset_1(C_269,k1_zfmisc_1(k2_zfmisc_1(A_267,B_268))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_8793,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8018,c_8773])).

tff(c_10584,plain,(
    ! [B_323,C_324,A_325] :
      ( k1_xboole_0 = B_323
      | v1_funct_2(C_324,A_325,B_323)
      | k1_relset_1(A_325,B_323,C_324) != A_325
      | ~ m1_subset_1(C_324,k1_zfmisc_1(k2_zfmisc_1(A_325,B_323))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_10590,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_8018,c_10584])).

tff(c_10609,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8793,c_10590])).

tff(c_10610,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_8017,c_10609])).

tff(c_10633,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_10610])).

tff(c_10636,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_10633])).

tff(c_10639,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_78,c_72,c_8596,c_10636])).

tff(c_10640,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_10610])).

tff(c_10681,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10640,c_2])).

tff(c_10683,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8034,c_10681])).

tff(c_10685,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_8030])).

tff(c_113,plain,(
    ! [B_43,A_44] :
      ( ~ v1_xboole_0(B_43)
      | B_43 = A_44
      | ~ v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_116,plain,(
    ! [A_44] :
      ( k1_xboole_0 = A_44
      | ~ v1_xboole_0(A_44) ) ),
    inference(resolution,[status(thm)],[c_2,c_113])).

tff(c_10701,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_10685,c_116])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_10736,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_2',B_4) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10701,c_10701,c_10])).

tff(c_207,plain,(
    ! [B_59,A_60] :
      ( v1_xboole_0(B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60))
      | ~ v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_224,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_74,c_207])).

tff(c_252,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_224])).

tff(c_10855,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10736,c_252])).

tff(c_10859,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10685,c_10855])).

tff(c_10860,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_296])).

tff(c_10867,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10860,c_116])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_10885,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10867,c_10867,c_8])).

tff(c_10861,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_296])).

tff(c_10874,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_10861,c_116])).

tff(c_10895,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10867,c_10874])).

tff(c_10897,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10895,c_252])).

tff(c_11014,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10860,c_10885,c_10897])).

tff(c_11015,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_11022,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_11015,c_116])).

tff(c_125,plain,(
    ! [A_48] : m1_subset_1(k6_partfun1(A_48),k1_zfmisc_1(k2_zfmisc_1(A_48,A_48))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_133,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_125])).

tff(c_210,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_133,c_207])).

tff(c_222,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_210])).

tff(c_232,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_222,c_116])).

tff(c_58,plain,(
    ! [A_36] : v1_partfun1(k6_partfun1(A_36),A_36) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_246,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_58])).

tff(c_30528,plain,(
    v1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11022,c_11022,c_246])).

tff(c_12,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_30535,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11022,c_12])).

tff(c_31577,plain,(
    ! [C_750,A_751,B_752] :
      ( v1_funct_2(C_750,A_751,B_752)
      | ~ v1_partfun1(C_750,A_751)
      | ~ v1_funct_1(C_750)
      | ~ m1_subset_1(C_750,k1_zfmisc_1(k2_zfmisc_1(A_751,B_752))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_31590,plain,(
    ! [A_751,B_752] :
      ( v1_funct_2('#skF_4',A_751,B_752)
      | ~ v1_partfun1('#skF_4',A_751)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30535,c_31577])).

tff(c_31601,plain,(
    ! [A_753,B_754] :
      ( v1_funct_2('#skF_4',A_753,B_754)
      | ~ v1_partfun1('#skF_4',A_753) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_31590])).

tff(c_30537,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11022,c_11022,c_10])).

tff(c_30536,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11022,c_11022,c_8])).

tff(c_11016,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_30575,plain,(
    ! [A_687] :
      ( A_687 = '#skF_4'
      | ~ v1_xboole_0(A_687) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11022,c_116])).

tff(c_30582,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_11016,c_30575])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_30663,plain,(
    ! [B_694,A_695] :
      ( B_694 = '#skF_4'
      | A_695 = '#skF_4'
      | k2_zfmisc_1(A_695,B_694) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11022,c_11022,c_11022,c_6])).

tff(c_30673,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_30582,c_30663])).

tff(c_30678,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_30673])).

tff(c_11034,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11022,c_11022,c_10])).

tff(c_11033,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11022,c_11022,c_8])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_11059,plain,(
    ! [A_339] :
      ( A_339 = '#skF_4'
      | ~ v1_xboole_0(A_339) ) ),
    inference(resolution,[status(thm)],[c_11015,c_4])).

tff(c_11066,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_11016,c_11059])).

tff(c_11151,plain,(
    ! [B_347,A_348] :
      ( B_347 = '#skF_4'
      | A_348 = '#skF_4'
      | k2_zfmisc_1(A_348,B_347) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11022,c_11022,c_11022,c_6])).

tff(c_11163,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_11066,c_11151])).

tff(c_11166,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_11163])).

tff(c_11024,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_11168,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11166,c_11024])).

tff(c_11172,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11033,c_11168])).

tff(c_11032,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11022,c_12])).

tff(c_12598,plain,(
    ! [A_410,B_411,C_412] :
      ( k2_relset_1(A_410,B_411,C_412) = k2_relat_1(C_412)
      | ~ m1_subset_1(C_412,k1_zfmisc_1(k2_zfmisc_1(A_410,B_411))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_12618,plain,(
    ! [A_413,B_414] : k2_relset_1(A_413,B_414,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_11032,c_12598])).

tff(c_11169,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11166,c_70])).

tff(c_12622,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_12618,c_11169])).

tff(c_11519,plain,(
    ! [A_378] :
      ( k1_relat_1(k2_funct_1(A_378)) = k2_relat_1(A_378)
      | ~ v2_funct_1(A_378)
      | ~ v1_funct_1(A_378)
      | ~ v1_relat_1(A_378) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_18460,plain,(
    ! [A_500] :
      ( v1_funct_2(k2_funct_1(A_500),k2_relat_1(A_500),k2_relat_1(k2_funct_1(A_500)))
      | ~ v1_funct_1(k2_funct_1(A_500))
      | ~ v1_relat_1(k2_funct_1(A_500))
      | ~ v2_funct_1(A_500)
      | ~ v1_funct_1(A_500)
      | ~ v1_relat_1(A_500) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11519,c_64])).

tff(c_18475,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12622,c_18460])).

tff(c_18491,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_78,c_72,c_163,c_18475])).

tff(c_18492,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_18491])).

tff(c_18495,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_18492])).

tff(c_18499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_78,c_18495])).

tff(c_18501,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_18491])).

tff(c_12217,plain,(
    ! [A_395,B_396,C_397] :
      ( k1_relset_1(A_395,B_396,C_397) = k1_relat_1(C_397)
      | ~ m1_subset_1(C_397,k1_zfmisc_1(k2_zfmisc_1(A_395,B_396))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_12235,plain,(
    ! [A_395,B_396] : k1_relset_1(A_395,B_396,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_11032,c_12217])).

tff(c_50,plain,(
    ! [C_35,B_34] :
      ( v1_funct_2(C_35,k1_xboole_0,B_34)
      | k1_relset_1(k1_xboole_0,B_34,C_35) != k1_xboole_0
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_82,plain,(
    ! [C_35,B_34] :
      ( v1_funct_2(C_35,k1_xboole_0,B_34)
      | k1_relset_1(k1_xboole_0,B_34,C_35) != k1_xboole_0
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_50])).

tff(c_13426,plain,(
    ! [C_431,B_432] :
      ( v1_funct_2(C_431,'#skF_4',B_432)
      | k1_relset_1('#skF_4',B_432,C_431) != '#skF_4'
      | ~ m1_subset_1(C_431,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11022,c_11022,c_11022,c_11022,c_82])).

tff(c_13429,plain,(
    ! [B_432] :
      ( v1_funct_2('#skF_4','#skF_4',B_432)
      | k1_relset_1('#skF_4',B_432,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_11032,c_13426])).

tff(c_13431,plain,(
    ! [B_432] :
      ( v1_funct_2('#skF_4','#skF_4',B_432)
      | k1_relat_1('#skF_4') != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12235,c_13429])).

tff(c_13432,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_13431])).

tff(c_11170,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11166,c_76])).

tff(c_54,plain,(
    ! [B_34,C_35] :
      ( k1_relset_1(k1_xboole_0,B_34,C_35) = k1_xboole_0
      | ~ v1_funct_2(C_35,k1_xboole_0,B_34)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_81,plain,(
    ! [B_34,C_35] :
      ( k1_relset_1(k1_xboole_0,B_34,C_35) = k1_xboole_0
      | ~ v1_funct_2(C_35,k1_xboole_0,B_34)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_54])).

tff(c_13844,plain,(
    ! [B_441,C_442] :
      ( k1_relset_1('#skF_4',B_441,C_442) = '#skF_4'
      | ~ v1_funct_2(C_442,'#skF_4',B_441)
      | ~ m1_subset_1(C_442,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11022,c_11022,c_11022,c_11022,c_81])).

tff(c_13846,plain,
    ( k1_relset_1('#skF_4','#skF_3','#skF_4') = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_11170,c_13844])).

tff(c_13852,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11032,c_12235,c_13846])).

tff(c_13854,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13432,c_13852])).

tff(c_13856,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_13431])).

tff(c_11751,plain,(
    ! [A_384] :
      ( m1_subset_1(A_384,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_384),k2_relat_1(A_384))))
      | ~ v1_funct_1(A_384)
      | ~ v1_relat_1(A_384) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_19159,plain,(
    ! [A_513] :
      ( m1_subset_1(k2_funct_1(A_513),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_513)),k1_relat_1(A_513))))
      | ~ v1_funct_1(k2_funct_1(A_513))
      | ~ v1_relat_1(k2_funct_1(A_513))
      | ~ v2_funct_1(A_513)
      | ~ v1_funct_1(A_513)
      | ~ v1_relat_1(A_513) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_11751])).

tff(c_19203,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_13856,c_19159])).

tff(c_19229,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_78,c_72,c_18501,c_163,c_11033,c_19203])).

tff(c_19231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11172,c_19229])).

tff(c_19232,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_11163])).

tff(c_19235,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19232,c_11024])).

tff(c_19239,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11034,c_19235])).

tff(c_19776,plain,(
    ! [A_547,B_548,C_549] :
      ( k1_relset_1(A_547,B_548,C_549) = k1_relat_1(C_549)
      | ~ m1_subset_1(C_549,k1_zfmisc_1(k2_zfmisc_1(A_547,B_548))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_19790,plain,(
    ! [A_547,B_548] : k1_relset_1(A_547,B_548,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_11032,c_19776])).

tff(c_21980,plain,(
    ! [C_605,B_606] :
      ( v1_funct_2(C_605,'#skF_4',B_606)
      | k1_relset_1('#skF_4',B_606,C_605) != '#skF_4'
      | ~ m1_subset_1(C_605,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11022,c_11022,c_11022,c_11022,c_82])).

tff(c_21983,plain,(
    ! [B_606] :
      ( v1_funct_2('#skF_4','#skF_4',B_606)
      | k1_relset_1('#skF_4',B_606,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_11032,c_21980])).

tff(c_21985,plain,(
    ! [B_606] :
      ( v1_funct_2('#skF_4','#skF_4',B_606)
      | k1_relat_1('#skF_4') != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19790,c_21983])).

tff(c_21986,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_21985])).

tff(c_11025,plain,(
    v1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11022,c_11022,c_246])).

tff(c_23864,plain,(
    ! [C_617,A_618,B_619] :
      ( v1_funct_2(C_617,A_618,B_619)
      | ~ v1_partfun1(C_617,A_618)
      | ~ v1_funct_1(C_617)
      | ~ m1_subset_1(C_617,k1_zfmisc_1(k2_zfmisc_1(A_618,B_619))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_23877,plain,(
    ! [A_618,B_619] :
      ( v1_funct_2('#skF_4',A_618,B_619)
      | ~ v1_partfun1('#skF_4',A_618)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_11032,c_23864])).

tff(c_23888,plain,(
    ! [A_620,B_621] :
      ( v1_funct_2('#skF_4',A_620,B_621)
      | ~ v1_partfun1('#skF_4',A_620) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_23877])).

tff(c_22080,plain,(
    ! [B_34,C_35] :
      ( k1_relset_1('#skF_4',B_34,C_35) = '#skF_4'
      | ~ v1_funct_2(C_35,'#skF_4',B_34)
      | ~ m1_subset_1(C_35,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11022,c_11022,c_11022,c_11022,c_81])).

tff(c_23891,plain,(
    ! [B_621] :
      ( k1_relset_1('#skF_4',B_621,'#skF_4') = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
      | ~ v1_partfun1('#skF_4','#skF_4') ) ),
    inference(resolution,[status(thm)],[c_23888,c_22080])).

tff(c_23897,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11025,c_11032,c_19790,c_23891])).

tff(c_23899,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21986,c_23897])).

tff(c_23901,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_21985])).

tff(c_19390,plain,(
    ! [A_537] :
      ( k2_relat_1(k2_funct_1(A_537)) = k1_relat_1(A_537)
      | ~ v2_funct_1(A_537)
      | ~ v1_funct_1(A_537)
      | ~ v1_relat_1(A_537) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_29691,plain,(
    ! [A_674] :
      ( v1_funct_2(k2_funct_1(A_674),k1_relat_1(k2_funct_1(A_674)),k1_relat_1(A_674))
      | ~ v1_funct_1(k2_funct_1(A_674))
      | ~ v1_relat_1(k2_funct_1(A_674))
      | ~ v2_funct_1(A_674)
      | ~ v1_funct_1(A_674)
      | ~ v1_relat_1(A_674) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19390,c_64])).

tff(c_29709,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_23901,c_29691])).

tff(c_29727,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_78,c_72,c_163,c_29709])).

tff(c_29728,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_29727])).

tff(c_29731,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_29728])).

tff(c_29735,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_78,c_29731])).

tff(c_29737,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_29727])).

tff(c_21175,plain,(
    ! [A_582,B_583,C_584] :
      ( k2_relset_1(A_582,B_583,C_584) = k2_relat_1(C_584)
      | ~ m1_subset_1(C_584,k1_zfmisc_1(k2_zfmisc_1(A_582,B_583))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_21191,plain,(
    ! [A_585,B_586] : k2_relset_1(A_585,B_586,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_11032,c_21175])).

tff(c_19236,plain,(
    k2_relset_1('#skF_2','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19232,c_19232,c_70])).

tff(c_21195,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_21191,c_19236])).

tff(c_21561,plain,(
    ! [A_593] :
      ( m1_subset_1(A_593,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_593),k2_relat_1(A_593))))
      | ~ v1_funct_1(A_593)
      | ~ v1_relat_1(A_593) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_30448,plain,(
    ! [A_685] :
      ( m1_subset_1(k2_funct_1(A_685),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_685),k2_relat_1(k2_funct_1(A_685)))))
      | ~ v1_funct_1(k2_funct_1(A_685))
      | ~ v1_relat_1(k2_funct_1(A_685))
      | ~ v2_funct_1(A_685)
      | ~ v1_funct_1(A_685)
      | ~ v1_relat_1(A_685) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_21561])).

tff(c_30495,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_21195,c_30448])).

tff(c_30523,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_78,c_72,c_29737,c_163,c_11034,c_30495])).

tff(c_30525,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19239,c_30523])).

tff(c_30527,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_14,plain,(
    ! [B_8,A_6] :
      ( v1_xboole_0(B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_6))
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30636,plain,
    ( v1_xboole_0(k2_funct_1('#skF_4'))
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30527,c_14])).

tff(c_30649,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_30636])).

tff(c_30679,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30678,c_30649])).

tff(c_30687,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11015,c_30536,c_30679])).

tff(c_30688,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_30673])).

tff(c_30716,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30688,c_30649])).

tff(c_30724,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11015,c_30537,c_30716])).

tff(c_30726,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_30636])).

tff(c_30533,plain,(
    ! [A_44] :
      ( A_44 = '#skF_4'
      | ~ v1_xboole_0(A_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11022,c_116])).

tff(c_30762,plain,(
    k2_zfmisc_1('#skF_3','#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30726,c_30533])).

tff(c_30795,plain,(
    ! [B_705,A_706] :
      ( B_705 = '#skF_4'
      | A_706 = '#skF_4'
      | k2_zfmisc_1(A_706,B_705) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11022,c_11022,c_11022,c_6])).

tff(c_30808,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_30762,c_30795])).

tff(c_30814,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_30808])).

tff(c_30725,plain,(
    v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_30636])).

tff(c_30732,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30725,c_30533])).

tff(c_30526,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_30737,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30732,c_30526])).

tff(c_30842,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30814,c_30737])).

tff(c_31604,plain,(
    ~ v1_partfun1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_31601,c_30842])).

tff(c_31608,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30528,c_31604])).

tff(c_31610,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_30808])).

tff(c_46,plain,(
    ! [A_33] :
      ( v1_funct_2(k1_xboole_0,A_33,k1_xboole_0)
      | k1_xboole_0 = A_33
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_33,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_80,plain,(
    ! [A_33] :
      ( v1_funct_2(k1_xboole_0,A_33,k1_xboole_0)
      | k1_xboole_0 = A_33 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_46])).

tff(c_30534,plain,(
    ! [A_33] :
      ( v1_funct_2('#skF_4',A_33,'#skF_4')
      | A_33 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11022,c_11022,c_11022,c_80])).

tff(c_31609,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_30808])).

tff(c_31612,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31609,c_30737])).

tff(c_31626,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30534,c_31612])).

tff(c_31630,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31610,c_31626])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:13:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.32/4.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.53/4.27  
% 11.53/4.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.53/4.27  %$ v1_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.53/4.27  
% 11.53/4.27  %Foreground sorts:
% 11.53/4.27  
% 11.53/4.27  
% 11.53/4.27  %Background operators:
% 11.53/4.27  
% 11.53/4.27  
% 11.53/4.27  %Foreground operators:
% 11.53/4.27  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.53/4.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.53/4.27  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 11.53/4.27  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.53/4.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.53/4.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.53/4.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.53/4.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.53/4.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.53/4.27  tff('#skF_2', type, '#skF_2': $i).
% 11.53/4.27  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 11.53/4.27  tff('#skF_3', type, '#skF_3': $i).
% 11.53/4.27  tff('#skF_1', type, '#skF_1': $i).
% 11.53/4.27  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.53/4.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.53/4.27  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 11.53/4.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.53/4.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.53/4.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.53/4.27  tff('#skF_4', type, '#skF_4': $i).
% 11.53/4.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.53/4.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.53/4.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.53/4.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.53/4.27  
% 11.60/4.30  tff(f_166, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 11.60/4.30  tff(f_99, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 11.60/4.30  tff(f_72, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 11.60/4.30  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.60/4.30  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.60/4.30  tff(f_135, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 11.60/4.30  tff(f_88, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 11.60/4.30  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.60/4.30  tff(f_149, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 11.60/4.30  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 11.60/4.30  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 11.60/4.30  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 11.60/4.30  tff(f_49, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 11.60/4.30  tff(f_139, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 11.60/4.30  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 11.60/4.30  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 11.60/4.30  tff(c_74, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_166])).
% 11.60/4.30  tff(c_278, plain, (![C_67, B_68, A_69]: (v1_xboole_0(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(B_68, A_69))) | ~v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_99])).
% 11.60/4.30  tff(c_296, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_74, c_278])).
% 11.60/4.30  tff(c_301, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_296])).
% 11.60/4.30  tff(c_78, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_166])).
% 11.60/4.30  tff(c_20, plain, (![A_15]: (v1_funct_1(k2_funct_1(A_15)) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.60/4.30  tff(c_68, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_166])).
% 11.60/4.30  tff(c_134, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_68])).
% 11.60/4.30  tff(c_137, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_134])).
% 11.60/4.30  tff(c_140, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_137])).
% 11.60/4.30  tff(c_142, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.60/4.30  tff(c_148, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_142])).
% 11.60/4.30  tff(c_161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_140, c_148])).
% 11.60/4.30  tff(c_162, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_68])).
% 11.60/4.30  tff(c_401, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_162])).
% 11.60/4.30  tff(c_165, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.60/4.30  tff(c_181, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_165])).
% 11.60/4.30  tff(c_72, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_166])).
% 11.60/4.30  tff(c_76, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 11.60/4.30  tff(c_1197, plain, (![A_117, B_118, C_119]: (k1_relset_1(A_117, B_118, C_119)=k1_relat_1(C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.60/4.30  tff(c_1223, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_1197])).
% 11.60/4.30  tff(c_1605, plain, (![B_151, A_152, C_153]: (k1_xboole_0=B_151 | k1_relset_1(A_152, B_151, C_153)=A_152 | ~v1_funct_2(C_153, A_152, B_151) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_152, B_151))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 11.60/4.30  tff(c_1617, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_1605])).
% 11.60/4.30  tff(c_1636, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1223, c_1617])).
% 11.60/4.30  tff(c_1640, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_1636])).
% 11.60/4.30  tff(c_30, plain, (![A_16]: (k2_relat_1(k2_funct_1(A_16))=k1_relat_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.60/4.30  tff(c_22, plain, (![A_15]: (v1_relat_1(k2_funct_1(A_15)) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.60/4.30  tff(c_163, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_68])).
% 11.60/4.30  tff(c_70, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_166])).
% 11.60/4.30  tff(c_924, plain, (![A_101, B_102, C_103]: (k2_relset_1(A_101, B_102, C_103)=k2_relat_1(C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 11.60/4.30  tff(c_933, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_924])).
% 11.60/4.30  tff(c_947, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_933])).
% 11.60/4.30  tff(c_445, plain, (![A_88]: (k1_relat_1(k2_funct_1(A_88))=k2_relat_1(A_88) | ~v2_funct_1(A_88) | ~v1_funct_1(A_88) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.60/4.30  tff(c_64, plain, (![A_37]: (v1_funct_2(A_37, k1_relat_1(A_37), k2_relat_1(A_37)) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_149])).
% 11.60/4.30  tff(c_5911, plain, (![A_217]: (v1_funct_2(k2_funct_1(A_217), k2_relat_1(A_217), k2_relat_1(k2_funct_1(A_217))) | ~v1_funct_1(k2_funct_1(A_217)) | ~v1_relat_1(k2_funct_1(A_217)) | ~v2_funct_1(A_217) | ~v1_funct_1(A_217) | ~v1_relat_1(A_217))), inference(superposition, [status(thm), theory('equality')], [c_445, c_64])).
% 11.60/4.30  tff(c_5923, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_947, c_5911])).
% 11.60/4.30  tff(c_5937, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_78, c_72, c_163, c_5923])).
% 11.60/4.30  tff(c_5938, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_5937])).
% 11.60/4.30  tff(c_5941, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_5938])).
% 11.60/4.30  tff(c_5945, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_181, c_78, c_5941])).
% 11.60/4.30  tff(c_5947, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_5937])).
% 11.60/4.30  tff(c_32, plain, (![A_16]: (k1_relat_1(k2_funct_1(A_16))=k2_relat_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.60/4.30  tff(c_690, plain, (![A_97]: (m1_subset_1(A_97, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_97), k2_relat_1(A_97)))) | ~v1_funct_1(A_97) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_149])).
% 11.60/4.30  tff(c_7858, plain, (![A_231]: (m1_subset_1(k2_funct_1(A_231), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_231), k2_relat_1(k2_funct_1(A_231))))) | ~v1_funct_1(k2_funct_1(A_231)) | ~v1_relat_1(k2_funct_1(A_231)) | ~v2_funct_1(A_231) | ~v1_funct_1(A_231) | ~v1_relat_1(A_231))), inference(superposition, [status(thm), theory('equality')], [c_32, c_690])).
% 11.60/4.30  tff(c_7902, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_947, c_7858])).
% 11.60/4.30  tff(c_7928, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_78, c_72, c_5947, c_163, c_7902])).
% 11.60/4.30  tff(c_7960, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_4')))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_30, c_7928])).
% 11.60/4.30  tff(c_7979, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_78, c_72, c_1640, c_7960])).
% 11.60/4.30  tff(c_7981, plain, $false, inference(negUnitSimplification, [status(thm)], [c_401, c_7979])).
% 11.60/4.30  tff(c_7982, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1636])).
% 11.60/4.30  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 11.60/4.30  tff(c_8014, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7982, c_2])).
% 11.60/4.30  tff(c_8016, plain, $false, inference(negUnitSimplification, [status(thm)], [c_301, c_8014])).
% 11.60/4.30  tff(c_8018, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_162])).
% 11.60/4.30  tff(c_36, plain, (![C_23, B_21, A_20]: (v1_xboole_0(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(B_21, A_20))) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_99])).
% 11.60/4.30  tff(c_8030, plain, (v1_xboole_0(k2_funct_1('#skF_4')) | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_8018, c_36])).
% 11.60/4.30  tff(c_8034, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_8030])).
% 11.60/4.30  tff(c_8573, plain, (![A_255, B_256, C_257]: (k2_relset_1(A_255, B_256, C_257)=k2_relat_1(C_257) | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(A_255, B_256))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 11.60/4.30  tff(c_8582, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_8573])).
% 11.60/4.30  tff(c_8596, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_8582])).
% 11.60/4.30  tff(c_8017, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_162])).
% 11.60/4.30  tff(c_8773, plain, (![A_267, B_268, C_269]: (k1_relset_1(A_267, B_268, C_269)=k1_relat_1(C_269) | ~m1_subset_1(C_269, k1_zfmisc_1(k2_zfmisc_1(A_267, B_268))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.60/4.30  tff(c_8793, plain, (k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_8018, c_8773])).
% 11.60/4.30  tff(c_10584, plain, (![B_323, C_324, A_325]: (k1_xboole_0=B_323 | v1_funct_2(C_324, A_325, B_323) | k1_relset_1(A_325, B_323, C_324)!=A_325 | ~m1_subset_1(C_324, k1_zfmisc_1(k2_zfmisc_1(A_325, B_323))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 11.60/4.30  tff(c_10590, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))!='#skF_3'), inference(resolution, [status(thm)], [c_8018, c_10584])).
% 11.60/4.30  tff(c_10609, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8793, c_10590])).
% 11.60/4.30  tff(c_10610, plain, (k1_xboole_0='#skF_2' | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_8017, c_10609])).
% 11.60/4.30  tff(c_10633, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_10610])).
% 11.60/4.30  tff(c_10636, plain, (k2_relat_1('#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_32, c_10633])).
% 11.60/4.30  tff(c_10639, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_181, c_78, c_72, c_8596, c_10636])).
% 11.60/4.30  tff(c_10640, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_10610])).
% 11.60/4.30  tff(c_10681, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10640, c_2])).
% 11.60/4.30  tff(c_10683, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8034, c_10681])).
% 11.60/4.30  tff(c_10685, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_8030])).
% 11.60/4.30  tff(c_113, plain, (![B_43, A_44]: (~v1_xboole_0(B_43) | B_43=A_44 | ~v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.60/4.30  tff(c_116, plain, (![A_44]: (k1_xboole_0=A_44 | ~v1_xboole_0(A_44))), inference(resolution, [status(thm)], [c_2, c_113])).
% 11.60/4.30  tff(c_10701, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_10685, c_116])).
% 11.60/4.30  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.60/4.30  tff(c_10736, plain, (![B_4]: (k2_zfmisc_1('#skF_2', B_4)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10701, c_10701, c_10])).
% 11.60/4.30  tff(c_207, plain, (![B_59, A_60]: (v1_xboole_0(B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)) | ~v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.60/4.30  tff(c_224, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_74, c_207])).
% 11.60/4.30  tff(c_252, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_224])).
% 11.60/4.30  tff(c_10855, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10736, c_252])).
% 11.60/4.30  tff(c_10859, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10685, c_10855])).
% 11.60/4.30  tff(c_10860, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_296])).
% 11.60/4.30  tff(c_10867, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_10860, c_116])).
% 11.60/4.30  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.60/4.30  tff(c_10885, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10867, c_10867, c_8])).
% 11.60/4.30  tff(c_10861, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_296])).
% 11.60/4.30  tff(c_10874, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_10861, c_116])).
% 11.60/4.30  tff(c_10895, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10867, c_10874])).
% 11.60/4.30  tff(c_10897, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10895, c_252])).
% 11.60/4.30  tff(c_11014, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10860, c_10885, c_10897])).
% 11.60/4.30  tff(c_11015, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_224])).
% 11.60/4.30  tff(c_11022, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_11015, c_116])).
% 11.60/4.30  tff(c_125, plain, (![A_48]: (m1_subset_1(k6_partfun1(A_48), k1_zfmisc_1(k2_zfmisc_1(A_48, A_48))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 11.60/4.30  tff(c_133, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_125])).
% 11.60/4.30  tff(c_210, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_133, c_207])).
% 11.60/4.30  tff(c_222, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_210])).
% 11.60/4.30  tff(c_232, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_222, c_116])).
% 11.60/4.30  tff(c_58, plain, (![A_36]: (v1_partfun1(k6_partfun1(A_36), A_36))), inference(cnfTransformation, [status(thm)], [f_139])).
% 11.60/4.30  tff(c_246, plain, (v1_partfun1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_232, c_58])).
% 11.60/4.30  tff(c_30528, plain, (v1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11022, c_11022, c_246])).
% 11.60/4.30  tff(c_12, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.60/4.30  tff(c_30535, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_11022, c_12])).
% 11.60/4.30  tff(c_31577, plain, (![C_750, A_751, B_752]: (v1_funct_2(C_750, A_751, B_752) | ~v1_partfun1(C_750, A_751) | ~v1_funct_1(C_750) | ~m1_subset_1(C_750, k1_zfmisc_1(k2_zfmisc_1(A_751, B_752))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 11.60/4.31  tff(c_31590, plain, (![A_751, B_752]: (v1_funct_2('#skF_4', A_751, B_752) | ~v1_partfun1('#skF_4', A_751) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_30535, c_31577])).
% 11.60/4.31  tff(c_31601, plain, (![A_753, B_754]: (v1_funct_2('#skF_4', A_753, B_754) | ~v1_partfun1('#skF_4', A_753))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_31590])).
% 11.60/4.31  tff(c_30537, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11022, c_11022, c_10])).
% 11.60/4.31  tff(c_30536, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11022, c_11022, c_8])).
% 11.60/4.31  tff(c_11016, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_224])).
% 11.60/4.31  tff(c_30575, plain, (![A_687]: (A_687='#skF_4' | ~v1_xboole_0(A_687))), inference(demodulation, [status(thm), theory('equality')], [c_11022, c_116])).
% 11.60/4.31  tff(c_30582, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_11016, c_30575])).
% 11.60/4.31  tff(c_6, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.60/4.31  tff(c_30663, plain, (![B_694, A_695]: (B_694='#skF_4' | A_695='#skF_4' | k2_zfmisc_1(A_695, B_694)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11022, c_11022, c_11022, c_6])).
% 11.60/4.31  tff(c_30673, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_30582, c_30663])).
% 11.60/4.31  tff(c_30678, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_30673])).
% 11.60/4.31  tff(c_11034, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11022, c_11022, c_10])).
% 11.60/4.31  tff(c_11033, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11022, c_11022, c_8])).
% 11.60/4.31  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.60/4.31  tff(c_11059, plain, (![A_339]: (A_339='#skF_4' | ~v1_xboole_0(A_339))), inference(resolution, [status(thm)], [c_11015, c_4])).
% 11.60/4.31  tff(c_11066, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_11016, c_11059])).
% 11.60/4.31  tff(c_11151, plain, (![B_347, A_348]: (B_347='#skF_4' | A_348='#skF_4' | k2_zfmisc_1(A_348, B_347)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11022, c_11022, c_11022, c_6])).
% 11.60/4.31  tff(c_11163, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_11066, c_11151])).
% 11.60/4.31  tff(c_11166, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_11163])).
% 11.60/4.31  tff(c_11024, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_162])).
% 11.60/4.31  tff(c_11168, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_11166, c_11024])).
% 11.60/4.31  tff(c_11172, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11033, c_11168])).
% 11.60/4.31  tff(c_11032, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_11022, c_12])).
% 11.60/4.31  tff(c_12598, plain, (![A_410, B_411, C_412]: (k2_relset_1(A_410, B_411, C_412)=k2_relat_1(C_412) | ~m1_subset_1(C_412, k1_zfmisc_1(k2_zfmisc_1(A_410, B_411))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 11.60/4.31  tff(c_12618, plain, (![A_413, B_414]: (k2_relset_1(A_413, B_414, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_11032, c_12598])).
% 11.60/4.31  tff(c_11169, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11166, c_70])).
% 11.60/4.31  tff(c_12622, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_12618, c_11169])).
% 11.60/4.31  tff(c_11519, plain, (![A_378]: (k1_relat_1(k2_funct_1(A_378))=k2_relat_1(A_378) | ~v2_funct_1(A_378) | ~v1_funct_1(A_378) | ~v1_relat_1(A_378))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.60/4.31  tff(c_18460, plain, (![A_500]: (v1_funct_2(k2_funct_1(A_500), k2_relat_1(A_500), k2_relat_1(k2_funct_1(A_500))) | ~v1_funct_1(k2_funct_1(A_500)) | ~v1_relat_1(k2_funct_1(A_500)) | ~v2_funct_1(A_500) | ~v1_funct_1(A_500) | ~v1_relat_1(A_500))), inference(superposition, [status(thm), theory('equality')], [c_11519, c_64])).
% 11.60/4.31  tff(c_18475, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12622, c_18460])).
% 11.60/4.31  tff(c_18491, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_78, c_72, c_163, c_18475])).
% 11.60/4.31  tff(c_18492, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_18491])).
% 11.60/4.31  tff(c_18495, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_18492])).
% 11.60/4.31  tff(c_18499, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_181, c_78, c_18495])).
% 11.60/4.31  tff(c_18501, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_18491])).
% 11.60/4.31  tff(c_12217, plain, (![A_395, B_396, C_397]: (k1_relset_1(A_395, B_396, C_397)=k1_relat_1(C_397) | ~m1_subset_1(C_397, k1_zfmisc_1(k2_zfmisc_1(A_395, B_396))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.60/4.31  tff(c_12235, plain, (![A_395, B_396]: (k1_relset_1(A_395, B_396, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_11032, c_12217])).
% 11.60/4.31  tff(c_50, plain, (![C_35, B_34]: (v1_funct_2(C_35, k1_xboole_0, B_34) | k1_relset_1(k1_xboole_0, B_34, C_35)!=k1_xboole_0 | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_34))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 11.60/4.31  tff(c_82, plain, (![C_35, B_34]: (v1_funct_2(C_35, k1_xboole_0, B_34) | k1_relset_1(k1_xboole_0, B_34, C_35)!=k1_xboole_0 | ~m1_subset_1(C_35, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_50])).
% 11.60/4.31  tff(c_13426, plain, (![C_431, B_432]: (v1_funct_2(C_431, '#skF_4', B_432) | k1_relset_1('#skF_4', B_432, C_431)!='#skF_4' | ~m1_subset_1(C_431, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_11022, c_11022, c_11022, c_11022, c_82])).
% 11.60/4.31  tff(c_13429, plain, (![B_432]: (v1_funct_2('#skF_4', '#skF_4', B_432) | k1_relset_1('#skF_4', B_432, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_11032, c_13426])).
% 11.60/4.31  tff(c_13431, plain, (![B_432]: (v1_funct_2('#skF_4', '#skF_4', B_432) | k1_relat_1('#skF_4')!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12235, c_13429])).
% 11.60/4.31  tff(c_13432, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(splitLeft, [status(thm)], [c_13431])).
% 11.60/4.31  tff(c_11170, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11166, c_76])).
% 11.60/4.31  tff(c_54, plain, (![B_34, C_35]: (k1_relset_1(k1_xboole_0, B_34, C_35)=k1_xboole_0 | ~v1_funct_2(C_35, k1_xboole_0, B_34) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_34))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 11.60/4.31  tff(c_81, plain, (![B_34, C_35]: (k1_relset_1(k1_xboole_0, B_34, C_35)=k1_xboole_0 | ~v1_funct_2(C_35, k1_xboole_0, B_34) | ~m1_subset_1(C_35, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_54])).
% 11.60/4.31  tff(c_13844, plain, (![B_441, C_442]: (k1_relset_1('#skF_4', B_441, C_442)='#skF_4' | ~v1_funct_2(C_442, '#skF_4', B_441) | ~m1_subset_1(C_442, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_11022, c_11022, c_11022, c_11022, c_81])).
% 11.60/4.31  tff(c_13846, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_4')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_11170, c_13844])).
% 11.60/4.31  tff(c_13852, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11032, c_12235, c_13846])).
% 11.60/4.31  tff(c_13854, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13432, c_13852])).
% 11.60/4.31  tff(c_13856, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_13431])).
% 11.60/4.31  tff(c_11751, plain, (![A_384]: (m1_subset_1(A_384, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_384), k2_relat_1(A_384)))) | ~v1_funct_1(A_384) | ~v1_relat_1(A_384))), inference(cnfTransformation, [status(thm)], [f_149])).
% 11.60/4.31  tff(c_19159, plain, (![A_513]: (m1_subset_1(k2_funct_1(A_513), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_513)), k1_relat_1(A_513)))) | ~v1_funct_1(k2_funct_1(A_513)) | ~v1_relat_1(k2_funct_1(A_513)) | ~v2_funct_1(A_513) | ~v1_funct_1(A_513) | ~v1_relat_1(A_513))), inference(superposition, [status(thm), theory('equality')], [c_30, c_11751])).
% 11.60/4.31  tff(c_19203, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_13856, c_19159])).
% 11.60/4.31  tff(c_19229, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_78, c_72, c_18501, c_163, c_11033, c_19203])).
% 11.60/4.31  tff(c_19231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11172, c_19229])).
% 11.60/4.31  tff(c_19232, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_11163])).
% 11.60/4.31  tff(c_19235, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_19232, c_11024])).
% 11.60/4.31  tff(c_19239, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11034, c_19235])).
% 11.60/4.31  tff(c_19776, plain, (![A_547, B_548, C_549]: (k1_relset_1(A_547, B_548, C_549)=k1_relat_1(C_549) | ~m1_subset_1(C_549, k1_zfmisc_1(k2_zfmisc_1(A_547, B_548))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.60/4.31  tff(c_19790, plain, (![A_547, B_548]: (k1_relset_1(A_547, B_548, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_11032, c_19776])).
% 11.60/4.31  tff(c_21980, plain, (![C_605, B_606]: (v1_funct_2(C_605, '#skF_4', B_606) | k1_relset_1('#skF_4', B_606, C_605)!='#skF_4' | ~m1_subset_1(C_605, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_11022, c_11022, c_11022, c_11022, c_82])).
% 11.60/4.31  tff(c_21983, plain, (![B_606]: (v1_funct_2('#skF_4', '#skF_4', B_606) | k1_relset_1('#skF_4', B_606, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_11032, c_21980])).
% 11.60/4.31  tff(c_21985, plain, (![B_606]: (v1_funct_2('#skF_4', '#skF_4', B_606) | k1_relat_1('#skF_4')!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19790, c_21983])).
% 11.60/4.31  tff(c_21986, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(splitLeft, [status(thm)], [c_21985])).
% 11.60/4.31  tff(c_11025, plain, (v1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11022, c_11022, c_246])).
% 11.60/4.31  tff(c_23864, plain, (![C_617, A_618, B_619]: (v1_funct_2(C_617, A_618, B_619) | ~v1_partfun1(C_617, A_618) | ~v1_funct_1(C_617) | ~m1_subset_1(C_617, k1_zfmisc_1(k2_zfmisc_1(A_618, B_619))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 11.60/4.31  tff(c_23877, plain, (![A_618, B_619]: (v1_funct_2('#skF_4', A_618, B_619) | ~v1_partfun1('#skF_4', A_618) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_11032, c_23864])).
% 11.60/4.31  tff(c_23888, plain, (![A_620, B_621]: (v1_funct_2('#skF_4', A_620, B_621) | ~v1_partfun1('#skF_4', A_620))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_23877])).
% 11.60/4.31  tff(c_22080, plain, (![B_34, C_35]: (k1_relset_1('#skF_4', B_34, C_35)='#skF_4' | ~v1_funct_2(C_35, '#skF_4', B_34) | ~m1_subset_1(C_35, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_11022, c_11022, c_11022, c_11022, c_81])).
% 11.60/4.31  tff(c_23891, plain, (![B_621]: (k1_relset_1('#skF_4', B_621, '#skF_4')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~v1_partfun1('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_23888, c_22080])).
% 11.60/4.31  tff(c_23897, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11025, c_11032, c_19790, c_23891])).
% 11.60/4.31  tff(c_23899, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21986, c_23897])).
% 11.60/4.31  tff(c_23901, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_21985])).
% 11.60/4.31  tff(c_19390, plain, (![A_537]: (k2_relat_1(k2_funct_1(A_537))=k1_relat_1(A_537) | ~v2_funct_1(A_537) | ~v1_funct_1(A_537) | ~v1_relat_1(A_537))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.60/4.31  tff(c_29691, plain, (![A_674]: (v1_funct_2(k2_funct_1(A_674), k1_relat_1(k2_funct_1(A_674)), k1_relat_1(A_674)) | ~v1_funct_1(k2_funct_1(A_674)) | ~v1_relat_1(k2_funct_1(A_674)) | ~v2_funct_1(A_674) | ~v1_funct_1(A_674) | ~v1_relat_1(A_674))), inference(superposition, [status(thm), theory('equality')], [c_19390, c_64])).
% 11.60/4.31  tff(c_29709, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_23901, c_29691])).
% 11.60/4.31  tff(c_29727, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_78, c_72, c_163, c_29709])).
% 11.60/4.31  tff(c_29728, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_29727])).
% 11.60/4.31  tff(c_29731, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_29728])).
% 11.60/4.31  tff(c_29735, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_181, c_78, c_29731])).
% 11.60/4.31  tff(c_29737, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_29727])).
% 11.60/4.31  tff(c_21175, plain, (![A_582, B_583, C_584]: (k2_relset_1(A_582, B_583, C_584)=k2_relat_1(C_584) | ~m1_subset_1(C_584, k1_zfmisc_1(k2_zfmisc_1(A_582, B_583))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 11.60/4.31  tff(c_21191, plain, (![A_585, B_586]: (k2_relset_1(A_585, B_586, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_11032, c_21175])).
% 11.60/4.31  tff(c_19236, plain, (k2_relset_1('#skF_2', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_19232, c_19232, c_70])).
% 11.60/4.31  tff(c_21195, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_21191, c_19236])).
% 11.60/4.31  tff(c_21561, plain, (![A_593]: (m1_subset_1(A_593, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_593), k2_relat_1(A_593)))) | ~v1_funct_1(A_593) | ~v1_relat_1(A_593))), inference(cnfTransformation, [status(thm)], [f_149])).
% 11.60/4.31  tff(c_30448, plain, (![A_685]: (m1_subset_1(k2_funct_1(A_685), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_685), k2_relat_1(k2_funct_1(A_685))))) | ~v1_funct_1(k2_funct_1(A_685)) | ~v1_relat_1(k2_funct_1(A_685)) | ~v2_funct_1(A_685) | ~v1_funct_1(A_685) | ~v1_relat_1(A_685))), inference(superposition, [status(thm), theory('equality')], [c_32, c_21561])).
% 11.60/4.31  tff(c_30495, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_21195, c_30448])).
% 11.60/4.31  tff(c_30523, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_78, c_72, c_29737, c_163, c_11034, c_30495])).
% 11.60/4.31  tff(c_30525, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19239, c_30523])).
% 11.60/4.31  tff(c_30527, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_162])).
% 11.60/4.31  tff(c_14, plain, (![B_8, A_6]: (v1_xboole_0(B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_6)) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.60/4.31  tff(c_30636, plain, (v1_xboole_0(k2_funct_1('#skF_4')) | ~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_30527, c_14])).
% 11.60/4.31  tff(c_30649, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_30636])).
% 11.60/4.31  tff(c_30679, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_30678, c_30649])).
% 11.60/4.31  tff(c_30687, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11015, c_30536, c_30679])).
% 11.60/4.31  tff(c_30688, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_30673])).
% 11.60/4.31  tff(c_30716, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30688, c_30649])).
% 11.60/4.31  tff(c_30724, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11015, c_30537, c_30716])).
% 11.60/4.31  tff(c_30726, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_30636])).
% 11.60/4.31  tff(c_30533, plain, (![A_44]: (A_44='#skF_4' | ~v1_xboole_0(A_44))), inference(demodulation, [status(thm), theory('equality')], [c_11022, c_116])).
% 11.60/4.31  tff(c_30762, plain, (k2_zfmisc_1('#skF_3', '#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_30726, c_30533])).
% 11.60/4.31  tff(c_30795, plain, (![B_705, A_706]: (B_705='#skF_4' | A_706='#skF_4' | k2_zfmisc_1(A_706, B_705)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11022, c_11022, c_11022, c_6])).
% 11.60/4.31  tff(c_30808, plain, ('#skF_2'='#skF_4' | '#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_30762, c_30795])).
% 11.60/4.31  tff(c_30814, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_30808])).
% 11.60/4.31  tff(c_30725, plain, (v1_xboole_0(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_30636])).
% 11.60/4.31  tff(c_30732, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_30725, c_30533])).
% 11.60/4.31  tff(c_30526, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_162])).
% 11.60/4.31  tff(c_30737, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30732, c_30526])).
% 11.60/4.31  tff(c_30842, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30814, c_30737])).
% 11.60/4.31  tff(c_31604, plain, (~v1_partfun1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_31601, c_30842])).
% 11.60/4.31  tff(c_31608, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30528, c_31604])).
% 11.60/4.31  tff(c_31610, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_30808])).
% 11.60/4.31  tff(c_46, plain, (![A_33]: (v1_funct_2(k1_xboole_0, A_33, k1_xboole_0) | k1_xboole_0=A_33 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_33, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 11.60/4.31  tff(c_80, plain, (![A_33]: (v1_funct_2(k1_xboole_0, A_33, k1_xboole_0) | k1_xboole_0=A_33)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_46])).
% 11.60/4.31  tff(c_30534, plain, (![A_33]: (v1_funct_2('#skF_4', A_33, '#skF_4') | A_33='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11022, c_11022, c_11022, c_80])).
% 11.60/4.31  tff(c_31609, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_30808])).
% 11.60/4.31  tff(c_31612, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_31609, c_30737])).
% 11.60/4.31  tff(c_31626, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_30534, c_31612])).
% 11.60/4.31  tff(c_31630, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31610, c_31626])).
% 11.60/4.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.60/4.31  
% 11.60/4.31  Inference rules
% 11.60/4.31  ----------------------
% 11.60/4.31  #Ref     : 0
% 11.60/4.31  #Sup     : 8732
% 11.60/4.31  #Fact    : 0
% 11.60/4.31  #Define  : 0
% 11.60/4.31  #Split   : 50
% 11.60/4.31  #Chain   : 0
% 11.60/4.31  #Close   : 0
% 11.60/4.31  
% 11.60/4.31  Ordering : KBO
% 11.60/4.31  
% 11.60/4.31  Simplification rules
% 11.60/4.31  ----------------------
% 11.60/4.31  #Subsume      : 3368
% 11.60/4.31  #Demod        : 6024
% 11.60/4.31  #Tautology    : 2464
% 11.60/4.31  #SimpNegUnit  : 19
% 11.60/4.31  #BackRed      : 213
% 11.60/4.31  
% 11.60/4.31  #Partial instantiations: 0
% 11.60/4.31  #Strategies tried      : 1
% 11.60/4.31  
% 11.60/4.31  Timing (in seconds)
% 11.60/4.31  ----------------------
% 11.60/4.31  Preprocessing        : 0.35
% 11.60/4.31  Parsing              : 0.19
% 11.60/4.31  CNF conversion       : 0.02
% 11.60/4.31  Main loop            : 3.15
% 11.60/4.31  Inferencing          : 0.78
% 11.60/4.31  Reduction            : 1.10
% 11.60/4.31  Demodulation         : 0.83
% 11.60/4.31  BG Simplification    : 0.10
% 11.60/4.31  Subsumption          : 0.97
% 11.60/4.31  Abstraction          : 0.14
% 11.60/4.31  MUC search           : 0.00
% 11.60/4.31  Cooper               : 0.00
% 11.60/4.31  Total                : 3.58
% 11.60/4.31  Index Insertion      : 0.00
% 11.60/4.31  Index Deletion       : 0.00
% 11.60/4.31  Index Matching       : 0.00
% 11.60/4.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
