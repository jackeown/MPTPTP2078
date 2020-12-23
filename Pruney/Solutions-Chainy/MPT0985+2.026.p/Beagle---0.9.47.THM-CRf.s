%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:29 EST 2020

% Result     : Theorem 4.82s
% Output     : CNFRefutation 4.82s
% Verified   : 
% Statistics : Number of formulae       :  191 (1923 expanded)
%              Number of leaves         :   38 ( 625 expanded)
%              Depth                    :   18
%              Number of atoms          :  337 (5134 expanded)
%              Number of equality atoms :   93 (1124 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_151,negated_conjecture,(
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

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_122,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_112,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_47,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_134,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_112,plain,(
    ! [C_41,A_42,B_43] :
      ( v1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_120,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_112])).

tff(c_72,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_1232,plain,(
    ! [C_123,A_124,B_125] :
      ( v1_xboole_0(C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125)))
      | ~ v1_xboole_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1244,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_1232])).

tff(c_1247,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1244])).

tff(c_66,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_64,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_1369,plain,(
    ! [A_140,B_141,C_142] :
      ( k2_relset_1(A_140,B_141,C_142) = k2_relat_1(C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1378,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1369])).

tff(c_1386,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1378])).

tff(c_28,plain,(
    ! [A_11] :
      ( k1_relat_1(k2_funct_1(A_11)) = k2_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    ! [A_10] :
      ( v1_funct_1(k2_funct_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_62,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_122,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_135,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_122])).

tff(c_139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_72,c_135])).

tff(c_140,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_170,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_291,plain,(
    ! [A_64,B_65,C_66] :
      ( k2_relset_1(A_64,B_65,C_66) = k2_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_297,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_291])).

tff(c_304,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_297])).

tff(c_24,plain,(
    ! [A_10] :
      ( v1_relat_1(k2_funct_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_141,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_228,plain,(
    ! [A_57] :
      ( m1_subset_1(A_57,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_57),k2_relat_1(A_57))))
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_32,plain,(
    ! [C_18,A_15,B_16] :
      ( v1_xboole_0(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16)))
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_256,plain,(
    ! [A_58] :
      ( v1_xboole_0(A_58)
      | ~ v1_xboole_0(k1_relat_1(A_58))
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(resolution,[status(thm)],[c_228,c_32])).

tff(c_982,plain,(
    ! [A_116] :
      ( v1_xboole_0(k2_funct_1(A_116))
      | ~ v1_xboole_0(k2_relat_1(A_116))
      | ~ v1_funct_1(k2_funct_1(A_116))
      | ~ v1_relat_1(k2_funct_1(A_116))
      | ~ v2_funct_1(A_116)
      | ~ v1_funct_1(A_116)
      | ~ v1_relat_1(A_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_256])).

tff(c_988,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0('#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_304,c_982])).

tff(c_998,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_72,c_66,c_141,c_988])).

tff(c_1001,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_998])).

tff(c_1004,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_1001])).

tff(c_1008,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_72,c_1004])).

tff(c_1010,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_998])).

tff(c_16,plain,(
    ! [A_8] :
      ( k1_relat_1(A_8) = k1_xboole_0
      | k2_relat_1(A_8) != k1_xboole_0
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_145,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_120,c_16])).

tff(c_152,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_307,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_152])).

tff(c_70,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_265,plain,(
    ! [A_59,B_60,C_61] :
      ( k1_relset_1(A_59,B_60,C_61) = k1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_277,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_265])).

tff(c_661,plain,(
    ! [B_93,A_94,C_95] :
      ( k1_xboole_0 = B_93
      | k1_relset_1(A_94,B_93,C_95) = A_94
      | ~ v1_funct_2(C_95,A_94,B_93)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_94,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_673,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_661])).

tff(c_686,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_277,c_673])).

tff(c_687,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_307,c_686])).

tff(c_26,plain,(
    ! [A_11] :
      ( k2_relat_1(k2_funct_1(A_11)) = k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1111,plain,(
    ! [A_119] :
      ( m1_subset_1(k2_funct_1(A_119),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_119)),k1_relat_1(A_119))))
      | ~ v1_funct_1(k2_funct_1(A_119))
      | ~ v1_relat_1(k2_funct_1(A_119))
      | ~ v2_funct_1(A_119)
      | ~ v1_funct_1(A_119)
      | ~ v1_relat_1(A_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_228])).

tff(c_1140,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_687,c_1111])).

tff(c_1158,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_72,c_66,c_1010,c_141,c_1140])).

tff(c_1186,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1158])).

tff(c_1203,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_72,c_66,c_304,c_1186])).

tff(c_1205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_1203])).

tff(c_1206,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_1207,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_1326,plain,(
    ! [A_134,B_135,C_136] :
      ( k1_relset_1(A_134,B_135,C_136) = k1_relat_1(C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1341,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1207,c_1326])).

tff(c_1709,plain,(
    ! [B_166,C_167,A_168] :
      ( k1_xboole_0 = B_166
      | v1_funct_2(C_167,A_168,B_166)
      | k1_relset_1(A_168,B_166,C_167) != A_168
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_168,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1721,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_1207,c_1709])).

tff(c_1736,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1341,c_1721])).

tff(c_1737,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_1206,c_1736])).

tff(c_1743,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1737])).

tff(c_1746,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1743])).

tff(c_1749,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_72,c_66,c_1386,c_1746])).

tff(c_1750,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1737])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1776,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1750,c_2])).

tff(c_1778,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1247,c_1776])).

tff(c_1780,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1244])).

tff(c_95,plain,(
    ! [B_35,A_36] :
      ( ~ v1_xboole_0(B_35)
      | B_35 = A_36
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_98,plain,(
    ! [A_36] :
      ( k1_xboole_0 = A_36
      | ~ v1_xboole_0(A_36) ) ),
    inference(resolution,[status(thm)],[c_2,c_95])).

tff(c_1801,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1780,c_98])).

tff(c_1779,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1244])).

tff(c_1789,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1779,c_98])).

tff(c_1837,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1801,c_1789])).

tff(c_14,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1827,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1789,c_1789,c_14])).

tff(c_1861,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1837,c_1837,c_1827])).

tff(c_153,plain,(
    ! [A_44] :
      ( k2_relat_1(A_44) = k1_xboole_0
      | k1_relat_1(A_44) != k1_xboole_0
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_159,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_120,c_153])).

tff(c_168,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_159])).

tff(c_1817,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1789,c_168])).

tff(c_1894,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1861,c_1837,c_1837,c_1817])).

tff(c_1896,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_1991,plain,(
    ! [A_185,B_186,C_187] :
      ( k2_relset_1(A_185,B_186,C_187) = k2_relat_1(C_187)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1994,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1991])).

tff(c_2000,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1896,c_64,c_1994])).

tff(c_2018,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2000,c_2])).

tff(c_1895,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_2008,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2000,c_1895])).

tff(c_2007,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2000,c_1896])).

tff(c_2113,plain,(
    ! [A_194] :
      ( m1_subset_1(A_194,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_194),k2_relat_1(A_194))))
      | ~ v1_funct_1(A_194)
      | ~ v1_relat_1(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2139,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2007,c_2113])).

tff(c_2158,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_72,c_2008,c_2139])).

tff(c_2190,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2158,c_32])).

tff(c_2201,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2018,c_2190])).

tff(c_2011,plain,(
    ! [A_36] :
      ( A_36 = '#skF_2'
      | ~ v1_xboole_0(A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2000,c_98])).

tff(c_2226,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2201,c_2011])).

tff(c_8,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2014,plain,(
    ! [A_4] : m1_subset_1('#skF_2',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2000,c_8])).

tff(c_2237,plain,(
    ! [A_4] : m1_subset_1('#skF_3',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2226,c_2014])).

tff(c_2246,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2226,c_2007])).

tff(c_2475,plain,(
    ! [A_225] :
      ( v1_xboole_0(A_225)
      | ~ v1_xboole_0(k1_relat_1(A_225))
      | ~ v1_funct_1(A_225)
      | ~ v1_relat_1(A_225) ) ),
    inference(resolution,[status(thm)],[c_2113,c_32])).

tff(c_2766,plain,(
    ! [A_251] :
      ( v1_xboole_0(k2_funct_1(A_251))
      | ~ v1_xboole_0(k2_relat_1(A_251))
      | ~ v1_funct_1(k2_funct_1(A_251))
      | ~ v1_relat_1(k2_funct_1(A_251))
      | ~ v2_funct_1(A_251)
      | ~ v1_funct_1(A_251)
      | ~ v1_relat_1(A_251) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2475])).

tff(c_2772,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2246,c_2766])).

tff(c_2779,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_72,c_66,c_141,c_2201,c_2772])).

tff(c_2780,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2779])).

tff(c_2783,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_2780])).

tff(c_2787,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_72,c_2783])).

tff(c_2788,plain,(
    v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2779])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( ~ v1_xboole_0(B_3)
      | B_3 = A_2
      | ~ v1_xboole_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2227,plain,(
    ! [A_2] :
      ( A_2 = '#skF_3'
      | ~ v1_xboole_0(A_2) ) ),
    inference(resolution,[status(thm)],[c_2201,c_6])).

tff(c_2798,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2788,c_2227])).

tff(c_1901,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_2250,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2226,c_1901])).

tff(c_2830,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2798,c_2250])).

tff(c_2836,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2237,c_2830])).

tff(c_2838,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_3003,plain,(
    ! [C_274,A_275,B_276] :
      ( v1_xboole_0(C_274)
      | ~ m1_subset_1(C_274,k1_zfmisc_1(k2_zfmisc_1(A_275,B_276)))
      | ~ v1_xboole_0(A_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_3014,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2838,c_3003])).

tff(c_3019,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3014])).

tff(c_3092,plain,(
    ! [A_284,B_285,C_286] :
      ( k2_relset_1(A_284,B_285,C_286) = k2_relat_1(C_286)
      | ~ m1_subset_1(C_286,k1_zfmisc_1(k2_zfmisc_1(A_284,B_285))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3098,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_3092])).

tff(c_3106,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1896,c_3098])).

tff(c_3129,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3106,c_2])).

tff(c_3131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3019,c_3129])).

tff(c_3133,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3014])).

tff(c_3142,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_3133,c_98])).

tff(c_3153,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3142,c_1895])).

tff(c_3152,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3142,c_1896])).

tff(c_3306,plain,(
    ! [A_292] :
      ( m1_subset_1(A_292,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_292),k2_relat_1(A_292))))
      | ~ v1_funct_1(A_292)
      | ~ v1_relat_1(A_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_3329,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3152,c_3306])).

tff(c_3341,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_72,c_3153,c_3329])).

tff(c_3349,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_3341,c_32])).

tff(c_3357,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3133,c_3349])).

tff(c_3143,plain,(
    ! [A_2] :
      ( A_2 = '#skF_2'
      | ~ v1_xboole_0(A_2) ) ),
    inference(resolution,[status(thm)],[c_3133,c_6])).

tff(c_3369,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3357,c_3143])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_3162,plain,(
    ! [A_1] : r1_tarski('#skF_2',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3142,c_4])).

tff(c_3384,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3369,c_3162])).

tff(c_3385,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3369,c_3152])).

tff(c_3161,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3142,c_3142,c_14])).

tff(c_3382,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3369,c_3369,c_3161])).

tff(c_3528,plain,(
    ! [B_309,A_310] :
      ( v1_funct_2(B_309,k1_relat_1(B_309),A_310)
      | ~ r1_tarski(k2_relat_1(B_309),A_310)
      | ~ v1_funct_1(B_309)
      | ~ v1_relat_1(B_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_3531,plain,(
    ! [A_310] :
      ( v1_funct_2('#skF_3','#skF_3',A_310)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_310)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3382,c_3528])).

tff(c_3536,plain,(
    ! [A_310] : v1_funct_2('#skF_3','#skF_3',A_310) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_72,c_3384,c_3385,c_3531])).

tff(c_3132,plain,(
    v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3014])).

tff(c_3227,plain,(
    ! [A_289] :
      ( A_289 = '#skF_2'
      | ~ v1_xboole_0(A_289) ) ),
    inference(resolution,[status(thm)],[c_3133,c_6])).

tff(c_3234,plain,(
    k2_funct_1('#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_3132,c_3227])).

tff(c_2837,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_3241,plain,(
    ~ v1_funct_2('#skF_2','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3234,c_2837])).

tff(c_3376,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3369,c_3369,c_3241])).

tff(c_3540,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3536,c_3376])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:49:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.82/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.82/1.85  
% 4.82/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.82/1.85  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.82/1.85  
% 4.82/1.85  %Foreground sorts:
% 4.82/1.85  
% 4.82/1.85  
% 4.82/1.85  %Background operators:
% 4.82/1.85  
% 4.82/1.85  
% 4.82/1.85  %Foreground operators:
% 4.82/1.85  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.82/1.85  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.82/1.85  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.82/1.85  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.82/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.82/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.82/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.82/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.82/1.85  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.82/1.85  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.82/1.85  tff('#skF_2', type, '#skF_2': $i).
% 4.82/1.85  tff('#skF_3', type, '#skF_3': $i).
% 4.82/1.85  tff('#skF_1', type, '#skF_1': $i).
% 4.82/1.85  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.82/1.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.82/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.82/1.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.82/1.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.82/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.82/1.85  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.82/1.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.82/1.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.82/1.85  
% 4.82/1.88  tff(f_151, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 4.82/1.88  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.82/1.88  tff(f_86, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 4.82/1.88  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.82/1.88  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 4.82/1.88  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 4.82/1.88  tff(f_122, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 4.82/1.88  tff(f_53, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 4.82/1.88  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.82/1.88  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.82/1.88  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.82/1.88  tff(f_36, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 4.82/1.88  tff(f_47, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 4.82/1.88  tff(f_38, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.82/1.88  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.82/1.88  tff(f_134, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 4.82/1.88  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.82/1.88  tff(c_112, plain, (![C_41, A_42, B_43]: (v1_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.82/1.88  tff(c_120, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_112])).
% 4.82/1.88  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.82/1.88  tff(c_1232, plain, (![C_123, A_124, B_125]: (v1_xboole_0(C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))) | ~v1_xboole_0(A_124))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.82/1.88  tff(c_1244, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_68, c_1232])).
% 4.82/1.88  tff(c_1247, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_1244])).
% 4.82/1.88  tff(c_66, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.82/1.88  tff(c_64, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.82/1.88  tff(c_1369, plain, (![A_140, B_141, C_142]: (k2_relset_1(A_140, B_141, C_142)=k2_relat_1(C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.82/1.88  tff(c_1378, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1369])).
% 4.82/1.88  tff(c_1386, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1378])).
% 4.82/1.88  tff(c_28, plain, (![A_11]: (k1_relat_1(k2_funct_1(A_11))=k2_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.82/1.88  tff(c_22, plain, (![A_10]: (v1_funct_1(k2_funct_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.82/1.88  tff(c_62, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.82/1.88  tff(c_122, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_62])).
% 4.82/1.88  tff(c_135, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_122])).
% 4.82/1.88  tff(c_139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_120, c_72, c_135])).
% 4.82/1.88  tff(c_140, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_62])).
% 4.82/1.88  tff(c_170, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_140])).
% 4.82/1.88  tff(c_291, plain, (![A_64, B_65, C_66]: (k2_relset_1(A_64, B_65, C_66)=k2_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.82/1.88  tff(c_297, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_291])).
% 4.82/1.88  tff(c_304, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_297])).
% 4.82/1.88  tff(c_24, plain, (![A_10]: (v1_relat_1(k2_funct_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.82/1.88  tff(c_141, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_62])).
% 4.82/1.88  tff(c_228, plain, (![A_57]: (m1_subset_1(A_57, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_57), k2_relat_1(A_57)))) | ~v1_funct_1(A_57) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.82/1.88  tff(c_32, plain, (![C_18, A_15, B_16]: (v1_xboole_0(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))) | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.82/1.88  tff(c_256, plain, (![A_58]: (v1_xboole_0(A_58) | ~v1_xboole_0(k1_relat_1(A_58)) | ~v1_funct_1(A_58) | ~v1_relat_1(A_58))), inference(resolution, [status(thm)], [c_228, c_32])).
% 4.82/1.88  tff(c_982, plain, (![A_116]: (v1_xboole_0(k2_funct_1(A_116)) | ~v1_xboole_0(k2_relat_1(A_116)) | ~v1_funct_1(k2_funct_1(A_116)) | ~v1_relat_1(k2_funct_1(A_116)) | ~v2_funct_1(A_116) | ~v1_funct_1(A_116) | ~v1_relat_1(A_116))), inference(superposition, [status(thm), theory('equality')], [c_28, c_256])).
% 4.82/1.88  tff(c_988, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0('#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_304, c_982])).
% 4.82/1.88  tff(c_998, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_72, c_66, c_141, c_988])).
% 4.82/1.88  tff(c_1001, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_998])).
% 4.82/1.88  tff(c_1004, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_1001])).
% 4.82/1.88  tff(c_1008, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_120, c_72, c_1004])).
% 4.82/1.88  tff(c_1010, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_998])).
% 4.82/1.88  tff(c_16, plain, (![A_8]: (k1_relat_1(A_8)=k1_xboole_0 | k2_relat_1(A_8)!=k1_xboole_0 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.82/1.88  tff(c_145, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_120, c_16])).
% 4.82/1.88  tff(c_152, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_145])).
% 4.82/1.88  tff(c_307, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_304, c_152])).
% 4.82/1.88  tff(c_70, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.82/1.88  tff(c_265, plain, (![A_59, B_60, C_61]: (k1_relset_1(A_59, B_60, C_61)=k1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.82/1.88  tff(c_277, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_265])).
% 4.82/1.88  tff(c_661, plain, (![B_93, A_94, C_95]: (k1_xboole_0=B_93 | k1_relset_1(A_94, B_93, C_95)=A_94 | ~v1_funct_2(C_95, A_94, B_93) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_94, B_93))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.82/1.88  tff(c_673, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_661])).
% 4.82/1.88  tff(c_686, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_277, c_673])).
% 4.82/1.88  tff(c_687, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_307, c_686])).
% 4.82/1.88  tff(c_26, plain, (![A_11]: (k2_relat_1(k2_funct_1(A_11))=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.82/1.88  tff(c_1111, plain, (![A_119]: (m1_subset_1(k2_funct_1(A_119), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_119)), k1_relat_1(A_119)))) | ~v1_funct_1(k2_funct_1(A_119)) | ~v1_relat_1(k2_funct_1(A_119)) | ~v2_funct_1(A_119) | ~v1_funct_1(A_119) | ~v1_relat_1(A_119))), inference(superposition, [status(thm), theory('equality')], [c_26, c_228])).
% 4.82/1.88  tff(c_1140, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_687, c_1111])).
% 4.82/1.88  tff(c_1158, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_72, c_66, c_1010, c_141, c_1140])).
% 4.82/1.88  tff(c_1186, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_1158])).
% 4.82/1.88  tff(c_1203, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_72, c_66, c_304, c_1186])).
% 4.82/1.88  tff(c_1205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_170, c_1203])).
% 4.82/1.88  tff(c_1206, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_140])).
% 4.82/1.88  tff(c_1207, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_140])).
% 4.82/1.88  tff(c_1326, plain, (![A_134, B_135, C_136]: (k1_relset_1(A_134, B_135, C_136)=k1_relat_1(C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.82/1.88  tff(c_1341, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1207, c_1326])).
% 4.82/1.88  tff(c_1709, plain, (![B_166, C_167, A_168]: (k1_xboole_0=B_166 | v1_funct_2(C_167, A_168, B_166) | k1_relset_1(A_168, B_166, C_167)!=A_168 | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_168, B_166))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.82/1.88  tff(c_1721, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_1207, c_1709])).
% 4.82/1.88  tff(c_1736, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1341, c_1721])).
% 4.82/1.88  tff(c_1737, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_1206, c_1736])).
% 4.82/1.88  tff(c_1743, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_1737])).
% 4.82/1.88  tff(c_1746, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_1743])).
% 4.82/1.88  tff(c_1749, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_120, c_72, c_66, c_1386, c_1746])).
% 4.82/1.88  tff(c_1750, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_1737])).
% 4.82/1.88  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.82/1.88  tff(c_1776, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1750, c_2])).
% 4.82/1.88  tff(c_1778, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1247, c_1776])).
% 4.82/1.88  tff(c_1780, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_1244])).
% 4.82/1.88  tff(c_95, plain, (![B_35, A_36]: (~v1_xboole_0(B_35) | B_35=A_36 | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.82/1.88  tff(c_98, plain, (![A_36]: (k1_xboole_0=A_36 | ~v1_xboole_0(A_36))), inference(resolution, [status(thm)], [c_2, c_95])).
% 4.82/1.88  tff(c_1801, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_1780, c_98])).
% 4.82/1.88  tff(c_1779, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_1244])).
% 4.82/1.88  tff(c_1789, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1779, c_98])).
% 4.82/1.88  tff(c_1837, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1801, c_1789])).
% 4.82/1.88  tff(c_14, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.82/1.88  tff(c_1827, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1789, c_1789, c_14])).
% 4.82/1.88  tff(c_1861, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1837, c_1837, c_1827])).
% 4.82/1.88  tff(c_153, plain, (![A_44]: (k2_relat_1(A_44)=k1_xboole_0 | k1_relat_1(A_44)!=k1_xboole_0 | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.82/1.88  tff(c_159, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_120, c_153])).
% 4.82/1.88  tff(c_168, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_152, c_159])).
% 4.82/1.88  tff(c_1817, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1789, c_168])).
% 4.82/1.88  tff(c_1894, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1861, c_1837, c_1837, c_1817])).
% 4.82/1.88  tff(c_1896, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_145])).
% 4.82/1.88  tff(c_1991, plain, (![A_185, B_186, C_187]: (k2_relset_1(A_185, B_186, C_187)=k2_relat_1(C_187) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.82/1.88  tff(c_1994, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1991])).
% 4.82/1.88  tff(c_2000, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1896, c_64, c_1994])).
% 4.82/1.88  tff(c_2018, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2000, c_2])).
% 4.82/1.88  tff(c_1895, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_145])).
% 4.82/1.88  tff(c_2008, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2000, c_1895])).
% 4.82/1.88  tff(c_2007, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2000, c_1896])).
% 4.82/1.88  tff(c_2113, plain, (![A_194]: (m1_subset_1(A_194, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_194), k2_relat_1(A_194)))) | ~v1_funct_1(A_194) | ~v1_relat_1(A_194))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.82/1.88  tff(c_2139, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2007, c_2113])).
% 4.82/1.88  tff(c_2158, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_72, c_2008, c_2139])).
% 4.82/1.88  tff(c_2190, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_2158, c_32])).
% 4.82/1.88  tff(c_2201, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2018, c_2190])).
% 4.82/1.88  tff(c_2011, plain, (![A_36]: (A_36='#skF_2' | ~v1_xboole_0(A_36))), inference(demodulation, [status(thm), theory('equality')], [c_2000, c_98])).
% 4.82/1.88  tff(c_2226, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_2201, c_2011])).
% 4.82/1.88  tff(c_8, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.82/1.88  tff(c_2014, plain, (![A_4]: (m1_subset_1('#skF_2', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_2000, c_8])).
% 4.82/1.88  tff(c_2237, plain, (![A_4]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_2226, c_2014])).
% 4.82/1.88  tff(c_2246, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2226, c_2007])).
% 4.82/1.88  tff(c_2475, plain, (![A_225]: (v1_xboole_0(A_225) | ~v1_xboole_0(k1_relat_1(A_225)) | ~v1_funct_1(A_225) | ~v1_relat_1(A_225))), inference(resolution, [status(thm)], [c_2113, c_32])).
% 4.82/1.88  tff(c_2766, plain, (![A_251]: (v1_xboole_0(k2_funct_1(A_251)) | ~v1_xboole_0(k2_relat_1(A_251)) | ~v1_funct_1(k2_funct_1(A_251)) | ~v1_relat_1(k2_funct_1(A_251)) | ~v2_funct_1(A_251) | ~v1_funct_1(A_251) | ~v1_relat_1(A_251))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2475])).
% 4.82/1.88  tff(c_2772, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2246, c_2766])).
% 4.82/1.88  tff(c_2779, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_72, c_66, c_141, c_2201, c_2772])).
% 4.82/1.88  tff(c_2780, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2779])).
% 4.82/1.88  tff(c_2783, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_2780])).
% 4.82/1.88  tff(c_2787, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_120, c_72, c_2783])).
% 4.82/1.88  tff(c_2788, plain, (v1_xboole_0(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2779])).
% 4.82/1.88  tff(c_6, plain, (![B_3, A_2]: (~v1_xboole_0(B_3) | B_3=A_2 | ~v1_xboole_0(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.82/1.88  tff(c_2227, plain, (![A_2]: (A_2='#skF_3' | ~v1_xboole_0(A_2))), inference(resolution, [status(thm)], [c_2201, c_6])).
% 4.82/1.88  tff(c_2798, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_2788, c_2227])).
% 4.82/1.88  tff(c_1901, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_140])).
% 4.82/1.88  tff(c_2250, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2226, c_1901])).
% 4.82/1.88  tff(c_2830, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2798, c_2250])).
% 4.82/1.88  tff(c_2836, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2237, c_2830])).
% 4.82/1.88  tff(c_2838, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_140])).
% 4.82/1.88  tff(c_3003, plain, (![C_274, A_275, B_276]: (v1_xboole_0(C_274) | ~m1_subset_1(C_274, k1_zfmisc_1(k2_zfmisc_1(A_275, B_276))) | ~v1_xboole_0(A_275))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.82/1.88  tff(c_3014, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_2838, c_3003])).
% 4.82/1.88  tff(c_3019, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_3014])).
% 4.82/1.88  tff(c_3092, plain, (![A_284, B_285, C_286]: (k2_relset_1(A_284, B_285, C_286)=k2_relat_1(C_286) | ~m1_subset_1(C_286, k1_zfmisc_1(k2_zfmisc_1(A_284, B_285))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.82/1.88  tff(c_3098, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_3092])).
% 4.82/1.88  tff(c_3106, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1896, c_3098])).
% 4.82/1.88  tff(c_3129, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3106, c_2])).
% 4.82/1.88  tff(c_3131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3019, c_3129])).
% 4.82/1.88  tff(c_3133, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_3014])).
% 4.82/1.88  tff(c_3142, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_3133, c_98])).
% 4.82/1.88  tff(c_3153, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3142, c_1895])).
% 4.82/1.88  tff(c_3152, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3142, c_1896])).
% 4.82/1.88  tff(c_3306, plain, (![A_292]: (m1_subset_1(A_292, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_292), k2_relat_1(A_292)))) | ~v1_funct_1(A_292) | ~v1_relat_1(A_292))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.82/1.88  tff(c_3329, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3152, c_3306])).
% 4.82/1.88  tff(c_3341, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_72, c_3153, c_3329])).
% 4.82/1.88  tff(c_3349, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_3341, c_32])).
% 4.82/1.88  tff(c_3357, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3133, c_3349])).
% 4.82/1.88  tff(c_3143, plain, (![A_2]: (A_2='#skF_2' | ~v1_xboole_0(A_2))), inference(resolution, [status(thm)], [c_3133, c_6])).
% 4.82/1.88  tff(c_3369, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_3357, c_3143])).
% 4.82/1.88  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 4.82/1.88  tff(c_3162, plain, (![A_1]: (r1_tarski('#skF_2', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_3142, c_4])).
% 4.82/1.88  tff(c_3384, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_3369, c_3162])).
% 4.82/1.88  tff(c_3385, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3369, c_3152])).
% 4.82/1.88  tff(c_3161, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3142, c_3142, c_14])).
% 4.82/1.88  tff(c_3382, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3369, c_3369, c_3161])).
% 4.82/1.88  tff(c_3528, plain, (![B_309, A_310]: (v1_funct_2(B_309, k1_relat_1(B_309), A_310) | ~r1_tarski(k2_relat_1(B_309), A_310) | ~v1_funct_1(B_309) | ~v1_relat_1(B_309))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.82/1.88  tff(c_3531, plain, (![A_310]: (v1_funct_2('#skF_3', '#skF_3', A_310) | ~r1_tarski(k2_relat_1('#skF_3'), A_310) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3382, c_3528])).
% 4.82/1.88  tff(c_3536, plain, (![A_310]: (v1_funct_2('#skF_3', '#skF_3', A_310))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_72, c_3384, c_3385, c_3531])).
% 4.82/1.88  tff(c_3132, plain, (v1_xboole_0(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_3014])).
% 4.82/1.88  tff(c_3227, plain, (![A_289]: (A_289='#skF_2' | ~v1_xboole_0(A_289))), inference(resolution, [status(thm)], [c_3133, c_6])).
% 4.82/1.88  tff(c_3234, plain, (k2_funct_1('#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_3132, c_3227])).
% 4.82/1.88  tff(c_2837, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_140])).
% 4.82/1.88  tff(c_3241, plain, (~v1_funct_2('#skF_2', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3234, c_2837])).
% 4.82/1.88  tff(c_3376, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3369, c_3369, c_3241])).
% 4.82/1.88  tff(c_3540, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3536, c_3376])).
% 4.82/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.82/1.88  
% 4.82/1.88  Inference rules
% 4.82/1.88  ----------------------
% 4.82/1.88  #Ref     : 0
% 4.82/1.88  #Sup     : 738
% 4.82/1.88  #Fact    : 0
% 4.82/1.88  #Define  : 0
% 4.82/1.88  #Split   : 23
% 4.82/1.88  #Chain   : 0
% 4.82/1.88  #Close   : 0
% 4.82/1.88  
% 4.82/1.88  Ordering : KBO
% 4.82/1.88  
% 4.82/1.88  Simplification rules
% 4.82/1.88  ----------------------
% 4.82/1.88  #Subsume      : 72
% 4.82/1.88  #Demod        : 1131
% 4.82/1.88  #Tautology    : 409
% 4.82/1.88  #SimpNegUnit  : 19
% 4.82/1.88  #BackRed      : 178
% 4.82/1.88  
% 4.82/1.88  #Partial instantiations: 0
% 4.82/1.88  #Strategies tried      : 1
% 4.82/1.88  
% 4.82/1.88  Timing (in seconds)
% 4.82/1.88  ----------------------
% 4.82/1.88  Preprocessing        : 0.34
% 4.82/1.88  Parsing              : 0.18
% 4.82/1.88  CNF conversion       : 0.02
% 4.82/1.88  Main loop            : 0.77
% 4.82/1.88  Inferencing          : 0.28
% 4.82/1.88  Reduction            : 0.26
% 4.82/1.88  Demodulation         : 0.19
% 4.82/1.88  BG Simplification    : 0.03
% 4.82/1.88  Subsumption          : 0.13
% 4.82/1.88  Abstraction          : 0.05
% 4.82/1.88  MUC search           : 0.00
% 4.82/1.88  Cooper               : 0.00
% 4.82/1.88  Total                : 1.16
% 4.82/1.88  Index Insertion      : 0.00
% 4.82/1.88  Index Deletion       : 0.00
% 4.82/1.88  Index Matching       : 0.00
% 4.82/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
