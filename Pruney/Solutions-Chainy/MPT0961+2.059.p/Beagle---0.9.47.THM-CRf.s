%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:49 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 748 expanded)
%              Number of leaves         :   24 ( 252 expanded)
%              Depth                    :   13
%              Number of atoms          :  191 (1761 expanded)
%              Number of equality atoms :   51 ( 650 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_71,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_534,plain,(
    ! [A_121,B_122] :
      ( r1_tarski(A_121,B_122)
      | ~ m1_subset_1(A_121,k1_zfmisc_1(B_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_542,plain,(
    ! [A_2] : r1_tarski(A_2,A_2) ),
    inference(resolution,[status(thm)],[c_37,c_534])).

tff(c_380,plain,(
    ! [A_89,B_90] :
      ( r1_tarski(A_89,B_90)
      | ~ m1_subset_1(A_89,k1_zfmisc_1(B_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_384,plain,(
    ! [A_2] : r1_tarski(A_2,A_2) ),
    inference(resolution,[status(thm)],[c_37,c_380])).

tff(c_484,plain,(
    ! [C_116,A_117,B_118] :
      ( m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118)))
      | ~ r1_tarski(k2_relat_1(C_116),B_118)
      | ~ r1_tarski(k1_relat_1(C_116),A_117)
      | ~ v1_relat_1(C_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_61,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ m1_subset_1(A_19,k1_zfmisc_1(B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_65,plain,(
    ! [A_2] : r1_tarski(A_2,A_2) ),
    inference(resolution,[status(thm)],[c_37,c_61])).

tff(c_173,plain,(
    ! [C_49,A_50,B_51] :
      ( m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51)))
      | ~ r1_tarski(k2_relat_1(C_49),B_51)
      | ~ r1_tarski(k1_relat_1(C_49),A_50)
      | ~ v1_relat_1(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_202,plain,(
    ! [C_52,A_53,B_54] :
      ( r1_tarski(C_52,k2_zfmisc_1(A_53,B_54))
      | ~ r1_tarski(k2_relat_1(C_52),B_54)
      | ~ r1_tarski(k1_relat_1(C_52),A_53)
      | ~ v1_relat_1(C_52) ) ),
    inference(resolution,[status(thm)],[c_173,c_6])).

tff(c_207,plain,(
    ! [C_55,A_56] :
      ( r1_tarski(C_55,k2_zfmisc_1(A_56,k2_relat_1(C_55)))
      | ~ r1_tarski(k1_relat_1(C_55),A_56)
      | ~ v1_relat_1(C_55) ) ),
    inference(resolution,[status(thm)],[c_65,c_202])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_78,plain,(
    ! [A_26,B_27,C_28] :
      ( k1_relset_1(A_26,B_27,C_28) = k1_relat_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_87,plain,(
    ! [A_26,B_27,A_3] :
      ( k1_relset_1(A_26,B_27,A_3) = k1_relat_1(A_3)
      | ~ r1_tarski(A_3,k2_zfmisc_1(A_26,B_27)) ) ),
    inference(resolution,[status(thm)],[c_8,c_78])).

tff(c_226,plain,(
    ! [A_57,C_58] :
      ( k1_relset_1(A_57,k2_relat_1(C_58),C_58) = k1_relat_1(C_58)
      | ~ r1_tarski(k1_relat_1(C_58),A_57)
      | ~ v1_relat_1(C_58) ) ),
    inference(resolution,[status(thm)],[c_207,c_87])).

tff(c_234,plain,(
    ! [C_58] :
      ( k1_relset_1(k1_relat_1(C_58),k2_relat_1(C_58),C_58) = k1_relat_1(C_58)
      | ~ v1_relat_1(C_58) ) ),
    inference(resolution,[status(thm)],[c_65,c_226])).

tff(c_48,plain,(
    ! [A_17] :
      ( k2_relat_1(A_17) != k1_xboole_0
      | k1_xboole_0 = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_52,plain,
    ( k2_relat_1('#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_34,c_48])).

tff(c_58,plain,(
    k2_relat_1('#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_206,plain,(
    ! [C_52,A_53] :
      ( r1_tarski(C_52,k2_zfmisc_1(A_53,k2_relat_1(C_52)))
      | ~ r1_tarski(k1_relat_1(C_52),A_53)
      | ~ v1_relat_1(C_52) ) ),
    inference(resolution,[status(thm)],[c_65,c_202])).

tff(c_253,plain,(
    ! [B_63,C_64,A_65] :
      ( k1_xboole_0 = B_63
      | v1_funct_2(C_64,A_65,B_63)
      | k1_relset_1(A_65,B_63,C_64) != A_65
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_307,plain,(
    ! [B_73,A_74,A_75] :
      ( k1_xboole_0 = B_73
      | v1_funct_2(A_74,A_75,B_73)
      | k1_relset_1(A_75,B_73,A_74) != A_75
      | ~ r1_tarski(A_74,k2_zfmisc_1(A_75,B_73)) ) ),
    inference(resolution,[status(thm)],[c_8,c_253])).

tff(c_358,plain,(
    ! [C_87,A_88] :
      ( k2_relat_1(C_87) = k1_xboole_0
      | v1_funct_2(C_87,A_88,k2_relat_1(C_87))
      | k1_relset_1(A_88,k2_relat_1(C_87),C_87) != A_88
      | ~ r1_tarski(k1_relat_1(C_87),A_88)
      | ~ v1_relat_1(C_87) ) ),
    inference(resolution,[status(thm)],[c_206,c_307])).

tff(c_32,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_30,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_36,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30])).

tff(c_60,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_365,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_358,c_60])).

tff(c_369,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_65,c_365])).

tff(c_370,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_369])).

tff(c_373,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_370])).

tff(c_377,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_373])).

tff(c_378,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_506,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_484,c_378])).

tff(c_518,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_384,c_384,c_506])).

tff(c_519,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_520,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_527,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_520])).

tff(c_1028,plain,(
    ! [C_204,A_205,B_206] :
      ( m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(A_205,B_206)))
      | ~ r1_tarski(k2_relat_1(C_204),B_206)
      | ~ r1_tarski(k1_relat_1(C_204),A_205)
      | ~ v1_relat_1(C_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_569,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_527,c_36])).

tff(c_570,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_569])).

tff(c_665,plain,(
    ! [C_151,A_152,B_153] :
      ( m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153)))
      | ~ r1_tarski(k2_relat_1(C_151),B_153)
      | ~ r1_tarski(k1_relat_1(C_151),A_152)
      | ~ v1_relat_1(C_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    ! [A_12] :
      ( v1_funct_2(k1_xboole_0,A_12,k1_xboole_0)
      | k1_xboole_0 = A_12
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_12,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_587,plain,(
    ! [A_12] :
      ( v1_funct_2('#skF_1',A_12,'#skF_1')
      | A_12 = '#skF_1'
      | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(A_12,'#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_519,c_519,c_519,c_519,c_18])).

tff(c_681,plain,(
    ! [A_152] :
      ( v1_funct_2('#skF_1',A_152,'#skF_1')
      | A_152 = '#skF_1'
      | ~ r1_tarski(k2_relat_1('#skF_1'),'#skF_1')
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_152)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_665,c_587])).

tff(c_713,plain,(
    ! [A_157] :
      ( v1_funct_2('#skF_1',A_157,'#skF_1')
      | A_157 = '#skF_1'
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_542,c_527,c_681])).

tff(c_717,plain,
    ( v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1')
    | k1_relat_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_542,c_713])).

tff(c_720,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_570,c_717])).

tff(c_722,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_720,c_570])).

tff(c_14,plain,(
    ! [A_6,B_7,C_8] :
      ( k1_relset_1(A_6,B_7,C_8) = k1_relat_1(C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_817,plain,(
    ! [A_171,B_172,C_173] :
      ( k1_relset_1(A_171,B_172,C_173) = k1_relat_1(C_173)
      | ~ r1_tarski(k2_relat_1(C_173),B_172)
      | ~ r1_tarski(k1_relat_1(C_173),A_171)
      | ~ v1_relat_1(C_173) ) ),
    inference(resolution,[status(thm)],[c_665,c_14])).

tff(c_822,plain,(
    ! [A_171,B_172] :
      ( k1_relset_1(A_171,B_172,'#skF_1') = k1_relat_1('#skF_1')
      | ~ r1_tarski('#skF_1',B_172)
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_171)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_527,c_817])).

tff(c_826,plain,(
    ! [A_174,B_175] :
      ( k1_relset_1(A_174,B_175,'#skF_1') = '#skF_1'
      | ~ r1_tarski('#skF_1',B_175)
      | ~ r1_tarski('#skF_1',A_174) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_720,c_720,c_822])).

tff(c_834,plain,(
    ! [A_176] :
      ( k1_relset_1(A_176,'#skF_1','#skF_1') = '#skF_1'
      | ~ r1_tarski('#skF_1',A_176) ) ),
    inference(resolution,[status(thm)],[c_542,c_826])).

tff(c_843,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_542,c_834])).

tff(c_773,plain,(
    ! [C_166,A_167,B_168] :
      ( r1_tarski(C_166,k2_zfmisc_1(A_167,B_168))
      | ~ r1_tarski(k2_relat_1(C_166),B_168)
      | ~ r1_tarski(k1_relat_1(C_166),A_167)
      | ~ v1_relat_1(C_166) ) ),
    inference(resolution,[status(thm)],[c_665,c_6])).

tff(c_857,plain,(
    ! [C_179,A_180] :
      ( r1_tarski(C_179,k2_zfmisc_1(A_180,k2_relat_1(C_179)))
      | ~ r1_tarski(k1_relat_1(C_179),A_180)
      | ~ v1_relat_1(C_179) ) ),
    inference(resolution,[status(thm)],[c_542,c_773])).

tff(c_884,plain,(
    ! [A_180] :
      ( r1_tarski('#skF_1',k2_zfmisc_1(A_180,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_180)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_527,c_857])).

tff(c_898,plain,(
    ! [A_181] :
      ( r1_tarski('#skF_1',k2_zfmisc_1(A_181,'#skF_1'))
      | ~ r1_tarski('#skF_1',A_181) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_720,c_884])).

tff(c_22,plain,(
    ! [C_14,B_13] :
      ( v1_funct_2(C_14,k1_xboole_0,B_13)
      | k1_relset_1(k1_xboole_0,B_13,C_14) != k1_xboole_0
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_627,plain,(
    ! [C_143,B_144] :
      ( v1_funct_2(C_143,'#skF_1',B_144)
      | k1_relset_1('#skF_1',B_144,C_143) != '#skF_1'
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_144))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_519,c_519,c_519,c_22])).

tff(c_636,plain,(
    ! [A_3,B_144] :
      ( v1_funct_2(A_3,'#skF_1',B_144)
      | k1_relset_1('#skF_1',B_144,A_3) != '#skF_1'
      | ~ r1_tarski(A_3,k2_zfmisc_1('#skF_1',B_144)) ) ),
    inference(resolution,[status(thm)],[c_8,c_627])).

tff(c_907,plain,
    ( v1_funct_2('#skF_1','#skF_1','#skF_1')
    | k1_relset_1('#skF_1','#skF_1','#skF_1') != '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_898,c_636])).

tff(c_925,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_843,c_907])).

tff(c_927,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_722,c_925])).

tff(c_928,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),'#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_569])).

tff(c_1047,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),'#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1028,c_928])).

tff(c_1063,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_542,c_542,c_527,c_1047])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:54:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.42  
% 2.92/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.42  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.92/1.42  
% 2.92/1.42  %Foreground sorts:
% 2.92/1.42  
% 2.92/1.42  
% 2.92/1.42  %Background operators:
% 2.92/1.42  
% 2.92/1.42  
% 2.92/1.42  %Foreground operators:
% 2.92/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.92/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.92/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.92/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.92/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.92/1.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.92/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.92/1.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.92/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.92/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.92/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.92/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.92/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.92/1.42  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.92/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.92/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.92/1.42  
% 2.92/1.44  tff(f_82, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 2.92/1.44  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.92/1.44  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.92/1.44  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.92/1.44  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 2.92/1.44  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.92/1.44  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.92/1.44  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.92/1.44  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.92/1.44  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.92/1.44  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.92/1.44  tff(c_37, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 2.92/1.44  tff(c_534, plain, (![A_121, B_122]: (r1_tarski(A_121, B_122) | ~m1_subset_1(A_121, k1_zfmisc_1(B_122)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.92/1.44  tff(c_542, plain, (![A_2]: (r1_tarski(A_2, A_2))), inference(resolution, [status(thm)], [c_37, c_534])).
% 2.92/1.44  tff(c_380, plain, (![A_89, B_90]: (r1_tarski(A_89, B_90) | ~m1_subset_1(A_89, k1_zfmisc_1(B_90)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.92/1.44  tff(c_384, plain, (![A_2]: (r1_tarski(A_2, A_2))), inference(resolution, [status(thm)], [c_37, c_380])).
% 2.92/1.44  tff(c_484, plain, (![C_116, A_117, B_118]: (m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))) | ~r1_tarski(k2_relat_1(C_116), B_118) | ~r1_tarski(k1_relat_1(C_116), A_117) | ~v1_relat_1(C_116))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.92/1.44  tff(c_61, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~m1_subset_1(A_19, k1_zfmisc_1(B_20)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.92/1.44  tff(c_65, plain, (![A_2]: (r1_tarski(A_2, A_2))), inference(resolution, [status(thm)], [c_37, c_61])).
% 2.92/1.44  tff(c_173, plain, (![C_49, A_50, B_51]: (m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))) | ~r1_tarski(k2_relat_1(C_49), B_51) | ~r1_tarski(k1_relat_1(C_49), A_50) | ~v1_relat_1(C_49))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.92/1.44  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.92/1.44  tff(c_202, plain, (![C_52, A_53, B_54]: (r1_tarski(C_52, k2_zfmisc_1(A_53, B_54)) | ~r1_tarski(k2_relat_1(C_52), B_54) | ~r1_tarski(k1_relat_1(C_52), A_53) | ~v1_relat_1(C_52))), inference(resolution, [status(thm)], [c_173, c_6])).
% 2.92/1.44  tff(c_207, plain, (![C_55, A_56]: (r1_tarski(C_55, k2_zfmisc_1(A_56, k2_relat_1(C_55))) | ~r1_tarski(k1_relat_1(C_55), A_56) | ~v1_relat_1(C_55))), inference(resolution, [status(thm)], [c_65, c_202])).
% 2.92/1.44  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.92/1.44  tff(c_78, plain, (![A_26, B_27, C_28]: (k1_relset_1(A_26, B_27, C_28)=k1_relat_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.92/1.44  tff(c_87, plain, (![A_26, B_27, A_3]: (k1_relset_1(A_26, B_27, A_3)=k1_relat_1(A_3) | ~r1_tarski(A_3, k2_zfmisc_1(A_26, B_27)))), inference(resolution, [status(thm)], [c_8, c_78])).
% 2.92/1.44  tff(c_226, plain, (![A_57, C_58]: (k1_relset_1(A_57, k2_relat_1(C_58), C_58)=k1_relat_1(C_58) | ~r1_tarski(k1_relat_1(C_58), A_57) | ~v1_relat_1(C_58))), inference(resolution, [status(thm)], [c_207, c_87])).
% 2.92/1.44  tff(c_234, plain, (![C_58]: (k1_relset_1(k1_relat_1(C_58), k2_relat_1(C_58), C_58)=k1_relat_1(C_58) | ~v1_relat_1(C_58))), inference(resolution, [status(thm)], [c_65, c_226])).
% 2.92/1.44  tff(c_48, plain, (![A_17]: (k2_relat_1(A_17)!=k1_xboole_0 | k1_xboole_0=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.92/1.44  tff(c_52, plain, (k2_relat_1('#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_34, c_48])).
% 2.92/1.44  tff(c_58, plain, (k2_relat_1('#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_52])).
% 2.92/1.44  tff(c_206, plain, (![C_52, A_53]: (r1_tarski(C_52, k2_zfmisc_1(A_53, k2_relat_1(C_52))) | ~r1_tarski(k1_relat_1(C_52), A_53) | ~v1_relat_1(C_52))), inference(resolution, [status(thm)], [c_65, c_202])).
% 2.92/1.44  tff(c_253, plain, (![B_63, C_64, A_65]: (k1_xboole_0=B_63 | v1_funct_2(C_64, A_65, B_63) | k1_relset_1(A_65, B_63, C_64)!=A_65 | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_63))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.92/1.44  tff(c_307, plain, (![B_73, A_74, A_75]: (k1_xboole_0=B_73 | v1_funct_2(A_74, A_75, B_73) | k1_relset_1(A_75, B_73, A_74)!=A_75 | ~r1_tarski(A_74, k2_zfmisc_1(A_75, B_73)))), inference(resolution, [status(thm)], [c_8, c_253])).
% 2.92/1.44  tff(c_358, plain, (![C_87, A_88]: (k2_relat_1(C_87)=k1_xboole_0 | v1_funct_2(C_87, A_88, k2_relat_1(C_87)) | k1_relset_1(A_88, k2_relat_1(C_87), C_87)!=A_88 | ~r1_tarski(k1_relat_1(C_87), A_88) | ~v1_relat_1(C_87))), inference(resolution, [status(thm)], [c_206, c_307])).
% 2.92/1.44  tff(c_32, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.92/1.44  tff(c_30, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.92/1.44  tff(c_36, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30])).
% 2.92/1.44  tff(c_60, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_36])).
% 2.92/1.44  tff(c_365, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_358, c_60])).
% 2.92/1.44  tff(c_369, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_65, c_365])).
% 2.92/1.44  tff(c_370, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_58, c_369])).
% 2.92/1.44  tff(c_373, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_234, c_370])).
% 2.92/1.44  tff(c_377, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_373])).
% 2.92/1.44  tff(c_378, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_36])).
% 2.92/1.44  tff(c_506, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_484, c_378])).
% 2.92/1.44  tff(c_518, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_384, c_384, c_506])).
% 2.92/1.44  tff(c_519, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_52])).
% 2.92/1.44  tff(c_520, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 2.92/1.44  tff(c_527, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_519, c_520])).
% 2.92/1.44  tff(c_1028, plain, (![C_204, A_205, B_206]: (m1_subset_1(C_204, k1_zfmisc_1(k2_zfmisc_1(A_205, B_206))) | ~r1_tarski(k2_relat_1(C_204), B_206) | ~r1_tarski(k1_relat_1(C_204), A_205) | ~v1_relat_1(C_204))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.92/1.44  tff(c_569, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_527, c_527, c_36])).
% 2.92/1.44  tff(c_570, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_569])).
% 2.92/1.44  tff(c_665, plain, (![C_151, A_152, B_153]: (m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))) | ~r1_tarski(k2_relat_1(C_151), B_153) | ~r1_tarski(k1_relat_1(C_151), A_152) | ~v1_relat_1(C_151))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.92/1.44  tff(c_18, plain, (![A_12]: (v1_funct_2(k1_xboole_0, A_12, k1_xboole_0) | k1_xboole_0=A_12 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_12, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.92/1.44  tff(c_587, plain, (![A_12]: (v1_funct_2('#skF_1', A_12, '#skF_1') | A_12='#skF_1' | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(A_12, '#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_519, c_519, c_519, c_519, c_519, c_18])).
% 2.92/1.44  tff(c_681, plain, (![A_152]: (v1_funct_2('#skF_1', A_152, '#skF_1') | A_152='#skF_1' | ~r1_tarski(k2_relat_1('#skF_1'), '#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), A_152) | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_665, c_587])).
% 2.92/1.44  tff(c_713, plain, (![A_157]: (v1_funct_2('#skF_1', A_157, '#skF_1') | A_157='#skF_1' | ~r1_tarski(k1_relat_1('#skF_1'), A_157))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_542, c_527, c_681])).
% 2.92/1.44  tff(c_717, plain, (v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1') | k1_relat_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_542, c_713])).
% 2.92/1.44  tff(c_720, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_570, c_717])).
% 2.92/1.44  tff(c_722, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_720, c_570])).
% 2.92/1.44  tff(c_14, plain, (![A_6, B_7, C_8]: (k1_relset_1(A_6, B_7, C_8)=k1_relat_1(C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.92/1.44  tff(c_817, plain, (![A_171, B_172, C_173]: (k1_relset_1(A_171, B_172, C_173)=k1_relat_1(C_173) | ~r1_tarski(k2_relat_1(C_173), B_172) | ~r1_tarski(k1_relat_1(C_173), A_171) | ~v1_relat_1(C_173))), inference(resolution, [status(thm)], [c_665, c_14])).
% 2.92/1.44  tff(c_822, plain, (![A_171, B_172]: (k1_relset_1(A_171, B_172, '#skF_1')=k1_relat_1('#skF_1') | ~r1_tarski('#skF_1', B_172) | ~r1_tarski(k1_relat_1('#skF_1'), A_171) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_527, c_817])).
% 2.92/1.44  tff(c_826, plain, (![A_174, B_175]: (k1_relset_1(A_174, B_175, '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', B_175) | ~r1_tarski('#skF_1', A_174))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_720, c_720, c_822])).
% 2.92/1.44  tff(c_834, plain, (![A_176]: (k1_relset_1(A_176, '#skF_1', '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', A_176))), inference(resolution, [status(thm)], [c_542, c_826])).
% 2.92/1.44  tff(c_843, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_542, c_834])).
% 2.92/1.44  tff(c_773, plain, (![C_166, A_167, B_168]: (r1_tarski(C_166, k2_zfmisc_1(A_167, B_168)) | ~r1_tarski(k2_relat_1(C_166), B_168) | ~r1_tarski(k1_relat_1(C_166), A_167) | ~v1_relat_1(C_166))), inference(resolution, [status(thm)], [c_665, c_6])).
% 2.92/1.44  tff(c_857, plain, (![C_179, A_180]: (r1_tarski(C_179, k2_zfmisc_1(A_180, k2_relat_1(C_179))) | ~r1_tarski(k1_relat_1(C_179), A_180) | ~v1_relat_1(C_179))), inference(resolution, [status(thm)], [c_542, c_773])).
% 2.92/1.44  tff(c_884, plain, (![A_180]: (r1_tarski('#skF_1', k2_zfmisc_1(A_180, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_1'), A_180) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_527, c_857])).
% 2.92/1.44  tff(c_898, plain, (![A_181]: (r1_tarski('#skF_1', k2_zfmisc_1(A_181, '#skF_1')) | ~r1_tarski('#skF_1', A_181))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_720, c_884])).
% 2.92/1.44  tff(c_22, plain, (![C_14, B_13]: (v1_funct_2(C_14, k1_xboole_0, B_13) | k1_relset_1(k1_xboole_0, B_13, C_14)!=k1_xboole_0 | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_13))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.92/1.44  tff(c_627, plain, (![C_143, B_144]: (v1_funct_2(C_143, '#skF_1', B_144) | k1_relset_1('#skF_1', B_144, C_143)!='#skF_1' | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_144))))), inference(demodulation, [status(thm), theory('equality')], [c_519, c_519, c_519, c_519, c_22])).
% 2.92/1.44  tff(c_636, plain, (![A_3, B_144]: (v1_funct_2(A_3, '#skF_1', B_144) | k1_relset_1('#skF_1', B_144, A_3)!='#skF_1' | ~r1_tarski(A_3, k2_zfmisc_1('#skF_1', B_144)))), inference(resolution, [status(thm)], [c_8, c_627])).
% 2.92/1.44  tff(c_907, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1') | k1_relset_1('#skF_1', '#skF_1', '#skF_1')!='#skF_1' | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_898, c_636])).
% 2.92/1.44  tff(c_925, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_542, c_843, c_907])).
% 2.92/1.44  tff(c_927, plain, $false, inference(negUnitSimplification, [status(thm)], [c_722, c_925])).
% 2.92/1.44  tff(c_928, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), '#skF_1')))), inference(splitRight, [status(thm)], [c_569])).
% 2.92/1.44  tff(c_1047, plain, (~r1_tarski(k2_relat_1('#skF_1'), '#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1028, c_928])).
% 2.92/1.44  tff(c_1063, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_542, c_542, c_527, c_1047])).
% 2.92/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.44  
% 2.92/1.44  Inference rules
% 2.92/1.44  ----------------------
% 2.92/1.44  #Ref     : 0
% 2.92/1.44  #Sup     : 187
% 2.92/1.44  #Fact    : 0
% 2.92/1.44  #Define  : 0
% 2.92/1.44  #Split   : 5
% 2.92/1.44  #Chain   : 0
% 2.92/1.44  #Close   : 0
% 2.92/1.44  
% 2.92/1.44  Ordering : KBO
% 2.92/1.44  
% 2.92/1.44  Simplification rules
% 2.92/1.44  ----------------------
% 2.92/1.44  #Subsume      : 18
% 2.92/1.44  #Demod        : 112
% 2.92/1.44  #Tautology    : 51
% 2.92/1.44  #SimpNegUnit  : 3
% 2.92/1.44  #BackRed      : 4
% 2.92/1.44  
% 2.92/1.44  #Partial instantiations: 0
% 2.92/1.44  #Strategies tried      : 1
% 2.92/1.44  
% 2.92/1.44  Timing (in seconds)
% 2.92/1.44  ----------------------
% 2.92/1.45  Preprocessing        : 0.29
% 2.92/1.45  Parsing              : 0.15
% 2.92/1.45  CNF conversion       : 0.02
% 2.92/1.45  Main loop            : 0.38
% 2.92/1.45  Inferencing          : 0.15
% 2.92/1.45  Reduction            : 0.10
% 2.92/1.45  Demodulation         : 0.07
% 2.92/1.45  BG Simplification    : 0.02
% 2.92/1.45  Subsumption          : 0.08
% 2.92/1.45  Abstraction          : 0.02
% 2.92/1.45  MUC search           : 0.00
% 2.92/1.45  Cooper               : 0.00
% 2.92/1.45  Total                : 0.71
% 2.92/1.45  Index Insertion      : 0.00
% 2.92/1.45  Index Deletion       : 0.00
% 2.92/1.45  Index Matching       : 0.00
% 2.92/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
