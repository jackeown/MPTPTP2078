%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:57 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 244 expanded)
%              Number of leaves         :   26 (  90 expanded)
%              Depth                    :    9
%              Number of atoms          :  181 ( 655 expanded)
%              Number of equality atoms :   65 ( 195 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_82,axiom,(
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

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_44,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    r1_tarski(k2_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_967,plain,(
    ! [C_189,A_190,B_191] :
      ( m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_190,B_191)))
      | ~ r1_tarski(k2_relat_1(C_189),B_191)
      | ~ r1_tarski(k1_relat_1(C_189),A_190)
      | ~ v1_relat_1(C_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_42,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_38,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_46,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38])).

tff(c_62,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_145,plain,(
    ! [C_44,A_45,B_46] :
      ( m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46)))
      | ~ r1_tarski(k2_relat_1(C_44),B_46)
      | ~ r1_tarski(k1_relat_1(C_44),A_45)
      | ~ v1_relat_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    ! [A_9,B_10,C_11] :
      ( k1_relset_1(A_9,B_10,C_11) = k1_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_168,plain,(
    ! [A_47,B_48,C_49] :
      ( k1_relset_1(A_47,B_48,C_49) = k1_relat_1(C_49)
      | ~ r1_tarski(k2_relat_1(C_49),B_48)
      | ~ r1_tarski(k1_relat_1(C_49),A_47)
      | ~ v1_relat_1(C_49) ) ),
    inference(resolution,[status(thm)],[c_145,c_22])).

tff(c_170,plain,(
    ! [A_47] :
      ( k1_relset_1(A_47,'#skF_1','#skF_2') = k1_relat_1('#skF_2')
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_47)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_168])).

tff(c_182,plain,(
    ! [A_50] :
      ( k1_relset_1(A_50,'#skF_1','#skF_2') = k1_relat_1('#skF_2')
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_170])).

tff(c_187,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_182])).

tff(c_24,plain,(
    ! [C_14,A_12,B_13] :
      ( m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13)))
      | ~ r1_tarski(k2_relat_1(C_14),B_13)
      | ~ r1_tarski(k1_relat_1(C_14),A_12)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_228,plain,(
    ! [B_54,C_55,A_56] :
      ( k1_xboole_0 = B_54
      | v1_funct_2(C_55,A_56,B_54)
      | k1_relset_1(A_56,B_54,C_55) != A_56
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_368,plain,(
    ! [B_79,C_80,A_81] :
      ( k1_xboole_0 = B_79
      | v1_funct_2(C_80,A_81,B_79)
      | k1_relset_1(A_81,B_79,C_80) != A_81
      | ~ r1_tarski(k2_relat_1(C_80),B_79)
      | ~ r1_tarski(k1_relat_1(C_80),A_81)
      | ~ v1_relat_1(C_80) ) ),
    inference(resolution,[status(thm)],[c_24,c_228])).

tff(c_370,plain,(
    ! [A_81] :
      ( k1_xboole_0 = '#skF_1'
      | v1_funct_2('#skF_2',A_81,'#skF_1')
      | k1_relset_1(A_81,'#skF_1','#skF_2') != A_81
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_81)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_368])).

tff(c_378,plain,(
    ! [A_81] :
      ( k1_xboole_0 = '#skF_1'
      | v1_funct_2('#skF_2',A_81,'#skF_1')
      | k1_relset_1(A_81,'#skF_1','#skF_2') != A_81
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_370])).

tff(c_382,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_378])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_409,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_8])).

tff(c_74,plain,(
    ! [B_24,A_25] :
      ( B_24 = A_25
      | ~ r1_tarski(B_24,A_25)
      | ~ r1_tarski(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_81,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_74])).

tff(c_101,plain,(
    ~ r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_428,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_101])).

tff(c_431,plain,(
    ! [A_82] :
      ( v1_funct_2('#skF_2',A_82,'#skF_1')
      | k1_relset_1(A_82,'#skF_1','#skF_2') != A_82
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_82) ) ),
    inference(splitRight,[status(thm)],[c_378])).

tff(c_435,plain,
    ( v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') != k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_431])).

tff(c_438,plain,(
    v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_435])).

tff(c_440,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_438])).

tff(c_441,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_63,plain,(
    ! [A_22] :
      ( k2_relat_1(A_22) != k1_xboole_0
      | k1_xboole_0 = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_67,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_44,c_63])).

tff(c_68,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_447,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_68])).

tff(c_492,plain,(
    ! [C_99,A_100,B_101] :
      ( m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ r1_tarski(k2_relat_1(C_99),B_101)
      | ~ r1_tarski(k1_relat_1(C_99),A_100)
      | ~ v1_relat_1(C_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_516,plain,(
    ! [A_103,B_104,C_105] :
      ( k1_relset_1(A_103,B_104,C_105) = k1_relat_1(C_105)
      | ~ r1_tarski(k2_relat_1(C_105),B_104)
      | ~ r1_tarski(k1_relat_1(C_105),A_103)
      | ~ v1_relat_1(C_105) ) ),
    inference(resolution,[status(thm)],[c_492,c_22])).

tff(c_529,plain,(
    ! [A_106,C_107] :
      ( k1_relset_1(A_106,k2_relat_1(C_107),C_107) = k1_relat_1(C_107)
      | ~ r1_tarski(k1_relat_1(C_107),A_106)
      | ~ v1_relat_1(C_107) ) ),
    inference(resolution,[status(thm)],[c_6,c_516])).

tff(c_543,plain,(
    ! [C_110] :
      ( k1_relset_1(k1_relat_1(C_110),k2_relat_1(C_110),C_110) = k1_relat_1(C_110)
      | ~ v1_relat_1(C_110) ) ),
    inference(resolution,[status(thm)],[c_6,c_529])).

tff(c_560,plain,
    ( k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_441,c_543])).

tff(c_572,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_560])).

tff(c_586,plain,(
    ! [B_112,C_113,A_114] :
      ( k1_xboole_0 = B_112
      | v1_funct_2(C_113,A_114,B_112)
      | k1_relset_1(A_114,B_112,C_113) != A_114
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_114,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_739,plain,(
    ! [B_137,C_138,A_139] :
      ( k1_xboole_0 = B_137
      | v1_funct_2(C_138,A_139,B_137)
      | k1_relset_1(A_139,B_137,C_138) != A_139
      | ~ r1_tarski(k2_relat_1(C_138),B_137)
      | ~ r1_tarski(k1_relat_1(C_138),A_139)
      | ~ v1_relat_1(C_138) ) ),
    inference(resolution,[status(thm)],[c_24,c_586])).

tff(c_741,plain,(
    ! [B_137,A_139] :
      ( k1_xboole_0 = B_137
      | v1_funct_2('#skF_2',A_139,B_137)
      | k1_relset_1(A_139,B_137,'#skF_2') != A_139
      | ~ r1_tarski('#skF_1',B_137)
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_139)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_441,c_739])).

tff(c_752,plain,(
    ! [B_140,A_141] :
      ( k1_xboole_0 = B_140
      | v1_funct_2('#skF_2',A_141,B_140)
      | k1_relset_1(A_141,B_140,'#skF_2') != A_141
      | ~ r1_tarski('#skF_1',B_140)
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_741])).

tff(c_757,plain,(
    ! [B_142] :
      ( k1_xboole_0 = B_142
      | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),B_142)
      | k1_relset_1(k1_relat_1('#skF_2'),B_142,'#skF_2') != k1_relat_1('#skF_2')
      | ~ r1_tarski('#skF_1',B_142) ) ),
    inference(resolution,[status(thm)],[c_6,c_752])).

tff(c_762,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') != k1_relat_1('#skF_2')
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_757,c_62])).

tff(c_768,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_572,c_762])).

tff(c_770,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_447,c_768])).

tff(c_771,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_16,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_776,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_771,c_16])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_775,plain,(
    ! [A_4] : m1_subset_1('#skF_2',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_10])).

tff(c_841,plain,(
    ! [A_154,B_155,C_156] :
      ( k1_relset_1(A_154,B_155,C_156) = k1_relat_1(C_156)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_845,plain,(
    ! [A_154,B_155] : k1_relset_1(A_154,B_155,'#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_775,c_841])).

tff(c_847,plain,(
    ! [A_154,B_155] : k1_relset_1(A_154,B_155,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_776,c_845])).

tff(c_30,plain,(
    ! [C_17,B_16] :
      ( v1_funct_2(C_17,k1_xboole_0,B_16)
      | k1_relset_1(k1_xboole_0,B_16,C_17) != k1_xboole_0
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_873,plain,(
    ! [C_165,B_166] :
      ( v1_funct_2(C_165,'#skF_2',B_166)
      | k1_relset_1('#skF_2',B_166,C_165) != '#skF_2'
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_166))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_771,c_771,c_771,c_30])).

tff(c_877,plain,(
    ! [B_166] :
      ( v1_funct_2('#skF_2','#skF_2',B_166)
      | k1_relset_1('#skF_2',B_166,'#skF_2') != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_775,c_873])).

tff(c_880,plain,(
    ! [B_166] : v1_funct_2('#skF_2','#skF_2',B_166) ),
    inference(demodulation,[status(thm),theory(equality)],[c_847,c_877])).

tff(c_799,plain,(
    ~ v1_funct_2('#skF_2','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_776,c_62])).

tff(c_883,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_880,c_799])).

tff(c_884,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_987,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_967,c_884])).

tff(c_996,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_6,c_40,c_987])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:16:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.58  
% 3.13/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.59  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.13/1.59  
% 3.13/1.59  %Foreground sorts:
% 3.13/1.59  
% 3.13/1.59  
% 3.13/1.59  %Background operators:
% 3.13/1.59  
% 3.13/1.59  
% 3.13/1.59  %Foreground operators:
% 3.13/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.13/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.13/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.13/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.13/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.13/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.13/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.13/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.13/1.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.13/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.13/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.13/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.13/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.13/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.13/1.59  
% 3.13/1.60  tff(f_95, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 3.13/1.60  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.13/1.60  tff(f_64, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 3.13/1.60  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.13/1.60  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.13/1.60  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.13/1.60  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.13/1.60  tff(f_44, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.13/1.60  tff(f_35, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.13/1.60  tff(c_44, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.13/1.60  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.13/1.60  tff(c_40, plain, (r1_tarski(k2_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.13/1.60  tff(c_967, plain, (![C_189, A_190, B_191]: (m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_190, B_191))) | ~r1_tarski(k2_relat_1(C_189), B_191) | ~r1_tarski(k1_relat_1(C_189), A_190) | ~v1_relat_1(C_189))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.13/1.60  tff(c_42, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.13/1.60  tff(c_38, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.13/1.60  tff(c_46, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38])).
% 3.13/1.60  tff(c_62, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 3.13/1.60  tff(c_145, plain, (![C_44, A_45, B_46]: (m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))) | ~r1_tarski(k2_relat_1(C_44), B_46) | ~r1_tarski(k1_relat_1(C_44), A_45) | ~v1_relat_1(C_44))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.13/1.60  tff(c_22, plain, (![A_9, B_10, C_11]: (k1_relset_1(A_9, B_10, C_11)=k1_relat_1(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.13/1.60  tff(c_168, plain, (![A_47, B_48, C_49]: (k1_relset_1(A_47, B_48, C_49)=k1_relat_1(C_49) | ~r1_tarski(k2_relat_1(C_49), B_48) | ~r1_tarski(k1_relat_1(C_49), A_47) | ~v1_relat_1(C_49))), inference(resolution, [status(thm)], [c_145, c_22])).
% 3.13/1.60  tff(c_170, plain, (![A_47]: (k1_relset_1(A_47, '#skF_1', '#skF_2')=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), A_47) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_168])).
% 3.13/1.60  tff(c_182, plain, (![A_50]: (k1_relset_1(A_50, '#skF_1', '#skF_2')=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), A_50))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_170])).
% 3.13/1.60  tff(c_187, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_6, c_182])).
% 3.13/1.60  tff(c_24, plain, (![C_14, A_12, B_13]: (m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))) | ~r1_tarski(k2_relat_1(C_14), B_13) | ~r1_tarski(k1_relat_1(C_14), A_12) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.13/1.60  tff(c_228, plain, (![B_54, C_55, A_56]: (k1_xboole_0=B_54 | v1_funct_2(C_55, A_56, B_54) | k1_relset_1(A_56, B_54, C_55)!=A_56 | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_54))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.13/1.60  tff(c_368, plain, (![B_79, C_80, A_81]: (k1_xboole_0=B_79 | v1_funct_2(C_80, A_81, B_79) | k1_relset_1(A_81, B_79, C_80)!=A_81 | ~r1_tarski(k2_relat_1(C_80), B_79) | ~r1_tarski(k1_relat_1(C_80), A_81) | ~v1_relat_1(C_80))), inference(resolution, [status(thm)], [c_24, c_228])).
% 3.13/1.60  tff(c_370, plain, (![A_81]: (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', A_81, '#skF_1') | k1_relset_1(A_81, '#skF_1', '#skF_2')!=A_81 | ~r1_tarski(k1_relat_1('#skF_2'), A_81) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_368])).
% 3.13/1.60  tff(c_378, plain, (![A_81]: (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', A_81, '#skF_1') | k1_relset_1(A_81, '#skF_1', '#skF_2')!=A_81 | ~r1_tarski(k1_relat_1('#skF_2'), A_81))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_370])).
% 3.13/1.60  tff(c_382, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_378])).
% 3.13/1.60  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.13/1.60  tff(c_409, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_382, c_8])).
% 3.13/1.60  tff(c_74, plain, (![B_24, A_25]: (B_24=A_25 | ~r1_tarski(B_24, A_25) | ~r1_tarski(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.13/1.60  tff(c_81, plain, (k2_relat_1('#skF_2')='#skF_1' | ~r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_74])).
% 3.13/1.60  tff(c_101, plain, (~r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_81])).
% 3.13/1.60  tff(c_428, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_409, c_101])).
% 3.13/1.60  tff(c_431, plain, (![A_82]: (v1_funct_2('#skF_2', A_82, '#skF_1') | k1_relset_1(A_82, '#skF_1', '#skF_2')!=A_82 | ~r1_tarski(k1_relat_1('#skF_2'), A_82))), inference(splitRight, [status(thm)], [c_378])).
% 3.13/1.60  tff(c_435, plain, (v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')!=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_6, c_431])).
% 3.13/1.60  tff(c_438, plain, (v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_187, c_435])).
% 3.13/1.60  tff(c_440, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_438])).
% 3.13/1.60  tff(c_441, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_81])).
% 3.13/1.60  tff(c_63, plain, (![A_22]: (k2_relat_1(A_22)!=k1_xboole_0 | k1_xboole_0=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.13/1.60  tff(c_67, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_44, c_63])).
% 3.13/1.60  tff(c_68, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_67])).
% 3.13/1.60  tff(c_447, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_441, c_68])).
% 3.13/1.60  tff(c_492, plain, (![C_99, A_100, B_101]: (m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | ~r1_tarski(k2_relat_1(C_99), B_101) | ~r1_tarski(k1_relat_1(C_99), A_100) | ~v1_relat_1(C_99))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.13/1.60  tff(c_516, plain, (![A_103, B_104, C_105]: (k1_relset_1(A_103, B_104, C_105)=k1_relat_1(C_105) | ~r1_tarski(k2_relat_1(C_105), B_104) | ~r1_tarski(k1_relat_1(C_105), A_103) | ~v1_relat_1(C_105))), inference(resolution, [status(thm)], [c_492, c_22])).
% 3.13/1.60  tff(c_529, plain, (![A_106, C_107]: (k1_relset_1(A_106, k2_relat_1(C_107), C_107)=k1_relat_1(C_107) | ~r1_tarski(k1_relat_1(C_107), A_106) | ~v1_relat_1(C_107))), inference(resolution, [status(thm)], [c_6, c_516])).
% 3.13/1.60  tff(c_543, plain, (![C_110]: (k1_relset_1(k1_relat_1(C_110), k2_relat_1(C_110), C_110)=k1_relat_1(C_110) | ~v1_relat_1(C_110))), inference(resolution, [status(thm)], [c_6, c_529])).
% 3.13/1.60  tff(c_560, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_441, c_543])).
% 3.13/1.60  tff(c_572, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_560])).
% 3.13/1.60  tff(c_586, plain, (![B_112, C_113, A_114]: (k1_xboole_0=B_112 | v1_funct_2(C_113, A_114, B_112) | k1_relset_1(A_114, B_112, C_113)!=A_114 | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_114, B_112))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.13/1.60  tff(c_739, plain, (![B_137, C_138, A_139]: (k1_xboole_0=B_137 | v1_funct_2(C_138, A_139, B_137) | k1_relset_1(A_139, B_137, C_138)!=A_139 | ~r1_tarski(k2_relat_1(C_138), B_137) | ~r1_tarski(k1_relat_1(C_138), A_139) | ~v1_relat_1(C_138))), inference(resolution, [status(thm)], [c_24, c_586])).
% 3.13/1.60  tff(c_741, plain, (![B_137, A_139]: (k1_xboole_0=B_137 | v1_funct_2('#skF_2', A_139, B_137) | k1_relset_1(A_139, B_137, '#skF_2')!=A_139 | ~r1_tarski('#skF_1', B_137) | ~r1_tarski(k1_relat_1('#skF_2'), A_139) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_441, c_739])).
% 3.13/1.60  tff(c_752, plain, (![B_140, A_141]: (k1_xboole_0=B_140 | v1_funct_2('#skF_2', A_141, B_140) | k1_relset_1(A_141, B_140, '#skF_2')!=A_141 | ~r1_tarski('#skF_1', B_140) | ~r1_tarski(k1_relat_1('#skF_2'), A_141))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_741])).
% 3.13/1.60  tff(c_757, plain, (![B_142]: (k1_xboole_0=B_142 | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), B_142) | k1_relset_1(k1_relat_1('#skF_2'), B_142, '#skF_2')!=k1_relat_1('#skF_2') | ~r1_tarski('#skF_1', B_142))), inference(resolution, [status(thm)], [c_6, c_752])).
% 3.13/1.60  tff(c_762, plain, (k1_xboole_0='#skF_1' | k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')!=k1_relat_1('#skF_2') | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_757, c_62])).
% 3.13/1.60  tff(c_768, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_572, c_762])).
% 3.13/1.60  tff(c_770, plain, $false, inference(negUnitSimplification, [status(thm)], [c_447, c_768])).
% 3.13/1.60  tff(c_771, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_67])).
% 3.13/1.60  tff(c_16, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.13/1.60  tff(c_776, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_771, c_771, c_16])).
% 3.13/1.60  tff(c_10, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.13/1.60  tff(c_775, plain, (![A_4]: (m1_subset_1('#skF_2', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_771, c_10])).
% 3.13/1.60  tff(c_841, plain, (![A_154, B_155, C_156]: (k1_relset_1(A_154, B_155, C_156)=k1_relat_1(C_156) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.13/1.60  tff(c_845, plain, (![A_154, B_155]: (k1_relset_1(A_154, B_155, '#skF_2')=k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_775, c_841])).
% 3.13/1.60  tff(c_847, plain, (![A_154, B_155]: (k1_relset_1(A_154, B_155, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_776, c_845])).
% 3.13/1.60  tff(c_30, plain, (![C_17, B_16]: (v1_funct_2(C_17, k1_xboole_0, B_16) | k1_relset_1(k1_xboole_0, B_16, C_17)!=k1_xboole_0 | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_16))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.13/1.60  tff(c_873, plain, (![C_165, B_166]: (v1_funct_2(C_165, '#skF_2', B_166) | k1_relset_1('#skF_2', B_166, C_165)!='#skF_2' | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_166))))), inference(demodulation, [status(thm), theory('equality')], [c_771, c_771, c_771, c_771, c_30])).
% 3.13/1.60  tff(c_877, plain, (![B_166]: (v1_funct_2('#skF_2', '#skF_2', B_166) | k1_relset_1('#skF_2', B_166, '#skF_2')!='#skF_2')), inference(resolution, [status(thm)], [c_775, c_873])).
% 3.13/1.60  tff(c_880, plain, (![B_166]: (v1_funct_2('#skF_2', '#skF_2', B_166))), inference(demodulation, [status(thm), theory('equality')], [c_847, c_877])).
% 3.13/1.60  tff(c_799, plain, (~v1_funct_2('#skF_2', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_776, c_62])).
% 3.13/1.60  tff(c_883, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_880, c_799])).
% 3.13/1.60  tff(c_884, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')))), inference(splitRight, [status(thm)], [c_46])).
% 3.13/1.60  tff(c_987, plain, (~r1_tarski(k2_relat_1('#skF_2'), '#skF_1') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_967, c_884])).
% 3.13/1.60  tff(c_996, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_6, c_40, c_987])).
% 3.13/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.60  
% 3.13/1.60  Inference rules
% 3.13/1.60  ----------------------
% 3.13/1.60  #Ref     : 0
% 3.13/1.60  #Sup     : 173
% 3.13/1.60  #Fact    : 0
% 3.13/1.60  #Define  : 0
% 3.13/1.60  #Split   : 11
% 3.13/1.60  #Chain   : 0
% 3.13/1.60  #Close   : 0
% 3.13/1.60  
% 3.13/1.60  Ordering : KBO
% 3.13/1.60  
% 3.13/1.60  Simplification rules
% 3.13/1.60  ----------------------
% 3.13/1.60  #Subsume      : 8
% 3.13/1.60  #Demod        : 300
% 3.13/1.60  #Tautology    : 100
% 3.13/1.60  #SimpNegUnit  : 2
% 3.13/1.60  #BackRed      : 40
% 3.13/1.60  
% 3.13/1.60  #Partial instantiations: 0
% 3.13/1.60  #Strategies tried      : 1
% 3.13/1.60  
% 3.13/1.60  Timing (in seconds)
% 3.13/1.60  ----------------------
% 3.13/1.61  Preprocessing        : 0.36
% 3.13/1.61  Parsing              : 0.19
% 3.13/1.61  CNF conversion       : 0.02
% 3.13/1.61  Main loop            : 0.40
% 3.13/1.61  Inferencing          : 0.14
% 3.13/1.61  Reduction            : 0.12
% 3.13/1.61  Demodulation         : 0.09
% 3.13/1.61  BG Simplification    : 0.02
% 3.13/1.61  Subsumption          : 0.08
% 3.13/1.61  Abstraction          : 0.02
% 3.13/1.61  MUC search           : 0.00
% 3.13/1.61  Cooper               : 0.00
% 3.13/1.61  Total                : 0.80
% 3.13/1.61  Index Insertion      : 0.00
% 3.13/1.61  Index Deletion       : 0.00
% 3.13/1.61  Index Matching       : 0.00
% 3.13/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
