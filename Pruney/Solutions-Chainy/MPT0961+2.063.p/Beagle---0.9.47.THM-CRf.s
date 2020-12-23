%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:50 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :  124 (1076 expanded)
%              Number of leaves         :   29 ( 362 expanded)
%              Depth                    :   12
%              Number of atoms          :  195 (2472 expanded)
%              Number of equality atoms :   80 ( 752 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_40,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_45,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1673,plain,(
    ! [A_235] :
      ( r1_tarski(A_235,k2_zfmisc_1(k1_relat_1(A_235),k2_relat_1(A_235)))
      | ~ v1_relat_1(A_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_58,plain,(
    ! [A_18,B_19] :
      ( v1_xboole_0(k2_zfmisc_1(A_18,B_19))
      | ~ v1_xboole_0(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_63,plain,(
    ! [A_20,B_21] :
      ( k2_zfmisc_1(A_20,B_21) = k1_xboole_0
      | ~ v1_xboole_0(B_21) ) ),
    inference(resolution,[status(thm)],[c_58,c_4])).

tff(c_69,plain,(
    ! [A_20] : k2_zfmisc_1(A_20,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_63])).

tff(c_14,plain,(
    ! [A_7] :
      ( r1_tarski(A_7,k2_zfmisc_1(k1_relat_1(A_7),k2_relat_1(A_7)))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_448,plain,(
    ! [A_88,B_89,C_90] :
      ( k1_relset_1(A_88,B_89,C_90) = k1_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_503,plain,(
    ! [A_99,B_100,A_101] :
      ( k1_relset_1(A_99,B_100,A_101) = k1_relat_1(A_101)
      | ~ r1_tarski(A_101,k2_zfmisc_1(A_99,B_100)) ) ),
    inference(resolution,[status(thm)],[c_10,c_448])).

tff(c_513,plain,(
    ! [A_7] :
      ( k1_relset_1(k1_relat_1(A_7),k2_relat_1(A_7),A_7) = k1_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_14,c_503])).

tff(c_1301,plain,(
    ! [B_197,C_198,A_199] :
      ( k1_xboole_0 = B_197
      | v1_funct_2(C_198,A_199,B_197)
      | k1_relset_1(A_199,B_197,C_198) != A_199
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(A_199,B_197))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1419,plain,(
    ! [B_215,A_216,A_217] :
      ( k1_xboole_0 = B_215
      | v1_funct_2(A_216,A_217,B_215)
      | k1_relset_1(A_217,B_215,A_216) != A_217
      | ~ r1_tarski(A_216,k2_zfmisc_1(A_217,B_215)) ) ),
    inference(resolution,[status(thm)],[c_10,c_1301])).

tff(c_1446,plain,(
    ! [A_221] :
      ( k2_relat_1(A_221) = k1_xboole_0
      | v1_funct_2(A_221,k1_relat_1(A_221),k2_relat_1(A_221))
      | k1_relset_1(k1_relat_1(A_221),k2_relat_1(A_221),A_221) != k1_relat_1(A_221)
      | ~ v1_relat_1(A_221) ) ),
    inference(resolution,[status(thm)],[c_14,c_1419])).

tff(c_36,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_34,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_40,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34])).

tff(c_82,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_1449,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1446,c_82])).

tff(c_1455,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1449])).

tff(c_1458,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1455])).

tff(c_1461,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_513,c_1458])).

tff(c_1465,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1461])).

tff(c_1466,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1455])).

tff(c_1478,plain,
    ( r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k1_xboole_0))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1466,c_14])).

tff(c_1486,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_69,c_1478])).

tff(c_12,plain,(
    ! [A_6] : k9_relat_1(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_16,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_116,plain,(
    ! [A_31,B_32] :
      ( k9_relat_1(k6_relat_1(A_31),B_32) = B_32
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_121,plain,(
    ! [B_33,A_34] :
      ( k9_relat_1(k6_relat_1(B_33),A_34) = A_34
      | ~ r1_tarski(A_34,B_33) ) ),
    inference(resolution,[status(thm)],[c_10,c_116])).

tff(c_130,plain,(
    ! [A_34] :
      ( k9_relat_1(k1_xboole_0,A_34) = A_34
      | ~ r1_tarski(A_34,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_121])).

tff(c_133,plain,(
    ! [A_34] :
      ( k1_xboole_0 = A_34
      | ~ r1_tarski(A_34,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_130])).

tff(c_1494,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1486,c_133])).

tff(c_621,plain,(
    ! [B_115,C_116,A_117] :
      ( k1_xboole_0 = B_115
      | v1_funct_2(C_116,A_117,B_115)
      | k1_relset_1(A_117,B_115,C_116) != A_117
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_117,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_716,plain,(
    ! [B_135,A_136,A_137] :
      ( k1_xboole_0 = B_135
      | v1_funct_2(A_136,A_137,B_135)
      | k1_relset_1(A_137,B_135,A_136) != A_137
      | ~ r1_tarski(A_136,k2_zfmisc_1(A_137,B_135)) ) ),
    inference(resolution,[status(thm)],[c_10,c_621])).

tff(c_750,plain,(
    ! [A_144] :
      ( k2_relat_1(A_144) = k1_xboole_0
      | v1_funct_2(A_144,k1_relat_1(A_144),k2_relat_1(A_144))
      | k1_relset_1(k1_relat_1(A_144),k2_relat_1(A_144),A_144) != k1_relat_1(A_144)
      | ~ v1_relat_1(A_144) ) ),
    inference(resolution,[status(thm)],[c_14,c_716])).

tff(c_753,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_750,c_82])).

tff(c_756,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_753])).

tff(c_757,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_756])).

tff(c_760,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_513,c_757])).

tff(c_764,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_760])).

tff(c_765,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_756])).

tff(c_777,plain,
    ( r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k1_xboole_0))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_765,c_14])).

tff(c_785,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_69,c_777])).

tff(c_793,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_785,c_133])).

tff(c_137,plain,(
    ! [A_36,B_37,C_38] :
      ( k1_relset_1(A_36,B_37,C_38) = k1_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_159,plain,(
    ! [A_43,B_44,A_45] :
      ( k1_relset_1(A_43,B_44,A_45) = k1_relat_1(A_45)
      | ~ r1_tarski(A_45,k2_zfmisc_1(A_43,B_44)) ) ),
    inference(resolution,[status(thm)],[c_10,c_137])).

tff(c_169,plain,(
    ! [A_7] :
      ( k1_relset_1(k1_relat_1(A_7),k2_relat_1(A_7),A_7) = k1_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_14,c_159])).

tff(c_253,plain,(
    ! [B_66,C_67,A_68] :
      ( k1_xboole_0 = B_66
      | v1_funct_2(C_67,A_68,B_66)
      | k1_relset_1(A_68,B_66,C_67) != A_68
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_283,plain,(
    ! [B_72,A_73,A_74] :
      ( k1_xboole_0 = B_72
      | v1_funct_2(A_73,A_74,B_72)
      | k1_relset_1(A_74,B_72,A_73) != A_74
      | ~ r1_tarski(A_73,k2_zfmisc_1(A_74,B_72)) ) ),
    inference(resolution,[status(thm)],[c_10,c_253])).

tff(c_342,plain,(
    ! [A_87] :
      ( k2_relat_1(A_87) = k1_xboole_0
      | v1_funct_2(A_87,k1_relat_1(A_87),k2_relat_1(A_87))
      | k1_relset_1(k1_relat_1(A_87),k2_relat_1(A_87),A_87) != k1_relat_1(A_87)
      | ~ v1_relat_1(A_87) ) ),
    inference(resolution,[status(thm)],[c_14,c_283])).

tff(c_345,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_342,c_82])).

tff(c_348,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_345])).

tff(c_349,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_348])).

tff(c_352,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_349])).

tff(c_356,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_352])).

tff(c_357,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_348])).

tff(c_369,plain,
    ( r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k1_xboole_0))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_14])).

tff(c_377,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_69,c_369])).

tff(c_385,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_377,c_133])).

tff(c_386,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_377])).

tff(c_22,plain,(
    ! [A_13] :
      ( v1_funct_2(k1_xboole_0,A_13,k1_xboole_0)
      | k1_xboole_0 = A_13
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_13,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_135,plain,(
    ! [A_13] :
      ( v1_funct_2(k1_xboole_0,A_13,k1_xboole_0)
      | k1_xboole_0 = A_13
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_22])).

tff(c_136,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_152,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_136])).

tff(c_408,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_385,c_152])).

tff(c_445,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_408])).

tff(c_447,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_483,plain,(
    ! [A_94,C_95] :
      ( k1_relset_1(A_94,k1_xboole_0,C_95) = k1_relat_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_448])).

tff(c_489,plain,(
    ! [A_94] : k1_relset_1(A_94,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_447,c_483])).

tff(c_523,plain,(
    ! [C_103,B_104] :
      ( v1_funct_2(C_103,k1_xboole_0,B_104)
      | k1_relset_1(k1_xboole_0,B_104,C_103) != k1_xboole_0
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_554,plain,(
    ! [C_109] :
      ( v1_funct_2(C_109,k1_xboole_0,k1_xboole_0)
      | k1_relset_1(k1_xboole_0,k1_xboole_0,C_109) != k1_xboole_0
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_523])).

tff(c_557,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_447,c_554])).

tff(c_563,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_557])).

tff(c_565,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_563])).

tff(c_812,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_793,c_793,c_565])).

tff(c_446,plain,(
    ! [A_13] :
      ( v1_funct_2(k1_xboole_0,A_13,k1_xboole_0)
      | k1_xboole_0 = A_13 ) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_952,plain,(
    ! [A_155] :
      ( v1_funct_2('#skF_1',A_155,'#skF_1')
      | A_155 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_793,c_793,c_793,c_446])).

tff(c_767,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_765,c_82])).

tff(c_795,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_793,c_767])).

tff(c_958,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_952,c_795])).

tff(c_964,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_812,c_958])).

tff(c_966,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_563])).

tff(c_1518,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1494,c_1494,c_966])).

tff(c_1468,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1466,c_82])).

tff(c_1496,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1494,c_1468])).

tff(c_1594,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1518,c_1496])).

tff(c_965,plain,(
    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_563])).

tff(c_1517,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1494,c_1494,c_1494,c_965])).

tff(c_1615,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1594,c_1517])).

tff(c_1616,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1627,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_10,c_1616])).

tff(c_1676,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1673,c_1627])).

tff(c_1680,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1676])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:30:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.58  
% 3.70/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.58  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.70/1.58  
% 3.70/1.58  %Foreground sorts:
% 3.70/1.58  
% 3.70/1.58  
% 3.70/1.58  %Background operators:
% 3.70/1.58  
% 3.70/1.58  
% 3.70/1.58  %Foreground operators:
% 3.70/1.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.70/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.70/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.70/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.70/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.70/1.58  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.70/1.58  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.70/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.70/1.58  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.70/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.70/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.70/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.70/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.70/1.58  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.70/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.70/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.70/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.70/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.70/1.58  
% 3.70/1.60  tff(f_82, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 3.70/1.60  tff(f_44, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 3.70/1.60  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.70/1.60  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.70/1.60  tff(f_34, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 3.70/1.60  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.70/1.60  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.70/1.60  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.70/1.60  tff(f_40, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 3.70/1.60  tff(f_45, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 3.70/1.60  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 3.70/1.60  tff(c_38, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.70/1.60  tff(c_1673, plain, (![A_235]: (r1_tarski(A_235, k2_zfmisc_1(k1_relat_1(A_235), k2_relat_1(A_235))) | ~v1_relat_1(A_235))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.70/1.60  tff(c_10, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.70/1.60  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.70/1.60  tff(c_58, plain, (![A_18, B_19]: (v1_xboole_0(k2_zfmisc_1(A_18, B_19)) | ~v1_xboole_0(B_19))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.70/1.60  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.70/1.60  tff(c_63, plain, (![A_20, B_21]: (k2_zfmisc_1(A_20, B_21)=k1_xboole_0 | ~v1_xboole_0(B_21))), inference(resolution, [status(thm)], [c_58, c_4])).
% 3.70/1.60  tff(c_69, plain, (![A_20]: (k2_zfmisc_1(A_20, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_63])).
% 3.70/1.60  tff(c_14, plain, (![A_7]: (r1_tarski(A_7, k2_zfmisc_1(k1_relat_1(A_7), k2_relat_1(A_7))) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.70/1.60  tff(c_448, plain, (![A_88, B_89, C_90]: (k1_relset_1(A_88, B_89, C_90)=k1_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.70/1.60  tff(c_503, plain, (![A_99, B_100, A_101]: (k1_relset_1(A_99, B_100, A_101)=k1_relat_1(A_101) | ~r1_tarski(A_101, k2_zfmisc_1(A_99, B_100)))), inference(resolution, [status(thm)], [c_10, c_448])).
% 3.70/1.60  tff(c_513, plain, (![A_7]: (k1_relset_1(k1_relat_1(A_7), k2_relat_1(A_7), A_7)=k1_relat_1(A_7) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_14, c_503])).
% 3.70/1.60  tff(c_1301, plain, (![B_197, C_198, A_199]: (k1_xboole_0=B_197 | v1_funct_2(C_198, A_199, B_197) | k1_relset_1(A_199, B_197, C_198)!=A_199 | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(A_199, B_197))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.70/1.60  tff(c_1419, plain, (![B_215, A_216, A_217]: (k1_xboole_0=B_215 | v1_funct_2(A_216, A_217, B_215) | k1_relset_1(A_217, B_215, A_216)!=A_217 | ~r1_tarski(A_216, k2_zfmisc_1(A_217, B_215)))), inference(resolution, [status(thm)], [c_10, c_1301])).
% 3.70/1.60  tff(c_1446, plain, (![A_221]: (k2_relat_1(A_221)=k1_xboole_0 | v1_funct_2(A_221, k1_relat_1(A_221), k2_relat_1(A_221)) | k1_relset_1(k1_relat_1(A_221), k2_relat_1(A_221), A_221)!=k1_relat_1(A_221) | ~v1_relat_1(A_221))), inference(resolution, [status(thm)], [c_14, c_1419])).
% 3.70/1.60  tff(c_36, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.70/1.60  tff(c_34, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.70/1.60  tff(c_40, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34])).
% 3.70/1.60  tff(c_82, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_40])).
% 3.70/1.60  tff(c_1449, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1446, c_82])).
% 3.70/1.60  tff(c_1455, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1449])).
% 3.70/1.60  tff(c_1458, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_1455])).
% 3.70/1.60  tff(c_1461, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_513, c_1458])).
% 3.70/1.60  tff(c_1465, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_1461])).
% 3.70/1.60  tff(c_1466, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1455])).
% 3.70/1.60  tff(c_1478, plain, (r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k1_xboole_0)) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1466, c_14])).
% 3.70/1.60  tff(c_1486, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_69, c_1478])).
% 3.70/1.60  tff(c_12, plain, (![A_6]: (k9_relat_1(k1_xboole_0, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.70/1.60  tff(c_16, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.70/1.60  tff(c_116, plain, (![A_31, B_32]: (k9_relat_1(k6_relat_1(A_31), B_32)=B_32 | ~m1_subset_1(B_32, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.70/1.60  tff(c_121, plain, (![B_33, A_34]: (k9_relat_1(k6_relat_1(B_33), A_34)=A_34 | ~r1_tarski(A_34, B_33))), inference(resolution, [status(thm)], [c_10, c_116])).
% 3.70/1.60  tff(c_130, plain, (![A_34]: (k9_relat_1(k1_xboole_0, A_34)=A_34 | ~r1_tarski(A_34, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_121])).
% 3.70/1.60  tff(c_133, plain, (![A_34]: (k1_xboole_0=A_34 | ~r1_tarski(A_34, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_130])).
% 3.70/1.60  tff(c_1494, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_1486, c_133])).
% 3.70/1.60  tff(c_621, plain, (![B_115, C_116, A_117]: (k1_xboole_0=B_115 | v1_funct_2(C_116, A_117, B_115) | k1_relset_1(A_117, B_115, C_116)!=A_117 | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_117, B_115))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.70/1.60  tff(c_716, plain, (![B_135, A_136, A_137]: (k1_xboole_0=B_135 | v1_funct_2(A_136, A_137, B_135) | k1_relset_1(A_137, B_135, A_136)!=A_137 | ~r1_tarski(A_136, k2_zfmisc_1(A_137, B_135)))), inference(resolution, [status(thm)], [c_10, c_621])).
% 3.70/1.60  tff(c_750, plain, (![A_144]: (k2_relat_1(A_144)=k1_xboole_0 | v1_funct_2(A_144, k1_relat_1(A_144), k2_relat_1(A_144)) | k1_relset_1(k1_relat_1(A_144), k2_relat_1(A_144), A_144)!=k1_relat_1(A_144) | ~v1_relat_1(A_144))), inference(resolution, [status(thm)], [c_14, c_716])).
% 3.70/1.60  tff(c_753, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_750, c_82])).
% 3.70/1.60  tff(c_756, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_753])).
% 3.70/1.60  tff(c_757, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_756])).
% 3.70/1.60  tff(c_760, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_513, c_757])).
% 3.70/1.60  tff(c_764, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_760])).
% 3.70/1.60  tff(c_765, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_756])).
% 3.70/1.60  tff(c_777, plain, (r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k1_xboole_0)) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_765, c_14])).
% 3.70/1.60  tff(c_785, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_69, c_777])).
% 3.70/1.60  tff(c_793, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_785, c_133])).
% 3.70/1.60  tff(c_137, plain, (![A_36, B_37, C_38]: (k1_relset_1(A_36, B_37, C_38)=k1_relat_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.70/1.60  tff(c_159, plain, (![A_43, B_44, A_45]: (k1_relset_1(A_43, B_44, A_45)=k1_relat_1(A_45) | ~r1_tarski(A_45, k2_zfmisc_1(A_43, B_44)))), inference(resolution, [status(thm)], [c_10, c_137])).
% 3.70/1.60  tff(c_169, plain, (![A_7]: (k1_relset_1(k1_relat_1(A_7), k2_relat_1(A_7), A_7)=k1_relat_1(A_7) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_14, c_159])).
% 3.70/1.60  tff(c_253, plain, (![B_66, C_67, A_68]: (k1_xboole_0=B_66 | v1_funct_2(C_67, A_68, B_66) | k1_relset_1(A_68, B_66, C_67)!=A_68 | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_66))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.70/1.60  tff(c_283, plain, (![B_72, A_73, A_74]: (k1_xboole_0=B_72 | v1_funct_2(A_73, A_74, B_72) | k1_relset_1(A_74, B_72, A_73)!=A_74 | ~r1_tarski(A_73, k2_zfmisc_1(A_74, B_72)))), inference(resolution, [status(thm)], [c_10, c_253])).
% 3.70/1.60  tff(c_342, plain, (![A_87]: (k2_relat_1(A_87)=k1_xboole_0 | v1_funct_2(A_87, k1_relat_1(A_87), k2_relat_1(A_87)) | k1_relset_1(k1_relat_1(A_87), k2_relat_1(A_87), A_87)!=k1_relat_1(A_87) | ~v1_relat_1(A_87))), inference(resolution, [status(thm)], [c_14, c_283])).
% 3.70/1.60  tff(c_345, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_342, c_82])).
% 3.70/1.60  tff(c_348, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_345])).
% 3.70/1.60  tff(c_349, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_348])).
% 3.70/1.60  tff(c_352, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_169, c_349])).
% 3.70/1.60  tff(c_356, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_352])).
% 3.70/1.60  tff(c_357, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_348])).
% 3.70/1.60  tff(c_369, plain, (r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k1_xboole_0)) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_357, c_14])).
% 3.70/1.60  tff(c_377, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_69, c_369])).
% 3.70/1.60  tff(c_385, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_377, c_133])).
% 3.70/1.60  tff(c_386, plain, (r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_385, c_377])).
% 3.70/1.60  tff(c_22, plain, (![A_13]: (v1_funct_2(k1_xboole_0, A_13, k1_xboole_0) | k1_xboole_0=A_13 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_13, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.70/1.60  tff(c_135, plain, (![A_13]: (v1_funct_2(k1_xboole_0, A_13, k1_xboole_0) | k1_xboole_0=A_13 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_22])).
% 3.70/1.60  tff(c_136, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_135])).
% 3.70/1.60  tff(c_152, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_136])).
% 3.70/1.60  tff(c_408, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_385, c_385, c_152])).
% 3.70/1.60  tff(c_445, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_386, c_408])).
% 3.70/1.60  tff(c_447, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_135])).
% 3.70/1.60  tff(c_483, plain, (![A_94, C_95]: (k1_relset_1(A_94, k1_xboole_0, C_95)=k1_relat_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_69, c_448])).
% 3.70/1.60  tff(c_489, plain, (![A_94]: (k1_relset_1(A_94, k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_447, c_483])).
% 3.70/1.60  tff(c_523, plain, (![C_103, B_104]: (v1_funct_2(C_103, k1_xboole_0, B_104) | k1_relset_1(k1_xboole_0, B_104, C_103)!=k1_xboole_0 | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_104))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.70/1.60  tff(c_554, plain, (![C_109]: (v1_funct_2(C_109, k1_xboole_0, k1_xboole_0) | k1_relset_1(k1_xboole_0, k1_xboole_0, C_109)!=k1_xboole_0 | ~m1_subset_1(C_109, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_69, c_523])).
% 3.70/1.60  tff(c_557, plain, (v1_funct_2(k1_xboole_0, k1_xboole_0, k1_xboole_0) | k1_relset_1(k1_xboole_0, k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_447, c_554])).
% 3.70/1.60  tff(c_563, plain, (v1_funct_2(k1_xboole_0, k1_xboole_0, k1_xboole_0) | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_489, c_557])).
% 3.70/1.60  tff(c_565, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_563])).
% 3.70/1.60  tff(c_812, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_793, c_793, c_565])).
% 3.70/1.60  tff(c_446, plain, (![A_13]: (v1_funct_2(k1_xboole_0, A_13, k1_xboole_0) | k1_xboole_0=A_13)), inference(splitRight, [status(thm)], [c_135])).
% 3.70/1.60  tff(c_952, plain, (![A_155]: (v1_funct_2('#skF_1', A_155, '#skF_1') | A_155='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_793, c_793, c_793, c_446])).
% 3.70/1.60  tff(c_767, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_765, c_82])).
% 3.70/1.60  tff(c_795, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_793, c_767])).
% 3.70/1.60  tff(c_958, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_952, c_795])).
% 3.70/1.60  tff(c_964, plain, $false, inference(negUnitSimplification, [status(thm)], [c_812, c_958])).
% 3.70/1.60  tff(c_966, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_563])).
% 3.70/1.60  tff(c_1518, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1494, c_1494, c_966])).
% 3.70/1.60  tff(c_1468, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1466, c_82])).
% 3.70/1.60  tff(c_1496, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1494, c_1468])).
% 3.70/1.60  tff(c_1594, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1518, c_1496])).
% 3.70/1.60  tff(c_965, plain, (v1_funct_2(k1_xboole_0, k1_xboole_0, k1_xboole_0)), inference(splitRight, [status(thm)], [c_563])).
% 3.70/1.60  tff(c_1517, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1494, c_1494, c_1494, c_965])).
% 3.70/1.60  tff(c_1615, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1594, c_1517])).
% 3.70/1.60  tff(c_1616, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_40])).
% 3.70/1.60  tff(c_1627, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))), inference(resolution, [status(thm)], [c_10, c_1616])).
% 3.70/1.60  tff(c_1676, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1673, c_1627])).
% 3.70/1.60  tff(c_1680, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_1676])).
% 3.70/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.60  
% 3.70/1.60  Inference rules
% 3.70/1.60  ----------------------
% 3.70/1.60  #Ref     : 0
% 3.70/1.60  #Sup     : 330
% 3.70/1.60  #Fact    : 0
% 3.70/1.60  #Define  : 0
% 3.70/1.60  #Split   : 8
% 3.70/1.60  #Chain   : 0
% 3.70/1.60  #Close   : 0
% 3.70/1.60  
% 3.70/1.60  Ordering : KBO
% 3.70/1.60  
% 3.70/1.60  Simplification rules
% 3.70/1.60  ----------------------
% 3.70/1.60  #Subsume      : 52
% 3.70/1.60  #Demod        : 548
% 3.70/1.60  #Tautology    : 161
% 3.70/1.60  #SimpNegUnit  : 4
% 3.70/1.60  #BackRed      : 156
% 3.70/1.60  
% 3.70/1.60  #Partial instantiations: 0
% 3.70/1.60  #Strategies tried      : 1
% 3.70/1.60  
% 3.70/1.60  Timing (in seconds)
% 3.70/1.60  ----------------------
% 3.70/1.61  Preprocessing        : 0.30
% 3.70/1.61  Parsing              : 0.16
% 3.70/1.61  CNF conversion       : 0.02
% 3.70/1.61  Main loop            : 0.52
% 3.70/1.61  Inferencing          : 0.19
% 3.70/1.61  Reduction            : 0.16
% 3.70/1.61  Demodulation         : 0.11
% 3.70/1.61  BG Simplification    : 0.03
% 3.70/1.61  Subsumption          : 0.10
% 3.70/1.61  Abstraction          : 0.03
% 3.70/1.61  MUC search           : 0.00
% 3.70/1.61  Cooper               : 0.00
% 3.70/1.61  Total                : 0.87
% 3.70/1.61  Index Insertion      : 0.00
% 3.70/1.61  Index Deletion       : 0.00
% 3.70/1.61  Index Matching       : 0.00
% 3.70/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
