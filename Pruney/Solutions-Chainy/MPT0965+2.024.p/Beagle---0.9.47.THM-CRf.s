%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:03 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 143 expanded)
%              Number of leaves         :   38 (  66 expanded)
%              Depth                    :   10
%              Number of atoms          :  162 ( 322 expanded)
%              Number of equality atoms :   27 (  52 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_110,axiom,(
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

tff(f_63,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k1_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).

tff(c_48,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_56,plain,(
    ! [B_36,A_37] :
      ( ~ r2_hidden(B_36,A_37)
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_56])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_52,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_510,plain,(
    ! [A_156,B_157,C_158] :
      ( k1_relset_1(A_156,B_157,C_158) = k1_relat_1(C_158)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_519,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_510])).

tff(c_667,plain,(
    ! [B_210,A_211,C_212] :
      ( k1_xboole_0 = B_210
      | k1_relset_1(A_211,B_210,C_212) = A_211
      | ~ v1_funct_2(C_212,A_211,B_210)
      | ~ m1_subset_1(C_212,k1_zfmisc_1(k2_zfmisc_1(A_211,B_210))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_674,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_667])).

tff(c_678,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_519,c_674])).

tff(c_679,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_678])).

tff(c_20,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_432,plain,(
    ! [B_132,A_133] :
      ( v1_relat_1(B_132)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(A_133))
      | ~ v1_relat_1(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_438,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_50,c_432])).

tff(c_442,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_438])).

tff(c_128,plain,(
    ! [C_58,B_59,A_60] :
      ( v5_relat_1(C_58,B_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_60,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_137,plain,(
    v5_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_128])).

tff(c_86,plain,(
    ! [B_45,A_46] :
      ( v1_relat_1(B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_46))
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_92,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_50,c_86])).

tff(c_96,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_92])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_211,plain,(
    ! [A_81,B_82,C_83] :
      ( k1_relset_1(A_81,B_82,C_83) = k1_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_220,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_211])).

tff(c_316,plain,(
    ! [B_123,A_124,C_125] :
      ( k1_xboole_0 = B_123
      | k1_relset_1(A_124,B_123,C_125) = A_124
      | ~ v1_funct_2(C_125,A_124,B_123)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_124,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_323,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_316])).

tff(c_327,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_220,c_323])).

tff(c_328,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_327])).

tff(c_24,plain,(
    ! [C_24,B_23,A_22] :
      ( m1_subset_1(k1_funct_1(C_24,B_23),A_22)
      | ~ r2_hidden(B_23,k1_relat_1(C_24))
      | ~ v1_funct_1(C_24)
      | ~ v5_relat_1(C_24,A_22)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_332,plain,(
    ! [B_23,A_22] :
      ( m1_subset_1(k1_funct_1('#skF_6',B_23),A_22)
      | ~ r2_hidden(B_23,'#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',A_22)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_328,c_24])).

tff(c_370,plain,(
    ! [B_130,A_131] :
      ( m1_subset_1(k1_funct_1('#skF_6',B_130),A_131)
      | ~ r2_hidden(B_130,'#skF_3')
      | ~ v5_relat_1('#skF_6',A_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_54,c_332])).

tff(c_76,plain,(
    ! [A_43,B_44] :
      ( r2_hidden(A_43,B_44)
      | v1_xboole_0(B_44)
      | ~ m1_subset_1(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_44,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_84,plain,
    ( v1_xboole_0('#skF_4')
    | ~ m1_subset_1(k1_funct_1('#skF_6','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_44])).

tff(c_85,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_6','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_408,plain,
    ( ~ r2_hidden('#skF_5','#skF_3')
    | ~ v5_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_370,c_85])).

tff(c_429,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_48,c_408])).

tff(c_430,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_443,plain,(
    ! [C_134,B_135,A_136] :
      ( v5_relat_1(C_134,B_135)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_136,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_452,plain,(
    v5_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_443])).

tff(c_18,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k2_relat_1(B_16),A_15)
      | ~ v5_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_481,plain,(
    ! [C_146,B_147,A_148] :
      ( ~ v1_xboole_0(C_146)
      | ~ m1_subset_1(B_147,k1_zfmisc_1(C_146))
      | ~ r2_hidden(A_148,B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_499,plain,(
    ! [B_152,A_153,A_154] :
      ( ~ v1_xboole_0(B_152)
      | ~ r2_hidden(A_153,A_154)
      | ~ r1_tarski(A_154,B_152) ) ),
    inference(resolution,[status(thm)],[c_10,c_481])).

tff(c_524,plain,(
    ! [B_159,A_160] :
      ( ~ v1_xboole_0(B_159)
      | ~ r1_tarski(A_160,B_159)
      | v1_xboole_0(A_160) ) ),
    inference(resolution,[status(thm)],[c_4,c_499])).

tff(c_576,plain,(
    ! [A_172,B_173] :
      ( ~ v1_xboole_0(A_172)
      | v1_xboole_0(k2_relat_1(B_173))
      | ~ v5_relat_1(B_173,A_172)
      | ~ v1_relat_1(B_173) ) ),
    inference(resolution,[status(thm)],[c_18,c_524])).

tff(c_578,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0(k2_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_452,c_576])).

tff(c_581,plain,(
    v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_430,c_578])).

tff(c_551,plain,(
    ! [A_166,B_167] :
      ( r2_hidden('#skF_2'(A_166,B_167),k2_relat_1(B_167))
      | ~ r2_hidden(A_166,k1_relat_1(B_167))
      | ~ v1_relat_1(B_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_559,plain,(
    ! [B_168,A_169] :
      ( ~ v1_xboole_0(k2_relat_1(B_168))
      | ~ r2_hidden(A_169,k1_relat_1(B_168))
      | ~ v1_relat_1(B_168) ) ),
    inference(resolution,[status(thm)],[c_551,c_2])).

tff(c_569,plain,(
    ! [B_168] :
      ( ~ v1_xboole_0(k2_relat_1(B_168))
      | ~ v1_relat_1(B_168)
      | v1_xboole_0(k1_relat_1(B_168)) ) ),
    inference(resolution,[status(thm)],[c_4,c_559])).

tff(c_584,plain,
    ( ~ v1_relat_1('#skF_6')
    | v1_xboole_0(k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_581,c_569])).

tff(c_587,plain,(
    v1_xboole_0(k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_584])).

tff(c_680,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_679,c_587])).

tff(c_683,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_680])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:27:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.41  
% 2.79/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.41  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 2.79/1.41  
% 2.79/1.41  %Foreground sorts:
% 2.79/1.41  
% 2.79/1.41  
% 2.79/1.41  %Background operators:
% 2.79/1.41  
% 2.79/1.41  
% 2.79/1.41  %Foreground operators:
% 2.79/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.79/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.79/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.79/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.79/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.79/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.79/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.79/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.79/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.79/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.79/1.41  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.79/1.41  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.79/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.79/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.79/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.79/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.79/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.79/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.79/1.41  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.79/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.79/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.79/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.79/1.41  
% 2.79/1.43  tff(f_123, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.79/1.43  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.79/1.43  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.79/1.43  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.79/1.43  tff(f_63, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.79/1.43  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.79/1.43  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.79/1.43  tff(f_82, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_1)).
% 2.79/1.43  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.79/1.43  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.79/1.43  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.79/1.43  tff(f_48, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.79/1.43  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k1_relat_1(B)) & (![C]: ~r2_hidden(C, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_relat_1)).
% 2.79/1.43  tff(c_48, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.79/1.43  tff(c_56, plain, (![B_36, A_37]: (~r2_hidden(B_36, A_37) | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.79/1.43  tff(c_60, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_56])).
% 2.79/1.43  tff(c_46, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.79/1.43  tff(c_52, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.79/1.43  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.79/1.43  tff(c_510, plain, (![A_156, B_157, C_158]: (k1_relset_1(A_156, B_157, C_158)=k1_relat_1(C_158) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.79/1.43  tff(c_519, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_510])).
% 2.79/1.43  tff(c_667, plain, (![B_210, A_211, C_212]: (k1_xboole_0=B_210 | k1_relset_1(A_211, B_210, C_212)=A_211 | ~v1_funct_2(C_212, A_211, B_210) | ~m1_subset_1(C_212, k1_zfmisc_1(k2_zfmisc_1(A_211, B_210))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.79/1.43  tff(c_674, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_667])).
% 2.79/1.43  tff(c_678, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_519, c_674])).
% 2.79/1.43  tff(c_679, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_46, c_678])).
% 2.79/1.43  tff(c_20, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.79/1.43  tff(c_432, plain, (![B_132, A_133]: (v1_relat_1(B_132) | ~m1_subset_1(B_132, k1_zfmisc_1(A_133)) | ~v1_relat_1(A_133))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.79/1.43  tff(c_438, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_50, c_432])).
% 2.79/1.43  tff(c_442, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_438])).
% 2.79/1.43  tff(c_128, plain, (![C_58, B_59, A_60]: (v5_relat_1(C_58, B_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_60, B_59))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.79/1.43  tff(c_137, plain, (v5_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_128])).
% 2.79/1.43  tff(c_86, plain, (![B_45, A_46]: (v1_relat_1(B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(A_46)) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.79/1.43  tff(c_92, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_50, c_86])).
% 2.79/1.43  tff(c_96, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_92])).
% 2.79/1.43  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.79/1.43  tff(c_211, plain, (![A_81, B_82, C_83]: (k1_relset_1(A_81, B_82, C_83)=k1_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.79/1.43  tff(c_220, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_211])).
% 2.79/1.43  tff(c_316, plain, (![B_123, A_124, C_125]: (k1_xboole_0=B_123 | k1_relset_1(A_124, B_123, C_125)=A_124 | ~v1_funct_2(C_125, A_124, B_123) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_124, B_123))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.79/1.43  tff(c_323, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_316])).
% 2.79/1.43  tff(c_327, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_220, c_323])).
% 2.79/1.43  tff(c_328, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_46, c_327])).
% 2.79/1.43  tff(c_24, plain, (![C_24, B_23, A_22]: (m1_subset_1(k1_funct_1(C_24, B_23), A_22) | ~r2_hidden(B_23, k1_relat_1(C_24)) | ~v1_funct_1(C_24) | ~v5_relat_1(C_24, A_22) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.79/1.43  tff(c_332, plain, (![B_23, A_22]: (m1_subset_1(k1_funct_1('#skF_6', B_23), A_22) | ~r2_hidden(B_23, '#skF_3') | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', A_22) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_328, c_24])).
% 2.79/1.43  tff(c_370, plain, (![B_130, A_131]: (m1_subset_1(k1_funct_1('#skF_6', B_130), A_131) | ~r2_hidden(B_130, '#skF_3') | ~v5_relat_1('#skF_6', A_131))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_54, c_332])).
% 2.79/1.43  tff(c_76, plain, (![A_43, B_44]: (r2_hidden(A_43, B_44) | v1_xboole_0(B_44) | ~m1_subset_1(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.79/1.43  tff(c_44, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.79/1.43  tff(c_84, plain, (v1_xboole_0('#skF_4') | ~m1_subset_1(k1_funct_1('#skF_6', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_76, c_44])).
% 2.79/1.43  tff(c_85, plain, (~m1_subset_1(k1_funct_1('#skF_6', '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_84])).
% 2.79/1.43  tff(c_408, plain, (~r2_hidden('#skF_5', '#skF_3') | ~v5_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_370, c_85])).
% 2.79/1.43  tff(c_429, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_137, c_48, c_408])).
% 2.79/1.43  tff(c_430, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_84])).
% 2.79/1.43  tff(c_443, plain, (![C_134, B_135, A_136]: (v5_relat_1(C_134, B_135) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_136, B_135))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.79/1.43  tff(c_452, plain, (v5_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_443])).
% 2.79/1.43  tff(c_18, plain, (![B_16, A_15]: (r1_tarski(k2_relat_1(B_16), A_15) | ~v5_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.79/1.43  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.79/1.43  tff(c_10, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.79/1.43  tff(c_481, plain, (![C_146, B_147, A_148]: (~v1_xboole_0(C_146) | ~m1_subset_1(B_147, k1_zfmisc_1(C_146)) | ~r2_hidden(A_148, B_147))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.79/1.43  tff(c_499, plain, (![B_152, A_153, A_154]: (~v1_xboole_0(B_152) | ~r2_hidden(A_153, A_154) | ~r1_tarski(A_154, B_152))), inference(resolution, [status(thm)], [c_10, c_481])).
% 2.79/1.43  tff(c_524, plain, (![B_159, A_160]: (~v1_xboole_0(B_159) | ~r1_tarski(A_160, B_159) | v1_xboole_0(A_160))), inference(resolution, [status(thm)], [c_4, c_499])).
% 2.79/1.43  tff(c_576, plain, (![A_172, B_173]: (~v1_xboole_0(A_172) | v1_xboole_0(k2_relat_1(B_173)) | ~v5_relat_1(B_173, A_172) | ~v1_relat_1(B_173))), inference(resolution, [status(thm)], [c_18, c_524])).
% 2.79/1.43  tff(c_578, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0(k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_452, c_576])).
% 2.79/1.43  tff(c_581, plain, (v1_xboole_0(k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_442, c_430, c_578])).
% 2.79/1.43  tff(c_551, plain, (![A_166, B_167]: (r2_hidden('#skF_2'(A_166, B_167), k2_relat_1(B_167)) | ~r2_hidden(A_166, k1_relat_1(B_167)) | ~v1_relat_1(B_167))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.79/1.43  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.79/1.43  tff(c_559, plain, (![B_168, A_169]: (~v1_xboole_0(k2_relat_1(B_168)) | ~r2_hidden(A_169, k1_relat_1(B_168)) | ~v1_relat_1(B_168))), inference(resolution, [status(thm)], [c_551, c_2])).
% 2.79/1.43  tff(c_569, plain, (![B_168]: (~v1_xboole_0(k2_relat_1(B_168)) | ~v1_relat_1(B_168) | v1_xboole_0(k1_relat_1(B_168)))), inference(resolution, [status(thm)], [c_4, c_559])).
% 2.79/1.43  tff(c_584, plain, (~v1_relat_1('#skF_6') | v1_xboole_0(k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_581, c_569])).
% 2.79/1.43  tff(c_587, plain, (v1_xboole_0(k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_442, c_584])).
% 2.79/1.43  tff(c_680, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_679, c_587])).
% 2.79/1.43  tff(c_683, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_680])).
% 2.79/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.43  
% 2.79/1.43  Inference rules
% 2.79/1.43  ----------------------
% 2.79/1.43  #Ref     : 0
% 2.79/1.43  #Sup     : 123
% 2.79/1.43  #Fact    : 0
% 2.79/1.43  #Define  : 0
% 2.79/1.43  #Split   : 8
% 2.79/1.43  #Chain   : 0
% 2.79/1.43  #Close   : 0
% 2.79/1.43  
% 2.79/1.43  Ordering : KBO
% 2.79/1.43  
% 2.79/1.43  Simplification rules
% 2.79/1.43  ----------------------
% 2.79/1.43  #Subsume      : 10
% 2.79/1.43  #Demod        : 36
% 2.79/1.43  #Tautology    : 23
% 2.79/1.43  #SimpNegUnit  : 4
% 2.79/1.43  #BackRed      : 3
% 2.79/1.43  
% 2.79/1.43  #Partial instantiations: 0
% 2.79/1.43  #Strategies tried      : 1
% 2.79/1.43  
% 2.79/1.43  Timing (in seconds)
% 2.79/1.43  ----------------------
% 2.79/1.43  Preprocessing        : 0.32
% 2.79/1.43  Parsing              : 0.17
% 2.79/1.43  CNF conversion       : 0.02
% 2.79/1.43  Main loop            : 0.33
% 2.79/1.43  Inferencing          : 0.13
% 2.79/1.43  Reduction            : 0.09
% 2.79/1.43  Demodulation         : 0.06
% 2.79/1.43  BG Simplification    : 0.02
% 2.79/1.43  Subsumption          : 0.06
% 2.79/1.43  Abstraction          : 0.01
% 2.79/1.43  MUC search           : 0.00
% 2.79/1.43  Cooper               : 0.00
% 2.79/1.43  Total                : 0.70
% 2.79/1.43  Index Insertion      : 0.00
% 2.79/1.43  Index Deletion       : 0.00
% 2.79/1.43  Index Matching       : 0.00
% 2.79/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
