%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:02 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 240 expanded)
%              Number of leaves         :   39 (  99 expanded)
%              Depth                    :   10
%              Number of atoms          :  181 ( 584 expanded)
%              Number of equality atoms :   41 ( 137 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_104,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_70,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_56,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_441,plain,(
    ! [A_162,B_163,C_164] :
      ( k2_relset_1(A_162,B_163,C_164) = k2_relat_1(C_164)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_445,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_56,c_441])).

tff(c_453,plain,(
    ! [A_165,B_166,C_167] :
      ( m1_subset_1(k2_relset_1(A_165,B_166,C_167),k1_zfmisc_1(B_166))
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_472,plain,
    ( m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_445,c_453])).

tff(c_479,plain,(
    m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_472])).

tff(c_10,plain,(
    ! [C_11,B_10,A_9] :
      ( ~ v1_xboole_0(C_11)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(C_11))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_494,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0('#skF_7')
      | ~ r2_hidden(A_9,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_479,c_10])).

tff(c_495,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_494])).

tff(c_82,plain,(
    ! [C_79,A_80,B_81] :
      ( v1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_86,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_56,c_82])).

tff(c_60,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_14,plain,(
    ! [A_12,C_48] :
      ( k1_funct_1(A_12,'#skF_4'(A_12,k2_relat_1(A_12),C_48)) = C_48
      | ~ r2_hidden(C_48,k2_relat_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_58,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_432,plain,(
    ! [A_159,B_160,C_161] :
      ( k1_relset_1(A_159,B_160,C_161) = k1_relat_1(C_161)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_436,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_56,c_432])).

tff(c_644,plain,(
    ! [B_205,A_206,C_207] :
      ( k1_xboole_0 = B_205
      | k1_relset_1(A_206,B_205,C_207) = A_206
      | ~ v1_funct_2(C_207,A_206,B_205)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_206,B_205))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_651,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_644])).

tff(c_655,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_436,c_651])).

tff(c_656,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_655])).

tff(c_559,plain,(
    ! [A_186,C_187] :
      ( r2_hidden('#skF_4'(A_186,k2_relat_1(A_186),C_187),k1_relat_1(A_186))
      | ~ r2_hidden(C_187,k2_relat_1(A_186))
      | ~ v1_funct_1(A_186)
      | ~ v1_relat_1(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,B_3)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_573,plain,(
    ! [A_186,C_187] :
      ( m1_subset_1('#skF_4'(A_186,k2_relat_1(A_186),C_187),k1_relat_1(A_186))
      | ~ r2_hidden(C_187,k2_relat_1(A_186))
      | ~ v1_funct_1(A_186)
      | ~ v1_relat_1(A_186) ) ),
    inference(resolution,[status(thm)],[c_559,c_4])).

tff(c_674,plain,(
    ! [C_187] :
      ( m1_subset_1('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_187),'#skF_6')
      | ~ r2_hidden(C_187,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_656,c_573])).

tff(c_694,plain,(
    ! [C_211] :
      ( m1_subset_1('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_211),'#skF_6')
      | ~ r2_hidden(C_211,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_60,c_674])).

tff(c_52,plain,(
    ! [E_70] :
      ( k1_funct_1('#skF_8',E_70) != '#skF_5'
      | ~ m1_subset_1(E_70,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_716,plain,(
    ! [C_215] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_215)) != '#skF_5'
      | ~ r2_hidden(C_215,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_694,c_52])).

tff(c_720,plain,(
    ! [C_48] :
      ( C_48 != '#skF_5'
      | ~ r2_hidden(C_48,k2_relat_1('#skF_8'))
      | ~ r2_hidden(C_48,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_716])).

tff(c_758,plain,(
    ~ r2_hidden('#skF_5',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_60,c_720])).

tff(c_54,plain,(
    r2_hidden('#skF_5',k2_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_448,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_54])).

tff(c_760,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_758,c_448])).

tff(c_761,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_655])).

tff(c_104,plain,(
    ! [A_92,B_93,C_94] :
      ( k1_relset_1(A_92,B_93,C_94) = k1_relat_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_108,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_56,c_104])).

tff(c_290,plain,(
    ! [B_137,A_138,C_139] :
      ( k1_xboole_0 = B_137
      | k1_relset_1(A_138,B_137,C_139) = A_138
      | ~ v1_funct_2(C_139,A_138,B_137)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_138,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_297,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_290])).

tff(c_301,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_108,c_297])).

tff(c_313,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_301])).

tff(c_265,plain,(
    ! [A_130,C_131] :
      ( r2_hidden('#skF_4'(A_130,k2_relat_1(A_130),C_131),k1_relat_1(A_130))
      | ~ r2_hidden(C_131,k2_relat_1(A_130))
      | ~ v1_funct_1(A_130)
      | ~ v1_relat_1(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_279,plain,(
    ! [A_130,C_131] :
      ( m1_subset_1('#skF_4'(A_130,k2_relat_1(A_130),C_131),k1_relat_1(A_130))
      | ~ r2_hidden(C_131,k2_relat_1(A_130))
      | ~ v1_funct_1(A_130)
      | ~ v1_relat_1(A_130) ) ),
    inference(resolution,[status(thm)],[c_265,c_4])).

tff(c_323,plain,(
    ! [C_131] :
      ( m1_subset_1('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_131),'#skF_6')
      | ~ r2_hidden(C_131,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_279])).

tff(c_357,plain,(
    ! [C_146] :
      ( m1_subset_1('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_146),'#skF_6')
      | ~ r2_hidden(C_146,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_60,c_323])).

tff(c_384,plain,(
    ! [C_149] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_149)) != '#skF_5'
      | ~ r2_hidden(C_149,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_357,c_52])).

tff(c_388,plain,(
    ! [C_48] :
      ( C_48 != '#skF_5'
      | ~ r2_hidden(C_48,k2_relat_1('#skF_8'))
      | ~ r2_hidden(C_48,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_384])).

tff(c_391,plain,(
    ~ r2_hidden('#skF_5',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_60,c_388])).

tff(c_114,plain,(
    ! [A_96,B_97,C_98] :
      ( k2_relset_1(A_96,B_97,C_98) = k2_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_118,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_56,c_114])).

tff(c_143,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_54])).

tff(c_393,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_391,c_143])).

tff(c_394,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_301])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_73,plain,(
    ! [A_77,B_78] :
      ( r2_hidden(A_77,B_78)
      | v1_xboole_0(B_78)
      | ~ m1_subset_1(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30,plain,(
    ! [B_53,A_52] :
      ( ~ r1_tarski(B_53,A_52)
      | ~ r2_hidden(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_87,plain,(
    ! [B_82,A_83] :
      ( ~ r1_tarski(B_82,A_83)
      | v1_xboole_0(B_82)
      | ~ m1_subset_1(A_83,B_82) ) ),
    inference(resolution,[status(thm)],[c_73,c_30])).

tff(c_91,plain,(
    ! [A_1] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(A_1,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2,c_87])).

tff(c_92,plain,(
    ! [A_1] : ~ m1_subset_1(A_1,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_402,plain,(
    ! [A_1] : ~ m1_subset_1(A_1,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_92])).

tff(c_34,plain,(
    ! [A_57,B_58,C_59] :
      ( m1_subset_1(k2_relset_1(A_57,B_58,C_59),k1_zfmisc_1(B_58))
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_147,plain,
    ( m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_34])).

tff(c_151,plain,(
    m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_147])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( m1_subset_1(A_6,C_8)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(C_8))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_169,plain,(
    ! [A_102] :
      ( m1_subset_1(A_102,'#skF_7')
      | ~ r2_hidden(A_102,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_151,c_8])).

tff(c_177,plain,(
    m1_subset_1('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_143,c_169])).

tff(c_419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_402,c_177])).

tff(c_420,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_768,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_761,c_420])).

tff(c_771,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_495,c_768])).

tff(c_772,plain,(
    ! [A_9] : ~ r2_hidden(A_9,k2_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_494])).

tff(c_785,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_772,c_448])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:11:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.53  
% 2.91/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.53  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1
% 2.91/1.53  
% 2.91/1.53  %Foreground sorts:
% 2.91/1.53  
% 2.91/1.53  
% 2.91/1.53  %Background operators:
% 2.91/1.53  
% 2.91/1.53  
% 2.91/1.53  %Foreground operators:
% 2.91/1.53  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.91/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.91/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.91/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.91/1.53  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.91/1.53  tff('#skF_7', type, '#skF_7': $i).
% 2.91/1.53  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.91/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.91/1.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.91/1.53  tff('#skF_5', type, '#skF_5': $i).
% 2.91/1.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.91/1.53  tff('#skF_6', type, '#skF_6': $i).
% 2.91/1.53  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.91/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.91/1.53  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.91/1.53  tff('#skF_8', type, '#skF_8': $i).
% 2.91/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.91/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.91/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.91/1.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.91/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.91/1.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.91/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.91/1.53  
% 3.34/1.55  tff(f_120, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 3.34/1.55  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.34/1.55  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.34/1.55  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.34/1.55  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.34/1.55  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 3.34/1.55  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.34/1.55  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.34/1.55  tff(f_31, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.34/1.55  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.34/1.55  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.34/1.55  tff(f_70, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.34/1.55  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.34/1.55  tff(c_56, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.34/1.55  tff(c_441, plain, (![A_162, B_163, C_164]: (k2_relset_1(A_162, B_163, C_164)=k2_relat_1(C_164) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.34/1.55  tff(c_445, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_56, c_441])).
% 3.34/1.55  tff(c_453, plain, (![A_165, B_166, C_167]: (m1_subset_1(k2_relset_1(A_165, B_166, C_167), k1_zfmisc_1(B_166)) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.34/1.55  tff(c_472, plain, (m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_445, c_453])).
% 3.34/1.55  tff(c_479, plain, (m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_472])).
% 3.34/1.55  tff(c_10, plain, (![C_11, B_10, A_9]: (~v1_xboole_0(C_11) | ~m1_subset_1(B_10, k1_zfmisc_1(C_11)) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.34/1.55  tff(c_494, plain, (![A_9]: (~v1_xboole_0('#skF_7') | ~r2_hidden(A_9, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_479, c_10])).
% 3.34/1.55  tff(c_495, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_494])).
% 3.34/1.55  tff(c_82, plain, (![C_79, A_80, B_81]: (v1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.34/1.55  tff(c_86, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_56, c_82])).
% 3.34/1.55  tff(c_60, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.34/1.55  tff(c_14, plain, (![A_12, C_48]: (k1_funct_1(A_12, '#skF_4'(A_12, k2_relat_1(A_12), C_48))=C_48 | ~r2_hidden(C_48, k2_relat_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.34/1.55  tff(c_58, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.34/1.55  tff(c_432, plain, (![A_159, B_160, C_161]: (k1_relset_1(A_159, B_160, C_161)=k1_relat_1(C_161) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.34/1.55  tff(c_436, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_56, c_432])).
% 3.34/1.55  tff(c_644, plain, (![B_205, A_206, C_207]: (k1_xboole_0=B_205 | k1_relset_1(A_206, B_205, C_207)=A_206 | ~v1_funct_2(C_207, A_206, B_205) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_206, B_205))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.34/1.55  tff(c_651, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_56, c_644])).
% 3.34/1.55  tff(c_655, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_436, c_651])).
% 3.34/1.55  tff(c_656, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_655])).
% 3.34/1.55  tff(c_559, plain, (![A_186, C_187]: (r2_hidden('#skF_4'(A_186, k2_relat_1(A_186), C_187), k1_relat_1(A_186)) | ~r2_hidden(C_187, k2_relat_1(A_186)) | ~v1_funct_1(A_186) | ~v1_relat_1(A_186))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.34/1.55  tff(c_4, plain, (![A_2, B_3]: (m1_subset_1(A_2, B_3) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.34/1.55  tff(c_573, plain, (![A_186, C_187]: (m1_subset_1('#skF_4'(A_186, k2_relat_1(A_186), C_187), k1_relat_1(A_186)) | ~r2_hidden(C_187, k2_relat_1(A_186)) | ~v1_funct_1(A_186) | ~v1_relat_1(A_186))), inference(resolution, [status(thm)], [c_559, c_4])).
% 3.34/1.55  tff(c_674, plain, (![C_187]: (m1_subset_1('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_187), '#skF_6') | ~r2_hidden(C_187, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_656, c_573])).
% 3.34/1.55  tff(c_694, plain, (![C_211]: (m1_subset_1('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_211), '#skF_6') | ~r2_hidden(C_211, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_60, c_674])).
% 3.34/1.55  tff(c_52, plain, (![E_70]: (k1_funct_1('#skF_8', E_70)!='#skF_5' | ~m1_subset_1(E_70, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.34/1.55  tff(c_716, plain, (![C_215]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_215))!='#skF_5' | ~r2_hidden(C_215, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_694, c_52])).
% 3.34/1.55  tff(c_720, plain, (![C_48]: (C_48!='#skF_5' | ~r2_hidden(C_48, k2_relat_1('#skF_8')) | ~r2_hidden(C_48, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_716])).
% 3.34/1.55  tff(c_758, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_60, c_720])).
% 3.34/1.55  tff(c_54, plain, (r2_hidden('#skF_5', k2_relset_1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.34/1.55  tff(c_448, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_445, c_54])).
% 3.34/1.55  tff(c_760, plain, $false, inference(negUnitSimplification, [status(thm)], [c_758, c_448])).
% 3.34/1.55  tff(c_761, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_655])).
% 3.34/1.55  tff(c_104, plain, (![A_92, B_93, C_94]: (k1_relset_1(A_92, B_93, C_94)=k1_relat_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.34/1.55  tff(c_108, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_56, c_104])).
% 3.34/1.55  tff(c_290, plain, (![B_137, A_138, C_139]: (k1_xboole_0=B_137 | k1_relset_1(A_138, B_137, C_139)=A_138 | ~v1_funct_2(C_139, A_138, B_137) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_138, B_137))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.34/1.55  tff(c_297, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_56, c_290])).
% 3.34/1.55  tff(c_301, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_108, c_297])).
% 3.34/1.55  tff(c_313, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_301])).
% 3.34/1.55  tff(c_265, plain, (![A_130, C_131]: (r2_hidden('#skF_4'(A_130, k2_relat_1(A_130), C_131), k1_relat_1(A_130)) | ~r2_hidden(C_131, k2_relat_1(A_130)) | ~v1_funct_1(A_130) | ~v1_relat_1(A_130))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.34/1.55  tff(c_279, plain, (![A_130, C_131]: (m1_subset_1('#skF_4'(A_130, k2_relat_1(A_130), C_131), k1_relat_1(A_130)) | ~r2_hidden(C_131, k2_relat_1(A_130)) | ~v1_funct_1(A_130) | ~v1_relat_1(A_130))), inference(resolution, [status(thm)], [c_265, c_4])).
% 3.34/1.55  tff(c_323, plain, (![C_131]: (m1_subset_1('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_131), '#skF_6') | ~r2_hidden(C_131, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_313, c_279])).
% 3.34/1.55  tff(c_357, plain, (![C_146]: (m1_subset_1('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_146), '#skF_6') | ~r2_hidden(C_146, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_60, c_323])).
% 3.34/1.55  tff(c_384, plain, (![C_149]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_149))!='#skF_5' | ~r2_hidden(C_149, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_357, c_52])).
% 3.34/1.55  tff(c_388, plain, (![C_48]: (C_48!='#skF_5' | ~r2_hidden(C_48, k2_relat_1('#skF_8')) | ~r2_hidden(C_48, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_384])).
% 3.34/1.55  tff(c_391, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_60, c_388])).
% 3.34/1.55  tff(c_114, plain, (![A_96, B_97, C_98]: (k2_relset_1(A_96, B_97, C_98)=k2_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.34/1.55  tff(c_118, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_56, c_114])).
% 3.34/1.55  tff(c_143, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_54])).
% 3.34/1.55  tff(c_393, plain, $false, inference(negUnitSimplification, [status(thm)], [c_391, c_143])).
% 3.34/1.55  tff(c_394, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_301])).
% 3.34/1.55  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.34/1.55  tff(c_73, plain, (![A_77, B_78]: (r2_hidden(A_77, B_78) | v1_xboole_0(B_78) | ~m1_subset_1(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.34/1.55  tff(c_30, plain, (![B_53, A_52]: (~r1_tarski(B_53, A_52) | ~r2_hidden(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.34/1.55  tff(c_87, plain, (![B_82, A_83]: (~r1_tarski(B_82, A_83) | v1_xboole_0(B_82) | ~m1_subset_1(A_83, B_82))), inference(resolution, [status(thm)], [c_73, c_30])).
% 3.34/1.55  tff(c_91, plain, (![A_1]: (v1_xboole_0(k1_xboole_0) | ~m1_subset_1(A_1, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_87])).
% 3.34/1.55  tff(c_92, plain, (![A_1]: (~m1_subset_1(A_1, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_91])).
% 3.34/1.55  tff(c_402, plain, (![A_1]: (~m1_subset_1(A_1, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_394, c_92])).
% 3.34/1.55  tff(c_34, plain, (![A_57, B_58, C_59]: (m1_subset_1(k2_relset_1(A_57, B_58, C_59), k1_zfmisc_1(B_58)) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.34/1.55  tff(c_147, plain, (m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_118, c_34])).
% 3.34/1.55  tff(c_151, plain, (m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_147])).
% 3.34/1.55  tff(c_8, plain, (![A_6, C_8, B_7]: (m1_subset_1(A_6, C_8) | ~m1_subset_1(B_7, k1_zfmisc_1(C_8)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.34/1.55  tff(c_169, plain, (![A_102]: (m1_subset_1(A_102, '#skF_7') | ~r2_hidden(A_102, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_151, c_8])).
% 3.34/1.55  tff(c_177, plain, (m1_subset_1('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_143, c_169])).
% 3.34/1.55  tff(c_419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_402, c_177])).
% 3.34/1.55  tff(c_420, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_91])).
% 3.34/1.55  tff(c_768, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_761, c_420])).
% 3.34/1.55  tff(c_771, plain, $false, inference(negUnitSimplification, [status(thm)], [c_495, c_768])).
% 3.34/1.55  tff(c_772, plain, (![A_9]: (~r2_hidden(A_9, k2_relat_1('#skF_8')))), inference(splitRight, [status(thm)], [c_494])).
% 3.34/1.55  tff(c_785, plain, $false, inference(negUnitSimplification, [status(thm)], [c_772, c_448])).
% 3.34/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.55  
% 3.34/1.55  Inference rules
% 3.34/1.55  ----------------------
% 3.34/1.55  #Ref     : 0
% 3.34/1.55  #Sup     : 144
% 3.34/1.55  #Fact    : 0
% 3.34/1.55  #Define  : 0
% 3.34/1.55  #Split   : 11
% 3.34/1.55  #Chain   : 0
% 3.34/1.55  #Close   : 0
% 3.34/1.55  
% 3.34/1.55  Ordering : KBO
% 3.34/1.55  
% 3.34/1.55  Simplification rules
% 3.34/1.55  ----------------------
% 3.34/1.55  #Subsume      : 21
% 3.34/1.55  #Demod        : 103
% 3.34/1.55  #Tautology    : 29
% 3.34/1.55  #SimpNegUnit  : 9
% 3.34/1.55  #BackRed      : 34
% 3.34/1.55  
% 3.34/1.55  #Partial instantiations: 0
% 3.34/1.55  #Strategies tried      : 1
% 3.34/1.55  
% 3.34/1.55  Timing (in seconds)
% 3.34/1.55  ----------------------
% 3.34/1.56  Preprocessing        : 0.31
% 3.34/1.56  Parsing              : 0.15
% 3.34/1.56  CNF conversion       : 0.03
% 3.34/1.56  Main loop            : 0.39
% 3.34/1.56  Inferencing          : 0.15
% 3.34/1.56  Reduction            : 0.11
% 3.34/1.56  Demodulation         : 0.07
% 3.34/1.56  BG Simplification    : 0.02
% 3.34/1.56  Subsumption          : 0.07
% 3.34/1.56  Abstraction          : 0.02
% 3.34/1.56  MUC search           : 0.00
% 3.34/1.56  Cooper               : 0.00
% 3.34/1.56  Total                : 0.74
% 3.34/1.56  Index Insertion      : 0.00
% 3.34/1.56  Index Deletion       : 0.00
% 3.34/1.56  Index Matching       : 0.00
% 3.34/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
