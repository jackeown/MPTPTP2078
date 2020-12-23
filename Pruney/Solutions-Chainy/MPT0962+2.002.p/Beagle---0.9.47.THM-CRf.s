%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:51 EST 2020

% Result     : Theorem 3.96s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 248 expanded)
%              Number of leaves         :   32 (  95 expanded)
%              Depth                    :    9
%              Number of atoms          :  233 ( 663 expanded)
%              Number of equality atoms :   60 ( 137 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_wellord2 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(f_123,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_75,axiom,
    ( v1_relat_1(k1_wellord2(k1_xboole_0))
    & v1_xboole_0(k1_wellord2(k1_xboole_0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_wellord2)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_54,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    r1_tarski(k2_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1870,plain,(
    ! [C_409,A_410,B_411] :
      ( m1_subset_1(C_409,k1_zfmisc_1(k2_zfmisc_1(A_410,B_411)))
      | ~ r1_tarski(k2_relat_1(C_409),B_411)
      | ~ r1_tarski(k1_relat_1(C_409),A_410)
      | ~ v1_relat_1(C_409) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1374,plain,(
    ! [C_300,B_301,A_302] :
      ( v1_xboole_0(C_300)
      | ~ m1_subset_1(C_300,k1_zfmisc_1(k2_zfmisc_1(B_301,A_302)))
      | ~ v1_xboole_0(A_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1379,plain,(
    ! [A_302] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(A_302) ) ),
    inference(resolution,[status(thm)],[c_12,c_1374])).

tff(c_1380,plain,(
    ! [A_302] : ~ v1_xboole_0(A_302) ),
    inference(splitLeft,[status(thm)],[c_1379])).

tff(c_26,plain,(
    v1_xboole_0(k1_wellord2(k1_xboole_0)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1383,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1380,c_26])).

tff(c_1384,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1379])).

tff(c_52,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_48,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_56,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48])).

tff(c_64,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_222,plain,(
    ! [C_74,A_75,B_76] :
      ( m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76)))
      | ~ r1_tarski(k2_relat_1(C_74),B_76)
      | ~ r1_tarski(k1_relat_1(C_74),A_75)
      | ~ v1_relat_1(C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_22,plain,(
    ! [A_16,B_17,C_18] :
      ( k1_relset_1(A_16,B_17,C_18) = k1_relat_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_598,plain,(
    ! [A_147,B_148,C_149] :
      ( k1_relset_1(A_147,B_148,C_149) = k1_relat_1(C_149)
      | ~ r1_tarski(k2_relat_1(C_149),B_148)
      | ~ r1_tarski(k1_relat_1(C_149),A_147)
      | ~ v1_relat_1(C_149) ) ),
    inference(resolution,[status(thm)],[c_222,c_22])).

tff(c_600,plain,(
    ! [A_147] :
      ( k1_relset_1(A_147,'#skF_1','#skF_2') = k1_relat_1('#skF_2')
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_147)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_50,c_598])).

tff(c_615,plain,(
    ! [A_151] :
      ( k1_relset_1(A_151,'#skF_1','#skF_2') = k1_relat_1('#skF_2')
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_600])).

tff(c_620,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_615])).

tff(c_24,plain,(
    ! [C_21,A_19,B_20] :
      ( m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20)))
      | ~ r1_tarski(k2_relat_1(C_21),B_20)
      | ~ r1_tarski(k1_relat_1(C_21),A_19)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_555,plain,(
    ! [B_134,C_135,A_136] :
      ( k1_xboole_0 = B_134
      | v1_funct_2(C_135,A_136,B_134)
      | k1_relset_1(A_136,B_134,C_135) != A_136
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_136,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_750,plain,(
    ! [B_177,C_178,A_179] :
      ( k1_xboole_0 = B_177
      | v1_funct_2(C_178,A_179,B_177)
      | k1_relset_1(A_179,B_177,C_178) != A_179
      | ~ r1_tarski(k2_relat_1(C_178),B_177)
      | ~ r1_tarski(k1_relat_1(C_178),A_179)
      | ~ v1_relat_1(C_178) ) ),
    inference(resolution,[status(thm)],[c_24,c_555])).

tff(c_752,plain,(
    ! [A_179] :
      ( k1_xboole_0 = '#skF_1'
      | v1_funct_2('#skF_2',A_179,'#skF_1')
      | k1_relset_1(A_179,'#skF_1','#skF_2') != A_179
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_179)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_50,c_750])).

tff(c_758,plain,(
    ! [A_179] :
      ( k1_xboole_0 = '#skF_1'
      | v1_funct_2('#skF_2',A_179,'#skF_1')
      | k1_relset_1(A_179,'#skF_1','#skF_2') != A_179
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_179) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_752])).

tff(c_760,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_758])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_795,plain,(
    ! [A_6] : r1_tarski('#skF_1',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_760,c_10])).

tff(c_86,plain,(
    ! [B_38,A_39] :
      ( B_38 = A_39
      | ~ r1_tarski(B_38,A_39)
      | ~ r1_tarski(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_86])).

tff(c_112,plain,(
    ~ r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_803,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_795,c_112])).

tff(c_826,plain,(
    ! [A_183] :
      ( v1_funct_2('#skF_2',A_183,'#skF_1')
      | k1_relset_1(A_183,'#skF_1','#skF_2') != A_183
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_183) ) ),
    inference(splitRight,[status(thm)],[c_758])).

tff(c_830,plain,
    ( v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') != k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_826])).

tff(c_833,plain,(
    v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_620,c_830])).

tff(c_835,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_833])).

tff(c_836,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_65,plain,(
    ! [A_36] :
      ( k2_relat_1(A_36) = k1_xboole_0
      | k1_relat_1(A_36) != k1_xboole_0
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_73,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relat_1('#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_65])).

tff(c_74,plain,(
    k1_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_73])).

tff(c_75,plain,(
    ! [A_37] :
      ( k1_relat_1(A_37) = k1_xboole_0
      | k2_relat_1(A_37) != k1_xboole_0
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_81,plain,
    ( k1_relat_1('#skF_2') = k1_xboole_0
    | k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_75])).

tff(c_85,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_81])).

tff(c_838,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_836,c_85])).

tff(c_939,plain,(
    ! [C_216,A_217,B_218] :
      ( m1_subset_1(C_216,k1_zfmisc_1(k2_zfmisc_1(A_217,B_218)))
      | ~ r1_tarski(k2_relat_1(C_216),B_218)
      | ~ r1_tarski(k1_relat_1(C_216),A_217)
      | ~ v1_relat_1(C_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1079,plain,(
    ! [A_245,B_246,C_247] :
      ( k1_relset_1(A_245,B_246,C_247) = k1_relat_1(C_247)
      | ~ r1_tarski(k2_relat_1(C_247),B_246)
      | ~ r1_tarski(k1_relat_1(C_247),A_245)
      | ~ v1_relat_1(C_247) ) ),
    inference(resolution,[status(thm)],[c_939,c_22])).

tff(c_1088,plain,(
    ! [A_248,C_249] :
      ( k1_relset_1(A_248,k2_relat_1(C_249),C_249) = k1_relat_1(C_249)
      | ~ r1_tarski(k1_relat_1(C_249),A_248)
      | ~ v1_relat_1(C_249) ) ),
    inference(resolution,[status(thm)],[c_6,c_1079])).

tff(c_1098,plain,(
    ! [C_252] :
      ( k1_relset_1(k1_relat_1(C_252),k2_relat_1(C_252),C_252) = k1_relat_1(C_252)
      | ~ v1_relat_1(C_252) ) ),
    inference(resolution,[status(thm)],[c_6,c_1088])).

tff(c_1115,plain,
    ( k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_836,c_1098])).

tff(c_1121,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1115])).

tff(c_1010,plain,(
    ! [B_227,C_228,A_229] :
      ( k1_xboole_0 = B_227
      | v1_funct_2(C_228,A_229,B_227)
      | k1_relset_1(A_229,B_227,C_228) != A_229
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(A_229,B_227))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1274,plain,(
    ! [B_280,C_281,A_282] :
      ( k1_xboole_0 = B_280
      | v1_funct_2(C_281,A_282,B_280)
      | k1_relset_1(A_282,B_280,C_281) != A_282
      | ~ r1_tarski(k2_relat_1(C_281),B_280)
      | ~ r1_tarski(k1_relat_1(C_281),A_282)
      | ~ v1_relat_1(C_281) ) ),
    inference(resolution,[status(thm)],[c_24,c_1010])).

tff(c_1276,plain,(
    ! [B_280,A_282] :
      ( k1_xboole_0 = B_280
      | v1_funct_2('#skF_2',A_282,B_280)
      | k1_relset_1(A_282,B_280,'#skF_2') != A_282
      | ~ r1_tarski('#skF_1',B_280)
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_282)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_836,c_1274])).

tff(c_1283,plain,(
    ! [B_283,A_284] :
      ( k1_xboole_0 = B_283
      | v1_funct_2('#skF_2',A_284,B_283)
      | k1_relset_1(A_284,B_283,'#skF_2') != A_284
      | ~ r1_tarski('#skF_1',B_283)
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_284) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1276])).

tff(c_1288,plain,(
    ! [B_285] :
      ( k1_xboole_0 = B_285
      | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),B_285)
      | k1_relset_1(k1_relat_1('#skF_2'),B_285,'#skF_2') != k1_relat_1('#skF_2')
      | ~ r1_tarski('#skF_1',B_285) ) ),
    inference(resolution,[status(thm)],[c_6,c_1283])).

tff(c_1293,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') != k1_relat_1('#skF_2')
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_1288,c_64])).

tff(c_1299,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1121,c_1293])).

tff(c_1301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_838,c_1299])).

tff(c_1303,plain,(
    k1_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_1442,plain,(
    ! [C_322,A_323,B_324] :
      ( m1_subset_1(C_322,k1_zfmisc_1(k2_zfmisc_1(A_323,B_324)))
      | ~ r1_tarski(k2_relat_1(C_322),B_324)
      | ~ r1_tarski(k1_relat_1(C_322),A_323)
      | ~ v1_relat_1(C_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_34,plain,(
    ! [C_28,A_25,B_26] :
      ( v1_partfun1(C_28,A_25)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1509,plain,(
    ! [C_331,A_332,B_333] :
      ( v1_partfun1(C_331,A_332)
      | ~ v1_xboole_0(A_332)
      | ~ r1_tarski(k2_relat_1(C_331),B_333)
      | ~ r1_tarski(k1_relat_1(C_331),A_332)
      | ~ v1_relat_1(C_331) ) ),
    inference(resolution,[status(thm)],[c_1442,c_34])).

tff(c_1535,plain,(
    ! [C_340,A_341] :
      ( v1_partfun1(C_340,A_341)
      | ~ v1_xboole_0(A_341)
      | ~ r1_tarski(k1_relat_1(C_340),A_341)
      | ~ v1_relat_1(C_340) ) ),
    inference(resolution,[status(thm)],[c_6,c_1509])).

tff(c_1546,plain,(
    ! [C_342] :
      ( v1_partfun1(C_342,k1_relat_1(C_342))
      | ~ v1_xboole_0(k1_relat_1(C_342))
      | ~ v1_relat_1(C_342) ) ),
    inference(resolution,[status(thm)],[c_6,c_1535])).

tff(c_1549,plain,
    ( v1_partfun1('#skF_2',k1_xboole_0)
    | ~ v1_xboole_0(k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1303,c_1546])).

tff(c_1551,plain,(
    v1_partfun1('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1384,c_1303,c_1549])).

tff(c_1302,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_30,plain,(
    ! [C_24,A_22,B_23] :
      ( v1_funct_2(C_24,A_22,B_23)
      | ~ v1_partfun1(C_24,A_22)
      | ~ v1_funct_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1684,plain,(
    ! [C_363,A_364,B_365] :
      ( v1_funct_2(C_363,A_364,B_365)
      | ~ v1_partfun1(C_363,A_364)
      | ~ v1_funct_1(C_363)
      | ~ r1_tarski(k2_relat_1(C_363),B_365)
      | ~ r1_tarski(k1_relat_1(C_363),A_364)
      | ~ v1_relat_1(C_363) ) ),
    inference(resolution,[status(thm)],[c_1442,c_30])).

tff(c_1686,plain,(
    ! [A_364,B_365] :
      ( v1_funct_2('#skF_2',A_364,B_365)
      | ~ v1_partfun1('#skF_2',A_364)
      | ~ v1_funct_1('#skF_2')
      | ~ r1_tarski(k1_xboole_0,B_365)
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_364)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1302,c_1684])).

tff(c_1693,plain,(
    ! [A_366,B_367] :
      ( v1_funct_2('#skF_2',A_366,B_367)
      | ~ v1_partfun1('#skF_2',A_366) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_10,c_1303,c_10,c_52,c_1686])).

tff(c_1319,plain,(
    ~ v1_funct_2('#skF_2',k1_xboole_0,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1303,c_64])).

tff(c_1700,plain,(
    ~ v1_partfun1('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1693,c_1319])).

tff(c_1705,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1551,c_1700])).

tff(c_1706,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1899,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1870,c_1706])).

tff(c_1911,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_6,c_50,c_1899])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:04:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.96/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.72  
% 3.96/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.72  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_wellord2 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.96/1.72  
% 3.96/1.72  %Foreground sorts:
% 3.96/1.72  
% 3.96/1.72  
% 3.96/1.72  %Background operators:
% 3.96/1.72  
% 3.96/1.72  
% 3.96/1.72  %Foreground operators:
% 3.96/1.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.96/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.96/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.96/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.96/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.96/1.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.96/1.72  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 3.96/1.72  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.96/1.72  tff('#skF_2', type, '#skF_2': $i).
% 3.96/1.72  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.96/1.72  tff('#skF_1', type, '#skF_1': $i).
% 3.96/1.72  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.96/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.96/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.96/1.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.96/1.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.96/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.96/1.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.96/1.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.96/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.96/1.72  
% 3.96/1.74  tff(f_123, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 3.96/1.74  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.96/1.74  tff(f_72, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 3.96/1.74  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.96/1.74  tff(f_60, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 3.96/1.74  tff(f_75, axiom, (v1_relat_1(k1_wellord2(k1_xboole_0)) & v1_xboole_0(k1_wellord2(k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_wellord2)).
% 3.96/1.74  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.96/1.74  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.96/1.74  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.96/1.74  tff(f_53, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 3.96/1.74  tff(f_92, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_partfun1)).
% 3.96/1.74  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 3.96/1.74  tff(c_54, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.96/1.74  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.96/1.74  tff(c_50, plain, (r1_tarski(k2_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.96/1.74  tff(c_1870, plain, (![C_409, A_410, B_411]: (m1_subset_1(C_409, k1_zfmisc_1(k2_zfmisc_1(A_410, B_411))) | ~r1_tarski(k2_relat_1(C_409), B_411) | ~r1_tarski(k1_relat_1(C_409), A_410) | ~v1_relat_1(C_409))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.96/1.74  tff(c_12, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.96/1.74  tff(c_1374, plain, (![C_300, B_301, A_302]: (v1_xboole_0(C_300) | ~m1_subset_1(C_300, k1_zfmisc_1(k2_zfmisc_1(B_301, A_302))) | ~v1_xboole_0(A_302))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.96/1.74  tff(c_1379, plain, (![A_302]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(A_302))), inference(resolution, [status(thm)], [c_12, c_1374])).
% 3.96/1.74  tff(c_1380, plain, (![A_302]: (~v1_xboole_0(A_302))), inference(splitLeft, [status(thm)], [c_1379])).
% 3.96/1.74  tff(c_26, plain, (v1_xboole_0(k1_wellord2(k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.96/1.74  tff(c_1383, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1380, c_26])).
% 3.96/1.74  tff(c_1384, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_1379])).
% 3.96/1.74  tff(c_52, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.96/1.74  tff(c_48, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.96/1.74  tff(c_56, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48])).
% 3.96/1.74  tff(c_64, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_56])).
% 3.96/1.74  tff(c_222, plain, (![C_74, A_75, B_76]: (m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))) | ~r1_tarski(k2_relat_1(C_74), B_76) | ~r1_tarski(k1_relat_1(C_74), A_75) | ~v1_relat_1(C_74))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.96/1.74  tff(c_22, plain, (![A_16, B_17, C_18]: (k1_relset_1(A_16, B_17, C_18)=k1_relat_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.96/1.74  tff(c_598, plain, (![A_147, B_148, C_149]: (k1_relset_1(A_147, B_148, C_149)=k1_relat_1(C_149) | ~r1_tarski(k2_relat_1(C_149), B_148) | ~r1_tarski(k1_relat_1(C_149), A_147) | ~v1_relat_1(C_149))), inference(resolution, [status(thm)], [c_222, c_22])).
% 3.96/1.74  tff(c_600, plain, (![A_147]: (k1_relset_1(A_147, '#skF_1', '#skF_2')=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), A_147) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_598])).
% 3.96/1.74  tff(c_615, plain, (![A_151]: (k1_relset_1(A_151, '#skF_1', '#skF_2')=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), A_151))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_600])).
% 3.96/1.74  tff(c_620, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_6, c_615])).
% 3.96/1.74  tff(c_24, plain, (![C_21, A_19, B_20]: (m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))) | ~r1_tarski(k2_relat_1(C_21), B_20) | ~r1_tarski(k1_relat_1(C_21), A_19) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.96/1.74  tff(c_555, plain, (![B_134, C_135, A_136]: (k1_xboole_0=B_134 | v1_funct_2(C_135, A_136, B_134) | k1_relset_1(A_136, B_134, C_135)!=A_136 | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_136, B_134))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.96/1.74  tff(c_750, plain, (![B_177, C_178, A_179]: (k1_xboole_0=B_177 | v1_funct_2(C_178, A_179, B_177) | k1_relset_1(A_179, B_177, C_178)!=A_179 | ~r1_tarski(k2_relat_1(C_178), B_177) | ~r1_tarski(k1_relat_1(C_178), A_179) | ~v1_relat_1(C_178))), inference(resolution, [status(thm)], [c_24, c_555])).
% 3.96/1.74  tff(c_752, plain, (![A_179]: (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', A_179, '#skF_1') | k1_relset_1(A_179, '#skF_1', '#skF_2')!=A_179 | ~r1_tarski(k1_relat_1('#skF_2'), A_179) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_750])).
% 3.96/1.74  tff(c_758, plain, (![A_179]: (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', A_179, '#skF_1') | k1_relset_1(A_179, '#skF_1', '#skF_2')!=A_179 | ~r1_tarski(k1_relat_1('#skF_2'), A_179))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_752])).
% 3.96/1.74  tff(c_760, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_758])).
% 3.96/1.74  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.96/1.74  tff(c_795, plain, (![A_6]: (r1_tarski('#skF_1', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_760, c_10])).
% 3.96/1.74  tff(c_86, plain, (![B_38, A_39]: (B_38=A_39 | ~r1_tarski(B_38, A_39) | ~r1_tarski(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.96/1.74  tff(c_93, plain, (k2_relat_1('#skF_2')='#skF_1' | ~r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_86])).
% 3.96/1.74  tff(c_112, plain, (~r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_93])).
% 3.96/1.74  tff(c_803, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_795, c_112])).
% 3.96/1.74  tff(c_826, plain, (![A_183]: (v1_funct_2('#skF_2', A_183, '#skF_1') | k1_relset_1(A_183, '#skF_1', '#skF_2')!=A_183 | ~r1_tarski(k1_relat_1('#skF_2'), A_183))), inference(splitRight, [status(thm)], [c_758])).
% 3.96/1.74  tff(c_830, plain, (v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')!=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_6, c_826])).
% 3.96/1.74  tff(c_833, plain, (v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_620, c_830])).
% 3.96/1.74  tff(c_835, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_833])).
% 3.96/1.74  tff(c_836, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_93])).
% 3.96/1.74  tff(c_65, plain, (![A_36]: (k2_relat_1(A_36)=k1_xboole_0 | k1_relat_1(A_36)!=k1_xboole_0 | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.96/1.74  tff(c_73, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relat_1('#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_65])).
% 3.96/1.74  tff(c_74, plain, (k1_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_73])).
% 3.96/1.74  tff(c_75, plain, (![A_37]: (k1_relat_1(A_37)=k1_xboole_0 | k2_relat_1(A_37)!=k1_xboole_0 | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.96/1.74  tff(c_81, plain, (k1_relat_1('#skF_2')=k1_xboole_0 | k2_relat_1('#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_75])).
% 3.96/1.74  tff(c_85, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_74, c_81])).
% 3.96/1.74  tff(c_838, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_836, c_85])).
% 3.96/1.74  tff(c_939, plain, (![C_216, A_217, B_218]: (m1_subset_1(C_216, k1_zfmisc_1(k2_zfmisc_1(A_217, B_218))) | ~r1_tarski(k2_relat_1(C_216), B_218) | ~r1_tarski(k1_relat_1(C_216), A_217) | ~v1_relat_1(C_216))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.96/1.74  tff(c_1079, plain, (![A_245, B_246, C_247]: (k1_relset_1(A_245, B_246, C_247)=k1_relat_1(C_247) | ~r1_tarski(k2_relat_1(C_247), B_246) | ~r1_tarski(k1_relat_1(C_247), A_245) | ~v1_relat_1(C_247))), inference(resolution, [status(thm)], [c_939, c_22])).
% 3.96/1.74  tff(c_1088, plain, (![A_248, C_249]: (k1_relset_1(A_248, k2_relat_1(C_249), C_249)=k1_relat_1(C_249) | ~r1_tarski(k1_relat_1(C_249), A_248) | ~v1_relat_1(C_249))), inference(resolution, [status(thm)], [c_6, c_1079])).
% 3.96/1.74  tff(c_1098, plain, (![C_252]: (k1_relset_1(k1_relat_1(C_252), k2_relat_1(C_252), C_252)=k1_relat_1(C_252) | ~v1_relat_1(C_252))), inference(resolution, [status(thm)], [c_6, c_1088])).
% 3.96/1.74  tff(c_1115, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_836, c_1098])).
% 3.96/1.74  tff(c_1121, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1115])).
% 3.96/1.74  tff(c_1010, plain, (![B_227, C_228, A_229]: (k1_xboole_0=B_227 | v1_funct_2(C_228, A_229, B_227) | k1_relset_1(A_229, B_227, C_228)!=A_229 | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(A_229, B_227))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.96/1.74  tff(c_1274, plain, (![B_280, C_281, A_282]: (k1_xboole_0=B_280 | v1_funct_2(C_281, A_282, B_280) | k1_relset_1(A_282, B_280, C_281)!=A_282 | ~r1_tarski(k2_relat_1(C_281), B_280) | ~r1_tarski(k1_relat_1(C_281), A_282) | ~v1_relat_1(C_281))), inference(resolution, [status(thm)], [c_24, c_1010])).
% 3.96/1.74  tff(c_1276, plain, (![B_280, A_282]: (k1_xboole_0=B_280 | v1_funct_2('#skF_2', A_282, B_280) | k1_relset_1(A_282, B_280, '#skF_2')!=A_282 | ~r1_tarski('#skF_1', B_280) | ~r1_tarski(k1_relat_1('#skF_2'), A_282) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_836, c_1274])).
% 3.96/1.74  tff(c_1283, plain, (![B_283, A_284]: (k1_xboole_0=B_283 | v1_funct_2('#skF_2', A_284, B_283) | k1_relset_1(A_284, B_283, '#skF_2')!=A_284 | ~r1_tarski('#skF_1', B_283) | ~r1_tarski(k1_relat_1('#skF_2'), A_284))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1276])).
% 3.96/1.74  tff(c_1288, plain, (![B_285]: (k1_xboole_0=B_285 | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), B_285) | k1_relset_1(k1_relat_1('#skF_2'), B_285, '#skF_2')!=k1_relat_1('#skF_2') | ~r1_tarski('#skF_1', B_285))), inference(resolution, [status(thm)], [c_6, c_1283])).
% 3.96/1.74  tff(c_1293, plain, (k1_xboole_0='#skF_1' | k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')!=k1_relat_1('#skF_2') | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_1288, c_64])).
% 3.96/1.74  tff(c_1299, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1121, c_1293])).
% 3.96/1.74  tff(c_1301, plain, $false, inference(negUnitSimplification, [status(thm)], [c_838, c_1299])).
% 3.96/1.74  tff(c_1303, plain, (k1_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_73])).
% 3.96/1.74  tff(c_1442, plain, (![C_322, A_323, B_324]: (m1_subset_1(C_322, k1_zfmisc_1(k2_zfmisc_1(A_323, B_324))) | ~r1_tarski(k2_relat_1(C_322), B_324) | ~r1_tarski(k1_relat_1(C_322), A_323) | ~v1_relat_1(C_322))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.96/1.74  tff(c_34, plain, (![C_28, A_25, B_26]: (v1_partfun1(C_28, A_25) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.96/1.74  tff(c_1509, plain, (![C_331, A_332, B_333]: (v1_partfun1(C_331, A_332) | ~v1_xboole_0(A_332) | ~r1_tarski(k2_relat_1(C_331), B_333) | ~r1_tarski(k1_relat_1(C_331), A_332) | ~v1_relat_1(C_331))), inference(resolution, [status(thm)], [c_1442, c_34])).
% 3.96/1.74  tff(c_1535, plain, (![C_340, A_341]: (v1_partfun1(C_340, A_341) | ~v1_xboole_0(A_341) | ~r1_tarski(k1_relat_1(C_340), A_341) | ~v1_relat_1(C_340))), inference(resolution, [status(thm)], [c_6, c_1509])).
% 3.96/1.74  tff(c_1546, plain, (![C_342]: (v1_partfun1(C_342, k1_relat_1(C_342)) | ~v1_xboole_0(k1_relat_1(C_342)) | ~v1_relat_1(C_342))), inference(resolution, [status(thm)], [c_6, c_1535])).
% 3.96/1.74  tff(c_1549, plain, (v1_partfun1('#skF_2', k1_xboole_0) | ~v1_xboole_0(k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1303, c_1546])).
% 3.96/1.74  tff(c_1551, plain, (v1_partfun1('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1384, c_1303, c_1549])).
% 3.96/1.74  tff(c_1302, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_73])).
% 3.96/1.74  tff(c_30, plain, (![C_24, A_22, B_23]: (v1_funct_2(C_24, A_22, B_23) | ~v1_partfun1(C_24, A_22) | ~v1_funct_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.96/1.74  tff(c_1684, plain, (![C_363, A_364, B_365]: (v1_funct_2(C_363, A_364, B_365) | ~v1_partfun1(C_363, A_364) | ~v1_funct_1(C_363) | ~r1_tarski(k2_relat_1(C_363), B_365) | ~r1_tarski(k1_relat_1(C_363), A_364) | ~v1_relat_1(C_363))), inference(resolution, [status(thm)], [c_1442, c_30])).
% 3.96/1.74  tff(c_1686, plain, (![A_364, B_365]: (v1_funct_2('#skF_2', A_364, B_365) | ~v1_partfun1('#skF_2', A_364) | ~v1_funct_1('#skF_2') | ~r1_tarski(k1_xboole_0, B_365) | ~r1_tarski(k1_relat_1('#skF_2'), A_364) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1302, c_1684])).
% 3.96/1.74  tff(c_1693, plain, (![A_366, B_367]: (v1_funct_2('#skF_2', A_366, B_367) | ~v1_partfun1('#skF_2', A_366))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_10, c_1303, c_10, c_52, c_1686])).
% 3.96/1.74  tff(c_1319, plain, (~v1_funct_2('#skF_2', k1_xboole_0, '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1303, c_64])).
% 3.96/1.74  tff(c_1700, plain, (~v1_partfun1('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_1693, c_1319])).
% 3.96/1.74  tff(c_1705, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1551, c_1700])).
% 3.96/1.74  tff(c_1706, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')))), inference(splitRight, [status(thm)], [c_56])).
% 3.96/1.74  tff(c_1899, plain, (~r1_tarski(k2_relat_1('#skF_2'), '#skF_1') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1870, c_1706])).
% 3.96/1.74  tff(c_1911, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_6, c_50, c_1899])).
% 3.96/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.74  
% 3.96/1.74  Inference rules
% 3.96/1.74  ----------------------
% 3.96/1.74  #Ref     : 0
% 3.96/1.74  #Sup     : 315
% 3.96/1.74  #Fact    : 0
% 3.96/1.74  #Define  : 0
% 3.96/1.74  #Split   : 38
% 3.96/1.74  #Chain   : 0
% 3.96/1.74  #Close   : 0
% 3.96/1.74  
% 3.96/1.74  Ordering : KBO
% 3.96/1.74  
% 3.96/1.74  Simplification rules
% 3.96/1.74  ----------------------
% 3.96/1.74  #Subsume      : 50
% 3.96/1.74  #Demod        : 372
% 3.96/1.74  #Tautology    : 106
% 3.96/1.74  #SimpNegUnit  : 35
% 3.96/1.74  #BackRed      : 112
% 3.96/1.74  
% 3.96/1.74  #Partial instantiations: 0
% 3.96/1.74  #Strategies tried      : 1
% 3.96/1.74  
% 3.96/1.74  Timing (in seconds)
% 3.96/1.74  ----------------------
% 3.96/1.74  Preprocessing        : 0.32
% 3.96/1.75  Parsing              : 0.17
% 3.96/1.75  CNF conversion       : 0.02
% 3.96/1.75  Main loop            : 0.61
% 3.96/1.75  Inferencing          : 0.21
% 3.96/1.75  Reduction            : 0.18
% 3.96/1.75  Demodulation         : 0.12
% 3.96/1.75  BG Simplification    : 0.03
% 3.96/1.75  Subsumption          : 0.14
% 3.96/1.75  Abstraction          : 0.03
% 3.96/1.75  MUC search           : 0.00
% 3.96/1.75  Cooper               : 0.00
% 3.96/1.75  Total                : 0.97
% 3.96/1.75  Index Insertion      : 0.00
% 3.96/1.75  Index Deletion       : 0.00
% 3.96/1.75  Index Matching       : 0.00
% 3.96/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
