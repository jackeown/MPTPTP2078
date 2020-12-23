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
% DateTime   : Thu Dec  3 10:11:22 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 770 expanded)
%              Number of leaves         :   38 ( 286 expanded)
%              Depth                    :   12
%              Number of atoms          :  154 (2530 expanded)
%              Number of equality atoms :   59 (1125 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_4 > #skF_10 > #skF_2 > #skF_7 > #skF_9 > #skF_8 > #skF_5 > #skF_11 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(E,D),C) )
      <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_98,axiom,(
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

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_39,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_106,plain,(
    ! [A_88,B_89,C_90] :
      ( k2_relset_1(A_88,B_89,C_90) = k2_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_110,plain,(
    k2_relset_1('#skF_8','#skF_9','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_64,c_106])).

tff(c_62,plain,(
    k2_relset_1('#skF_8','#skF_9','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_111,plain,(
    k2_relat_1('#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_62])).

tff(c_132,plain,(
    ! [A_109,B_110,C_111] :
      ( r2_hidden('#skF_6'(A_109,B_110,C_111),B_110)
      | k2_relset_1(A_109,B_110,C_111) = B_110
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_134,plain,
    ( r2_hidden('#skF_6'('#skF_8','#skF_9','#skF_10'),'#skF_9')
    | k2_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_64,c_132])).

tff(c_136,plain,
    ( r2_hidden('#skF_6'('#skF_8','#skF_9','#skF_10'),'#skF_9')
    | k2_relat_1('#skF_10') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_134])).

tff(c_137,plain,(
    r2_hidden('#skF_6'('#skF_8','#skF_9','#skF_10'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_136])).

tff(c_82,plain,(
    ! [C_80,A_81,B_82] :
      ( v1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_86,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_64,c_82])).

tff(c_72,plain,(
    ! [D_77] :
      ( r2_hidden('#skF_11'(D_77),'#skF_8')
      | ~ r2_hidden(D_77,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_68,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_66,plain,(
    v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_97,plain,(
    ! [A_85,B_86,C_87] :
      ( k1_relset_1(A_85,B_86,C_87) = k1_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_101,plain,(
    k1_relset_1('#skF_8','#skF_9','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_64,c_97])).

tff(c_138,plain,(
    ! [B_112,A_113,C_114] :
      ( k1_xboole_0 = B_112
      | k1_relset_1(A_113,B_112,C_114) = A_113
      | ~ v1_funct_2(C_114,A_113,B_112)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_113,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_141,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_64,c_138])).

tff(c_144,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_101,c_141])).

tff(c_145,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_70,plain,(
    ! [D_77] :
      ( k1_funct_1('#skF_10','#skF_11'(D_77)) = D_77
      | ~ r2_hidden(D_77,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_161,plain,(
    ! [A_117,E_118,B_119] :
      ( r2_hidden(k1_funct_1(A_117,E_118),k9_relat_1(A_117,B_119))
      | ~ r2_hidden(E_118,B_119)
      | ~ r2_hidden(E_118,k1_relat_1(A_117))
      | ~ v1_funct_1(A_117)
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_164,plain,(
    ! [D_77,B_119] :
      ( r2_hidden(D_77,k9_relat_1('#skF_10',B_119))
      | ~ r2_hidden('#skF_11'(D_77),B_119)
      | ~ r2_hidden('#skF_11'(D_77),k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(D_77,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_161])).

tff(c_167,plain,(
    ! [D_120,B_121] :
      ( r2_hidden(D_120,k9_relat_1('#skF_10',B_121))
      | ~ r2_hidden('#skF_11'(D_120),B_121)
      | ~ r2_hidden('#skF_11'(D_120),'#skF_8')
      | ~ r2_hidden(D_120,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_68,c_145,c_164])).

tff(c_171,plain,(
    ! [D_122] :
      ( r2_hidden(D_122,k9_relat_1('#skF_10','#skF_8'))
      | ~ r2_hidden('#skF_11'(D_122),'#skF_8')
      | ~ r2_hidden(D_122,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_72,c_167])).

tff(c_175,plain,(
    ! [D_77] :
      ( r2_hidden(D_77,k9_relat_1('#skF_10','#skF_8'))
      | ~ r2_hidden(D_77,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_72,c_171])).

tff(c_6,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden(k4_tarski('#skF_1'(A_1,B_2,C_3),A_1),C_3)
      | ~ r2_hidden(A_1,k9_relat_1(C_3,B_2))
      | ~ v1_relat_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_257,plain,(
    ! [E_143,A_144,B_145,C_146] :
      ( ~ r2_hidden(k4_tarski(E_143,'#skF_6'(A_144,B_145,C_146)),C_146)
      | k2_relset_1(A_144,B_145,C_146) = B_145
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_303,plain,(
    ! [A_158,B_159,C_160,B_161] :
      ( k2_relset_1(A_158,B_159,C_160) = B_159
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159)))
      | ~ r2_hidden('#skF_6'(A_158,B_159,C_160),k9_relat_1(C_160,B_161))
      | ~ v1_relat_1(C_160) ) ),
    inference(resolution,[status(thm)],[c_6,c_257])).

tff(c_311,plain,(
    ! [A_158,B_159] :
      ( k2_relset_1(A_158,B_159,'#skF_10') = B_159
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1(A_158,B_159)))
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden('#skF_6'(A_158,B_159,'#skF_10'),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_175,c_303])).

tff(c_330,plain,(
    ! [A_165,B_166] :
      ( k2_relset_1(A_165,B_166,'#skF_10') = B_166
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1(A_165,B_166)))
      | ~ r2_hidden('#skF_6'(A_165,B_166,'#skF_10'),'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_311])).

tff(c_333,plain,
    ( k2_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_9'
    | ~ r2_hidden('#skF_6'('#skF_8','#skF_9','#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_64,c_330])).

tff(c_336,plain,(
    k2_relat_1('#skF_10') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_110,c_333])).

tff(c_338,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_336])).

tff(c_339,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_10,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_349,plain,(
    k2_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_339,c_10])).

tff(c_340,plain,(
    k1_relat_1('#skF_10') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_52,plain,(
    ! [C_73,A_71] :
      ( k1_xboole_0 = C_73
      | ~ v1_funct_2(C_73,A_71,k1_xboole_0)
      | k1_xboole_0 = A_71
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_367,plain,(
    ! [C_171,A_172] :
      ( C_171 = '#skF_9'
      | ~ v1_funct_2(C_171,A_172,'#skF_9')
      | A_172 = '#skF_9'
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_172,'#skF_9'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_339,c_339,c_339,c_52])).

tff(c_370,plain,
    ( '#skF_10' = '#skF_9'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_9')
    | '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_64,c_367])).

tff(c_373,plain,
    ( '#skF_10' = '#skF_9'
    | '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_370])).

tff(c_374,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_373])).

tff(c_388,plain,(
    v1_funct_2('#skF_10','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_66])).

tff(c_384,plain,(
    k1_relset_1('#skF_8','#skF_8','#skF_10') = k1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_101])).

tff(c_387,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_64])).

tff(c_58,plain,(
    ! [B_72,C_73] :
      ( k1_relset_1(k1_xboole_0,B_72,C_73) = k1_xboole_0
      | ~ v1_funct_2(C_73,k1_xboole_0,B_72)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_344,plain,(
    ! [B_72,C_73] :
      ( k1_relset_1('#skF_9',B_72,C_73) = '#skF_9'
      | ~ v1_funct_2(C_73,'#skF_9',B_72)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1('#skF_9',B_72))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_339,c_339,c_339,c_58])).

tff(c_478,plain,(
    ! [B_189,C_190] :
      ( k1_relset_1('#skF_8',B_189,C_190) = '#skF_8'
      | ~ v1_funct_2(C_190,'#skF_8',B_189)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1('#skF_8',B_189))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_374,c_374,c_374,c_344])).

tff(c_481,plain,
    ( k1_relset_1('#skF_8','#skF_8','#skF_10') = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_387,c_478])).

tff(c_484,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_384,c_481])).

tff(c_486,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_340,c_484])).

tff(c_487,plain,(
    '#skF_10' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_373])).

tff(c_491,plain,(
    k2_relat_1('#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_111])).

tff(c_502,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_491])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:26:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.44  
% 2.83/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.44  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_4 > #skF_10 > #skF_2 > #skF_7 > #skF_9 > #skF_8 > #skF_5 > #skF_11 > #skF_3
% 2.83/1.44  
% 2.83/1.44  %Foreground sorts:
% 2.83/1.44  
% 2.83/1.44  
% 2.83/1.44  %Background operators:
% 2.83/1.44  
% 2.83/1.44  
% 2.83/1.44  %Foreground operators:
% 2.83/1.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.83/1.44  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.83/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.83/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.83/1.44  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.83/1.44  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.83/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.83/1.44  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.83/1.44  tff('#skF_10', type, '#skF_10': $i).
% 2.83/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.83/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.83/1.44  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.83/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.83/1.44  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 2.83/1.44  tff('#skF_9', type, '#skF_9': $i).
% 2.83/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.83/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.83/1.44  tff('#skF_8', type, '#skF_8': $i).
% 2.83/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.44  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.83/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.83/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.83/1.44  tff('#skF_11', type, '#skF_11': $i > $i).
% 2.83/1.44  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.83/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.83/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.44  
% 3.10/1.46  tff(f_117, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 3.10/1.46  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.10/1.46  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(E, D), C)))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_relset_1)).
% 3.10/1.46  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.10/1.46  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.10/1.46  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.10/1.46  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 3.10/1.46  tff(f_36, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 3.10/1.46  tff(f_39, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.10/1.46  tff(c_64, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.10/1.46  tff(c_106, plain, (![A_88, B_89, C_90]: (k2_relset_1(A_88, B_89, C_90)=k2_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.10/1.46  tff(c_110, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_64, c_106])).
% 3.10/1.46  tff(c_62, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.10/1.46  tff(c_111, plain, (k2_relat_1('#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_62])).
% 3.10/1.46  tff(c_132, plain, (![A_109, B_110, C_111]: (r2_hidden('#skF_6'(A_109, B_110, C_111), B_110) | k2_relset_1(A_109, B_110, C_111)=B_110 | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.10/1.46  tff(c_134, plain, (r2_hidden('#skF_6'('#skF_8', '#skF_9', '#skF_10'), '#skF_9') | k2_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_64, c_132])).
% 3.10/1.46  tff(c_136, plain, (r2_hidden('#skF_6'('#skF_8', '#skF_9', '#skF_10'), '#skF_9') | k2_relat_1('#skF_10')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_134])).
% 3.10/1.46  tff(c_137, plain, (r2_hidden('#skF_6'('#skF_8', '#skF_9', '#skF_10'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_111, c_136])).
% 3.10/1.46  tff(c_82, plain, (![C_80, A_81, B_82]: (v1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.10/1.46  tff(c_86, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_64, c_82])).
% 3.10/1.46  tff(c_72, plain, (![D_77]: (r2_hidden('#skF_11'(D_77), '#skF_8') | ~r2_hidden(D_77, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.10/1.46  tff(c_68, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.10/1.46  tff(c_66, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.10/1.46  tff(c_97, plain, (![A_85, B_86, C_87]: (k1_relset_1(A_85, B_86, C_87)=k1_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.10/1.46  tff(c_101, plain, (k1_relset_1('#skF_8', '#skF_9', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_64, c_97])).
% 3.10/1.46  tff(c_138, plain, (![B_112, A_113, C_114]: (k1_xboole_0=B_112 | k1_relset_1(A_113, B_112, C_114)=A_113 | ~v1_funct_2(C_114, A_113, B_112) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_113, B_112))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.10/1.46  tff(c_141, plain, (k1_xboole_0='#skF_9' | k1_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_8' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_64, c_138])).
% 3.10/1.46  tff(c_144, plain, (k1_xboole_0='#skF_9' | k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_101, c_141])).
% 3.10/1.46  tff(c_145, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(splitLeft, [status(thm)], [c_144])).
% 3.10/1.46  tff(c_70, plain, (![D_77]: (k1_funct_1('#skF_10', '#skF_11'(D_77))=D_77 | ~r2_hidden(D_77, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.10/1.46  tff(c_161, plain, (![A_117, E_118, B_119]: (r2_hidden(k1_funct_1(A_117, E_118), k9_relat_1(A_117, B_119)) | ~r2_hidden(E_118, B_119) | ~r2_hidden(E_118, k1_relat_1(A_117)) | ~v1_funct_1(A_117) | ~v1_relat_1(A_117))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.10/1.46  tff(c_164, plain, (![D_77, B_119]: (r2_hidden(D_77, k9_relat_1('#skF_10', B_119)) | ~r2_hidden('#skF_11'(D_77), B_119) | ~r2_hidden('#skF_11'(D_77), k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(D_77, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_161])).
% 3.10/1.46  tff(c_167, plain, (![D_120, B_121]: (r2_hidden(D_120, k9_relat_1('#skF_10', B_121)) | ~r2_hidden('#skF_11'(D_120), B_121) | ~r2_hidden('#skF_11'(D_120), '#skF_8') | ~r2_hidden(D_120, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_68, c_145, c_164])).
% 3.10/1.46  tff(c_171, plain, (![D_122]: (r2_hidden(D_122, k9_relat_1('#skF_10', '#skF_8')) | ~r2_hidden('#skF_11'(D_122), '#skF_8') | ~r2_hidden(D_122, '#skF_9'))), inference(resolution, [status(thm)], [c_72, c_167])).
% 3.10/1.46  tff(c_175, plain, (![D_77]: (r2_hidden(D_77, k9_relat_1('#skF_10', '#skF_8')) | ~r2_hidden(D_77, '#skF_9'))), inference(resolution, [status(thm)], [c_72, c_171])).
% 3.10/1.46  tff(c_6, plain, (![A_1, B_2, C_3]: (r2_hidden(k4_tarski('#skF_1'(A_1, B_2, C_3), A_1), C_3) | ~r2_hidden(A_1, k9_relat_1(C_3, B_2)) | ~v1_relat_1(C_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.10/1.46  tff(c_257, plain, (![E_143, A_144, B_145, C_146]: (~r2_hidden(k4_tarski(E_143, '#skF_6'(A_144, B_145, C_146)), C_146) | k2_relset_1(A_144, B_145, C_146)=B_145 | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.10/1.46  tff(c_303, plain, (![A_158, B_159, C_160, B_161]: (k2_relset_1(A_158, B_159, C_160)=B_159 | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))) | ~r2_hidden('#skF_6'(A_158, B_159, C_160), k9_relat_1(C_160, B_161)) | ~v1_relat_1(C_160))), inference(resolution, [status(thm)], [c_6, c_257])).
% 3.10/1.46  tff(c_311, plain, (![A_158, B_159]: (k2_relset_1(A_158, B_159, '#skF_10')=B_159 | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))) | ~v1_relat_1('#skF_10') | ~r2_hidden('#skF_6'(A_158, B_159, '#skF_10'), '#skF_9'))), inference(resolution, [status(thm)], [c_175, c_303])).
% 3.10/1.46  tff(c_330, plain, (![A_165, B_166]: (k2_relset_1(A_165, B_166, '#skF_10')=B_166 | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))) | ~r2_hidden('#skF_6'(A_165, B_166, '#skF_10'), '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_311])).
% 3.10/1.46  tff(c_333, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_9' | ~r2_hidden('#skF_6'('#skF_8', '#skF_9', '#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_64, c_330])).
% 3.10/1.46  tff(c_336, plain, (k2_relat_1('#skF_10')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_137, c_110, c_333])).
% 3.10/1.46  tff(c_338, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111, c_336])).
% 3.10/1.46  tff(c_339, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_144])).
% 3.10/1.46  tff(c_10, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.10/1.46  tff(c_349, plain, (k2_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_339, c_339, c_10])).
% 3.10/1.46  tff(c_340, plain, (k1_relat_1('#skF_10')!='#skF_8'), inference(splitRight, [status(thm)], [c_144])).
% 3.10/1.46  tff(c_52, plain, (![C_73, A_71]: (k1_xboole_0=C_73 | ~v1_funct_2(C_73, A_71, k1_xboole_0) | k1_xboole_0=A_71 | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.10/1.46  tff(c_367, plain, (![C_171, A_172]: (C_171='#skF_9' | ~v1_funct_2(C_171, A_172, '#skF_9') | A_172='#skF_9' | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_172, '#skF_9'))))), inference(demodulation, [status(thm), theory('equality')], [c_339, c_339, c_339, c_339, c_52])).
% 3.10/1.46  tff(c_370, plain, ('#skF_10'='#skF_9' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9') | '#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_64, c_367])).
% 3.10/1.46  tff(c_373, plain, ('#skF_10'='#skF_9' | '#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_370])).
% 3.10/1.46  tff(c_374, plain, ('#skF_9'='#skF_8'), inference(splitLeft, [status(thm)], [c_373])).
% 3.10/1.46  tff(c_388, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_374, c_66])).
% 3.10/1.46  tff(c_384, plain, (k1_relset_1('#skF_8', '#skF_8', '#skF_10')=k1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_374, c_101])).
% 3.10/1.46  tff(c_387, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_374, c_64])).
% 3.10/1.46  tff(c_58, plain, (![B_72, C_73]: (k1_relset_1(k1_xboole_0, B_72, C_73)=k1_xboole_0 | ~v1_funct_2(C_73, k1_xboole_0, B_72) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_72))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.10/1.46  tff(c_344, plain, (![B_72, C_73]: (k1_relset_1('#skF_9', B_72, C_73)='#skF_9' | ~v1_funct_2(C_73, '#skF_9', B_72) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1('#skF_9', B_72))))), inference(demodulation, [status(thm), theory('equality')], [c_339, c_339, c_339, c_339, c_58])).
% 3.10/1.46  tff(c_478, plain, (![B_189, C_190]: (k1_relset_1('#skF_8', B_189, C_190)='#skF_8' | ~v1_funct_2(C_190, '#skF_8', B_189) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1('#skF_8', B_189))))), inference(demodulation, [status(thm), theory('equality')], [c_374, c_374, c_374, c_374, c_344])).
% 3.10/1.46  tff(c_481, plain, (k1_relset_1('#skF_8', '#skF_8', '#skF_10')='#skF_8' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_387, c_478])).
% 3.10/1.46  tff(c_484, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_388, c_384, c_481])).
% 3.10/1.46  tff(c_486, plain, $false, inference(negUnitSimplification, [status(thm)], [c_340, c_484])).
% 3.10/1.46  tff(c_487, plain, ('#skF_10'='#skF_9'), inference(splitRight, [status(thm)], [c_373])).
% 3.10/1.46  tff(c_491, plain, (k2_relat_1('#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_487, c_111])).
% 3.10/1.46  tff(c_502, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_349, c_491])).
% 3.10/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.46  
% 3.10/1.46  Inference rules
% 3.10/1.46  ----------------------
% 3.10/1.46  #Ref     : 0
% 3.10/1.46  #Sup     : 96
% 3.10/1.46  #Fact    : 0
% 3.10/1.46  #Define  : 0
% 3.10/1.46  #Split   : 3
% 3.10/1.46  #Chain   : 0
% 3.10/1.46  #Close   : 0
% 3.10/1.46  
% 3.10/1.46  Ordering : KBO
% 3.10/1.46  
% 3.10/1.46  Simplification rules
% 3.10/1.46  ----------------------
% 3.10/1.46  #Subsume      : 7
% 3.10/1.46  #Demod        : 102
% 3.10/1.46  #Tautology    : 42
% 3.10/1.46  #SimpNegUnit  : 4
% 3.10/1.46  #BackRed      : 35
% 3.10/1.46  
% 3.10/1.46  #Partial instantiations: 0
% 3.10/1.46  #Strategies tried      : 1
% 3.10/1.46  
% 3.10/1.46  Timing (in seconds)
% 3.10/1.46  ----------------------
% 3.10/1.46  Preprocessing        : 0.35
% 3.10/1.46  Parsing              : 0.18
% 3.10/1.46  CNF conversion       : 0.03
% 3.10/1.46  Main loop            : 0.32
% 3.10/1.46  Inferencing          : 0.11
% 3.10/1.46  Reduction            : 0.10
% 3.10/1.46  Demodulation         : 0.07
% 3.10/1.46  BG Simplification    : 0.02
% 3.10/1.46  Subsumption          : 0.06
% 3.10/1.46  Abstraction          : 0.02
% 3.10/1.46  MUC search           : 0.00
% 3.10/1.46  Cooper               : 0.00
% 3.10/1.46  Total                : 0.71
% 3.10/1.46  Index Insertion      : 0.00
% 3.10/1.46  Index Deletion       : 0.00
% 3.10/1.46  Index Matching       : 0.00
% 3.10/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
