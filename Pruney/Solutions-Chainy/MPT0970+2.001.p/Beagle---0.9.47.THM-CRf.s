%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:18 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 173 expanded)
%              Number of leaves         :   44 (  81 expanded)
%              Depth                    :   12
%              Number of atoms          :  147 ( 434 expanded)
%              Number of equality atoms :   44 ( 144 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_4 > #skF_10 > #skF_2 > #skF_7 > #skF_9 > #skF_8 > #skF_5 > #skF_11 > #skF_3

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_134,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(E,D),C) )
      <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_115,axiom,(
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

tff(f_67,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_76,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_167,plain,(
    ! [A_113,B_114,C_115] :
      ( k2_relset_1(A_113,B_114,C_115) = k2_relat_1(C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_171,plain,(
    k2_relset_1('#skF_8','#skF_9','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_76,c_167])).

tff(c_74,plain,(
    k2_relset_1('#skF_8','#skF_9','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_172,plain,(
    k2_relat_1('#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_74])).

tff(c_89,plain,(
    ! [C_90,A_91,B_92] :
      ( v1_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_93,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_76,c_89])).

tff(c_141,plain,(
    ! [C_103,B_104,A_105] :
      ( v5_relat_1(C_103,B_104)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_105,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_145,plain,(
    v5_relat_1('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_76,c_141])).

tff(c_12,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_211,plain,(
    ! [A_138,B_139,C_140] :
      ( r2_hidden('#skF_6'(A_138,B_139,C_140),B_139)
      | k2_relset_1(A_138,B_139,C_140) = B_139
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_213,plain,
    ( r2_hidden('#skF_6'('#skF_8','#skF_9','#skF_10'),'#skF_9')
    | k2_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_76,c_211])).

tff(c_215,plain,
    ( r2_hidden('#skF_6'('#skF_8','#skF_9','#skF_10'),'#skF_9')
    | k2_relat_1('#skF_10') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_213])).

tff(c_216,plain,(
    r2_hidden('#skF_6'('#skF_8','#skF_9','#skF_10'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_215])).

tff(c_84,plain,(
    ! [D_85] :
      ( r2_hidden('#skF_11'(D_85),'#skF_8')
      | ~ r2_hidden(D_85,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_80,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_78,plain,(
    v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_158,plain,(
    ! [A_110,B_111,C_112] :
      ( k1_relset_1(A_110,B_111,C_112) = k1_relat_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_162,plain,(
    k1_relset_1('#skF_8','#skF_9','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_76,c_158])).

tff(c_217,plain,(
    ! [B_141,A_142,C_143] :
      ( k1_xboole_0 = B_141
      | k1_relset_1(A_142,B_141,C_143) = A_142
      | ~ v1_funct_2(C_143,A_142,B_141)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_142,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_220,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_76,c_217])).

tff(c_223,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_162,c_220])).

tff(c_224,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_223])).

tff(c_82,plain,(
    ! [D_85] :
      ( k1_funct_1('#skF_10','#skF_11'(D_85)) = D_85
      | ~ r2_hidden(D_85,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_240,plain,(
    ! [A_146,E_147,B_148] :
      ( r2_hidden(k1_funct_1(A_146,E_147),k9_relat_1(A_146,B_148))
      | ~ r2_hidden(E_147,B_148)
      | ~ r2_hidden(E_147,k1_relat_1(A_146))
      | ~ v1_funct_1(A_146)
      | ~ v1_relat_1(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_243,plain,(
    ! [D_85,B_148] :
      ( r2_hidden(D_85,k9_relat_1('#skF_10',B_148))
      | ~ r2_hidden('#skF_11'(D_85),B_148)
      | ~ r2_hidden('#skF_11'(D_85),k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(D_85,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_240])).

tff(c_246,plain,(
    ! [D_149,B_150] :
      ( r2_hidden(D_149,k9_relat_1('#skF_10',B_150))
      | ~ r2_hidden('#skF_11'(D_149),B_150)
      | ~ r2_hidden('#skF_11'(D_149),'#skF_8')
      | ~ r2_hidden(D_149,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_80,c_224,c_243])).

tff(c_250,plain,(
    ! [D_151] :
      ( r2_hidden(D_151,k9_relat_1('#skF_10','#skF_8'))
      | ~ r2_hidden('#skF_11'(D_151),'#skF_8')
      | ~ r2_hidden(D_151,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_84,c_246])).

tff(c_254,plain,(
    ! [D_85] :
      ( r2_hidden(D_85,k9_relat_1('#skF_10','#skF_8'))
      | ~ r2_hidden(D_85,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_84,c_250])).

tff(c_18,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden(k4_tarski('#skF_1'(A_6,B_7,C_8),A_6),C_8)
      | ~ r2_hidden(A_6,k9_relat_1(C_8,B_7))
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_333,plain,(
    ! [E_172,A_173,B_174,C_175] :
      ( ~ r2_hidden(k4_tarski(E_172,'#skF_6'(A_173,B_174,C_175)),C_175)
      | k2_relset_1(A_173,B_174,C_175) = B_174
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_376,plain,(
    ! [A_187,B_188,C_189,B_190] :
      ( k2_relset_1(A_187,B_188,C_189) = B_188
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188)))
      | ~ r2_hidden('#skF_6'(A_187,B_188,C_189),k9_relat_1(C_189,B_190))
      | ~ v1_relat_1(C_189) ) ),
    inference(resolution,[status(thm)],[c_18,c_333])).

tff(c_384,plain,(
    ! [A_187,B_188] :
      ( k2_relset_1(A_187,B_188,'#skF_10') = B_188
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1(A_187,B_188)))
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden('#skF_6'(A_187,B_188,'#skF_10'),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_254,c_376])).

tff(c_403,plain,(
    ! [A_194,B_195] :
      ( k2_relset_1(A_194,B_195,'#skF_10') = B_195
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1(A_194,B_195)))
      | ~ r2_hidden('#skF_6'(A_194,B_195,'#skF_10'),'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_384])).

tff(c_406,plain,
    ( k2_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_9'
    | ~ r2_hidden('#skF_6'('#skF_8','#skF_9','#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_76,c_403])).

tff(c_409,plain,(
    k2_relat_1('#skF_10') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_171,c_406])).

tff(c_411,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_409])).

tff(c_412,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_103,plain,(
    ! [B_94,A_95] :
      ( B_94 = A_95
      | ~ r1_tarski(B_94,A_95)
      | ~ r1_tarski(A_95,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_112,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_103])).

tff(c_436,plain,(
    ! [A_197] :
      ( A_197 = '#skF_9'
      | ~ r1_tarski(A_197,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_412,c_112])).

tff(c_455,plain,(
    ! [B_201] :
      ( k2_relat_1(B_201) = '#skF_9'
      | ~ v5_relat_1(B_201,'#skF_9')
      | ~ v1_relat_1(B_201) ) ),
    inference(resolution,[status(thm)],[c_12,c_436])).

tff(c_458,plain,
    ( k2_relat_1('#skF_10') = '#skF_9'
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_145,c_455])).

tff(c_461,plain,(
    k2_relat_1('#skF_10') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_458])).

tff(c_463,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_461])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:00:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.38  
% 2.62/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.38  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_4 > #skF_10 > #skF_2 > #skF_7 > #skF_9 > #skF_8 > #skF_5 > #skF_11 > #skF_3
% 2.62/1.38  
% 2.62/1.38  %Foreground sorts:
% 2.62/1.38  
% 2.62/1.38  
% 2.62/1.38  %Background operators:
% 2.62/1.38  
% 2.62/1.38  
% 2.62/1.38  %Foreground operators:
% 2.62/1.38  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.62/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.62/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.62/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.62/1.38  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.62/1.38  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.62/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.62/1.38  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.62/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.62/1.38  tff('#skF_10', type, '#skF_10': $i).
% 2.62/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.62/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.62/1.38  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.62/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.62/1.38  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 2.62/1.38  tff('#skF_9', type, '#skF_9': $i).
% 2.62/1.38  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.62/1.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.62/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.62/1.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.62/1.38  tff('#skF_8', type, '#skF_8': $i).
% 2.62/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.38  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.62/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.62/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.62/1.38  tff('#skF_11', type, '#skF_11': $i > $i).
% 2.62/1.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.62/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.62/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.62/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.62/1.38  
% 2.96/1.40  tff(f_134, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 2.96/1.40  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.96/1.40  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.96/1.40  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.96/1.40  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.96/1.40  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(E, D), C)))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_relset_1)).
% 2.96/1.40  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.96/1.40  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.96/1.40  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 2.96/1.40  tff(f_50, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 2.96/1.40  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.96/1.40  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.96/1.40  tff(c_76, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.96/1.40  tff(c_167, plain, (![A_113, B_114, C_115]: (k2_relset_1(A_113, B_114, C_115)=k2_relat_1(C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.96/1.40  tff(c_171, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_76, c_167])).
% 2.96/1.40  tff(c_74, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.96/1.40  tff(c_172, plain, (k2_relat_1('#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_171, c_74])).
% 2.96/1.40  tff(c_89, plain, (![C_90, A_91, B_92]: (v1_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.96/1.40  tff(c_93, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_76, c_89])).
% 2.96/1.40  tff(c_141, plain, (![C_103, B_104, A_105]: (v5_relat_1(C_103, B_104) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_105, B_104))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.96/1.40  tff(c_145, plain, (v5_relat_1('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_76, c_141])).
% 2.96/1.40  tff(c_12, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.96/1.40  tff(c_211, plain, (![A_138, B_139, C_140]: (r2_hidden('#skF_6'(A_138, B_139, C_140), B_139) | k2_relset_1(A_138, B_139, C_140)=B_139 | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.96/1.40  tff(c_213, plain, (r2_hidden('#skF_6'('#skF_8', '#skF_9', '#skF_10'), '#skF_9') | k2_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_76, c_211])).
% 2.96/1.40  tff(c_215, plain, (r2_hidden('#skF_6'('#skF_8', '#skF_9', '#skF_10'), '#skF_9') | k2_relat_1('#skF_10')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_171, c_213])).
% 2.96/1.40  tff(c_216, plain, (r2_hidden('#skF_6'('#skF_8', '#skF_9', '#skF_10'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_172, c_215])).
% 2.96/1.40  tff(c_84, plain, (![D_85]: (r2_hidden('#skF_11'(D_85), '#skF_8') | ~r2_hidden(D_85, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.96/1.40  tff(c_80, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.96/1.40  tff(c_78, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.96/1.40  tff(c_158, plain, (![A_110, B_111, C_112]: (k1_relset_1(A_110, B_111, C_112)=k1_relat_1(C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.96/1.40  tff(c_162, plain, (k1_relset_1('#skF_8', '#skF_9', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_76, c_158])).
% 2.96/1.40  tff(c_217, plain, (![B_141, A_142, C_143]: (k1_xboole_0=B_141 | k1_relset_1(A_142, B_141, C_143)=A_142 | ~v1_funct_2(C_143, A_142, B_141) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_142, B_141))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.96/1.40  tff(c_220, plain, (k1_xboole_0='#skF_9' | k1_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_8' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_76, c_217])).
% 2.96/1.40  tff(c_223, plain, (k1_xboole_0='#skF_9' | k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_162, c_220])).
% 2.96/1.40  tff(c_224, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(splitLeft, [status(thm)], [c_223])).
% 2.96/1.40  tff(c_82, plain, (![D_85]: (k1_funct_1('#skF_10', '#skF_11'(D_85))=D_85 | ~r2_hidden(D_85, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.96/1.40  tff(c_240, plain, (![A_146, E_147, B_148]: (r2_hidden(k1_funct_1(A_146, E_147), k9_relat_1(A_146, B_148)) | ~r2_hidden(E_147, B_148) | ~r2_hidden(E_147, k1_relat_1(A_146)) | ~v1_funct_1(A_146) | ~v1_relat_1(A_146))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.96/1.40  tff(c_243, plain, (![D_85, B_148]: (r2_hidden(D_85, k9_relat_1('#skF_10', B_148)) | ~r2_hidden('#skF_11'(D_85), B_148) | ~r2_hidden('#skF_11'(D_85), k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(D_85, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_240])).
% 2.96/1.40  tff(c_246, plain, (![D_149, B_150]: (r2_hidden(D_149, k9_relat_1('#skF_10', B_150)) | ~r2_hidden('#skF_11'(D_149), B_150) | ~r2_hidden('#skF_11'(D_149), '#skF_8') | ~r2_hidden(D_149, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_80, c_224, c_243])).
% 2.96/1.40  tff(c_250, plain, (![D_151]: (r2_hidden(D_151, k9_relat_1('#skF_10', '#skF_8')) | ~r2_hidden('#skF_11'(D_151), '#skF_8') | ~r2_hidden(D_151, '#skF_9'))), inference(resolution, [status(thm)], [c_84, c_246])).
% 2.96/1.40  tff(c_254, plain, (![D_85]: (r2_hidden(D_85, k9_relat_1('#skF_10', '#skF_8')) | ~r2_hidden(D_85, '#skF_9'))), inference(resolution, [status(thm)], [c_84, c_250])).
% 2.96/1.40  tff(c_18, plain, (![A_6, B_7, C_8]: (r2_hidden(k4_tarski('#skF_1'(A_6, B_7, C_8), A_6), C_8) | ~r2_hidden(A_6, k9_relat_1(C_8, B_7)) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.96/1.40  tff(c_333, plain, (![E_172, A_173, B_174, C_175]: (~r2_hidden(k4_tarski(E_172, '#skF_6'(A_173, B_174, C_175)), C_175) | k2_relset_1(A_173, B_174, C_175)=B_174 | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.96/1.40  tff(c_376, plain, (![A_187, B_188, C_189, B_190]: (k2_relset_1(A_187, B_188, C_189)=B_188 | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))) | ~r2_hidden('#skF_6'(A_187, B_188, C_189), k9_relat_1(C_189, B_190)) | ~v1_relat_1(C_189))), inference(resolution, [status(thm)], [c_18, c_333])).
% 2.96/1.40  tff(c_384, plain, (![A_187, B_188]: (k2_relset_1(A_187, B_188, '#skF_10')=B_188 | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))) | ~v1_relat_1('#skF_10') | ~r2_hidden('#skF_6'(A_187, B_188, '#skF_10'), '#skF_9'))), inference(resolution, [status(thm)], [c_254, c_376])).
% 2.96/1.40  tff(c_403, plain, (![A_194, B_195]: (k2_relset_1(A_194, B_195, '#skF_10')=B_195 | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1(A_194, B_195))) | ~r2_hidden('#skF_6'(A_194, B_195, '#skF_10'), '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_384])).
% 2.96/1.40  tff(c_406, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_9' | ~r2_hidden('#skF_6'('#skF_8', '#skF_9', '#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_76, c_403])).
% 2.96/1.40  tff(c_409, plain, (k2_relat_1('#skF_10')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_216, c_171, c_406])).
% 2.96/1.40  tff(c_411, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172, c_409])).
% 2.96/1.40  tff(c_412, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_223])).
% 2.96/1.40  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.96/1.40  tff(c_103, plain, (![B_94, A_95]: (B_94=A_95 | ~r1_tarski(B_94, A_95) | ~r1_tarski(A_95, B_94))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.96/1.40  tff(c_112, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_103])).
% 2.96/1.40  tff(c_436, plain, (![A_197]: (A_197='#skF_9' | ~r1_tarski(A_197, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_412, c_412, c_112])).
% 2.96/1.40  tff(c_455, plain, (![B_201]: (k2_relat_1(B_201)='#skF_9' | ~v5_relat_1(B_201, '#skF_9') | ~v1_relat_1(B_201))), inference(resolution, [status(thm)], [c_12, c_436])).
% 2.96/1.40  tff(c_458, plain, (k2_relat_1('#skF_10')='#skF_9' | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_145, c_455])).
% 2.96/1.40  tff(c_461, plain, (k2_relat_1('#skF_10')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_93, c_458])).
% 2.96/1.40  tff(c_463, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172, c_461])).
% 2.96/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.40  
% 2.96/1.40  Inference rules
% 2.96/1.40  ----------------------
% 2.96/1.40  #Ref     : 0
% 2.96/1.40  #Sup     : 78
% 2.96/1.40  #Fact    : 0
% 2.96/1.40  #Define  : 0
% 2.96/1.40  #Split   : 1
% 2.96/1.40  #Chain   : 0
% 2.96/1.40  #Close   : 0
% 2.96/1.40  
% 2.96/1.40  Ordering : KBO
% 2.96/1.40  
% 2.96/1.40  Simplification rules
% 2.96/1.40  ----------------------
% 2.96/1.40  #Subsume      : 3
% 2.96/1.40  #Demod        : 46
% 2.96/1.40  #Tautology    : 24
% 2.96/1.40  #SimpNegUnit  : 3
% 2.96/1.40  #BackRed      : 11
% 2.96/1.40  
% 2.96/1.40  #Partial instantiations: 0
% 2.96/1.40  #Strategies tried      : 1
% 2.96/1.40  
% 2.96/1.40  Timing (in seconds)
% 2.96/1.40  ----------------------
% 2.96/1.40  Preprocessing        : 0.35
% 2.96/1.40  Parsing              : 0.18
% 2.96/1.40  CNF conversion       : 0.03
% 2.96/1.40  Main loop            : 0.29
% 2.96/1.40  Inferencing          : 0.10
% 2.96/1.41  Reduction            : 0.08
% 2.96/1.41  Demodulation         : 0.06
% 2.96/1.41  BG Simplification    : 0.02
% 2.96/1.41  Subsumption          : 0.05
% 2.96/1.41  Abstraction          : 0.02
% 2.96/1.41  MUC search           : 0.00
% 2.96/1.41  Cooper               : 0.00
% 2.96/1.41  Total                : 0.68
% 2.96/1.41  Index Insertion      : 0.00
% 2.96/1.41  Index Deletion       : 0.00
% 2.96/1.41  Index Matching       : 0.00
% 2.96/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
