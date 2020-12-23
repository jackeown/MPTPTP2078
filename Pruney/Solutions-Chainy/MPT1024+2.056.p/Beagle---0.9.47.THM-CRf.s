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
% DateTime   : Thu Dec  3 10:16:29 EST 2020

% Result     : Theorem 4.19s
% Output     : CNFRefutation 4.46s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 986 expanded)
%              Number of leaves         :   38 ( 350 expanded)
%              Depth                    :   11
%              Number of atoms          :  236 (2910 expanded)
%              Number of equality atoms :   72 ( 921 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ~ ( r2_hidden(F,A)
                    & r2_hidden(F,C)
                    & E = k1_funct_1(D,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_70,axiom,(
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

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_54,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_182,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( k7_relset_1(A_95,B_96,C_97,D_98) = k9_relat_1(C_97,D_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_189,plain,(
    ! [D_98] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_98) = k9_relat_1('#skF_7',D_98) ),
    inference(resolution,[status(thm)],[c_54,c_182])).

tff(c_52,plain,(
    r2_hidden('#skF_8',k7_relset_1('#skF_4','#skF_5','#skF_7','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_191,plain,(
    r2_hidden('#skF_8',k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_52])).

tff(c_10,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_76,plain,(
    ! [B_57,A_58] :
      ( v1_relat_1(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58))
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_82,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_54,c_76])).

tff(c_86,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_82])).

tff(c_56,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_115,plain,(
    ! [A_65,B_66,C_67] :
      ( k1_relset_1(A_65,B_66,C_67) = k1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_124,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_115])).

tff(c_1051,plain,(
    ! [B_226,A_227,C_228] :
      ( k1_xboole_0 = B_226
      | k1_relset_1(A_227,B_226,C_228) = A_227
      | ~ v1_funct_2(C_228,A_227,B_226)
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(A_227,B_226))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1058,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_1051])).

tff(c_1062,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_124,c_1058])).

tff(c_1063,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1062])).

tff(c_18,plain,(
    ! [A_9,B_10,C_11] :
      ( r2_hidden('#skF_1'(A_9,B_10,C_11),k1_relat_1(C_11))
      | ~ r2_hidden(A_9,k9_relat_1(C_11,B_10))
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1071,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_1'(A_9,B_10,'#skF_7'),'#skF_4')
      | ~ r2_hidden(A_9,k9_relat_1('#skF_7',B_10))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1063,c_18])).

tff(c_1145,plain,(
    ! [A_239,B_240] :
      ( r2_hidden('#skF_1'(A_239,B_240,'#skF_7'),'#skF_4')
      | ~ r2_hidden(A_239,k9_relat_1('#skF_7',B_240)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1071])).

tff(c_148,plain,(
    ! [A_76,B_77,C_78] :
      ( r2_hidden('#skF_1'(A_76,B_77,C_78),B_77)
      | ~ r2_hidden(A_76,k9_relat_1(C_78,B_77))
      | ~ v1_relat_1(C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_50,plain,(
    ! [F_47] :
      ( k1_funct_1('#skF_7',F_47) != '#skF_8'
      | ~ r2_hidden(F_47,'#skF_6')
      | ~ r2_hidden(F_47,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_156,plain,(
    ! [A_76,C_78] :
      ( k1_funct_1('#skF_7','#skF_1'(A_76,'#skF_6',C_78)) != '#skF_8'
      | ~ r2_hidden('#skF_1'(A_76,'#skF_6',C_78),'#skF_4')
      | ~ r2_hidden(A_76,k9_relat_1(C_78,'#skF_6'))
      | ~ v1_relat_1(C_78) ) ),
    inference(resolution,[status(thm)],[c_148,c_50])).

tff(c_1149,plain,(
    ! [A_239] :
      ( k1_funct_1('#skF_7','#skF_1'(A_239,'#skF_6','#skF_7')) != '#skF_8'
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(A_239,k9_relat_1('#skF_7','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_1145,c_156])).

tff(c_1177,plain,(
    ! [A_243] :
      ( k1_funct_1('#skF_7','#skF_1'(A_243,'#skF_6','#skF_7')) != '#skF_8'
      | ~ r2_hidden(A_243,k9_relat_1('#skF_7','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1149])).

tff(c_1195,plain,(
    k1_funct_1('#skF_7','#skF_1'('#skF_8','#skF_6','#skF_7')) != '#skF_8' ),
    inference(resolution,[status(thm)],[c_191,c_1177])).

tff(c_58,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_302,plain,(
    ! [A_125,B_126,C_127] :
      ( r2_hidden(k4_tarski('#skF_1'(A_125,B_126,C_127),A_125),C_127)
      | ~ r2_hidden(A_125,k9_relat_1(C_127,B_126))
      | ~ v1_relat_1(C_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [C_17,A_15,B_16] :
      ( k1_funct_1(C_17,A_15) = B_16
      | ~ r2_hidden(k4_tarski(A_15,B_16),C_17)
      | ~ v1_funct_1(C_17)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1388,plain,(
    ! [C_276,A_277,B_278] :
      ( k1_funct_1(C_276,'#skF_1'(A_277,B_278,C_276)) = A_277
      | ~ v1_funct_1(C_276)
      | ~ r2_hidden(A_277,k9_relat_1(C_276,B_278))
      | ~ v1_relat_1(C_276) ) ),
    inference(resolution,[status(thm)],[c_302,c_22])).

tff(c_1398,plain,
    ( k1_funct_1('#skF_7','#skF_1'('#skF_8','#skF_6','#skF_7')) = '#skF_8'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_191,c_1388])).

tff(c_1407,plain,(
    k1_funct_1('#skF_7','#skF_1'('#skF_8','#skF_6','#skF_7')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_58,c_1398])).

tff(c_1409,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1195,c_1407])).

tff(c_1410,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1062])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,k1_zfmisc_1(B_3))
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_87,plain,(
    ! [A_59,B_60] :
      ( v1_relat_1(A_59)
      | ~ v1_relat_1(B_60)
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(resolution,[status(thm)],[c_6,c_76])).

tff(c_97,plain,(
    ! [A_1] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_87])).

tff(c_98,plain,(
    ! [A_1] : ~ v1_relat_1(A_1) ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_104,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_86])).

tff(c_105,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_354,plain,(
    ! [A_133,B_134,C_135] :
      ( r2_hidden('#skF_2'(A_133,B_134,C_135),B_134)
      | k1_relset_1(B_134,A_133,C_135) = B_134
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(B_134,A_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_359,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_4','#skF_7'),'#skF_4')
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_54,c_354])).

tff(c_362,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_4','#skF_7'),'#skF_4')
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_359])).

tff(c_364,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_362])).

tff(c_372,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_1'(A_9,B_10,'#skF_7'),'#skF_4')
      | ~ r2_hidden(A_9,k9_relat_1('#skF_7',B_10))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_18])).

tff(c_404,plain,(
    ! [A_138,B_139] :
      ( r2_hidden('#skF_1'(A_138,B_139,'#skF_7'),'#skF_4')
      | ~ r2_hidden(A_138,k9_relat_1('#skF_7',B_139)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_372])).

tff(c_408,plain,(
    ! [A_138] :
      ( k1_funct_1('#skF_7','#skF_1'(A_138,'#skF_6','#skF_7')) != '#skF_8'
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(A_138,k9_relat_1('#skF_7','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_404,c_156])).

tff(c_416,plain,(
    ! [A_140] :
      ( k1_funct_1('#skF_7','#skF_1'(A_140,'#skF_6','#skF_7')) != '#skF_8'
      | ~ r2_hidden(A_140,k9_relat_1('#skF_7','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_408])).

tff(c_434,plain,(
    k1_funct_1('#skF_7','#skF_1'('#skF_8','#skF_6','#skF_7')) != '#skF_8' ),
    inference(resolution,[status(thm)],[c_191,c_416])).

tff(c_676,plain,(
    ! [C_182,A_183,B_184] :
      ( k1_funct_1(C_182,'#skF_1'(A_183,B_184,C_182)) = A_183
      | ~ v1_funct_1(C_182)
      | ~ r2_hidden(A_183,k9_relat_1(C_182,B_184))
      | ~ v1_relat_1(C_182) ) ),
    inference(resolution,[status(thm)],[c_302,c_22])).

tff(c_687,plain,
    ( k1_funct_1('#skF_7','#skF_1'('#skF_8','#skF_6','#skF_7')) = '#skF_8'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_191,c_676])).

tff(c_696,plain,(
    k1_funct_1('#skF_7','#skF_1'('#skF_8','#skF_6','#skF_7')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_58,c_687])).

tff(c_698,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_434,c_696])).

tff(c_700,plain,(
    k1_relat_1('#skF_7') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_362])).

tff(c_705,plain,(
    ! [B_185,A_186,C_187] :
      ( k1_xboole_0 = B_185
      | k1_relset_1(A_186,B_185,C_187) = A_186
      | ~ v1_funct_2(C_187,A_186,B_185)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_186,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_712,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_705])).

tff(c_716,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_124,c_712])).

tff(c_717,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_700,c_716])).

tff(c_251,plain,(
    ! [A_118,C_119] :
      ( r2_hidden(k4_tarski(A_118,k1_funct_1(C_119,A_118)),C_119)
      | ~ r2_hidden(A_118,k1_relat_1(C_119))
      | ~ v1_funct_1(C_119)
      | ~ v1_relat_1(C_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_26,plain,(
    ! [B_19,A_18] :
      ( ~ r1_tarski(B_19,A_18)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_346,plain,(
    ! [C_131,A_132] :
      ( ~ r1_tarski(C_131,k4_tarski(A_132,k1_funct_1(C_131,A_132)))
      | ~ r2_hidden(A_132,k1_relat_1(C_131))
      | ~ v1_funct_1(C_131)
      | ~ v1_relat_1(C_131) ) ),
    inference(resolution,[status(thm)],[c_251,c_26])).

tff(c_350,plain,(
    ! [A_132] :
      ( ~ r2_hidden(A_132,k1_relat_1(k1_xboole_0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2,c_346])).

tff(c_353,plain,(
    ! [A_132] :
      ( ~ r2_hidden(A_132,k1_relat_1(k1_xboole_0))
      | ~ v1_funct_1(k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_350])).

tff(c_363,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_353])).

tff(c_719,plain,(
    ~ v1_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_717,c_363])).

tff(c_62,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(A_53,B_54)
      | ~ m1_subset_1(A_53,k1_zfmisc_1(B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_54,c_62])).

tff(c_201,plain,(
    ! [C_100,A_101] :
      ( k1_xboole_0 = C_100
      | ~ v1_funct_2(C_100,A_101,k1_xboole_0)
      | k1_xboole_0 = A_101
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_101,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_206,plain,(
    ! [A_2,A_101] :
      ( k1_xboole_0 = A_2
      | ~ v1_funct_2(A_2,A_101,k1_xboole_0)
      | k1_xboole_0 = A_101
      | ~ r1_tarski(A_2,k2_zfmisc_1(A_101,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_6,c_201])).

tff(c_855,plain,(
    ! [A_208,A_209] :
      ( A_208 = '#skF_5'
      | ~ v1_funct_2(A_208,A_209,'#skF_5')
      | A_209 = '#skF_5'
      | ~ r1_tarski(A_208,k2_zfmisc_1(A_209,'#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_717,c_717,c_717,c_717,c_206])).

tff(c_862,plain,
    ( '#skF_7' = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_66,c_855])).

tff(c_867,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_862])).

tff(c_874,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_867])).

tff(c_735,plain,(
    ! [A_1] : r1_tarski('#skF_5',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_717,c_2])).

tff(c_884,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_874,c_735])).

tff(c_699,plain,(
    r2_hidden('#skF_2'('#skF_5','#skF_4','#skF_7'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_362])).

tff(c_704,plain,(
    ~ r1_tarski('#skF_4','#skF_2'('#skF_5','#skF_4','#skF_7')) ),
    inference(resolution,[status(thm)],[c_699,c_26])).

tff(c_885,plain,(
    ~ r1_tarski('#skF_4','#skF_2'('#skF_4','#skF_4','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_874,c_704])).

tff(c_1003,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_884,c_885])).

tff(c_1004,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_867])).

tff(c_1019,plain,(
    v1_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_58])).

tff(c_1025,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_719,c_1019])).

tff(c_1028,plain,(
    ! [A_225] : ~ r2_hidden(A_225,k1_relat_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_353])).

tff(c_1040,plain,(
    ! [A_9,B_10] :
      ( ~ r2_hidden(A_9,k9_relat_1(k1_xboole_0,B_10))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_1028])).

tff(c_1049,plain,(
    ! [A_9,B_10] : ~ r2_hidden(A_9,k9_relat_1(k1_xboole_0,B_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_1040])).

tff(c_1512,plain,(
    ! [A_9,B_10] : ~ r2_hidden(A_9,k9_relat_1('#skF_5',B_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1410,c_1049])).

tff(c_1754,plain,(
    ! [A_323,A_324] :
      ( A_323 = '#skF_5'
      | ~ v1_funct_2(A_323,A_324,'#skF_5')
      | A_324 = '#skF_5'
      | ~ r1_tarski(A_323,k2_zfmisc_1(A_324,'#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1410,c_1410,c_1410,c_1410,c_206])).

tff(c_1761,plain,
    ( '#skF_7' = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_66,c_1754])).

tff(c_1766,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1761])).

tff(c_1767,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1766])).

tff(c_1430,plain,(
    ! [A_1] : r1_tarski('#skF_5',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1410,c_2])).

tff(c_1784,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1767,c_1430])).

tff(c_1411,plain,(
    k1_relat_1('#skF_7') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1062])).

tff(c_1474,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_362])).

tff(c_1475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1411,c_1474])).

tff(c_1476,plain,(
    r2_hidden('#skF_2'('#skF_5','#skF_4','#skF_7'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_362])).

tff(c_1780,plain,(
    r2_hidden('#skF_2'('#skF_4','#skF_4','#skF_7'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1767,c_1476])).

tff(c_1935,plain,(
    ~ r1_tarski('#skF_4','#skF_2'('#skF_4','#skF_4','#skF_7')) ),
    inference(resolution,[status(thm)],[c_1780,c_26])).

tff(c_1940,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1784,c_1935])).

tff(c_1941,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1766])).

tff(c_1956,plain,(
    r2_hidden('#skF_8',k9_relat_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1941,c_191])).

tff(c_1968,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1512,c_1956])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:38:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.19/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.19/1.81  
% 4.19/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.19/1.81  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4 > #skF_3
% 4.19/1.81  
% 4.19/1.81  %Foreground sorts:
% 4.19/1.81  
% 4.19/1.81  
% 4.19/1.81  %Background operators:
% 4.19/1.81  
% 4.19/1.81  
% 4.19/1.81  %Foreground operators:
% 4.19/1.81  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.19/1.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.19/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.19/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.19/1.81  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.19/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.19/1.81  tff('#skF_7', type, '#skF_7': $i).
% 4.19/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.19/1.81  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.19/1.81  tff('#skF_5', type, '#skF_5': $i).
% 4.19/1.81  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.19/1.81  tff('#skF_6', type, '#skF_6': $i).
% 4.19/1.81  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.19/1.81  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.19/1.81  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.19/1.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.19/1.81  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.19/1.81  tff('#skF_8', type, '#skF_8': $i).
% 4.19/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.19/1.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.19/1.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.19/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.19/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.19/1.81  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.19/1.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.19/1.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.19/1.81  
% 4.46/1.83  tff(f_123, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 4.46/1.83  tff(f_74, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.46/1.83  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.46/1.83  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.46/1.83  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.46/1.83  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.46/1.83  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 4.46/1.83  tff(f_61, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 4.46/1.83  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.46/1.83  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.46/1.83  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 4.46/1.83  tff(f_66, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.46/1.83  tff(c_54, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.46/1.83  tff(c_182, plain, (![A_95, B_96, C_97, D_98]: (k7_relset_1(A_95, B_96, C_97, D_98)=k9_relat_1(C_97, D_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.46/1.83  tff(c_189, plain, (![D_98]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_98)=k9_relat_1('#skF_7', D_98))), inference(resolution, [status(thm)], [c_54, c_182])).
% 4.46/1.83  tff(c_52, plain, (r2_hidden('#skF_8', k7_relset_1('#skF_4', '#skF_5', '#skF_7', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.46/1.83  tff(c_191, plain, (r2_hidden('#skF_8', k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_52])).
% 4.46/1.83  tff(c_10, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.46/1.83  tff(c_76, plain, (![B_57, A_58]: (v1_relat_1(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.46/1.83  tff(c_82, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_54, c_76])).
% 4.46/1.83  tff(c_86, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_82])).
% 4.46/1.83  tff(c_56, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.46/1.83  tff(c_115, plain, (![A_65, B_66, C_67]: (k1_relset_1(A_65, B_66, C_67)=k1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.46/1.83  tff(c_124, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_54, c_115])).
% 4.46/1.83  tff(c_1051, plain, (![B_226, A_227, C_228]: (k1_xboole_0=B_226 | k1_relset_1(A_227, B_226, C_228)=A_227 | ~v1_funct_2(C_228, A_227, B_226) | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(A_227, B_226))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.46/1.83  tff(c_1058, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_1051])).
% 4.46/1.83  tff(c_1062, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_124, c_1058])).
% 4.46/1.83  tff(c_1063, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_1062])).
% 4.46/1.83  tff(c_18, plain, (![A_9, B_10, C_11]: (r2_hidden('#skF_1'(A_9, B_10, C_11), k1_relat_1(C_11)) | ~r2_hidden(A_9, k9_relat_1(C_11, B_10)) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.46/1.83  tff(c_1071, plain, (![A_9, B_10]: (r2_hidden('#skF_1'(A_9, B_10, '#skF_7'), '#skF_4') | ~r2_hidden(A_9, k9_relat_1('#skF_7', B_10)) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1063, c_18])).
% 4.46/1.83  tff(c_1145, plain, (![A_239, B_240]: (r2_hidden('#skF_1'(A_239, B_240, '#skF_7'), '#skF_4') | ~r2_hidden(A_239, k9_relat_1('#skF_7', B_240)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1071])).
% 4.46/1.83  tff(c_148, plain, (![A_76, B_77, C_78]: (r2_hidden('#skF_1'(A_76, B_77, C_78), B_77) | ~r2_hidden(A_76, k9_relat_1(C_78, B_77)) | ~v1_relat_1(C_78))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.46/1.83  tff(c_50, plain, (![F_47]: (k1_funct_1('#skF_7', F_47)!='#skF_8' | ~r2_hidden(F_47, '#skF_6') | ~r2_hidden(F_47, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.46/1.83  tff(c_156, plain, (![A_76, C_78]: (k1_funct_1('#skF_7', '#skF_1'(A_76, '#skF_6', C_78))!='#skF_8' | ~r2_hidden('#skF_1'(A_76, '#skF_6', C_78), '#skF_4') | ~r2_hidden(A_76, k9_relat_1(C_78, '#skF_6')) | ~v1_relat_1(C_78))), inference(resolution, [status(thm)], [c_148, c_50])).
% 4.46/1.83  tff(c_1149, plain, (![A_239]: (k1_funct_1('#skF_7', '#skF_1'(A_239, '#skF_6', '#skF_7'))!='#skF_8' | ~v1_relat_1('#skF_7') | ~r2_hidden(A_239, k9_relat_1('#skF_7', '#skF_6')))), inference(resolution, [status(thm)], [c_1145, c_156])).
% 4.46/1.83  tff(c_1177, plain, (![A_243]: (k1_funct_1('#skF_7', '#skF_1'(A_243, '#skF_6', '#skF_7'))!='#skF_8' | ~r2_hidden(A_243, k9_relat_1('#skF_7', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1149])).
% 4.46/1.83  tff(c_1195, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_8', '#skF_6', '#skF_7'))!='#skF_8'), inference(resolution, [status(thm)], [c_191, c_1177])).
% 4.46/1.83  tff(c_58, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.46/1.83  tff(c_302, plain, (![A_125, B_126, C_127]: (r2_hidden(k4_tarski('#skF_1'(A_125, B_126, C_127), A_125), C_127) | ~r2_hidden(A_125, k9_relat_1(C_127, B_126)) | ~v1_relat_1(C_127))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.46/1.83  tff(c_22, plain, (![C_17, A_15, B_16]: (k1_funct_1(C_17, A_15)=B_16 | ~r2_hidden(k4_tarski(A_15, B_16), C_17) | ~v1_funct_1(C_17) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.46/1.83  tff(c_1388, plain, (![C_276, A_277, B_278]: (k1_funct_1(C_276, '#skF_1'(A_277, B_278, C_276))=A_277 | ~v1_funct_1(C_276) | ~r2_hidden(A_277, k9_relat_1(C_276, B_278)) | ~v1_relat_1(C_276))), inference(resolution, [status(thm)], [c_302, c_22])).
% 4.46/1.83  tff(c_1398, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_8', '#skF_6', '#skF_7'))='#skF_8' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_191, c_1388])).
% 4.46/1.83  tff(c_1407, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_8', '#skF_6', '#skF_7'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_58, c_1398])).
% 4.46/1.83  tff(c_1409, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1195, c_1407])).
% 4.46/1.83  tff(c_1410, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1062])).
% 4.46/1.83  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.46/1.83  tff(c_6, plain, (![A_2, B_3]: (m1_subset_1(A_2, k1_zfmisc_1(B_3)) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.46/1.83  tff(c_87, plain, (![A_59, B_60]: (v1_relat_1(A_59) | ~v1_relat_1(B_60) | ~r1_tarski(A_59, B_60))), inference(resolution, [status(thm)], [c_6, c_76])).
% 4.46/1.83  tff(c_97, plain, (![A_1]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_1))), inference(resolution, [status(thm)], [c_2, c_87])).
% 4.46/1.83  tff(c_98, plain, (![A_1]: (~v1_relat_1(A_1))), inference(splitLeft, [status(thm)], [c_97])).
% 4.46/1.83  tff(c_104, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_86])).
% 4.46/1.83  tff(c_105, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_97])).
% 4.46/1.83  tff(c_354, plain, (![A_133, B_134, C_135]: (r2_hidden('#skF_2'(A_133, B_134, C_135), B_134) | k1_relset_1(B_134, A_133, C_135)=B_134 | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(B_134, A_133))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.46/1.83  tff(c_359, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_4', '#skF_7'), '#skF_4') | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4'), inference(resolution, [status(thm)], [c_54, c_354])).
% 4.46/1.83  tff(c_362, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_4', '#skF_7'), '#skF_4') | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_359])).
% 4.46/1.83  tff(c_364, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_362])).
% 4.46/1.83  tff(c_372, plain, (![A_9, B_10]: (r2_hidden('#skF_1'(A_9, B_10, '#skF_7'), '#skF_4') | ~r2_hidden(A_9, k9_relat_1('#skF_7', B_10)) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_364, c_18])).
% 4.46/1.83  tff(c_404, plain, (![A_138, B_139]: (r2_hidden('#skF_1'(A_138, B_139, '#skF_7'), '#skF_4') | ~r2_hidden(A_138, k9_relat_1('#skF_7', B_139)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_372])).
% 4.46/1.83  tff(c_408, plain, (![A_138]: (k1_funct_1('#skF_7', '#skF_1'(A_138, '#skF_6', '#skF_7'))!='#skF_8' | ~v1_relat_1('#skF_7') | ~r2_hidden(A_138, k9_relat_1('#skF_7', '#skF_6')))), inference(resolution, [status(thm)], [c_404, c_156])).
% 4.46/1.83  tff(c_416, plain, (![A_140]: (k1_funct_1('#skF_7', '#skF_1'(A_140, '#skF_6', '#skF_7'))!='#skF_8' | ~r2_hidden(A_140, k9_relat_1('#skF_7', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_408])).
% 4.46/1.83  tff(c_434, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_8', '#skF_6', '#skF_7'))!='#skF_8'), inference(resolution, [status(thm)], [c_191, c_416])).
% 4.46/1.83  tff(c_676, plain, (![C_182, A_183, B_184]: (k1_funct_1(C_182, '#skF_1'(A_183, B_184, C_182))=A_183 | ~v1_funct_1(C_182) | ~r2_hidden(A_183, k9_relat_1(C_182, B_184)) | ~v1_relat_1(C_182))), inference(resolution, [status(thm)], [c_302, c_22])).
% 4.46/1.83  tff(c_687, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_8', '#skF_6', '#skF_7'))='#skF_8' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_191, c_676])).
% 4.46/1.83  tff(c_696, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_8', '#skF_6', '#skF_7'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_58, c_687])).
% 4.46/1.83  tff(c_698, plain, $false, inference(negUnitSimplification, [status(thm)], [c_434, c_696])).
% 4.46/1.83  tff(c_700, plain, (k1_relat_1('#skF_7')!='#skF_4'), inference(splitRight, [status(thm)], [c_362])).
% 4.46/1.83  tff(c_705, plain, (![B_185, A_186, C_187]: (k1_xboole_0=B_185 | k1_relset_1(A_186, B_185, C_187)=A_186 | ~v1_funct_2(C_187, A_186, B_185) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_186, B_185))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.46/1.83  tff(c_712, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_705])).
% 4.46/1.83  tff(c_716, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_124, c_712])).
% 4.46/1.83  tff(c_717, plain, (k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_700, c_716])).
% 4.46/1.83  tff(c_251, plain, (![A_118, C_119]: (r2_hidden(k4_tarski(A_118, k1_funct_1(C_119, A_118)), C_119) | ~r2_hidden(A_118, k1_relat_1(C_119)) | ~v1_funct_1(C_119) | ~v1_relat_1(C_119))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.46/1.83  tff(c_26, plain, (![B_19, A_18]: (~r1_tarski(B_19, A_18) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.46/1.83  tff(c_346, plain, (![C_131, A_132]: (~r1_tarski(C_131, k4_tarski(A_132, k1_funct_1(C_131, A_132))) | ~r2_hidden(A_132, k1_relat_1(C_131)) | ~v1_funct_1(C_131) | ~v1_relat_1(C_131))), inference(resolution, [status(thm)], [c_251, c_26])).
% 4.46/1.83  tff(c_350, plain, (![A_132]: (~r2_hidden(A_132, k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_346])).
% 4.46/1.83  tff(c_353, plain, (![A_132]: (~r2_hidden(A_132, k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_350])).
% 4.46/1.83  tff(c_363, plain, (~v1_funct_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_353])).
% 4.46/1.83  tff(c_719, plain, (~v1_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_717, c_363])).
% 4.46/1.83  tff(c_62, plain, (![A_53, B_54]: (r1_tarski(A_53, B_54) | ~m1_subset_1(A_53, k1_zfmisc_1(B_54)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.46/1.83  tff(c_66, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_54, c_62])).
% 4.46/1.83  tff(c_201, plain, (![C_100, A_101]: (k1_xboole_0=C_100 | ~v1_funct_2(C_100, A_101, k1_xboole_0) | k1_xboole_0=A_101 | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_101, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.46/1.83  tff(c_206, plain, (![A_2, A_101]: (k1_xboole_0=A_2 | ~v1_funct_2(A_2, A_101, k1_xboole_0) | k1_xboole_0=A_101 | ~r1_tarski(A_2, k2_zfmisc_1(A_101, k1_xboole_0)))), inference(resolution, [status(thm)], [c_6, c_201])).
% 4.46/1.83  tff(c_855, plain, (![A_208, A_209]: (A_208='#skF_5' | ~v1_funct_2(A_208, A_209, '#skF_5') | A_209='#skF_5' | ~r1_tarski(A_208, k2_zfmisc_1(A_209, '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_717, c_717, c_717, c_717, c_206])).
% 4.46/1.83  tff(c_862, plain, ('#skF_7'='#skF_5' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_66, c_855])).
% 4.46/1.83  tff(c_867, plain, ('#skF_7'='#skF_5' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_862])).
% 4.46/1.83  tff(c_874, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_867])).
% 4.46/1.83  tff(c_735, plain, (![A_1]: (r1_tarski('#skF_5', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_717, c_2])).
% 4.46/1.83  tff(c_884, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_874, c_735])).
% 4.46/1.83  tff(c_699, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_4', '#skF_7'), '#skF_4')), inference(splitRight, [status(thm)], [c_362])).
% 4.46/1.83  tff(c_704, plain, (~r1_tarski('#skF_4', '#skF_2'('#skF_5', '#skF_4', '#skF_7'))), inference(resolution, [status(thm)], [c_699, c_26])).
% 4.46/1.83  tff(c_885, plain, (~r1_tarski('#skF_4', '#skF_2'('#skF_4', '#skF_4', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_874, c_704])).
% 4.46/1.83  tff(c_1003, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_884, c_885])).
% 4.46/1.83  tff(c_1004, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_867])).
% 4.46/1.83  tff(c_1019, plain, (v1_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_58])).
% 4.46/1.83  tff(c_1025, plain, $false, inference(negUnitSimplification, [status(thm)], [c_719, c_1019])).
% 4.46/1.83  tff(c_1028, plain, (![A_225]: (~r2_hidden(A_225, k1_relat_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_353])).
% 4.46/1.83  tff(c_1040, plain, (![A_9, B_10]: (~r2_hidden(A_9, k9_relat_1(k1_xboole_0, B_10)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_1028])).
% 4.46/1.83  tff(c_1049, plain, (![A_9, B_10]: (~r2_hidden(A_9, k9_relat_1(k1_xboole_0, B_10)))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_1040])).
% 4.46/1.83  tff(c_1512, plain, (![A_9, B_10]: (~r2_hidden(A_9, k9_relat_1('#skF_5', B_10)))), inference(demodulation, [status(thm), theory('equality')], [c_1410, c_1049])).
% 4.46/1.83  tff(c_1754, plain, (![A_323, A_324]: (A_323='#skF_5' | ~v1_funct_2(A_323, A_324, '#skF_5') | A_324='#skF_5' | ~r1_tarski(A_323, k2_zfmisc_1(A_324, '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_1410, c_1410, c_1410, c_1410, c_206])).
% 4.46/1.83  tff(c_1761, plain, ('#skF_7'='#skF_5' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_66, c_1754])).
% 4.46/1.83  tff(c_1766, plain, ('#skF_7'='#skF_5' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1761])).
% 4.46/1.83  tff(c_1767, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_1766])).
% 4.46/1.83  tff(c_1430, plain, (![A_1]: (r1_tarski('#skF_5', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1410, c_2])).
% 4.46/1.83  tff(c_1784, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1767, c_1430])).
% 4.46/1.83  tff(c_1411, plain, (k1_relat_1('#skF_7')!='#skF_4'), inference(splitRight, [status(thm)], [c_1062])).
% 4.46/1.83  tff(c_1474, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_362])).
% 4.46/1.83  tff(c_1475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1411, c_1474])).
% 4.46/1.83  tff(c_1476, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_4', '#skF_7'), '#skF_4')), inference(splitRight, [status(thm)], [c_362])).
% 4.46/1.83  tff(c_1780, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_4', '#skF_7'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1767, c_1476])).
% 4.46/1.83  tff(c_1935, plain, (~r1_tarski('#skF_4', '#skF_2'('#skF_4', '#skF_4', '#skF_7'))), inference(resolution, [status(thm)], [c_1780, c_26])).
% 4.46/1.83  tff(c_1940, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1784, c_1935])).
% 4.46/1.83  tff(c_1941, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_1766])).
% 4.46/1.83  tff(c_1956, plain, (r2_hidden('#skF_8', k9_relat_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1941, c_191])).
% 4.46/1.83  tff(c_1968, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1512, c_1956])).
% 4.46/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.46/1.83  
% 4.46/1.83  Inference rules
% 4.46/1.83  ----------------------
% 4.46/1.83  #Ref     : 0
% 4.46/1.83  #Sup     : 354
% 4.46/1.83  #Fact    : 0
% 4.46/1.83  #Define  : 0
% 4.46/1.83  #Split   : 12
% 4.46/1.83  #Chain   : 0
% 4.46/1.83  #Close   : 0
% 4.46/1.83  
% 4.46/1.83  Ordering : KBO
% 4.46/1.83  
% 4.46/1.83  Simplification rules
% 4.46/1.83  ----------------------
% 4.46/1.83  #Subsume      : 38
% 4.46/1.83  #Demod        : 285
% 4.46/1.83  #Tautology    : 78
% 4.46/1.83  #SimpNegUnit  : 12
% 4.46/1.83  #BackRed      : 119
% 4.46/1.83  
% 4.46/1.83  #Partial instantiations: 0
% 4.46/1.83  #Strategies tried      : 1
% 4.46/1.83  
% 4.46/1.83  Timing (in seconds)
% 4.46/1.83  ----------------------
% 4.46/1.83  Preprocessing        : 0.39
% 4.46/1.83  Parsing              : 0.19
% 4.46/1.83  CNF conversion       : 0.03
% 4.46/1.83  Main loop            : 0.60
% 4.46/1.83  Inferencing          : 0.21
% 4.46/1.83  Reduction            : 0.17
% 4.46/1.83  Demodulation         : 0.12
% 4.46/1.83  BG Simplification    : 0.03
% 4.46/1.83  Subsumption          : 0.12
% 4.46/1.83  Abstraction          : 0.03
% 4.46/1.83  MUC search           : 0.00
% 4.46/1.84  Cooper               : 0.00
% 4.46/1.84  Total                : 1.03
% 4.46/1.84  Index Insertion      : 0.00
% 4.46/1.84  Index Deletion       : 0.00
% 4.46/1.84  Index Matching       : 0.00
% 4.46/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
