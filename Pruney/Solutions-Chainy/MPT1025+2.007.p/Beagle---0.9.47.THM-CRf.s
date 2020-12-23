%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:31 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 4.02s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 359 expanded)
%              Number of leaves         :   44 ( 144 expanded)
%              Depth                    :   11
%              Number of atoms          :  180 ( 991 expanded)
%              Number of equality atoms :   42 ( 197 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_146,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_109,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_127,axiom,(
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

tff(f_86,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_76,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_78,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_136,plain,(
    ! [C_94,A_95,B_96] :
      ( v1_relat_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_144,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_78,c_136])).

tff(c_251,plain,(
    ! [A_150,B_151,C_152,D_153] :
      ( k7_relset_1(A_150,B_151,C_152,D_153) = k9_relat_1(C_152,D_153)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_258,plain,(
    ! [D_153] : k7_relset_1('#skF_6','#skF_7','#skF_9',D_153) = k9_relat_1('#skF_9',D_153) ),
    inference(resolution,[status(thm)],[c_78,c_251])).

tff(c_76,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_261,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_76])).

tff(c_24,plain,(
    ! [A_12,B_13,C_14] :
      ( r2_hidden('#skF_1'(A_12,B_13,C_14),k1_relat_1(C_14))
      | ~ r2_hidden(A_12,k9_relat_1(C_14,B_13))
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_208,plain,(
    ! [A_134,B_135,C_136] :
      ( r2_hidden('#skF_1'(A_134,B_135,C_136),B_135)
      | ~ r2_hidden(A_134,k9_relat_1(C_136,B_135))
      | ~ v1_relat_1(C_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_74,plain,(
    ! [F_83] :
      ( k1_funct_1('#skF_9',F_83) != '#skF_10'
      | ~ r2_hidden(F_83,'#skF_8')
      | ~ m1_subset_1(F_83,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_323,plain,(
    ! [A_176,C_177] :
      ( k1_funct_1('#skF_9','#skF_1'(A_176,'#skF_8',C_177)) != '#skF_10'
      | ~ m1_subset_1('#skF_1'(A_176,'#skF_8',C_177),'#skF_6')
      | ~ r2_hidden(A_176,k9_relat_1(C_177,'#skF_8'))
      | ~ v1_relat_1(C_177) ) ),
    inference(resolution,[status(thm)],[c_208,c_74])).

tff(c_330,plain,
    ( k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_8','#skF_9')) != '#skF_10'
    | ~ m1_subset_1('#skF_1'('#skF_10','#skF_8','#skF_9'),'#skF_6')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_261,c_323])).

tff(c_338,plain,
    ( k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_8','#skF_9')) != '#skF_10'
    | ~ m1_subset_1('#skF_1'('#skF_10','#skF_8','#skF_9'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_330])).

tff(c_340,plain,(
    ~ m1_subset_1('#skF_1'('#skF_10','#skF_8','#skF_9'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_338])).

tff(c_80,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_186,plain,(
    ! [A_117,B_118,C_119] :
      ( k1_relset_1(A_117,B_118,C_119) = k1_relat_1(C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_196,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_78,c_186])).

tff(c_699,plain,(
    ! [B_209,A_210,C_211] :
      ( k1_xboole_0 = B_209
      | k1_relset_1(A_210,B_209,C_211) = A_210
      | ~ v1_funct_2(C_211,A_210,B_209)
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(A_210,B_209))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_710,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_78,c_699])).

tff(c_721,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_196,c_710])).

tff(c_723,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_721])).

tff(c_82,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_289,plain,(
    ! [A_167,B_168,C_169] :
      ( r2_hidden(k4_tarski('#skF_1'(A_167,B_168,C_169),A_167),C_169)
      | ~ r2_hidden(A_167,k9_relat_1(C_169,B_168))
      | ~ v1_relat_1(C_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_46,plain,(
    ! [C_60,A_58,B_59] :
      ( k1_funct_1(C_60,A_58) = B_59
      | ~ r2_hidden(k4_tarski(A_58,B_59),C_60)
      | ~ v1_funct_1(C_60)
      | ~ v1_relat_1(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_551,plain,(
    ! [C_194,A_195,B_196] :
      ( k1_funct_1(C_194,'#skF_1'(A_195,B_196,C_194)) = A_195
      | ~ v1_funct_1(C_194)
      | ~ r2_hidden(A_195,k9_relat_1(C_194,B_196))
      | ~ v1_relat_1(C_194) ) ),
    inference(resolution,[status(thm)],[c_289,c_46])).

tff(c_559,plain,
    ( k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_8','#skF_9')) = '#skF_10'
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_261,c_551])).

tff(c_567,plain,(
    k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_8','#skF_9')) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_82,c_559])).

tff(c_233,plain,(
    ! [A_145,D_146] :
      ( r2_hidden(k1_funct_1(A_145,D_146),k2_relat_1(A_145))
      | ~ r2_hidden(D_146,k1_relat_1(A_145))
      | ~ v1_funct_1(A_145)
      | ~ v1_relat_1(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,B_4)
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_241,plain,(
    ! [A_145,D_146] :
      ( m1_subset_1(k1_funct_1(A_145,D_146),k2_relat_1(A_145))
      | ~ r2_hidden(D_146,k1_relat_1(A_145))
      | ~ v1_funct_1(A_145)
      | ~ v1_relat_1(A_145) ) ),
    inference(resolution,[status(thm)],[c_233,c_8])).

tff(c_581,plain,
    ( m1_subset_1('#skF_10',k2_relat_1('#skF_9'))
    | ~ r2_hidden('#skF_1'('#skF_10','#skF_8','#skF_9'),k1_relat_1('#skF_9'))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_567,c_241])).

tff(c_600,plain,
    ( m1_subset_1('#skF_10',k2_relat_1('#skF_9'))
    | ~ r2_hidden('#skF_1'('#skF_10','#skF_8','#skF_9'),k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_82,c_581])).

tff(c_610,plain,(
    ~ r2_hidden('#skF_1'('#skF_10','#skF_8','#skF_9'),k1_relat_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_600])).

tff(c_613,plain,
    ( ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_24,c_610])).

tff(c_617,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_261,c_613])).

tff(c_619,plain,(
    r2_hidden('#skF_1'('#skF_10','#skF_8','#skF_9'),k1_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_600])).

tff(c_627,plain,(
    m1_subset_1('#skF_1'('#skF_10','#skF_8','#skF_9'),k1_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_619,c_8])).

tff(c_724,plain,(
    m1_subset_1('#skF_1'('#skF_10','#skF_8','#skF_9'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_723,c_627])).

tff(c_729,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_340,c_724])).

tff(c_730,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_721])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_746,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_730,c_730,c_4])).

tff(c_777,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_746,c_78])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_173,plain,(
    ! [C_111,B_112,A_113] :
      ( v5_relat_1(C_111,B_112)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_113,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_182,plain,(
    ! [C_111,B_2] :
      ( v5_relat_1(C_111,B_2)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_173])).

tff(c_878,plain,(
    ! [C_225,B_226] :
      ( v5_relat_1(C_225,B_226)
      | ~ m1_subset_1(C_225,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_730,c_182])).

tff(c_887,plain,(
    ! [B_226] : v5_relat_1('#skF_9',B_226) ),
    inference(resolution,[status(thm)],[c_777,c_878])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v5_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_50,plain,(
    ! [B_62,A_61] :
      ( ~ r1_tarski(B_62,A_61)
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_315,plain,(
    ! [A_170,D_171] :
      ( ~ r1_tarski(k2_relat_1(A_170),k1_funct_1(A_170,D_171))
      | ~ r2_hidden(D_171,k1_relat_1(A_170))
      | ~ v1_funct_1(A_170)
      | ~ v1_relat_1(A_170) ) ),
    inference(resolution,[status(thm)],[c_233,c_50])).

tff(c_320,plain,(
    ! [D_171,B_9] :
      ( ~ r2_hidden(D_171,k1_relat_1(B_9))
      | ~ v1_funct_1(B_9)
      | ~ v5_relat_1(B_9,k1_funct_1(B_9,D_171))
      | ~ v1_relat_1(B_9) ) ),
    inference(resolution,[status(thm)],[c_14,c_315])).

tff(c_584,plain,
    ( ~ r2_hidden('#skF_1'('#skF_10','#skF_8','#skF_9'),k1_relat_1('#skF_9'))
    | ~ v1_funct_1('#skF_9')
    | ~ v5_relat_1('#skF_9','#skF_10')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_567,c_320])).

tff(c_602,plain,
    ( ~ r2_hidden('#skF_1'('#skF_10','#skF_8','#skF_9'),k1_relat_1('#skF_9'))
    | ~ v5_relat_1('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_82,c_584])).

tff(c_608,plain,(
    ~ v5_relat_1('#skF_9','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_602])).

tff(c_893,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_887,c_608])).

tff(c_894,plain,(
    ~ r2_hidden('#skF_1'('#skF_10','#skF_8','#skF_9'),k1_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_602])).

tff(c_899,plain,
    ( ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_24,c_894])).

tff(c_903,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_261,c_899])).

tff(c_904,plain,(
    k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_8','#skF_9')) != '#skF_10' ),
    inference(splitRight,[status(thm)],[c_338])).

tff(c_1117,plain,(
    ! [C_248,A_249,B_250] :
      ( k1_funct_1(C_248,'#skF_1'(A_249,B_250,C_248)) = A_249
      | ~ v1_funct_1(C_248)
      | ~ r2_hidden(A_249,k9_relat_1(C_248,B_250))
      | ~ v1_relat_1(C_248) ) ),
    inference(resolution,[status(thm)],[c_289,c_46])).

tff(c_1125,plain,
    ( k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_8','#skF_9')) = '#skF_10'
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_261,c_1117])).

tff(c_1133,plain,(
    k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_8','#skF_9')) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_82,c_1125])).

tff(c_1135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_904,c_1133])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n007.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:46:21 EST 2020
% 0.18/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.68/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.68/1.63  
% 3.68/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.68/1.64  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4
% 3.68/1.64  
% 3.68/1.64  %Foreground sorts:
% 3.68/1.64  
% 3.68/1.64  
% 3.68/1.64  %Background operators:
% 3.68/1.64  
% 3.68/1.64  
% 3.68/1.64  %Foreground operators:
% 3.68/1.64  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.68/1.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.68/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.68/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.68/1.64  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.68/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.68/1.64  tff('#skF_7', type, '#skF_7': $i).
% 3.68/1.64  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.68/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.68/1.64  tff('#skF_10', type, '#skF_10': $i).
% 3.68/1.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.68/1.64  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.68/1.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.68/1.64  tff('#skF_6', type, '#skF_6': $i).
% 3.68/1.64  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.68/1.64  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.68/1.64  tff('#skF_9', type, '#skF_9': $i).
% 3.68/1.64  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.68/1.64  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.68/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.68/1.64  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.68/1.64  tff('#skF_8', type, '#skF_8': $i).
% 3.68/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.68/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.68/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.68/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.68/1.64  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.68/1.64  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.68/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.68/1.64  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.68/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.68/1.64  
% 4.02/1.67  tff(f_146, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 4.02/1.67  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.02/1.67  tff(f_109, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.02/1.67  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 4.02/1.67  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.02/1.67  tff(f_127, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.02/1.67  tff(f_86, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 4.02/1.67  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 4.02/1.67  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 4.02/1.67  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.02/1.67  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.02/1.67  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 4.02/1.67  tff(f_91, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.02/1.67  tff(c_78, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.02/1.67  tff(c_136, plain, (![C_94, A_95, B_96]: (v1_relat_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.02/1.67  tff(c_144, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_78, c_136])).
% 4.02/1.67  tff(c_251, plain, (![A_150, B_151, C_152, D_153]: (k7_relset_1(A_150, B_151, C_152, D_153)=k9_relat_1(C_152, D_153) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.02/1.67  tff(c_258, plain, (![D_153]: (k7_relset_1('#skF_6', '#skF_7', '#skF_9', D_153)=k9_relat_1('#skF_9', D_153))), inference(resolution, [status(thm)], [c_78, c_251])).
% 4.02/1.67  tff(c_76, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.02/1.67  tff(c_261, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_258, c_76])).
% 4.02/1.67  tff(c_24, plain, (![A_12, B_13, C_14]: (r2_hidden('#skF_1'(A_12, B_13, C_14), k1_relat_1(C_14)) | ~r2_hidden(A_12, k9_relat_1(C_14, B_13)) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.02/1.67  tff(c_208, plain, (![A_134, B_135, C_136]: (r2_hidden('#skF_1'(A_134, B_135, C_136), B_135) | ~r2_hidden(A_134, k9_relat_1(C_136, B_135)) | ~v1_relat_1(C_136))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.02/1.67  tff(c_74, plain, (![F_83]: (k1_funct_1('#skF_9', F_83)!='#skF_10' | ~r2_hidden(F_83, '#skF_8') | ~m1_subset_1(F_83, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.02/1.67  tff(c_323, plain, (![A_176, C_177]: (k1_funct_1('#skF_9', '#skF_1'(A_176, '#skF_8', C_177))!='#skF_10' | ~m1_subset_1('#skF_1'(A_176, '#skF_8', C_177), '#skF_6') | ~r2_hidden(A_176, k9_relat_1(C_177, '#skF_8')) | ~v1_relat_1(C_177))), inference(resolution, [status(thm)], [c_208, c_74])).
% 4.02/1.67  tff(c_330, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_8', '#skF_9'))!='#skF_10' | ~m1_subset_1('#skF_1'('#skF_10', '#skF_8', '#skF_9'), '#skF_6') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_261, c_323])).
% 4.02/1.67  tff(c_338, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_8', '#skF_9'))!='#skF_10' | ~m1_subset_1('#skF_1'('#skF_10', '#skF_8', '#skF_9'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_330])).
% 4.02/1.67  tff(c_340, plain, (~m1_subset_1('#skF_1'('#skF_10', '#skF_8', '#skF_9'), '#skF_6')), inference(splitLeft, [status(thm)], [c_338])).
% 4.02/1.67  tff(c_80, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.02/1.67  tff(c_186, plain, (![A_117, B_118, C_119]: (k1_relset_1(A_117, B_118, C_119)=k1_relat_1(C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.02/1.67  tff(c_196, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_78, c_186])).
% 4.02/1.67  tff(c_699, plain, (![B_209, A_210, C_211]: (k1_xboole_0=B_209 | k1_relset_1(A_210, B_209, C_211)=A_210 | ~v1_funct_2(C_211, A_210, B_209) | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(A_210, B_209))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.02/1.67  tff(c_710, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_78, c_699])).
% 4.02/1.67  tff(c_721, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_196, c_710])).
% 4.02/1.67  tff(c_723, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_721])).
% 4.02/1.67  tff(c_82, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.02/1.67  tff(c_289, plain, (![A_167, B_168, C_169]: (r2_hidden(k4_tarski('#skF_1'(A_167, B_168, C_169), A_167), C_169) | ~r2_hidden(A_167, k9_relat_1(C_169, B_168)) | ~v1_relat_1(C_169))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.02/1.67  tff(c_46, plain, (![C_60, A_58, B_59]: (k1_funct_1(C_60, A_58)=B_59 | ~r2_hidden(k4_tarski(A_58, B_59), C_60) | ~v1_funct_1(C_60) | ~v1_relat_1(C_60))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.02/1.67  tff(c_551, plain, (![C_194, A_195, B_196]: (k1_funct_1(C_194, '#skF_1'(A_195, B_196, C_194))=A_195 | ~v1_funct_1(C_194) | ~r2_hidden(A_195, k9_relat_1(C_194, B_196)) | ~v1_relat_1(C_194))), inference(resolution, [status(thm)], [c_289, c_46])).
% 4.02/1.67  tff(c_559, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_8', '#skF_9'))='#skF_10' | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_261, c_551])).
% 4.02/1.67  tff(c_567, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_8', '#skF_9'))='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_144, c_82, c_559])).
% 4.02/1.67  tff(c_233, plain, (![A_145, D_146]: (r2_hidden(k1_funct_1(A_145, D_146), k2_relat_1(A_145)) | ~r2_hidden(D_146, k1_relat_1(A_145)) | ~v1_funct_1(A_145) | ~v1_relat_1(A_145))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.02/1.67  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(A_3, B_4) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.02/1.67  tff(c_241, plain, (![A_145, D_146]: (m1_subset_1(k1_funct_1(A_145, D_146), k2_relat_1(A_145)) | ~r2_hidden(D_146, k1_relat_1(A_145)) | ~v1_funct_1(A_145) | ~v1_relat_1(A_145))), inference(resolution, [status(thm)], [c_233, c_8])).
% 4.02/1.67  tff(c_581, plain, (m1_subset_1('#skF_10', k2_relat_1('#skF_9')) | ~r2_hidden('#skF_1'('#skF_10', '#skF_8', '#skF_9'), k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_567, c_241])).
% 4.02/1.67  tff(c_600, plain, (m1_subset_1('#skF_10', k2_relat_1('#skF_9')) | ~r2_hidden('#skF_1'('#skF_10', '#skF_8', '#skF_9'), k1_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_82, c_581])).
% 4.02/1.67  tff(c_610, plain, (~r2_hidden('#skF_1'('#skF_10', '#skF_8', '#skF_9'), k1_relat_1('#skF_9'))), inference(splitLeft, [status(thm)], [c_600])).
% 4.02/1.67  tff(c_613, plain, (~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_24, c_610])).
% 4.02/1.67  tff(c_617, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_144, c_261, c_613])).
% 4.02/1.67  tff(c_619, plain, (r2_hidden('#skF_1'('#skF_10', '#skF_8', '#skF_9'), k1_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_600])).
% 4.02/1.67  tff(c_627, plain, (m1_subset_1('#skF_1'('#skF_10', '#skF_8', '#skF_9'), k1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_619, c_8])).
% 4.02/1.67  tff(c_724, plain, (m1_subset_1('#skF_1'('#skF_10', '#skF_8', '#skF_9'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_723, c_627])).
% 4.02/1.67  tff(c_729, plain, $false, inference(negUnitSimplification, [status(thm)], [c_340, c_724])).
% 4.02/1.67  tff(c_730, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_721])).
% 4.02/1.67  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.02/1.67  tff(c_746, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_730, c_730, c_4])).
% 4.02/1.67  tff(c_777, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_746, c_78])).
% 4.02/1.67  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.02/1.67  tff(c_173, plain, (![C_111, B_112, A_113]: (v5_relat_1(C_111, B_112) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_113, B_112))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.02/1.67  tff(c_182, plain, (![C_111, B_2]: (v5_relat_1(C_111, B_2) | ~m1_subset_1(C_111, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_173])).
% 4.02/1.67  tff(c_878, plain, (![C_225, B_226]: (v5_relat_1(C_225, B_226) | ~m1_subset_1(C_225, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_730, c_182])).
% 4.02/1.67  tff(c_887, plain, (![B_226]: (v5_relat_1('#skF_9', B_226))), inference(resolution, [status(thm)], [c_777, c_878])).
% 4.02/1.67  tff(c_14, plain, (![B_9, A_8]: (r1_tarski(k2_relat_1(B_9), A_8) | ~v5_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.02/1.67  tff(c_50, plain, (![B_62, A_61]: (~r1_tarski(B_62, A_61) | ~r2_hidden(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.02/1.67  tff(c_315, plain, (![A_170, D_171]: (~r1_tarski(k2_relat_1(A_170), k1_funct_1(A_170, D_171)) | ~r2_hidden(D_171, k1_relat_1(A_170)) | ~v1_funct_1(A_170) | ~v1_relat_1(A_170))), inference(resolution, [status(thm)], [c_233, c_50])).
% 4.02/1.67  tff(c_320, plain, (![D_171, B_9]: (~r2_hidden(D_171, k1_relat_1(B_9)) | ~v1_funct_1(B_9) | ~v5_relat_1(B_9, k1_funct_1(B_9, D_171)) | ~v1_relat_1(B_9))), inference(resolution, [status(thm)], [c_14, c_315])).
% 4.02/1.67  tff(c_584, plain, (~r2_hidden('#skF_1'('#skF_10', '#skF_8', '#skF_9'), k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v5_relat_1('#skF_9', '#skF_10') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_567, c_320])).
% 4.02/1.67  tff(c_602, plain, (~r2_hidden('#skF_1'('#skF_10', '#skF_8', '#skF_9'), k1_relat_1('#skF_9')) | ~v5_relat_1('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_82, c_584])).
% 4.02/1.67  tff(c_608, plain, (~v5_relat_1('#skF_9', '#skF_10')), inference(splitLeft, [status(thm)], [c_602])).
% 4.02/1.67  tff(c_893, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_887, c_608])).
% 4.02/1.67  tff(c_894, plain, (~r2_hidden('#skF_1'('#skF_10', '#skF_8', '#skF_9'), k1_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_602])).
% 4.02/1.67  tff(c_899, plain, (~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_24, c_894])).
% 4.02/1.67  tff(c_903, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_144, c_261, c_899])).
% 4.02/1.67  tff(c_904, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_8', '#skF_9'))!='#skF_10'), inference(splitRight, [status(thm)], [c_338])).
% 4.02/1.67  tff(c_1117, plain, (![C_248, A_249, B_250]: (k1_funct_1(C_248, '#skF_1'(A_249, B_250, C_248))=A_249 | ~v1_funct_1(C_248) | ~r2_hidden(A_249, k9_relat_1(C_248, B_250)) | ~v1_relat_1(C_248))), inference(resolution, [status(thm)], [c_289, c_46])).
% 4.02/1.67  tff(c_1125, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_8', '#skF_9'))='#skF_10' | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_261, c_1117])).
% 4.02/1.67  tff(c_1133, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_8', '#skF_9'))='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_144, c_82, c_1125])).
% 4.02/1.67  tff(c_1135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_904, c_1133])).
% 4.02/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.02/1.67  
% 4.02/1.67  Inference rules
% 4.02/1.67  ----------------------
% 4.02/1.67  #Ref     : 0
% 4.02/1.67  #Sup     : 226
% 4.02/1.67  #Fact    : 0
% 4.02/1.67  #Define  : 0
% 4.02/1.67  #Split   : 7
% 4.02/1.67  #Chain   : 0
% 4.02/1.67  #Close   : 0
% 4.02/1.67  
% 4.02/1.67  Ordering : KBO
% 4.02/1.67  
% 4.02/1.67  Simplification rules
% 4.02/1.67  ----------------------
% 4.02/1.67  #Subsume      : 18
% 4.02/1.67  #Demod        : 101
% 4.02/1.67  #Tautology    : 49
% 4.02/1.67  #SimpNegUnit  : 2
% 4.02/1.67  #BackRed      : 26
% 4.02/1.67  
% 4.02/1.67  #Partial instantiations: 0
% 4.02/1.67  #Strategies tried      : 1
% 4.02/1.67  
% 4.02/1.67  Timing (in seconds)
% 4.02/1.67  ----------------------
% 4.02/1.67  Preprocessing        : 0.37
% 4.02/1.67  Parsing              : 0.19
% 4.02/1.67  CNF conversion       : 0.03
% 4.02/1.67  Main loop            : 0.51
% 4.02/1.67  Inferencing          : 0.18
% 4.02/1.67  Reduction            : 0.15
% 4.02/1.67  Demodulation         : 0.11
% 4.02/1.67  BG Simplification    : 0.03
% 4.02/1.67  Subsumption          : 0.09
% 4.02/1.67  Abstraction          : 0.03
% 4.02/1.67  MUC search           : 0.00
% 4.02/1.67  Cooper               : 0.00
% 4.02/1.67  Total                : 0.94
% 4.02/1.67  Index Insertion      : 0.00
% 4.02/1.68  Index Deletion       : 0.00
% 4.02/1.68  Index Matching       : 0.00
% 4.02/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
