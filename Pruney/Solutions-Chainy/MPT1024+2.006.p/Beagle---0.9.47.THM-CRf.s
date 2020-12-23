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
% DateTime   : Thu Dec  3 10:16:22 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 333 expanded)
%              Number of leaves         :   43 ( 136 expanded)
%              Depth                    :   13
%              Number of atoms          :  160 ( 917 expanded)
%              Number of equality atoms :   36 ( 183 expanded)
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

tff(f_142,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_105,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_123,axiom,(
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

tff(f_72,axiom,(
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

tff(f_87,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(c_76,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_119,plain,(
    ! [C_89,A_90,B_91] :
      ( v1_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_127,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_76,c_119])).

tff(c_217,plain,(
    ! [A_139,B_140,C_141,D_142] :
      ( k7_relset_1(A_139,B_140,C_141,D_142) = k9_relat_1(C_141,D_142)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_224,plain,(
    ! [D_142] : k7_relset_1('#skF_6','#skF_7','#skF_9',D_142) = k9_relat_1('#skF_9',D_142) ),
    inference(resolution,[status(thm)],[c_76,c_217])).

tff(c_74,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_226,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_74])).

tff(c_22,plain,(
    ! [A_10,B_11,C_12] :
      ( r2_hidden('#skF_1'(A_10,B_11,C_12),k1_relat_1(C_12))
      | ~ r2_hidden(A_10,k9_relat_1(C_12,B_11))
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    ! [A_10,B_11,C_12] :
      ( r2_hidden('#skF_1'(A_10,B_11,C_12),B_11)
      | ~ r2_hidden(A_10,k9_relat_1(C_12,B_11))
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_80,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_279,plain,(
    ! [A_164,B_165,C_166] :
      ( r2_hidden(k4_tarski('#skF_1'(A_164,B_165,C_166),A_164),C_166)
      | ~ r2_hidden(A_164,k9_relat_1(C_166,B_165))
      | ~ v1_relat_1(C_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_44,plain,(
    ! [C_58,A_56,B_57] :
      ( k1_funct_1(C_58,A_56) = B_57
      | ~ r2_hidden(k4_tarski(A_56,B_57),C_58)
      | ~ v1_funct_1(C_58)
      | ~ v1_relat_1(C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_338,plain,(
    ! [C_176,A_177,B_178] :
      ( k1_funct_1(C_176,'#skF_1'(A_177,B_178,C_176)) = A_177
      | ~ v1_funct_1(C_176)
      | ~ r2_hidden(A_177,k9_relat_1(C_176,B_178))
      | ~ v1_relat_1(C_176) ) ),
    inference(resolution,[status(thm)],[c_279,c_44])).

tff(c_346,plain,
    ( k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_8','#skF_9')) = '#skF_10'
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_226,c_338])).

tff(c_354,plain,(
    k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_8','#skF_9')) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_80,c_346])).

tff(c_78,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_179,plain,(
    ! [A_112,B_113,C_114] :
      ( k1_relset_1(A_112,B_113,C_114) = k1_relat_1(C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_189,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_76,c_179])).

tff(c_434,plain,(
    ! [B_181,A_182,C_183] :
      ( k1_xboole_0 = B_181
      | k1_relset_1(A_182,B_181,C_183) = A_182
      | ~ v1_funct_2(C_183,A_182,B_181)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(A_182,B_181))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_437,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_76,c_434])).

tff(c_446,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_189,c_437])).

tff(c_448,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_446])).

tff(c_247,plain,(
    ! [A_153,D_154] :
      ( r2_hidden(k1_funct_1(A_153,D_154),k2_relat_1(A_153))
      | ~ r2_hidden(D_154,k1_relat_1(A_153))
      | ~ v1_funct_1(A_153)
      | ~ v1_relat_1(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_48,plain,(
    ! [B_60,A_59] :
      ( ~ r1_tarski(B_60,A_59)
      | ~ r2_hidden(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_251,plain,(
    ! [A_153,D_154] :
      ( ~ r1_tarski(k2_relat_1(A_153),k1_funct_1(A_153,D_154))
      | ~ r2_hidden(D_154,k1_relat_1(A_153))
      | ~ v1_funct_1(A_153)
      | ~ v1_relat_1(A_153) ) ),
    inference(resolution,[status(thm)],[c_247,c_48])).

tff(c_366,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_9'),'#skF_10')
    | ~ r2_hidden('#skF_1'('#skF_10','#skF_8','#skF_9'),k1_relat_1('#skF_9'))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_251])).

tff(c_380,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_9'),'#skF_10')
    | ~ r2_hidden('#skF_1'('#skF_10','#skF_8','#skF_9'),k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_80,c_366])).

tff(c_387,plain,(
    ~ r2_hidden('#skF_1'('#skF_10','#skF_8','#skF_9'),k1_relat_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_380])).

tff(c_391,plain,
    ( ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_22,c_387])).

tff(c_395,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_226,c_391])).

tff(c_397,plain,(
    r2_hidden('#skF_1'('#skF_10','#skF_8','#skF_9'),k1_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_380])).

tff(c_450,plain,(
    r2_hidden('#skF_1'('#skF_10','#skF_8','#skF_9'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_397])).

tff(c_72,plain,(
    ! [F_81] :
      ( k1_funct_1('#skF_9',F_81) != '#skF_10'
      | ~ r2_hidden(F_81,'#skF_8')
      | ~ r2_hidden(F_81,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_486,plain,
    ( k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_8','#skF_9')) != '#skF_10'
    | ~ r2_hidden('#skF_1'('#skF_10','#skF_8','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_450,c_72])).

tff(c_492,plain,(
    ~ r2_hidden('#skF_1'('#skF_10','#skF_8','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_486])).

tff(c_496,plain,
    ( ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_18,c_492])).

tff(c_500,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_226,c_496])).

tff(c_501,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_446])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_516,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_501,c_4])).

tff(c_557,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_516,c_76])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_165,plain,(
    ! [C_106,B_107,A_108] :
      ( v5_relat_1(C_106,B_107)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_108,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_174,plain,(
    ! [C_106,B_2] :
      ( v5_relat_1(C_106,B_2)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_165])).

tff(c_605,plain,(
    ! [C_191,B_192] :
      ( v5_relat_1(C_191,B_192)
      | ~ m1_subset_1(C_191,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_174])).

tff(c_608,plain,(
    ! [B_192] : v5_relat_1('#skF_9',B_192) ),
    inference(resolution,[status(thm)],[c_557,c_605])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_272,plain,(
    ! [A_160,D_161] :
      ( ~ r1_tarski(k2_relat_1(A_160),k1_funct_1(A_160,D_161))
      | ~ r2_hidden(D_161,k1_relat_1(A_160))
      | ~ v1_funct_1(A_160)
      | ~ v1_relat_1(A_160) ) ),
    inference(resolution,[status(thm)],[c_247,c_48])).

tff(c_277,plain,(
    ! [D_161,B_7] :
      ( ~ r2_hidden(D_161,k1_relat_1(B_7))
      | ~ v1_funct_1(B_7)
      | ~ v5_relat_1(B_7,k1_funct_1(B_7,D_161))
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_272])).

tff(c_363,plain,
    ( ~ r2_hidden('#skF_1'('#skF_10','#skF_8','#skF_9'),k1_relat_1('#skF_9'))
    | ~ v1_funct_1('#skF_9')
    | ~ v5_relat_1('#skF_9','#skF_10')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_277])).

tff(c_378,plain,
    ( ~ r2_hidden('#skF_1'('#skF_10','#skF_8','#skF_9'),k1_relat_1('#skF_9'))
    | ~ v5_relat_1('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_80,c_363])).

tff(c_386,plain,(
    ~ v5_relat_1('#skF_9','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_378])).

tff(c_613,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_386])).

tff(c_614,plain,(
    ~ r2_hidden('#skF_1'('#skF_10','#skF_8','#skF_9'),k1_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_378])).

tff(c_618,plain,
    ( ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_22,c_614])).

tff(c_622,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_226,c_618])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n007.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 15:45:36 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.40  
% 2.86/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.40  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4
% 2.86/1.40  
% 2.86/1.40  %Foreground sorts:
% 2.86/1.40  
% 2.86/1.40  
% 2.86/1.40  %Background operators:
% 2.86/1.40  
% 2.86/1.40  
% 2.86/1.40  %Foreground operators:
% 2.86/1.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.86/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.86/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.86/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.86/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.86/1.40  tff('#skF_7', type, '#skF_7': $i).
% 2.86/1.40  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.86/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.86/1.40  tff('#skF_10', type, '#skF_10': $i).
% 2.86/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.86/1.40  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.86/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.86/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.86/1.40  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.86/1.40  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.86/1.40  tff('#skF_9', type, '#skF_9': $i).
% 2.86/1.40  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.86/1.40  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.86/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.86/1.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.86/1.40  tff('#skF_8', type, '#skF_8': $i).
% 2.86/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.86/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.86/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.86/1.40  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.86/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.86/1.40  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.86/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.86/1.40  
% 2.86/1.42  tff(f_142, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 2.86/1.42  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.86/1.42  tff(f_105, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.86/1.42  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 2.86/1.42  tff(f_82, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.86/1.42  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.86/1.42  tff(f_123, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.86/1.42  tff(f_72, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 2.86/1.42  tff(f_87, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.86/1.42  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.86/1.42  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.86/1.42  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.86/1.42  tff(c_76, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.86/1.42  tff(c_119, plain, (![C_89, A_90, B_91]: (v1_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.86/1.42  tff(c_127, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_76, c_119])).
% 2.86/1.42  tff(c_217, plain, (![A_139, B_140, C_141, D_142]: (k7_relset_1(A_139, B_140, C_141, D_142)=k9_relat_1(C_141, D_142) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.86/1.42  tff(c_224, plain, (![D_142]: (k7_relset_1('#skF_6', '#skF_7', '#skF_9', D_142)=k9_relat_1('#skF_9', D_142))), inference(resolution, [status(thm)], [c_76, c_217])).
% 2.86/1.42  tff(c_74, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.86/1.42  tff(c_226, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_224, c_74])).
% 2.86/1.42  tff(c_22, plain, (![A_10, B_11, C_12]: (r2_hidden('#skF_1'(A_10, B_11, C_12), k1_relat_1(C_12)) | ~r2_hidden(A_10, k9_relat_1(C_12, B_11)) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.86/1.42  tff(c_18, plain, (![A_10, B_11, C_12]: (r2_hidden('#skF_1'(A_10, B_11, C_12), B_11) | ~r2_hidden(A_10, k9_relat_1(C_12, B_11)) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.86/1.42  tff(c_80, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.86/1.42  tff(c_279, plain, (![A_164, B_165, C_166]: (r2_hidden(k4_tarski('#skF_1'(A_164, B_165, C_166), A_164), C_166) | ~r2_hidden(A_164, k9_relat_1(C_166, B_165)) | ~v1_relat_1(C_166))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.86/1.42  tff(c_44, plain, (![C_58, A_56, B_57]: (k1_funct_1(C_58, A_56)=B_57 | ~r2_hidden(k4_tarski(A_56, B_57), C_58) | ~v1_funct_1(C_58) | ~v1_relat_1(C_58))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.86/1.42  tff(c_338, plain, (![C_176, A_177, B_178]: (k1_funct_1(C_176, '#skF_1'(A_177, B_178, C_176))=A_177 | ~v1_funct_1(C_176) | ~r2_hidden(A_177, k9_relat_1(C_176, B_178)) | ~v1_relat_1(C_176))), inference(resolution, [status(thm)], [c_279, c_44])).
% 2.86/1.42  tff(c_346, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_8', '#skF_9'))='#skF_10' | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_226, c_338])).
% 2.86/1.42  tff(c_354, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_8', '#skF_9'))='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_127, c_80, c_346])).
% 2.86/1.42  tff(c_78, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.86/1.42  tff(c_179, plain, (![A_112, B_113, C_114]: (k1_relset_1(A_112, B_113, C_114)=k1_relat_1(C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.86/1.42  tff(c_189, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_76, c_179])).
% 2.86/1.42  tff(c_434, plain, (![B_181, A_182, C_183]: (k1_xboole_0=B_181 | k1_relset_1(A_182, B_181, C_183)=A_182 | ~v1_funct_2(C_183, A_182, B_181) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(A_182, B_181))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.86/1.42  tff(c_437, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_76, c_434])).
% 2.86/1.42  tff(c_446, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_189, c_437])).
% 2.86/1.42  tff(c_448, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_446])).
% 2.86/1.42  tff(c_247, plain, (![A_153, D_154]: (r2_hidden(k1_funct_1(A_153, D_154), k2_relat_1(A_153)) | ~r2_hidden(D_154, k1_relat_1(A_153)) | ~v1_funct_1(A_153) | ~v1_relat_1(A_153))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.86/1.42  tff(c_48, plain, (![B_60, A_59]: (~r1_tarski(B_60, A_59) | ~r2_hidden(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.86/1.42  tff(c_251, plain, (![A_153, D_154]: (~r1_tarski(k2_relat_1(A_153), k1_funct_1(A_153, D_154)) | ~r2_hidden(D_154, k1_relat_1(A_153)) | ~v1_funct_1(A_153) | ~v1_relat_1(A_153))), inference(resolution, [status(thm)], [c_247, c_48])).
% 2.86/1.42  tff(c_366, plain, (~r1_tarski(k2_relat_1('#skF_9'), '#skF_10') | ~r2_hidden('#skF_1'('#skF_10', '#skF_8', '#skF_9'), k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_354, c_251])).
% 2.86/1.42  tff(c_380, plain, (~r1_tarski(k2_relat_1('#skF_9'), '#skF_10') | ~r2_hidden('#skF_1'('#skF_10', '#skF_8', '#skF_9'), k1_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_80, c_366])).
% 2.86/1.42  tff(c_387, plain, (~r2_hidden('#skF_1'('#skF_10', '#skF_8', '#skF_9'), k1_relat_1('#skF_9'))), inference(splitLeft, [status(thm)], [c_380])).
% 2.86/1.42  tff(c_391, plain, (~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_22, c_387])).
% 2.86/1.42  tff(c_395, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_127, c_226, c_391])).
% 2.86/1.42  tff(c_397, plain, (r2_hidden('#skF_1'('#skF_10', '#skF_8', '#skF_9'), k1_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_380])).
% 2.86/1.42  tff(c_450, plain, (r2_hidden('#skF_1'('#skF_10', '#skF_8', '#skF_9'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_448, c_397])).
% 2.86/1.42  tff(c_72, plain, (![F_81]: (k1_funct_1('#skF_9', F_81)!='#skF_10' | ~r2_hidden(F_81, '#skF_8') | ~r2_hidden(F_81, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.86/1.42  tff(c_486, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_8', '#skF_9'))!='#skF_10' | ~r2_hidden('#skF_1'('#skF_10', '#skF_8', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_450, c_72])).
% 2.86/1.42  tff(c_492, plain, (~r2_hidden('#skF_1'('#skF_10', '#skF_8', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_354, c_486])).
% 2.86/1.42  tff(c_496, plain, (~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_18, c_492])).
% 2.86/1.42  tff(c_500, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_127, c_226, c_496])).
% 2.86/1.42  tff(c_501, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_446])).
% 2.86/1.42  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.86/1.42  tff(c_516, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_501, c_501, c_4])).
% 2.86/1.42  tff(c_557, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_516, c_76])).
% 2.86/1.42  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.86/1.42  tff(c_165, plain, (![C_106, B_107, A_108]: (v5_relat_1(C_106, B_107) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_108, B_107))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.86/1.42  tff(c_174, plain, (![C_106, B_2]: (v5_relat_1(C_106, B_2) | ~m1_subset_1(C_106, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_165])).
% 2.86/1.42  tff(c_605, plain, (![C_191, B_192]: (v5_relat_1(C_191, B_192) | ~m1_subset_1(C_191, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_501, c_174])).
% 2.86/1.42  tff(c_608, plain, (![B_192]: (v5_relat_1('#skF_9', B_192))), inference(resolution, [status(thm)], [c_557, c_605])).
% 2.86/1.42  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.86/1.42  tff(c_272, plain, (![A_160, D_161]: (~r1_tarski(k2_relat_1(A_160), k1_funct_1(A_160, D_161)) | ~r2_hidden(D_161, k1_relat_1(A_160)) | ~v1_funct_1(A_160) | ~v1_relat_1(A_160))), inference(resolution, [status(thm)], [c_247, c_48])).
% 2.86/1.42  tff(c_277, plain, (![D_161, B_7]: (~r2_hidden(D_161, k1_relat_1(B_7)) | ~v1_funct_1(B_7) | ~v5_relat_1(B_7, k1_funct_1(B_7, D_161)) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_12, c_272])).
% 2.86/1.42  tff(c_363, plain, (~r2_hidden('#skF_1'('#skF_10', '#skF_8', '#skF_9'), k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v5_relat_1('#skF_9', '#skF_10') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_354, c_277])).
% 2.86/1.42  tff(c_378, plain, (~r2_hidden('#skF_1'('#skF_10', '#skF_8', '#skF_9'), k1_relat_1('#skF_9')) | ~v5_relat_1('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_80, c_363])).
% 2.86/1.42  tff(c_386, plain, (~v5_relat_1('#skF_9', '#skF_10')), inference(splitLeft, [status(thm)], [c_378])).
% 2.86/1.42  tff(c_613, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_608, c_386])).
% 2.86/1.42  tff(c_614, plain, (~r2_hidden('#skF_1'('#skF_10', '#skF_8', '#skF_9'), k1_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_378])).
% 2.86/1.42  tff(c_618, plain, (~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_22, c_614])).
% 2.86/1.42  tff(c_622, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_127, c_226, c_618])).
% 2.86/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.42  
% 2.86/1.42  Inference rules
% 2.86/1.42  ----------------------
% 2.86/1.42  #Ref     : 0
% 2.86/1.42  #Sup     : 117
% 2.86/1.42  #Fact    : 0
% 2.86/1.42  #Define  : 0
% 2.86/1.42  #Split   : 5
% 2.86/1.42  #Chain   : 0
% 2.86/1.42  #Close   : 0
% 2.86/1.42  
% 2.86/1.42  Ordering : KBO
% 2.86/1.42  
% 2.86/1.42  Simplification rules
% 2.86/1.42  ----------------------
% 2.86/1.42  #Subsume      : 13
% 2.86/1.42  #Demod        : 92
% 2.86/1.42  #Tautology    : 44
% 2.86/1.42  #SimpNegUnit  : 0
% 2.86/1.42  #BackRed      : 23
% 2.86/1.42  
% 2.86/1.42  #Partial instantiations: 0
% 2.86/1.42  #Strategies tried      : 1
% 2.86/1.42  
% 2.86/1.42  Timing (in seconds)
% 2.86/1.42  ----------------------
% 3.10/1.42  Preprocessing        : 0.35
% 3.10/1.42  Parsing              : 0.18
% 3.10/1.42  CNF conversion       : 0.03
% 3.10/1.42  Main loop            : 0.32
% 3.10/1.42  Inferencing          : 0.11
% 3.10/1.42  Reduction            : 0.10
% 3.10/1.42  Demodulation         : 0.07
% 3.10/1.42  BG Simplification    : 0.02
% 3.10/1.42  Subsumption          : 0.06
% 3.10/1.42  Abstraction          : 0.02
% 3.10/1.42  MUC search           : 0.00
% 3.10/1.42  Cooper               : 0.00
% 3.10/1.42  Total                : 0.70
% 3.10/1.42  Index Insertion      : 0.00
% 3.10/1.42  Index Deletion       : 0.00
% 3.10/1.43  Index Matching       : 0.00
% 3.10/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
