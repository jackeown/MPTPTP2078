%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:24 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 182 expanded)
%              Number of leaves         :   45 (  84 expanded)
%              Depth                    :   12
%              Number of atoms          :  153 ( 452 expanded)
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

tff(f_139,negated_conjecture,(
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

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(E,D),C) )
      <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_120,axiom,(
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

tff(f_76,axiom,(
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

tff(f_59,axiom,(
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

tff(c_78,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_162,plain,(
    ! [A_112,B_113,C_114] :
      ( k2_relset_1(A_112,B_113,C_114) = k2_relat_1(C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_166,plain,(
    k2_relset_1('#skF_8','#skF_9','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_78,c_162])).

tff(c_76,plain,(
    k2_relset_1('#skF_8','#skF_9','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_167,plain,(
    k2_relat_1('#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_76])).

tff(c_16,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_124,plain,(
    ! [B_98,A_99] :
      ( v1_relat_1(B_98)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(A_99))
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_127,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_78,c_124])).

tff(c_130,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_127])).

tff(c_146,plain,(
    ! [C_106,B_107,A_108] :
      ( v5_relat_1(C_106,B_107)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_108,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_150,plain,(
    v5_relat_1('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_78,c_146])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v5_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_239,plain,(
    ! [A_146,B_147,C_148] :
      ( r2_hidden('#skF_6'(A_146,B_147,C_148),B_147)
      | k2_relset_1(A_146,B_147,C_148) = B_147
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_241,plain,
    ( r2_hidden('#skF_6'('#skF_8','#skF_9','#skF_10'),'#skF_9')
    | k2_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_78,c_239])).

tff(c_243,plain,
    ( r2_hidden('#skF_6'('#skF_8','#skF_9','#skF_10'),'#skF_9')
    | k2_relat_1('#skF_10') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_241])).

tff(c_244,plain,(
    r2_hidden('#skF_6'('#skF_8','#skF_9','#skF_10'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_243])).

tff(c_86,plain,(
    ! [D_87] :
      ( r2_hidden('#skF_11'(D_87),'#skF_8')
      | ~ r2_hidden(D_87,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_82,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_80,plain,(
    v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_172,plain,(
    ! [A_115,B_116,C_117] :
      ( k1_relset_1(A_115,B_116,C_117) = k1_relat_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_176,plain,(
    k1_relset_1('#skF_8','#skF_9','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_78,c_172])).

tff(c_216,plain,(
    ! [B_141,A_142,C_143] :
      ( k1_xboole_0 = B_141
      | k1_relset_1(A_142,B_141,C_143) = A_142
      | ~ v1_funct_2(C_143,A_142,B_141)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_142,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_219,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_78,c_216])).

tff(c_222,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_176,c_219])).

tff(c_223,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_222])).

tff(c_84,plain,(
    ! [D_87] :
      ( k1_funct_1('#skF_10','#skF_11'(D_87)) = D_87
      | ~ r2_hidden(D_87,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_246,plain,(
    ! [A_152,E_153,B_154] :
      ( r2_hidden(k1_funct_1(A_152,E_153),k9_relat_1(A_152,B_154))
      | ~ r2_hidden(E_153,B_154)
      | ~ r2_hidden(E_153,k1_relat_1(A_152))
      | ~ v1_funct_1(A_152)
      | ~ v1_relat_1(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_249,plain,(
    ! [D_87,B_154] :
      ( r2_hidden(D_87,k9_relat_1('#skF_10',B_154))
      | ~ r2_hidden('#skF_11'(D_87),B_154)
      | ~ r2_hidden('#skF_11'(D_87),k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(D_87,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_246])).

tff(c_258,plain,(
    ! [D_159,B_160] :
      ( r2_hidden(D_159,k9_relat_1('#skF_10',B_160))
      | ~ r2_hidden('#skF_11'(D_159),B_160)
      | ~ r2_hidden('#skF_11'(D_159),'#skF_8')
      | ~ r2_hidden(D_159,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_82,c_223,c_249])).

tff(c_262,plain,(
    ! [D_161] :
      ( r2_hidden(D_161,k9_relat_1('#skF_10','#skF_8'))
      | ~ r2_hidden('#skF_11'(D_161),'#skF_8')
      | ~ r2_hidden(D_161,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_86,c_258])).

tff(c_266,plain,(
    ! [D_87] :
      ( r2_hidden(D_87,k9_relat_1('#skF_10','#skF_8'))
      | ~ r2_hidden(D_87,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_86,c_262])).

tff(c_22,plain,(
    ! [A_11,B_12,C_13] :
      ( r2_hidden(k4_tarski('#skF_1'(A_11,B_12,C_13),A_11),C_13)
      | ~ r2_hidden(A_11,k9_relat_1(C_13,B_12))
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_252,plain,(
    ! [E_155,A_156,B_157,C_158] :
      ( ~ r2_hidden(k4_tarski(E_155,'#skF_6'(A_156,B_157,C_158)),C_158)
      | k2_relset_1(A_156,B_157,C_158) = B_157
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_393,plain,(
    ! [A_193,B_194,C_195,B_196] :
      ( k2_relset_1(A_193,B_194,C_195) = B_194
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_193,B_194)))
      | ~ r2_hidden('#skF_6'(A_193,B_194,C_195),k9_relat_1(C_195,B_196))
      | ~ v1_relat_1(C_195) ) ),
    inference(resolution,[status(thm)],[c_22,c_252])).

tff(c_401,plain,(
    ! [A_193,B_194] :
      ( k2_relset_1(A_193,B_194,'#skF_10') = B_194
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1(A_193,B_194)))
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden('#skF_6'(A_193,B_194,'#skF_10'),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_266,c_393])).

tff(c_408,plain,(
    ! [A_197,B_198] :
      ( k2_relset_1(A_197,B_198,'#skF_10') = B_198
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1(A_197,B_198)))
      | ~ r2_hidden('#skF_6'(A_197,B_198,'#skF_10'),'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_401])).

tff(c_411,plain,
    ( k2_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_9'
    | ~ r2_hidden('#skF_6'('#skF_8','#skF_9','#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_78,c_408])).

tff(c_414,plain,(
    k2_relat_1('#skF_10') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_166,c_411])).

tff(c_416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_414])).

tff(c_417,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_92,plain,(
    ! [B_94,A_95] :
      ( B_94 = A_95
      | ~ r1_tarski(B_94,A_95)
      | ~ r1_tarski(A_95,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_101,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_92])).

tff(c_447,plain,(
    ! [A_203] :
      ( A_203 = '#skF_9'
      | ~ r1_tarski(A_203,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_417,c_101])).

tff(c_466,plain,(
    ! [B_207] :
      ( k2_relat_1(B_207) = '#skF_9'
      | ~ v5_relat_1(B_207,'#skF_9')
      | ~ v1_relat_1(B_207) ) ),
    inference(resolution,[status(thm)],[c_14,c_447])).

tff(c_469,plain,
    ( k2_relat_1('#skF_10') = '#skF_9'
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_150,c_466])).

tff(c_472,plain,(
    k2_relat_1('#skF_10') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_469])).

tff(c_474,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_472])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:41:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.40  
% 2.94/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.40  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_4 > #skF_10 > #skF_2 > #skF_7 > #skF_9 > #skF_8 > #skF_5 > #skF_11 > #skF_3
% 2.94/1.40  
% 2.94/1.40  %Foreground sorts:
% 2.94/1.40  
% 2.94/1.40  
% 2.94/1.40  %Background operators:
% 2.94/1.40  
% 2.94/1.40  
% 2.94/1.40  %Foreground operators:
% 2.94/1.40  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.94/1.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.94/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.94/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.94/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.94/1.40  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.94/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.94/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.94/1.40  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.94/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.94/1.40  tff('#skF_10', type, '#skF_10': $i).
% 2.94/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.94/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.94/1.40  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.94/1.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.94/1.40  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 2.94/1.40  tff('#skF_9', type, '#skF_9': $i).
% 2.94/1.40  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.94/1.40  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.94/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.94/1.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.94/1.40  tff('#skF_8', type, '#skF_8': $i).
% 2.94/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.94/1.40  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.94/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.94/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.94/1.40  tff('#skF_11', type, '#skF_11': $i > $i).
% 2.94/1.40  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.94/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.94/1.40  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.94/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.94/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.94/1.40  
% 2.94/1.42  tff(f_139, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 2.94/1.42  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.94/1.42  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.94/1.42  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.94/1.42  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.94/1.42  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.94/1.42  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(E, D), C)))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_relset_1)).
% 2.94/1.42  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.94/1.42  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.94/1.42  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 2.94/1.42  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 2.94/1.42  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.94/1.42  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.94/1.42  tff(c_78, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.94/1.42  tff(c_162, plain, (![A_112, B_113, C_114]: (k2_relset_1(A_112, B_113, C_114)=k2_relat_1(C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.94/1.42  tff(c_166, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_78, c_162])).
% 2.94/1.42  tff(c_76, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.94/1.42  tff(c_167, plain, (k2_relat_1('#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_166, c_76])).
% 2.94/1.42  tff(c_16, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.94/1.42  tff(c_124, plain, (![B_98, A_99]: (v1_relat_1(B_98) | ~m1_subset_1(B_98, k1_zfmisc_1(A_99)) | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.94/1.42  tff(c_127, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_78, c_124])).
% 2.94/1.42  tff(c_130, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_127])).
% 2.94/1.42  tff(c_146, plain, (![C_106, B_107, A_108]: (v5_relat_1(C_106, B_107) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_108, B_107))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.94/1.42  tff(c_150, plain, (v5_relat_1('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_78, c_146])).
% 2.94/1.42  tff(c_14, plain, (![B_8, A_7]: (r1_tarski(k2_relat_1(B_8), A_7) | ~v5_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.94/1.42  tff(c_239, plain, (![A_146, B_147, C_148]: (r2_hidden('#skF_6'(A_146, B_147, C_148), B_147) | k2_relset_1(A_146, B_147, C_148)=B_147 | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.94/1.42  tff(c_241, plain, (r2_hidden('#skF_6'('#skF_8', '#skF_9', '#skF_10'), '#skF_9') | k2_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_78, c_239])).
% 2.94/1.42  tff(c_243, plain, (r2_hidden('#skF_6'('#skF_8', '#skF_9', '#skF_10'), '#skF_9') | k2_relat_1('#skF_10')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_166, c_241])).
% 2.94/1.42  tff(c_244, plain, (r2_hidden('#skF_6'('#skF_8', '#skF_9', '#skF_10'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_167, c_243])).
% 2.94/1.42  tff(c_86, plain, (![D_87]: (r2_hidden('#skF_11'(D_87), '#skF_8') | ~r2_hidden(D_87, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.94/1.42  tff(c_82, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.94/1.42  tff(c_80, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.94/1.42  tff(c_172, plain, (![A_115, B_116, C_117]: (k1_relset_1(A_115, B_116, C_117)=k1_relat_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.94/1.42  tff(c_176, plain, (k1_relset_1('#skF_8', '#skF_9', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_78, c_172])).
% 2.94/1.42  tff(c_216, plain, (![B_141, A_142, C_143]: (k1_xboole_0=B_141 | k1_relset_1(A_142, B_141, C_143)=A_142 | ~v1_funct_2(C_143, A_142, B_141) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_142, B_141))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.94/1.42  tff(c_219, plain, (k1_xboole_0='#skF_9' | k1_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_8' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_78, c_216])).
% 2.94/1.42  tff(c_222, plain, (k1_xboole_0='#skF_9' | k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_176, c_219])).
% 2.94/1.42  tff(c_223, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(splitLeft, [status(thm)], [c_222])).
% 2.94/1.42  tff(c_84, plain, (![D_87]: (k1_funct_1('#skF_10', '#skF_11'(D_87))=D_87 | ~r2_hidden(D_87, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.94/1.42  tff(c_246, plain, (![A_152, E_153, B_154]: (r2_hidden(k1_funct_1(A_152, E_153), k9_relat_1(A_152, B_154)) | ~r2_hidden(E_153, B_154) | ~r2_hidden(E_153, k1_relat_1(A_152)) | ~v1_funct_1(A_152) | ~v1_relat_1(A_152))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.94/1.42  tff(c_249, plain, (![D_87, B_154]: (r2_hidden(D_87, k9_relat_1('#skF_10', B_154)) | ~r2_hidden('#skF_11'(D_87), B_154) | ~r2_hidden('#skF_11'(D_87), k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(D_87, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_84, c_246])).
% 2.94/1.42  tff(c_258, plain, (![D_159, B_160]: (r2_hidden(D_159, k9_relat_1('#skF_10', B_160)) | ~r2_hidden('#skF_11'(D_159), B_160) | ~r2_hidden('#skF_11'(D_159), '#skF_8') | ~r2_hidden(D_159, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_82, c_223, c_249])).
% 2.94/1.42  tff(c_262, plain, (![D_161]: (r2_hidden(D_161, k9_relat_1('#skF_10', '#skF_8')) | ~r2_hidden('#skF_11'(D_161), '#skF_8') | ~r2_hidden(D_161, '#skF_9'))), inference(resolution, [status(thm)], [c_86, c_258])).
% 2.94/1.42  tff(c_266, plain, (![D_87]: (r2_hidden(D_87, k9_relat_1('#skF_10', '#skF_8')) | ~r2_hidden(D_87, '#skF_9'))), inference(resolution, [status(thm)], [c_86, c_262])).
% 2.94/1.42  tff(c_22, plain, (![A_11, B_12, C_13]: (r2_hidden(k4_tarski('#skF_1'(A_11, B_12, C_13), A_11), C_13) | ~r2_hidden(A_11, k9_relat_1(C_13, B_12)) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.94/1.42  tff(c_252, plain, (![E_155, A_156, B_157, C_158]: (~r2_hidden(k4_tarski(E_155, '#skF_6'(A_156, B_157, C_158)), C_158) | k2_relset_1(A_156, B_157, C_158)=B_157 | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.94/1.42  tff(c_393, plain, (![A_193, B_194, C_195, B_196]: (k2_relset_1(A_193, B_194, C_195)=B_194 | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_193, B_194))) | ~r2_hidden('#skF_6'(A_193, B_194, C_195), k9_relat_1(C_195, B_196)) | ~v1_relat_1(C_195))), inference(resolution, [status(thm)], [c_22, c_252])).
% 2.94/1.42  tff(c_401, plain, (![A_193, B_194]: (k2_relset_1(A_193, B_194, '#skF_10')=B_194 | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1(A_193, B_194))) | ~v1_relat_1('#skF_10') | ~r2_hidden('#skF_6'(A_193, B_194, '#skF_10'), '#skF_9'))), inference(resolution, [status(thm)], [c_266, c_393])).
% 2.94/1.42  tff(c_408, plain, (![A_197, B_198]: (k2_relset_1(A_197, B_198, '#skF_10')=B_198 | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))) | ~r2_hidden('#skF_6'(A_197, B_198, '#skF_10'), '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_401])).
% 2.94/1.42  tff(c_411, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_9' | ~r2_hidden('#skF_6'('#skF_8', '#skF_9', '#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_78, c_408])).
% 2.94/1.42  tff(c_414, plain, (k2_relat_1('#skF_10')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_244, c_166, c_411])).
% 2.94/1.42  tff(c_416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_414])).
% 2.94/1.42  tff(c_417, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_222])).
% 2.94/1.42  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.94/1.42  tff(c_92, plain, (![B_94, A_95]: (B_94=A_95 | ~r1_tarski(B_94, A_95) | ~r1_tarski(A_95, B_94))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.94/1.42  tff(c_101, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_92])).
% 2.94/1.42  tff(c_447, plain, (![A_203]: (A_203='#skF_9' | ~r1_tarski(A_203, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_417, c_417, c_101])).
% 2.94/1.42  tff(c_466, plain, (![B_207]: (k2_relat_1(B_207)='#skF_9' | ~v5_relat_1(B_207, '#skF_9') | ~v1_relat_1(B_207))), inference(resolution, [status(thm)], [c_14, c_447])).
% 2.94/1.42  tff(c_469, plain, (k2_relat_1('#skF_10')='#skF_9' | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_150, c_466])).
% 2.94/1.42  tff(c_472, plain, (k2_relat_1('#skF_10')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_130, c_469])).
% 2.94/1.42  tff(c_474, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_472])).
% 2.94/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.42  
% 2.94/1.42  Inference rules
% 2.94/1.42  ----------------------
% 2.94/1.42  #Ref     : 0
% 2.94/1.42  #Sup     : 79
% 2.94/1.42  #Fact    : 0
% 2.94/1.42  #Define  : 0
% 2.94/1.42  #Split   : 1
% 2.94/1.42  #Chain   : 0
% 2.94/1.42  #Close   : 0
% 2.94/1.42  
% 2.94/1.42  Ordering : KBO
% 2.94/1.42  
% 2.94/1.42  Simplification rules
% 2.94/1.42  ----------------------
% 2.94/1.42  #Subsume      : 3
% 2.94/1.42  #Demod        : 48
% 2.94/1.42  #Tautology    : 24
% 2.94/1.42  #SimpNegUnit  : 4
% 2.94/1.42  #BackRed      : 11
% 2.94/1.42  
% 2.94/1.42  #Partial instantiations: 0
% 2.94/1.42  #Strategies tried      : 1
% 2.94/1.42  
% 2.94/1.42  Timing (in seconds)
% 2.94/1.42  ----------------------
% 2.94/1.42  Preprocessing        : 0.36
% 2.94/1.42  Parsing              : 0.17
% 2.94/1.42  CNF conversion       : 0.03
% 2.94/1.42  Main loop            : 0.30
% 2.94/1.42  Inferencing          : 0.11
% 2.94/1.42  Reduction            : 0.09
% 2.94/1.42  Demodulation         : 0.06
% 2.94/1.42  BG Simplification    : 0.02
% 2.94/1.42  Subsumption          : 0.06
% 2.94/1.42  Abstraction          : 0.02
% 2.94/1.42  MUC search           : 0.00
% 2.94/1.42  Cooper               : 0.00
% 2.94/1.42  Total                : 0.69
% 2.94/1.42  Index Insertion      : 0.00
% 2.94/1.42  Index Deletion       : 0.00
% 2.94/1.42  Index Matching       : 0.00
% 2.94/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
