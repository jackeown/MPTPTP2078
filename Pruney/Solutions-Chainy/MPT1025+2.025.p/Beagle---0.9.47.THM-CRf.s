%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:33 EST 2020

% Result     : Theorem 12.08s
% Output     : CNFRefutation 12.19s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 764 expanded)
%              Number of leaves         :   39 ( 274 expanded)
%              Depth                    :   12
%              Number of atoms          :  363 (2144 expanded)
%              Number of equality atoms :   38 ( 322 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_144,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_125,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ~ v1_xboole_0(C)
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
                 => ! [E] :
                      ( m1_subset_1(E,A)
                     => ( r2_hidden(E,k7_relset_1(C,A,D,B))
                      <=> ? [F] :
                            ( m1_subset_1(F,C)
                            & r2_hidden(k4_tarski(F,E),D)
                            & r2_hidden(F,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_72,plain,(
    ! [C_154,A_155,B_156] :
      ( v1_relat_1(C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_76,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_52,c_72])).

tff(c_56,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_133,plain,(
    ! [A_178,B_179,C_180,D_181] :
      ( k7_relset_1(A_178,B_179,C_180,D_181) = k9_relat_1(C_180,D_181)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_136,plain,(
    ! [D_181] : k7_relset_1('#skF_6','#skF_7','#skF_9',D_181) = k9_relat_1('#skF_9',D_181) ),
    inference(resolution,[status(thm)],[c_52,c_133])).

tff(c_50,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_138,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_50])).

tff(c_123,plain,(
    ! [A_175,B_176,C_177] :
      ( r2_hidden('#skF_2'(A_175,B_176,C_177),B_176)
      | ~ r2_hidden(A_175,k9_relat_1(C_177,B_176))
      | ~ v1_relat_1(C_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_174,plain,(
    ! [B_185,A_186,C_187] :
      ( ~ v1_xboole_0(B_185)
      | ~ r2_hidden(A_186,k9_relat_1(C_187,B_185))
      | ~ v1_relat_1(C_187) ) ),
    inference(resolution,[status(thm)],[c_123,c_2])).

tff(c_177,plain,
    ( ~ v1_xboole_0('#skF_8')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_138,c_174])).

tff(c_192,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_177])).

tff(c_256,plain,(
    ! [A_207,B_208,C_209,D_210] :
      ( m1_subset_1(k7_relset_1(A_207,B_208,C_209,D_210),k1_zfmisc_1(B_208))
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_276,plain,(
    ! [D_181] :
      ( m1_subset_1(k9_relat_1('#skF_9',D_181),k1_zfmisc_1('#skF_7'))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_256])).

tff(c_284,plain,(
    ! [D_211] : m1_subset_1(k9_relat_1('#skF_9',D_211),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_276])).

tff(c_8,plain,(
    ! [A_7,C_9,B_8] :
      ( m1_subset_1(A_7,C_9)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(C_9))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_326,plain,(
    ! [A_215,D_216] :
      ( m1_subset_1(A_215,'#skF_7')
      | ~ r2_hidden(A_215,k9_relat_1('#skF_9',D_216)) ) ),
    inference(resolution,[status(thm)],[c_284,c_8])).

tff(c_347,plain,(
    m1_subset_1('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_138,c_326])).

tff(c_93,plain,(
    ! [C_162,B_163,A_164] :
      ( v1_xboole_0(C_162)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(B_163,A_164)))
      | ~ v1_xboole_0(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_97,plain,
    ( v1_xboole_0('#skF_9')
    | ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_93])).

tff(c_98,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_99,plain,(
    ! [A_165,B_166,C_167] :
      ( k1_relset_1(A_165,B_166,C_167) = k1_relat_1(C_167)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_103,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_52,c_99])).

tff(c_528,plain,(
    ! [A_241,B_242,C_243] :
      ( r2_hidden('#skF_3'(A_241,B_242,C_243),B_242)
      | k1_relset_1(B_242,A_241,C_243) = B_242
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k2_zfmisc_1(B_242,A_241))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_533,plain,
    ( r2_hidden('#skF_3'('#skF_7','#skF_6','#skF_9'),'#skF_6')
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_52,c_528])).

tff(c_536,plain,
    ( r2_hidden('#skF_3'('#skF_7','#skF_6','#skF_9'),'#skF_6')
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_533])).

tff(c_537,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_536])).

tff(c_204,plain,(
    ! [A_190,B_191,C_192] :
      ( r2_hidden('#skF_2'(A_190,B_191,C_192),k1_relat_1(C_192))
      | ~ r2_hidden(A_190,k9_relat_1(C_192,B_191))
      | ~ v1_relat_1(C_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_209,plain,(
    ! [C_193,A_194,B_195] :
      ( ~ v1_xboole_0(k1_relat_1(C_193))
      | ~ r2_hidden(A_194,k9_relat_1(C_193,B_195))
      | ~ v1_relat_1(C_193) ) ),
    inference(resolution,[status(thm)],[c_204,c_2])).

tff(c_212,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_138,c_209])).

tff(c_227,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_212])).

tff(c_538,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_537,c_227])).

tff(c_1396,plain,(
    ! [B_357,D_355,A_356,C_358,E_359] :
      ( m1_subset_1('#skF_5'(D_355,A_356,B_357,C_358,E_359),C_358)
      | ~ r2_hidden(E_359,k7_relset_1(C_358,A_356,D_355,B_357))
      | ~ m1_subset_1(E_359,A_356)
      | ~ m1_subset_1(D_355,k1_zfmisc_1(k2_zfmisc_1(C_358,A_356)))
      | v1_xboole_0(C_358)
      | v1_xboole_0(B_357)
      | v1_xboole_0(A_356) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1407,plain,(
    ! [D_181,E_359] :
      ( m1_subset_1('#skF_5'('#skF_9','#skF_7',D_181,'#skF_6',E_359),'#skF_6')
      | ~ r2_hidden(E_359,k9_relat_1('#skF_9',D_181))
      | ~ m1_subset_1(E_359,'#skF_7')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_181)
      | v1_xboole_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_1396])).

tff(c_1421,plain,(
    ! [D_181,E_359] :
      ( m1_subset_1('#skF_5'('#skF_9','#skF_7',D_181,'#skF_6',E_359),'#skF_6')
      | ~ r2_hidden(E_359,k9_relat_1('#skF_9',D_181))
      | ~ m1_subset_1(E_359,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_181)
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1407])).

tff(c_1546,plain,(
    ! [D_380,E_381] :
      ( m1_subset_1('#skF_5'('#skF_9','#skF_7',D_380,'#skF_6',E_381),'#skF_6')
      | ~ r2_hidden(E_381,k9_relat_1('#skF_9',D_380))
      | ~ m1_subset_1(E_381,'#skF_7')
      | v1_xboole_0(D_380) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_538,c_1421])).

tff(c_1565,plain,
    ( m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6','#skF_10'),'#skF_6')
    | ~ m1_subset_1('#skF_10','#skF_7')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_138,c_1546])).

tff(c_1587,plain,
    ( m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6','#skF_10'),'#skF_6')
    | v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_1565])).

tff(c_1588,plain,(
    m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6','#skF_10'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_192,c_1587])).

tff(c_1592,plain,(
    ! [A_383,E_386,D_382,C_385,B_384] :
      ( r2_hidden('#skF_5'(D_382,A_383,B_384,C_385,E_386),B_384)
      | ~ r2_hidden(E_386,k7_relset_1(C_385,A_383,D_382,B_384))
      | ~ m1_subset_1(E_386,A_383)
      | ~ m1_subset_1(D_382,k1_zfmisc_1(k2_zfmisc_1(C_385,A_383)))
      | v1_xboole_0(C_385)
      | v1_xboole_0(B_384)
      | v1_xboole_0(A_383) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1597,plain,(
    ! [B_384,E_386] :
      ( r2_hidden('#skF_5'('#skF_9','#skF_7',B_384,'#skF_6',E_386),B_384)
      | ~ r2_hidden(E_386,k7_relset_1('#skF_6','#skF_7','#skF_9',B_384))
      | ~ m1_subset_1(E_386,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(B_384)
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_52,c_1592])).

tff(c_1600,plain,(
    ! [B_384,E_386] :
      ( r2_hidden('#skF_5'('#skF_9','#skF_7',B_384,'#skF_6',E_386),B_384)
      | ~ r2_hidden(E_386,k9_relat_1('#skF_9',B_384))
      | ~ m1_subset_1(E_386,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(B_384)
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_1597])).

tff(c_1608,plain,(
    ! [B_390,E_391] :
      ( r2_hidden('#skF_5'('#skF_9','#skF_7',B_390,'#skF_6',E_391),B_390)
      | ~ r2_hidden(E_391,k9_relat_1('#skF_9',B_390))
      | ~ m1_subset_1(E_391,'#skF_7')
      | v1_xboole_0(B_390) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_538,c_1600])).

tff(c_48,plain,(
    ! [F_148] :
      ( k1_funct_1('#skF_9',F_148) != '#skF_10'
      | ~ r2_hidden(F_148,'#skF_8')
      | ~ m1_subset_1(F_148,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_1709,plain,(
    ! [E_391] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6',E_391)) != '#skF_10'
      | ~ m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6',E_391),'#skF_6')
      | ~ r2_hidden(E_391,k9_relat_1('#skF_9','#skF_8'))
      | ~ m1_subset_1(E_391,'#skF_7')
      | v1_xboole_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1608,c_48])).

tff(c_2207,plain,(
    ! [E_450] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6',E_450)) != '#skF_10'
      | ~ m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6',E_450),'#skF_6')
      | ~ r2_hidden(E_450,k9_relat_1('#skF_9','#skF_8'))
      | ~ m1_subset_1(E_450,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_192,c_1709])).

tff(c_2230,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6','#skF_10')) != '#skF_10'
    | ~ m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6','#skF_10'),'#skF_6')
    | ~ m1_subset_1('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_138,c_2207])).

tff(c_2252,plain,(
    k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6','#skF_10')) != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_1588,c_2230])).

tff(c_1827,plain,(
    ! [A_409,B_410,D_408,C_411,E_412] :
      ( r2_hidden(k4_tarski('#skF_5'(D_408,A_409,B_410,C_411,E_412),E_412),D_408)
      | ~ r2_hidden(E_412,k7_relset_1(C_411,A_409,D_408,B_410))
      | ~ m1_subset_1(E_412,A_409)
      | ~ m1_subset_1(D_408,k1_zfmisc_1(k2_zfmisc_1(C_411,A_409)))
      | v1_xboole_0(C_411)
      | v1_xboole_0(B_410)
      | v1_xboole_0(A_409) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_20,plain,(
    ! [C_18,A_16,B_17] :
      ( k1_funct_1(C_18,A_16) = B_17
      | ~ r2_hidden(k4_tarski(A_16,B_17),C_18)
      | ~ v1_funct_1(C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_7420,plain,(
    ! [E_829,B_826,D_825,A_827,C_828] :
      ( k1_funct_1(D_825,'#skF_5'(D_825,A_827,B_826,C_828,E_829)) = E_829
      | ~ v1_funct_1(D_825)
      | ~ v1_relat_1(D_825)
      | ~ r2_hidden(E_829,k7_relset_1(C_828,A_827,D_825,B_826))
      | ~ m1_subset_1(E_829,A_827)
      | ~ m1_subset_1(D_825,k1_zfmisc_1(k2_zfmisc_1(C_828,A_827)))
      | v1_xboole_0(C_828)
      | v1_xboole_0(B_826)
      | v1_xboole_0(A_827) ) ),
    inference(resolution,[status(thm)],[c_1827,c_20])).

tff(c_7440,plain,(
    ! [D_181,E_829] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_7',D_181,'#skF_6',E_829)) = E_829
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(E_829,k9_relat_1('#skF_9',D_181))
      | ~ m1_subset_1(E_829,'#skF_7')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_181)
      | v1_xboole_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_7420])).

tff(c_7457,plain,(
    ! [D_181,E_829] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_7',D_181,'#skF_6',E_829)) = E_829
      | ~ r2_hidden(E_829,k9_relat_1('#skF_9',D_181))
      | ~ m1_subset_1(E_829,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_181)
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_76,c_56,c_7440])).

tff(c_7645,plain,(
    ! [D_832,E_833] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_7',D_832,'#skF_6',E_833)) = E_833
      | ~ r2_hidden(E_833,k9_relat_1('#skF_9',D_832))
      | ~ m1_subset_1(E_833,'#skF_7')
      | v1_xboole_0(D_832) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_538,c_7457])).

tff(c_7742,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6','#skF_10')) = '#skF_10'
    | ~ m1_subset_1('#skF_10','#skF_7')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_138,c_7645])).

tff(c_7835,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6','#skF_10')) = '#skF_10'
    | v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_7742])).

tff(c_7837,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_192,c_2252,c_7835])).

tff(c_7838,plain,(
    r2_hidden('#skF_3'('#skF_7','#skF_6','#skF_9'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_536])).

tff(c_7844,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_7838,c_2])).

tff(c_8762,plain,(
    ! [C_971,E_972,A_969,B_970,D_968] :
      ( r2_hidden('#skF_5'(D_968,A_969,B_970,C_971,E_972),B_970)
      | ~ r2_hidden(E_972,k7_relset_1(C_971,A_969,D_968,B_970))
      | ~ m1_subset_1(E_972,A_969)
      | ~ m1_subset_1(D_968,k1_zfmisc_1(k2_zfmisc_1(C_971,A_969)))
      | v1_xboole_0(C_971)
      | v1_xboole_0(B_970)
      | v1_xboole_0(A_969) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_8767,plain,(
    ! [B_970,E_972] :
      ( r2_hidden('#skF_5'('#skF_9','#skF_7',B_970,'#skF_6',E_972),B_970)
      | ~ r2_hidden(E_972,k7_relset_1('#skF_6','#skF_7','#skF_9',B_970))
      | ~ m1_subset_1(E_972,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(B_970)
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_52,c_8762])).

tff(c_8770,plain,(
    ! [B_970,E_972] :
      ( r2_hidden('#skF_5'('#skF_9','#skF_7',B_970,'#skF_6',E_972),B_970)
      | ~ r2_hidden(E_972,k9_relat_1('#skF_9',B_970))
      | ~ m1_subset_1(E_972,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(B_970)
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_8767])).

tff(c_8772,plain,(
    ! [B_973,E_974] :
      ( r2_hidden('#skF_5'('#skF_9','#skF_7',B_973,'#skF_6',E_974),B_973)
      | ~ r2_hidden(E_974,k9_relat_1('#skF_9',B_973))
      | ~ m1_subset_1(E_974,'#skF_7')
      | v1_xboole_0(B_973) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_7844,c_8770])).

tff(c_8865,plain,(
    ! [E_974] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6',E_974)) != '#skF_10'
      | ~ m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6',E_974),'#skF_6')
      | ~ r2_hidden(E_974,k9_relat_1('#skF_9','#skF_8'))
      | ~ m1_subset_1(E_974,'#skF_7')
      | v1_xboole_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_8772,c_48])).

tff(c_8939,plain,(
    ! [E_980] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6',E_980)) != '#skF_10'
      | ~ m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6',E_980),'#skF_6')
      | ~ r2_hidden(E_980,k9_relat_1('#skF_9','#skF_8'))
      | ~ m1_subset_1(E_980,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_192,c_8865])).

tff(c_8958,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6','#skF_10')) != '#skF_10'
    | ~ m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6','#skF_10'),'#skF_6')
    | ~ m1_subset_1('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_138,c_8939])).

tff(c_8979,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6','#skF_10')) != '#skF_10'
    | ~ m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6','#skF_10'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_8958])).

tff(c_8987,plain,(
    ~ m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6','#skF_10'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_8979])).

tff(c_8570,plain,(
    ! [C_940,E_941,A_938,B_939,D_937] :
      ( m1_subset_1('#skF_5'(D_937,A_938,B_939,C_940,E_941),C_940)
      | ~ r2_hidden(E_941,k7_relset_1(C_940,A_938,D_937,B_939))
      | ~ m1_subset_1(E_941,A_938)
      | ~ m1_subset_1(D_937,k1_zfmisc_1(k2_zfmisc_1(C_940,A_938)))
      | v1_xboole_0(C_940)
      | v1_xboole_0(B_939)
      | v1_xboole_0(A_938) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_8581,plain,(
    ! [D_181,E_941] :
      ( m1_subset_1('#skF_5'('#skF_9','#skF_7',D_181,'#skF_6',E_941),'#skF_6')
      | ~ r2_hidden(E_941,k9_relat_1('#skF_9',D_181))
      | ~ m1_subset_1(E_941,'#skF_7')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_181)
      | v1_xboole_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_8570])).

tff(c_8595,plain,(
    ! [D_181,E_941] :
      ( m1_subset_1('#skF_5'('#skF_9','#skF_7',D_181,'#skF_6',E_941),'#skF_6')
      | ~ r2_hidden(E_941,k9_relat_1('#skF_9',D_181))
      | ~ m1_subset_1(E_941,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_181)
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_8581])).

tff(c_8988,plain,(
    ! [D_981,E_982] :
      ( m1_subset_1('#skF_5'('#skF_9','#skF_7',D_981,'#skF_6',E_982),'#skF_6')
      | ~ r2_hidden(E_982,k9_relat_1('#skF_9',D_981))
      | ~ m1_subset_1(E_982,'#skF_7')
      | v1_xboole_0(D_981) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_7844,c_8595])).

tff(c_9011,plain,
    ( m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6','#skF_10'),'#skF_6')
    | ~ m1_subset_1('#skF_10','#skF_7')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_138,c_8988])).

tff(c_9034,plain,
    ( m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6','#skF_10'),'#skF_6')
    | v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_9011])).

tff(c_9036,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_192,c_8987,c_9034])).

tff(c_9037,plain,(
    k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6','#skF_10')) != '#skF_10' ),
    inference(splitRight,[status(thm)],[c_8979])).

tff(c_9043,plain,(
    ! [E_987,A_984,C_986,B_985,D_983] :
      ( r2_hidden(k4_tarski('#skF_5'(D_983,A_984,B_985,C_986,E_987),E_987),D_983)
      | ~ r2_hidden(E_987,k7_relset_1(C_986,A_984,D_983,B_985))
      | ~ m1_subset_1(E_987,A_984)
      | ~ m1_subset_1(D_983,k1_zfmisc_1(k2_zfmisc_1(C_986,A_984)))
      | v1_xboole_0(C_986)
      | v1_xboole_0(B_985)
      | v1_xboole_0(A_984) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_18939,plain,(
    ! [A_1837,D_1838,E_1840,B_1836,C_1839] :
      ( k1_funct_1(D_1838,'#skF_5'(D_1838,A_1837,B_1836,C_1839,E_1840)) = E_1840
      | ~ v1_funct_1(D_1838)
      | ~ v1_relat_1(D_1838)
      | ~ r2_hidden(E_1840,k7_relset_1(C_1839,A_1837,D_1838,B_1836))
      | ~ m1_subset_1(E_1840,A_1837)
      | ~ m1_subset_1(D_1838,k1_zfmisc_1(k2_zfmisc_1(C_1839,A_1837)))
      | v1_xboole_0(C_1839)
      | v1_xboole_0(B_1836)
      | v1_xboole_0(A_1837) ) ),
    inference(resolution,[status(thm)],[c_9043,c_20])).

tff(c_18959,plain,(
    ! [D_181,E_1840] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_7',D_181,'#skF_6',E_1840)) = E_1840
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(E_1840,k9_relat_1('#skF_9',D_181))
      | ~ m1_subset_1(E_1840,'#skF_7')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_181)
      | v1_xboole_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_18939])).

tff(c_18976,plain,(
    ! [D_181,E_1840] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_7',D_181,'#skF_6',E_1840)) = E_1840
      | ~ r2_hidden(E_1840,k9_relat_1('#skF_9',D_181))
      | ~ m1_subset_1(E_1840,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_181)
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_76,c_56,c_18959])).

tff(c_18981,plain,(
    ! [D_1841,E_1842] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_7',D_1841,'#skF_6',E_1842)) = E_1842
      | ~ r2_hidden(E_1842,k9_relat_1('#skF_9',D_1841))
      | ~ m1_subset_1(E_1842,'#skF_7')
      | v1_xboole_0(D_1841) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_7844,c_18976])).

tff(c_19062,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6','#skF_10')) = '#skF_10'
    | ~ m1_subset_1('#skF_10','#skF_7')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_138,c_18981])).

tff(c_19136,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6','#skF_10')) = '#skF_10'
    | v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_19062])).

tff(c_19138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_192,c_9037,c_19136])).

tff(c_19139,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_19369,plain,(
    ! [A_1902,C_1903] :
      ( r2_hidden(k4_tarski(A_1902,k1_funct_1(C_1903,A_1902)),C_1903)
      | ~ r2_hidden(A_1902,k1_relat_1(C_1903))
      | ~ v1_funct_1(C_1903)
      | ~ v1_relat_1(C_1903) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_19418,plain,(
    ! [C_1904,A_1905] :
      ( ~ v1_xboole_0(C_1904)
      | ~ r2_hidden(A_1905,k1_relat_1(C_1904))
      | ~ v1_funct_1(C_1904)
      | ~ v1_relat_1(C_1904) ) ),
    inference(resolution,[status(thm)],[c_19369,c_2])).

tff(c_19443,plain,(
    ! [C_1906] :
      ( ~ v1_xboole_0(C_1906)
      | ~ v1_funct_1(C_1906)
      | ~ v1_relat_1(C_1906)
      | v1_xboole_0(k1_relat_1(C_1906)) ) ),
    inference(resolution,[status(thm)],[c_4,c_19418])).

tff(c_19225,plain,(
    ! [A_1870,B_1871,C_1872,D_1873] :
      ( k7_relset_1(A_1870,B_1871,C_1872,D_1873) = k9_relat_1(C_1872,D_1873)
      | ~ m1_subset_1(C_1872,k1_zfmisc_1(k2_zfmisc_1(A_1870,B_1871))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_19228,plain,(
    ! [D_1873] : k7_relset_1('#skF_6','#skF_7','#skF_9',D_1873) = k9_relat_1('#skF_9',D_1873) ),
    inference(resolution,[status(thm)],[c_52,c_19225])).

tff(c_19235,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19228,c_50])).

tff(c_19229,plain,(
    ! [A_1874,B_1875,C_1876] :
      ( r2_hidden('#skF_2'(A_1874,B_1875,C_1876),k1_relat_1(C_1876))
      | ~ r2_hidden(A_1874,k9_relat_1(C_1876,B_1875))
      | ~ v1_relat_1(C_1876) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_19267,plain,(
    ! [C_1878,A_1879,B_1880] :
      ( ~ v1_xboole_0(k1_relat_1(C_1878))
      | ~ r2_hidden(A_1879,k9_relat_1(C_1878,B_1880))
      | ~ v1_relat_1(C_1878) ) ),
    inference(resolution,[status(thm)],[c_19229,c_2])).

tff(c_19270,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_19235,c_19267])).

tff(c_19285,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_19270])).

tff(c_19446,plain,
    ( ~ v1_xboole_0('#skF_9')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_19443,c_19285])).

tff(c_19450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_56,c_19139,c_19446])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:16:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.08/5.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.19/5.61  
% 12.19/5.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.19/5.61  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 12.19/5.61  
% 12.19/5.61  %Foreground sorts:
% 12.19/5.61  
% 12.19/5.61  
% 12.19/5.61  %Background operators:
% 12.19/5.61  
% 12.19/5.61  
% 12.19/5.61  %Foreground operators:
% 12.19/5.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.19/5.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.19/5.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.19/5.61  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 12.19/5.61  tff('#skF_1', type, '#skF_1': $i > $i).
% 12.19/5.61  tff('#skF_7', type, '#skF_7': $i).
% 12.19/5.61  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i) > $i).
% 12.19/5.61  tff('#skF_10', type, '#skF_10': $i).
% 12.19/5.61  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 12.19/5.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.19/5.61  tff('#skF_6', type, '#skF_6': $i).
% 12.19/5.61  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 12.19/5.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 12.19/5.61  tff('#skF_9', type, '#skF_9': $i).
% 12.19/5.61  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 12.19/5.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.19/5.61  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 12.19/5.61  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 12.19/5.61  tff('#skF_8', type, '#skF_8': $i).
% 12.19/5.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.19/5.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.19/5.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.19/5.61  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 12.19/5.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.19/5.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.19/5.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.19/5.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.19/5.61  
% 12.19/5.63  tff(f_144, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 12.19/5.63  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 12.19/5.63  tff(f_87, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 12.19/5.63  tff(f_54, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 12.19/5.63  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 12.19/5.63  tff(f_79, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 12.19/5.63  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 12.19/5.63  tff(f_75, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 12.19/5.63  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 12.19/5.63  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 12.19/5.63  tff(f_125, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k7_relset_1(C, A, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(F, E), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relset_1)).
% 12.19/5.63  tff(f_64, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 12.19/5.63  tff(c_52, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 12.19/5.63  tff(c_72, plain, (![C_154, A_155, B_156]: (v1_relat_1(C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 12.19/5.63  tff(c_76, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_52, c_72])).
% 12.19/5.63  tff(c_56, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_144])).
% 12.19/5.63  tff(c_133, plain, (![A_178, B_179, C_180, D_181]: (k7_relset_1(A_178, B_179, C_180, D_181)=k9_relat_1(C_180, D_181) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 12.19/5.63  tff(c_136, plain, (![D_181]: (k7_relset_1('#skF_6', '#skF_7', '#skF_9', D_181)=k9_relat_1('#skF_9', D_181))), inference(resolution, [status(thm)], [c_52, c_133])).
% 12.19/5.63  tff(c_50, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 12.19/5.63  tff(c_138, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_50])).
% 12.19/5.63  tff(c_123, plain, (![A_175, B_176, C_177]: (r2_hidden('#skF_2'(A_175, B_176, C_177), B_176) | ~r2_hidden(A_175, k9_relat_1(C_177, B_176)) | ~v1_relat_1(C_177))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.19/5.63  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.19/5.63  tff(c_174, plain, (![B_185, A_186, C_187]: (~v1_xboole_0(B_185) | ~r2_hidden(A_186, k9_relat_1(C_187, B_185)) | ~v1_relat_1(C_187))), inference(resolution, [status(thm)], [c_123, c_2])).
% 12.19/5.63  tff(c_177, plain, (~v1_xboole_0('#skF_8') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_138, c_174])).
% 12.19/5.63  tff(c_192, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_177])).
% 12.19/5.63  tff(c_256, plain, (![A_207, B_208, C_209, D_210]: (m1_subset_1(k7_relset_1(A_207, B_208, C_209, D_210), k1_zfmisc_1(B_208)) | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.19/5.63  tff(c_276, plain, (![D_181]: (m1_subset_1(k9_relat_1('#skF_9', D_181), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_136, c_256])).
% 12.19/5.63  tff(c_284, plain, (![D_211]: (m1_subset_1(k9_relat_1('#skF_9', D_211), k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_276])).
% 12.19/5.63  tff(c_8, plain, (![A_7, C_9, B_8]: (m1_subset_1(A_7, C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(C_9)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.19/5.63  tff(c_326, plain, (![A_215, D_216]: (m1_subset_1(A_215, '#skF_7') | ~r2_hidden(A_215, k9_relat_1('#skF_9', D_216)))), inference(resolution, [status(thm)], [c_284, c_8])).
% 12.19/5.63  tff(c_347, plain, (m1_subset_1('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_138, c_326])).
% 12.19/5.63  tff(c_93, plain, (![C_162, B_163, A_164]: (v1_xboole_0(C_162) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(B_163, A_164))) | ~v1_xboole_0(A_164))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.19/5.63  tff(c_97, plain, (v1_xboole_0('#skF_9') | ~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_52, c_93])).
% 12.19/5.63  tff(c_98, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_97])).
% 12.19/5.63  tff(c_99, plain, (![A_165, B_166, C_167]: (k1_relset_1(A_165, B_166, C_167)=k1_relat_1(C_167) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 12.19/5.63  tff(c_103, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_52, c_99])).
% 12.19/5.63  tff(c_528, plain, (![A_241, B_242, C_243]: (r2_hidden('#skF_3'(A_241, B_242, C_243), B_242) | k1_relset_1(B_242, A_241, C_243)=B_242 | ~m1_subset_1(C_243, k1_zfmisc_1(k2_zfmisc_1(B_242, A_241))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 12.19/5.63  tff(c_533, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_6', '#skF_9'), '#skF_6') | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6'), inference(resolution, [status(thm)], [c_52, c_528])).
% 12.19/5.63  tff(c_536, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_6', '#skF_9'), '#skF_6') | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_103, c_533])).
% 12.19/5.63  tff(c_537, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_536])).
% 12.19/5.63  tff(c_204, plain, (![A_190, B_191, C_192]: (r2_hidden('#skF_2'(A_190, B_191, C_192), k1_relat_1(C_192)) | ~r2_hidden(A_190, k9_relat_1(C_192, B_191)) | ~v1_relat_1(C_192))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.19/5.63  tff(c_209, plain, (![C_193, A_194, B_195]: (~v1_xboole_0(k1_relat_1(C_193)) | ~r2_hidden(A_194, k9_relat_1(C_193, B_195)) | ~v1_relat_1(C_193))), inference(resolution, [status(thm)], [c_204, c_2])).
% 12.19/5.63  tff(c_212, plain, (~v1_xboole_0(k1_relat_1('#skF_9')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_138, c_209])).
% 12.19/5.63  tff(c_227, plain, (~v1_xboole_0(k1_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_212])).
% 12.19/5.63  tff(c_538, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_537, c_227])).
% 12.19/5.63  tff(c_1396, plain, (![B_357, D_355, A_356, C_358, E_359]: (m1_subset_1('#skF_5'(D_355, A_356, B_357, C_358, E_359), C_358) | ~r2_hidden(E_359, k7_relset_1(C_358, A_356, D_355, B_357)) | ~m1_subset_1(E_359, A_356) | ~m1_subset_1(D_355, k1_zfmisc_1(k2_zfmisc_1(C_358, A_356))) | v1_xboole_0(C_358) | v1_xboole_0(B_357) | v1_xboole_0(A_356))), inference(cnfTransformation, [status(thm)], [f_125])).
% 12.19/5.63  tff(c_1407, plain, (![D_181, E_359]: (m1_subset_1('#skF_5'('#skF_9', '#skF_7', D_181, '#skF_6', E_359), '#skF_6') | ~r2_hidden(E_359, k9_relat_1('#skF_9', D_181)) | ~m1_subset_1(E_359, '#skF_7') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | v1_xboole_0('#skF_6') | v1_xboole_0(D_181) | v1_xboole_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_136, c_1396])).
% 12.19/5.63  tff(c_1421, plain, (![D_181, E_359]: (m1_subset_1('#skF_5'('#skF_9', '#skF_7', D_181, '#skF_6', E_359), '#skF_6') | ~r2_hidden(E_359, k9_relat_1('#skF_9', D_181)) | ~m1_subset_1(E_359, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(D_181) | v1_xboole_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1407])).
% 12.19/5.63  tff(c_1546, plain, (![D_380, E_381]: (m1_subset_1('#skF_5'('#skF_9', '#skF_7', D_380, '#skF_6', E_381), '#skF_6') | ~r2_hidden(E_381, k9_relat_1('#skF_9', D_380)) | ~m1_subset_1(E_381, '#skF_7') | v1_xboole_0(D_380))), inference(negUnitSimplification, [status(thm)], [c_98, c_538, c_1421])).
% 12.19/5.63  tff(c_1565, plain, (m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', '#skF_10'), '#skF_6') | ~m1_subset_1('#skF_10', '#skF_7') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_138, c_1546])).
% 12.19/5.63  tff(c_1587, plain, (m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', '#skF_10'), '#skF_6') | v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_347, c_1565])).
% 12.19/5.63  tff(c_1588, plain, (m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', '#skF_10'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_192, c_1587])).
% 12.19/5.63  tff(c_1592, plain, (![A_383, E_386, D_382, C_385, B_384]: (r2_hidden('#skF_5'(D_382, A_383, B_384, C_385, E_386), B_384) | ~r2_hidden(E_386, k7_relset_1(C_385, A_383, D_382, B_384)) | ~m1_subset_1(E_386, A_383) | ~m1_subset_1(D_382, k1_zfmisc_1(k2_zfmisc_1(C_385, A_383))) | v1_xboole_0(C_385) | v1_xboole_0(B_384) | v1_xboole_0(A_383))), inference(cnfTransformation, [status(thm)], [f_125])).
% 12.19/5.63  tff(c_1597, plain, (![B_384, E_386]: (r2_hidden('#skF_5'('#skF_9', '#skF_7', B_384, '#skF_6', E_386), B_384) | ~r2_hidden(E_386, k7_relset_1('#skF_6', '#skF_7', '#skF_9', B_384)) | ~m1_subset_1(E_386, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(B_384) | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_52, c_1592])).
% 12.19/5.63  tff(c_1600, plain, (![B_384, E_386]: (r2_hidden('#skF_5'('#skF_9', '#skF_7', B_384, '#skF_6', E_386), B_384) | ~r2_hidden(E_386, k9_relat_1('#skF_9', B_384)) | ~m1_subset_1(E_386, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(B_384) | v1_xboole_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_1597])).
% 12.19/5.63  tff(c_1608, plain, (![B_390, E_391]: (r2_hidden('#skF_5'('#skF_9', '#skF_7', B_390, '#skF_6', E_391), B_390) | ~r2_hidden(E_391, k9_relat_1('#skF_9', B_390)) | ~m1_subset_1(E_391, '#skF_7') | v1_xboole_0(B_390))), inference(negUnitSimplification, [status(thm)], [c_98, c_538, c_1600])).
% 12.19/5.63  tff(c_48, plain, (![F_148]: (k1_funct_1('#skF_9', F_148)!='#skF_10' | ~r2_hidden(F_148, '#skF_8') | ~m1_subset_1(F_148, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 12.19/5.63  tff(c_1709, plain, (![E_391]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', E_391))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', E_391), '#skF_6') | ~r2_hidden(E_391, k9_relat_1('#skF_9', '#skF_8')) | ~m1_subset_1(E_391, '#skF_7') | v1_xboole_0('#skF_8'))), inference(resolution, [status(thm)], [c_1608, c_48])).
% 12.19/5.63  tff(c_2207, plain, (![E_450]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', E_450))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', E_450), '#skF_6') | ~r2_hidden(E_450, k9_relat_1('#skF_9', '#skF_8')) | ~m1_subset_1(E_450, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_192, c_1709])).
% 12.19/5.63  tff(c_2230, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', '#skF_10'))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', '#skF_10'), '#skF_6') | ~m1_subset_1('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_138, c_2207])).
% 12.19/5.63  tff(c_2252, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', '#skF_10'))!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_347, c_1588, c_2230])).
% 12.19/5.63  tff(c_1827, plain, (![A_409, B_410, D_408, C_411, E_412]: (r2_hidden(k4_tarski('#skF_5'(D_408, A_409, B_410, C_411, E_412), E_412), D_408) | ~r2_hidden(E_412, k7_relset_1(C_411, A_409, D_408, B_410)) | ~m1_subset_1(E_412, A_409) | ~m1_subset_1(D_408, k1_zfmisc_1(k2_zfmisc_1(C_411, A_409))) | v1_xboole_0(C_411) | v1_xboole_0(B_410) | v1_xboole_0(A_409))), inference(cnfTransformation, [status(thm)], [f_125])).
% 12.19/5.63  tff(c_20, plain, (![C_18, A_16, B_17]: (k1_funct_1(C_18, A_16)=B_17 | ~r2_hidden(k4_tarski(A_16, B_17), C_18) | ~v1_funct_1(C_18) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.19/5.63  tff(c_7420, plain, (![E_829, B_826, D_825, A_827, C_828]: (k1_funct_1(D_825, '#skF_5'(D_825, A_827, B_826, C_828, E_829))=E_829 | ~v1_funct_1(D_825) | ~v1_relat_1(D_825) | ~r2_hidden(E_829, k7_relset_1(C_828, A_827, D_825, B_826)) | ~m1_subset_1(E_829, A_827) | ~m1_subset_1(D_825, k1_zfmisc_1(k2_zfmisc_1(C_828, A_827))) | v1_xboole_0(C_828) | v1_xboole_0(B_826) | v1_xboole_0(A_827))), inference(resolution, [status(thm)], [c_1827, c_20])).
% 12.19/5.63  tff(c_7440, plain, (![D_181, E_829]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_7', D_181, '#skF_6', E_829))=E_829 | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(E_829, k9_relat_1('#skF_9', D_181)) | ~m1_subset_1(E_829, '#skF_7') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | v1_xboole_0('#skF_6') | v1_xboole_0(D_181) | v1_xboole_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_136, c_7420])).
% 12.19/5.63  tff(c_7457, plain, (![D_181, E_829]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_7', D_181, '#skF_6', E_829))=E_829 | ~r2_hidden(E_829, k9_relat_1('#skF_9', D_181)) | ~m1_subset_1(E_829, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(D_181) | v1_xboole_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_76, c_56, c_7440])).
% 12.19/5.63  tff(c_7645, plain, (![D_832, E_833]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_7', D_832, '#skF_6', E_833))=E_833 | ~r2_hidden(E_833, k9_relat_1('#skF_9', D_832)) | ~m1_subset_1(E_833, '#skF_7') | v1_xboole_0(D_832))), inference(negUnitSimplification, [status(thm)], [c_98, c_538, c_7457])).
% 12.19/5.63  tff(c_7742, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', '#skF_10'))='#skF_10' | ~m1_subset_1('#skF_10', '#skF_7') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_138, c_7645])).
% 12.19/5.63  tff(c_7835, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', '#skF_10'))='#skF_10' | v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_347, c_7742])).
% 12.19/5.63  tff(c_7837, plain, $false, inference(negUnitSimplification, [status(thm)], [c_192, c_2252, c_7835])).
% 12.19/5.63  tff(c_7838, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_6', '#skF_9'), '#skF_6')), inference(splitRight, [status(thm)], [c_536])).
% 12.19/5.63  tff(c_7844, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_7838, c_2])).
% 12.19/5.63  tff(c_8762, plain, (![C_971, E_972, A_969, B_970, D_968]: (r2_hidden('#skF_5'(D_968, A_969, B_970, C_971, E_972), B_970) | ~r2_hidden(E_972, k7_relset_1(C_971, A_969, D_968, B_970)) | ~m1_subset_1(E_972, A_969) | ~m1_subset_1(D_968, k1_zfmisc_1(k2_zfmisc_1(C_971, A_969))) | v1_xboole_0(C_971) | v1_xboole_0(B_970) | v1_xboole_0(A_969))), inference(cnfTransformation, [status(thm)], [f_125])).
% 12.19/5.63  tff(c_8767, plain, (![B_970, E_972]: (r2_hidden('#skF_5'('#skF_9', '#skF_7', B_970, '#skF_6', E_972), B_970) | ~r2_hidden(E_972, k7_relset_1('#skF_6', '#skF_7', '#skF_9', B_970)) | ~m1_subset_1(E_972, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(B_970) | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_52, c_8762])).
% 12.19/5.63  tff(c_8770, plain, (![B_970, E_972]: (r2_hidden('#skF_5'('#skF_9', '#skF_7', B_970, '#skF_6', E_972), B_970) | ~r2_hidden(E_972, k9_relat_1('#skF_9', B_970)) | ~m1_subset_1(E_972, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(B_970) | v1_xboole_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_8767])).
% 12.19/5.63  tff(c_8772, plain, (![B_973, E_974]: (r2_hidden('#skF_5'('#skF_9', '#skF_7', B_973, '#skF_6', E_974), B_973) | ~r2_hidden(E_974, k9_relat_1('#skF_9', B_973)) | ~m1_subset_1(E_974, '#skF_7') | v1_xboole_0(B_973))), inference(negUnitSimplification, [status(thm)], [c_98, c_7844, c_8770])).
% 12.19/5.63  tff(c_8865, plain, (![E_974]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', E_974))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', E_974), '#skF_6') | ~r2_hidden(E_974, k9_relat_1('#skF_9', '#skF_8')) | ~m1_subset_1(E_974, '#skF_7') | v1_xboole_0('#skF_8'))), inference(resolution, [status(thm)], [c_8772, c_48])).
% 12.19/5.63  tff(c_8939, plain, (![E_980]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', E_980))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', E_980), '#skF_6') | ~r2_hidden(E_980, k9_relat_1('#skF_9', '#skF_8')) | ~m1_subset_1(E_980, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_192, c_8865])).
% 12.19/5.63  tff(c_8958, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', '#skF_10'))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', '#skF_10'), '#skF_6') | ~m1_subset_1('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_138, c_8939])).
% 12.19/5.63  tff(c_8979, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', '#skF_10'))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', '#skF_10'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_347, c_8958])).
% 12.19/5.63  tff(c_8987, plain, (~m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', '#skF_10'), '#skF_6')), inference(splitLeft, [status(thm)], [c_8979])).
% 12.19/5.63  tff(c_8570, plain, (![C_940, E_941, A_938, B_939, D_937]: (m1_subset_1('#skF_5'(D_937, A_938, B_939, C_940, E_941), C_940) | ~r2_hidden(E_941, k7_relset_1(C_940, A_938, D_937, B_939)) | ~m1_subset_1(E_941, A_938) | ~m1_subset_1(D_937, k1_zfmisc_1(k2_zfmisc_1(C_940, A_938))) | v1_xboole_0(C_940) | v1_xboole_0(B_939) | v1_xboole_0(A_938))), inference(cnfTransformation, [status(thm)], [f_125])).
% 12.19/5.63  tff(c_8581, plain, (![D_181, E_941]: (m1_subset_1('#skF_5'('#skF_9', '#skF_7', D_181, '#skF_6', E_941), '#skF_6') | ~r2_hidden(E_941, k9_relat_1('#skF_9', D_181)) | ~m1_subset_1(E_941, '#skF_7') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | v1_xboole_0('#skF_6') | v1_xboole_0(D_181) | v1_xboole_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_136, c_8570])).
% 12.19/5.63  tff(c_8595, plain, (![D_181, E_941]: (m1_subset_1('#skF_5'('#skF_9', '#skF_7', D_181, '#skF_6', E_941), '#skF_6') | ~r2_hidden(E_941, k9_relat_1('#skF_9', D_181)) | ~m1_subset_1(E_941, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(D_181) | v1_xboole_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_8581])).
% 12.19/5.63  tff(c_8988, plain, (![D_981, E_982]: (m1_subset_1('#skF_5'('#skF_9', '#skF_7', D_981, '#skF_6', E_982), '#skF_6') | ~r2_hidden(E_982, k9_relat_1('#skF_9', D_981)) | ~m1_subset_1(E_982, '#skF_7') | v1_xboole_0(D_981))), inference(negUnitSimplification, [status(thm)], [c_98, c_7844, c_8595])).
% 12.19/5.63  tff(c_9011, plain, (m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', '#skF_10'), '#skF_6') | ~m1_subset_1('#skF_10', '#skF_7') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_138, c_8988])).
% 12.19/5.63  tff(c_9034, plain, (m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', '#skF_10'), '#skF_6') | v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_347, c_9011])).
% 12.19/5.63  tff(c_9036, plain, $false, inference(negUnitSimplification, [status(thm)], [c_192, c_8987, c_9034])).
% 12.19/5.63  tff(c_9037, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', '#skF_10'))!='#skF_10'), inference(splitRight, [status(thm)], [c_8979])).
% 12.19/5.63  tff(c_9043, plain, (![E_987, A_984, C_986, B_985, D_983]: (r2_hidden(k4_tarski('#skF_5'(D_983, A_984, B_985, C_986, E_987), E_987), D_983) | ~r2_hidden(E_987, k7_relset_1(C_986, A_984, D_983, B_985)) | ~m1_subset_1(E_987, A_984) | ~m1_subset_1(D_983, k1_zfmisc_1(k2_zfmisc_1(C_986, A_984))) | v1_xboole_0(C_986) | v1_xboole_0(B_985) | v1_xboole_0(A_984))), inference(cnfTransformation, [status(thm)], [f_125])).
% 12.19/5.63  tff(c_18939, plain, (![A_1837, D_1838, E_1840, B_1836, C_1839]: (k1_funct_1(D_1838, '#skF_5'(D_1838, A_1837, B_1836, C_1839, E_1840))=E_1840 | ~v1_funct_1(D_1838) | ~v1_relat_1(D_1838) | ~r2_hidden(E_1840, k7_relset_1(C_1839, A_1837, D_1838, B_1836)) | ~m1_subset_1(E_1840, A_1837) | ~m1_subset_1(D_1838, k1_zfmisc_1(k2_zfmisc_1(C_1839, A_1837))) | v1_xboole_0(C_1839) | v1_xboole_0(B_1836) | v1_xboole_0(A_1837))), inference(resolution, [status(thm)], [c_9043, c_20])).
% 12.19/5.63  tff(c_18959, plain, (![D_181, E_1840]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_7', D_181, '#skF_6', E_1840))=E_1840 | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(E_1840, k9_relat_1('#skF_9', D_181)) | ~m1_subset_1(E_1840, '#skF_7') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | v1_xboole_0('#skF_6') | v1_xboole_0(D_181) | v1_xboole_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_136, c_18939])).
% 12.19/5.63  tff(c_18976, plain, (![D_181, E_1840]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_7', D_181, '#skF_6', E_1840))=E_1840 | ~r2_hidden(E_1840, k9_relat_1('#skF_9', D_181)) | ~m1_subset_1(E_1840, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(D_181) | v1_xboole_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_76, c_56, c_18959])).
% 12.19/5.63  tff(c_18981, plain, (![D_1841, E_1842]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_7', D_1841, '#skF_6', E_1842))=E_1842 | ~r2_hidden(E_1842, k9_relat_1('#skF_9', D_1841)) | ~m1_subset_1(E_1842, '#skF_7') | v1_xboole_0(D_1841))), inference(negUnitSimplification, [status(thm)], [c_98, c_7844, c_18976])).
% 12.19/5.63  tff(c_19062, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', '#skF_10'))='#skF_10' | ~m1_subset_1('#skF_10', '#skF_7') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_138, c_18981])).
% 12.19/5.63  tff(c_19136, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', '#skF_10'))='#skF_10' | v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_347, c_19062])).
% 12.19/5.63  tff(c_19138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_192, c_9037, c_19136])).
% 12.19/5.63  tff(c_19139, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_97])).
% 12.19/5.63  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.19/5.63  tff(c_19369, plain, (![A_1902, C_1903]: (r2_hidden(k4_tarski(A_1902, k1_funct_1(C_1903, A_1902)), C_1903) | ~r2_hidden(A_1902, k1_relat_1(C_1903)) | ~v1_funct_1(C_1903) | ~v1_relat_1(C_1903))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.19/5.63  tff(c_19418, plain, (![C_1904, A_1905]: (~v1_xboole_0(C_1904) | ~r2_hidden(A_1905, k1_relat_1(C_1904)) | ~v1_funct_1(C_1904) | ~v1_relat_1(C_1904))), inference(resolution, [status(thm)], [c_19369, c_2])).
% 12.19/5.63  tff(c_19443, plain, (![C_1906]: (~v1_xboole_0(C_1906) | ~v1_funct_1(C_1906) | ~v1_relat_1(C_1906) | v1_xboole_0(k1_relat_1(C_1906)))), inference(resolution, [status(thm)], [c_4, c_19418])).
% 12.19/5.63  tff(c_19225, plain, (![A_1870, B_1871, C_1872, D_1873]: (k7_relset_1(A_1870, B_1871, C_1872, D_1873)=k9_relat_1(C_1872, D_1873) | ~m1_subset_1(C_1872, k1_zfmisc_1(k2_zfmisc_1(A_1870, B_1871))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 12.19/5.63  tff(c_19228, plain, (![D_1873]: (k7_relset_1('#skF_6', '#skF_7', '#skF_9', D_1873)=k9_relat_1('#skF_9', D_1873))), inference(resolution, [status(thm)], [c_52, c_19225])).
% 12.19/5.63  tff(c_19235, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_19228, c_50])).
% 12.19/5.63  tff(c_19229, plain, (![A_1874, B_1875, C_1876]: (r2_hidden('#skF_2'(A_1874, B_1875, C_1876), k1_relat_1(C_1876)) | ~r2_hidden(A_1874, k9_relat_1(C_1876, B_1875)) | ~v1_relat_1(C_1876))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.19/5.63  tff(c_19267, plain, (![C_1878, A_1879, B_1880]: (~v1_xboole_0(k1_relat_1(C_1878)) | ~r2_hidden(A_1879, k9_relat_1(C_1878, B_1880)) | ~v1_relat_1(C_1878))), inference(resolution, [status(thm)], [c_19229, c_2])).
% 12.19/5.63  tff(c_19270, plain, (~v1_xboole_0(k1_relat_1('#skF_9')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_19235, c_19267])).
% 12.19/5.63  tff(c_19285, plain, (~v1_xboole_0(k1_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_19270])).
% 12.19/5.63  tff(c_19446, plain, (~v1_xboole_0('#skF_9') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_19443, c_19285])).
% 12.19/5.63  tff(c_19450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_56, c_19139, c_19446])).
% 12.19/5.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.19/5.63  
% 12.19/5.63  Inference rules
% 12.19/5.63  ----------------------
% 12.19/5.63  #Ref     : 0
% 12.19/5.63  #Sup     : 4201
% 12.19/5.63  #Fact    : 0
% 12.19/5.63  #Define  : 0
% 12.19/5.63  #Split   : 46
% 12.19/5.63  #Chain   : 0
% 12.19/5.63  #Close   : 0
% 12.19/5.63  
% 12.19/5.63  Ordering : KBO
% 12.19/5.63  
% 12.19/5.63  Simplification rules
% 12.19/5.63  ----------------------
% 12.19/5.63  #Subsume      : 1256
% 12.19/5.63  #Demod        : 993
% 12.19/5.63  #Tautology    : 174
% 12.19/5.63  #SimpNegUnit  : 291
% 12.19/5.63  #BackRed      : 6
% 12.19/5.63  
% 12.19/5.63  #Partial instantiations: 0
% 12.19/5.63  #Strategies tried      : 1
% 12.19/5.63  
% 12.19/5.63  Timing (in seconds)
% 12.19/5.63  ----------------------
% 12.19/5.63  Preprocessing        : 0.36
% 12.19/5.63  Parsing              : 0.18
% 12.19/5.63  CNF conversion       : 0.04
% 12.19/5.63  Main loop            : 4.47
% 12.19/5.63  Inferencing          : 1.11
% 12.19/5.63  Reduction            : 0.90
% 12.19/5.63  Demodulation         : 0.63
% 12.19/5.63  BG Simplification    : 0.11
% 12.19/5.63  Subsumption          : 2.07
% 12.19/5.64  Abstraction          : 0.18
% 12.19/5.64  MUC search           : 0.00
% 12.19/5.64  Cooper               : 0.00
% 12.19/5.64  Total                : 4.88
% 12.19/5.64  Index Insertion      : 0.00
% 12.19/5.64  Index Deletion       : 0.00
% 12.19/5.64  Index Matching       : 0.00
% 12.19/5.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
