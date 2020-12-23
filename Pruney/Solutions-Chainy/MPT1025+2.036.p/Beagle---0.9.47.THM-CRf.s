%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:35 EST 2020

% Result     : Theorem 9.58s
% Output     : CNFRefutation 9.78s
% Verified   : 
% Statistics : Number of formulae       :  135 (1020 expanded)
%              Number of leaves         :   40 ( 358 expanded)
%              Depth                    :   13
%              Number of atoms          :  349 (2747 expanded)
%              Number of equality atoms :   37 ( 404 expanded)
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

tff(f_53,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_143,negated_conjecture,(
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

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_124,axiom,(
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

tff(f_74,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_12,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_52,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_68,plain,(
    ! [B_153,A_154] :
      ( v1_relat_1(B_153)
      | ~ m1_subset_1(B_153,k1_zfmisc_1(A_154))
      | ~ v1_relat_1(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_71,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_52,c_68])).

tff(c_74,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_71])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_104,plain,(
    ! [A_171,B_172,C_173] :
      ( r2_hidden('#skF_2'(A_171,B_172,C_173),B_172)
      | ~ r2_hidden(A_171,k9_relat_1(C_173,B_172))
      | ~ v1_relat_1(C_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_114,plain,(
    ! [B_174,A_175,C_176] :
      ( ~ v1_xboole_0(B_174)
      | ~ r2_hidden(A_175,k9_relat_1(C_176,B_174))
      | ~ v1_relat_1(C_176) ) ),
    inference(resolution,[status(thm)],[c_104,c_2])).

tff(c_124,plain,(
    ! [B_174,C_176] :
      ( ~ v1_xboole_0(B_174)
      | ~ v1_relat_1(C_176)
      | v1_xboole_0(k9_relat_1(C_176,B_174)) ) ),
    inference(resolution,[status(thm)],[c_4,c_114])).

tff(c_126,plain,(
    ! [A_179,B_180,C_181,D_182] :
      ( k7_relset_1(A_179,B_180,C_181,D_182) = k9_relat_1(C_181,D_182)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_129,plain,(
    ! [D_182] : k7_relset_1('#skF_6','#skF_7','#skF_9',D_182) = k9_relat_1('#skF_9',D_182) ),
    inference(resolution,[status(thm)],[c_52,c_126])).

tff(c_50,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_67,plain,(
    ~ v1_xboole_0(k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(resolution,[status(thm)],[c_50,c_2])).

tff(c_130,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_67])).

tff(c_143,plain,
    ( ~ v1_xboole_0('#skF_8')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_124,c_130])).

tff(c_146,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_143])).

tff(c_131,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_50])).

tff(c_169,plain,(
    ! [A_191,B_192,C_193,D_194] :
      ( m1_subset_1(k7_relset_1(A_191,B_192,C_193,D_194),k1_zfmisc_1(B_192))
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(A_191,B_192))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_187,plain,(
    ! [D_182] :
      ( m1_subset_1(k9_relat_1('#skF_9',D_182),k1_zfmisc_1('#skF_7'))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_169])).

tff(c_195,plain,(
    ! [D_195] : m1_subset_1(k9_relat_1('#skF_9',D_195),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_187])).

tff(c_8,plain,(
    ! [A_8,C_10,B_9] :
      ( m1_subset_1(A_8,C_10)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(C_10))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_231,plain,(
    ! [A_201,D_202] :
      ( m1_subset_1(A_201,'#skF_7')
      | ~ r2_hidden(A_201,k9_relat_1('#skF_9',D_202)) ) ),
    inference(resolution,[status(thm)],[c_195,c_8])).

tff(c_243,plain,(
    m1_subset_1('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_131,c_231])).

tff(c_6,plain,(
    ! [B_7,A_5] :
      ( v1_xboole_0(B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_5))
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_205,plain,(
    ! [D_195] :
      ( v1_xboole_0(k9_relat_1('#skF_9',D_195))
      | ~ v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_195,c_6])).

tff(c_207,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_205])).

tff(c_91,plain,(
    ! [A_161,B_162,C_163] :
      ( k1_relset_1(A_161,B_162,C_163) = k1_relat_1(C_163)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_95,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_52,c_91])).

tff(c_522,plain,(
    ! [A_246,B_247,C_248] :
      ( r2_hidden('#skF_3'(A_246,B_247,C_248),B_247)
      | k1_relset_1(B_247,A_246,C_248) = B_247
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(B_247,A_246))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_527,plain,
    ( r2_hidden('#skF_3'('#skF_7','#skF_6','#skF_9'),'#skF_6')
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_52,c_522])).

tff(c_530,plain,
    ( r2_hidden('#skF_3'('#skF_7','#skF_6','#skF_9'),'#skF_6')
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_527])).

tff(c_531,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_530])).

tff(c_208,plain,(
    ! [A_196,B_197,C_198] :
      ( r2_hidden('#skF_2'(A_196,B_197,C_198),k1_relat_1(C_198))
      | ~ r2_hidden(A_196,k9_relat_1(C_198,B_197))
      | ~ v1_relat_1(C_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_246,plain,(
    ! [C_203,A_204,B_205] :
      ( ~ v1_xboole_0(k1_relat_1(C_203))
      | ~ r2_hidden(A_204,k9_relat_1(C_203,B_205))
      | ~ v1_relat_1(C_203) ) ),
    inference(resolution,[status(thm)],[c_208,c_2])).

tff(c_249,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_131,c_246])).

tff(c_260,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_249])).

tff(c_532,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_531,c_260])).

tff(c_1301,plain,(
    ! [D_365,C_367,B_363,E_364,A_366] :
      ( r2_hidden('#skF_5'(B_363,E_364,D_365,A_366,C_367),B_363)
      | ~ r2_hidden(E_364,k7_relset_1(C_367,A_366,D_365,B_363))
      | ~ m1_subset_1(E_364,A_366)
      | ~ m1_subset_1(D_365,k1_zfmisc_1(k2_zfmisc_1(C_367,A_366)))
      | v1_xboole_0(C_367)
      | v1_xboole_0(B_363)
      | v1_xboole_0(A_366) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1306,plain,(
    ! [B_363,E_364] :
      ( r2_hidden('#skF_5'(B_363,E_364,'#skF_9','#skF_7','#skF_6'),B_363)
      | ~ r2_hidden(E_364,k7_relset_1('#skF_6','#skF_7','#skF_9',B_363))
      | ~ m1_subset_1(E_364,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(B_363)
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_52,c_1301])).

tff(c_1309,plain,(
    ! [B_363,E_364] :
      ( r2_hidden('#skF_5'(B_363,E_364,'#skF_9','#skF_7','#skF_6'),B_363)
      | ~ r2_hidden(E_364,k9_relat_1('#skF_9',B_363))
      | ~ m1_subset_1(E_364,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(B_363)
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_1306])).

tff(c_1311,plain,(
    ! [B_368,E_369] :
      ( r2_hidden('#skF_5'(B_368,E_369,'#skF_9','#skF_7','#skF_6'),B_368)
      | ~ r2_hidden(E_369,k9_relat_1('#skF_9',B_368))
      | ~ m1_subset_1(E_369,'#skF_7')
      | v1_xboole_0(B_368) ) ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_532,c_1309])).

tff(c_48,plain,(
    ! [F_147] :
      ( k1_funct_1('#skF_9',F_147) != '#skF_10'
      | ~ r2_hidden(F_147,'#skF_8')
      | ~ m1_subset_1(F_147,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1404,plain,(
    ! [E_369] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_8',E_369,'#skF_9','#skF_7','#skF_6')) != '#skF_10'
      | ~ m1_subset_1('#skF_5'('#skF_8',E_369,'#skF_9','#skF_7','#skF_6'),'#skF_6')
      | ~ r2_hidden(E_369,k9_relat_1('#skF_9','#skF_8'))
      | ~ m1_subset_1(E_369,'#skF_7')
      | v1_xboole_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1311,c_48])).

tff(c_1473,plain,(
    ! [E_375] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_8',E_375,'#skF_9','#skF_7','#skF_6')) != '#skF_10'
      | ~ m1_subset_1('#skF_5'('#skF_8',E_375,'#skF_9','#skF_7','#skF_6'),'#skF_6')
      | ~ r2_hidden(E_375,k9_relat_1('#skF_9','#skF_8'))
      | ~ m1_subset_1(E_375,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_1404])).

tff(c_1492,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_8','#skF_10','#skF_9','#skF_7','#skF_6')) != '#skF_10'
    | ~ m1_subset_1('#skF_5'('#skF_8','#skF_10','#skF_9','#skF_7','#skF_6'),'#skF_6')
    | ~ m1_subset_1('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_131,c_1473])).

tff(c_1509,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_8','#skF_10','#skF_9','#skF_7','#skF_6')) != '#skF_10'
    | ~ m1_subset_1('#skF_5'('#skF_8','#skF_10','#skF_9','#skF_7','#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_1492])).

tff(c_1514,plain,(
    ~ m1_subset_1('#skF_5'('#skF_8','#skF_10','#skF_9','#skF_7','#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1509])).

tff(c_1132,plain,(
    ! [D_335,C_337,A_336,E_334,B_333] :
      ( m1_subset_1('#skF_5'(B_333,E_334,D_335,A_336,C_337),C_337)
      | ~ r2_hidden(E_334,k7_relset_1(C_337,A_336,D_335,B_333))
      | ~ m1_subset_1(E_334,A_336)
      | ~ m1_subset_1(D_335,k1_zfmisc_1(k2_zfmisc_1(C_337,A_336)))
      | v1_xboole_0(C_337)
      | v1_xboole_0(B_333)
      | v1_xboole_0(A_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1143,plain,(
    ! [D_182,E_334] :
      ( m1_subset_1('#skF_5'(D_182,E_334,'#skF_9','#skF_7','#skF_6'),'#skF_6')
      | ~ r2_hidden(E_334,k9_relat_1('#skF_9',D_182))
      | ~ m1_subset_1(E_334,'#skF_7')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_182)
      | v1_xboole_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_1132])).

tff(c_1154,plain,(
    ! [D_182,E_334] :
      ( m1_subset_1('#skF_5'(D_182,E_334,'#skF_9','#skF_7','#skF_6'),'#skF_6')
      | ~ r2_hidden(E_334,k9_relat_1('#skF_9',D_182))
      | ~ m1_subset_1(E_334,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_182)
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1143])).

tff(c_1515,plain,(
    ! [D_376,E_377] :
      ( m1_subset_1('#skF_5'(D_376,E_377,'#skF_9','#skF_7','#skF_6'),'#skF_6')
      | ~ r2_hidden(E_377,k9_relat_1('#skF_9',D_376))
      | ~ m1_subset_1(E_377,'#skF_7')
      | v1_xboole_0(D_376) ) ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_532,c_1154])).

tff(c_1538,plain,
    ( m1_subset_1('#skF_5'('#skF_8','#skF_10','#skF_9','#skF_7','#skF_6'),'#skF_6')
    | ~ m1_subset_1('#skF_10','#skF_7')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_131,c_1515])).

tff(c_1557,plain,
    ( m1_subset_1('#skF_5'('#skF_8','#skF_10','#skF_9','#skF_7','#skF_6'),'#skF_6')
    | v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_1538])).

tff(c_1559,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_1514,c_1557])).

tff(c_1560,plain,(
    k1_funct_1('#skF_9','#skF_5'('#skF_8','#skF_10','#skF_9','#skF_7','#skF_6')) != '#skF_10' ),
    inference(splitRight,[status(thm)],[c_1509])).

tff(c_56,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1562,plain,(
    ! [C_382,E_379,A_381,B_378,D_380] :
      ( r2_hidden(k4_tarski('#skF_5'(B_378,E_379,D_380,A_381,C_382),E_379),D_380)
      | ~ r2_hidden(E_379,k7_relset_1(C_382,A_381,D_380,B_378))
      | ~ m1_subset_1(E_379,A_381)
      | ~ m1_subset_1(D_380,k1_zfmisc_1(k2_zfmisc_1(C_382,A_381)))
      | v1_xboole_0(C_382)
      | v1_xboole_0(B_378)
      | v1_xboole_0(A_381) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_24,plain,(
    ! [C_24,A_22,B_23] :
      ( k1_funct_1(C_24,A_22) = B_23
      | ~ r2_hidden(k4_tarski(A_22,B_23),C_24)
      | ~ v1_funct_1(C_24)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6394,plain,(
    ! [A_831,B_833,E_834,D_832,C_835] :
      ( k1_funct_1(D_832,'#skF_5'(B_833,E_834,D_832,A_831,C_835)) = E_834
      | ~ v1_funct_1(D_832)
      | ~ v1_relat_1(D_832)
      | ~ r2_hidden(E_834,k7_relset_1(C_835,A_831,D_832,B_833))
      | ~ m1_subset_1(E_834,A_831)
      | ~ m1_subset_1(D_832,k1_zfmisc_1(k2_zfmisc_1(C_835,A_831)))
      | v1_xboole_0(C_835)
      | v1_xboole_0(B_833)
      | v1_xboole_0(A_831) ) ),
    inference(resolution,[status(thm)],[c_1562,c_24])).

tff(c_6416,plain,(
    ! [D_182,E_834] :
      ( k1_funct_1('#skF_9','#skF_5'(D_182,E_834,'#skF_9','#skF_7','#skF_6')) = E_834
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(E_834,k9_relat_1('#skF_9',D_182))
      | ~ m1_subset_1(E_834,'#skF_7')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_182)
      | v1_xboole_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_6394])).

tff(c_6433,plain,(
    ! [D_182,E_834] :
      ( k1_funct_1('#skF_9','#skF_5'(D_182,E_834,'#skF_9','#skF_7','#skF_6')) = E_834
      | ~ r2_hidden(E_834,k9_relat_1('#skF_9',D_182))
      | ~ m1_subset_1(E_834,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_182)
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_74,c_56,c_6416])).

tff(c_6437,plain,(
    ! [D_836,E_837] :
      ( k1_funct_1('#skF_9','#skF_5'(D_836,E_837,'#skF_9','#skF_7','#skF_6')) = E_837
      | ~ r2_hidden(E_837,k9_relat_1('#skF_9',D_836))
      | ~ m1_subset_1(E_837,'#skF_7')
      | v1_xboole_0(D_836) ) ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_532,c_6433])).

tff(c_6515,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_8','#skF_10','#skF_9','#skF_7','#skF_6')) = '#skF_10'
    | ~ m1_subset_1('#skF_10','#skF_7')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_131,c_6437])).

tff(c_6584,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_8','#skF_10','#skF_9','#skF_7','#skF_6')) = '#skF_10'
    | v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_6515])).

tff(c_6586,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_1560,c_6584])).

tff(c_6587,plain,(
    r2_hidden('#skF_3'('#skF_7','#skF_6','#skF_9'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_530])).

tff(c_6592,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_6587,c_2])).

tff(c_7312,plain,(
    ! [B_953,E_954,D_955,C_957,A_956] :
      ( r2_hidden('#skF_5'(B_953,E_954,D_955,A_956,C_957),B_953)
      | ~ r2_hidden(E_954,k7_relset_1(C_957,A_956,D_955,B_953))
      | ~ m1_subset_1(E_954,A_956)
      | ~ m1_subset_1(D_955,k1_zfmisc_1(k2_zfmisc_1(C_957,A_956)))
      | v1_xboole_0(C_957)
      | v1_xboole_0(B_953)
      | v1_xboole_0(A_956) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_7317,plain,(
    ! [B_953,E_954] :
      ( r2_hidden('#skF_5'(B_953,E_954,'#skF_9','#skF_7','#skF_6'),B_953)
      | ~ r2_hidden(E_954,k7_relset_1('#skF_6','#skF_7','#skF_9',B_953))
      | ~ m1_subset_1(E_954,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(B_953)
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_52,c_7312])).

tff(c_7320,plain,(
    ! [B_953,E_954] :
      ( r2_hidden('#skF_5'(B_953,E_954,'#skF_9','#skF_7','#skF_6'),B_953)
      | ~ r2_hidden(E_954,k9_relat_1('#skF_9',B_953))
      | ~ m1_subset_1(E_954,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(B_953)
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_7317])).

tff(c_7323,plain,(
    ! [B_960,E_961] :
      ( r2_hidden('#skF_5'(B_960,E_961,'#skF_9','#skF_7','#skF_6'),B_960)
      | ~ r2_hidden(E_961,k9_relat_1('#skF_9',B_960))
      | ~ m1_subset_1(E_961,'#skF_7')
      | v1_xboole_0(B_960) ) ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_6592,c_7320])).

tff(c_7416,plain,(
    ! [E_961] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_8',E_961,'#skF_9','#skF_7','#skF_6')) != '#skF_10'
      | ~ m1_subset_1('#skF_5'('#skF_8',E_961,'#skF_9','#skF_7','#skF_6'),'#skF_6')
      | ~ r2_hidden(E_961,k9_relat_1('#skF_9','#skF_8'))
      | ~ m1_subset_1(E_961,'#skF_7')
      | v1_xboole_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_7323,c_48])).

tff(c_7484,plain,(
    ! [E_965] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_8',E_965,'#skF_9','#skF_7','#skF_6')) != '#skF_10'
      | ~ m1_subset_1('#skF_5'('#skF_8',E_965,'#skF_9','#skF_7','#skF_6'),'#skF_6')
      | ~ r2_hidden(E_965,k9_relat_1('#skF_9','#skF_8'))
      | ~ m1_subset_1(E_965,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_7416])).

tff(c_7503,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_8','#skF_10','#skF_9','#skF_7','#skF_6')) != '#skF_10'
    | ~ m1_subset_1('#skF_5'('#skF_8','#skF_10','#skF_9','#skF_7','#skF_6'),'#skF_6')
    | ~ m1_subset_1('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_131,c_7484])).

tff(c_7520,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_8','#skF_10','#skF_9','#skF_7','#skF_6')) != '#skF_10'
    | ~ m1_subset_1('#skF_5'('#skF_8','#skF_10','#skF_9','#skF_7','#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_7503])).

tff(c_7526,plain,(
    ~ m1_subset_1('#skF_5'('#skF_8','#skF_10','#skF_9','#skF_7','#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_7520])).

tff(c_7118,plain,(
    ! [C_924,A_923,E_921,D_922,B_920] :
      ( m1_subset_1('#skF_5'(B_920,E_921,D_922,A_923,C_924),C_924)
      | ~ r2_hidden(E_921,k7_relset_1(C_924,A_923,D_922,B_920))
      | ~ m1_subset_1(E_921,A_923)
      | ~ m1_subset_1(D_922,k1_zfmisc_1(k2_zfmisc_1(C_924,A_923)))
      | v1_xboole_0(C_924)
      | v1_xboole_0(B_920)
      | v1_xboole_0(A_923) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_7129,plain,(
    ! [D_182,E_921] :
      ( m1_subset_1('#skF_5'(D_182,E_921,'#skF_9','#skF_7','#skF_6'),'#skF_6')
      | ~ r2_hidden(E_921,k9_relat_1('#skF_9',D_182))
      | ~ m1_subset_1(E_921,'#skF_7')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_182)
      | v1_xboole_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_7118])).

tff(c_7140,plain,(
    ! [D_182,E_921] :
      ( m1_subset_1('#skF_5'(D_182,E_921,'#skF_9','#skF_7','#skF_6'),'#skF_6')
      | ~ r2_hidden(E_921,k9_relat_1('#skF_9',D_182))
      | ~ m1_subset_1(E_921,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_182)
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_7129])).

tff(c_7527,plain,(
    ! [D_968,E_969] :
      ( m1_subset_1('#skF_5'(D_968,E_969,'#skF_9','#skF_7','#skF_6'),'#skF_6')
      | ~ r2_hidden(E_969,k9_relat_1('#skF_9',D_968))
      | ~ m1_subset_1(E_969,'#skF_7')
      | v1_xboole_0(D_968) ) ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_6592,c_7140])).

tff(c_7550,plain,
    ( m1_subset_1('#skF_5'('#skF_8','#skF_10','#skF_9','#skF_7','#skF_6'),'#skF_6')
    | ~ m1_subset_1('#skF_10','#skF_7')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_131,c_7527])).

tff(c_7569,plain,
    ( m1_subset_1('#skF_5'('#skF_8','#skF_10','#skF_9','#skF_7','#skF_6'),'#skF_6')
    | v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_7550])).

tff(c_7571,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_7526,c_7569])).

tff(c_7572,plain,(
    k1_funct_1('#skF_9','#skF_5'('#skF_8','#skF_10','#skF_9','#skF_7','#skF_6')) != '#skF_10' ),
    inference(splitRight,[status(thm)],[c_7520])).

tff(c_7574,plain,(
    ! [C_974,A_973,B_970,E_971,D_972] :
      ( r2_hidden(k4_tarski('#skF_5'(B_970,E_971,D_972,A_973,C_974),E_971),D_972)
      | ~ r2_hidden(E_971,k7_relset_1(C_974,A_973,D_972,B_970))
      | ~ m1_subset_1(E_971,A_973)
      | ~ m1_subset_1(D_972,k1_zfmisc_1(k2_zfmisc_1(C_974,A_973)))
      | v1_xboole_0(C_974)
      | v1_xboole_0(B_970)
      | v1_xboole_0(A_973) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_12089,plain,(
    ! [A_1457,B_1458,D_1456,C_1455,E_1459] :
      ( k1_funct_1(D_1456,'#skF_5'(B_1458,E_1459,D_1456,A_1457,C_1455)) = E_1459
      | ~ v1_funct_1(D_1456)
      | ~ v1_relat_1(D_1456)
      | ~ r2_hidden(E_1459,k7_relset_1(C_1455,A_1457,D_1456,B_1458))
      | ~ m1_subset_1(E_1459,A_1457)
      | ~ m1_subset_1(D_1456,k1_zfmisc_1(k2_zfmisc_1(C_1455,A_1457)))
      | v1_xboole_0(C_1455)
      | v1_xboole_0(B_1458)
      | v1_xboole_0(A_1457) ) ),
    inference(resolution,[status(thm)],[c_7574,c_24])).

tff(c_12111,plain,(
    ! [D_182,E_1459] :
      ( k1_funct_1('#skF_9','#skF_5'(D_182,E_1459,'#skF_9','#skF_7','#skF_6')) = E_1459
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(E_1459,k9_relat_1('#skF_9',D_182))
      | ~ m1_subset_1(E_1459,'#skF_7')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_182)
      | v1_xboole_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_12089])).

tff(c_12128,plain,(
    ! [D_182,E_1459] :
      ( k1_funct_1('#skF_9','#skF_5'(D_182,E_1459,'#skF_9','#skF_7','#skF_6')) = E_1459
      | ~ r2_hidden(E_1459,k9_relat_1('#skF_9',D_182))
      | ~ m1_subset_1(E_1459,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_182)
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_74,c_56,c_12111])).

tff(c_12132,plain,(
    ! [D_1460,E_1461] :
      ( k1_funct_1('#skF_9','#skF_5'(D_1460,E_1461,'#skF_9','#skF_7','#skF_6')) = E_1461
      | ~ r2_hidden(E_1461,k9_relat_1('#skF_9',D_1460))
      | ~ m1_subset_1(E_1461,'#skF_7')
      | v1_xboole_0(D_1460) ) ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_6592,c_12128])).

tff(c_12198,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_8','#skF_10','#skF_9','#skF_7','#skF_6')) = '#skF_10'
    | ~ m1_subset_1('#skF_10','#skF_7')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_131,c_12132])).

tff(c_12254,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_8','#skF_10','#skF_9','#skF_7','#skF_6')) = '#skF_10'
    | v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_12198])).

tff(c_12256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_7572,c_12254])).

tff(c_12257,plain,(
    ! [D_195] : v1_xboole_0(k9_relat_1('#skF_9',D_195)) ),
    inference(splitRight,[status(thm)],[c_205])).

tff(c_12261,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12257,c_130])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:24:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.58/4.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.58/4.14  
% 9.58/4.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.58/4.15  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 9.58/4.15  
% 9.58/4.15  %Foreground sorts:
% 9.58/4.15  
% 9.58/4.15  
% 9.58/4.15  %Background operators:
% 9.58/4.15  
% 9.58/4.15  
% 9.58/4.15  %Foreground operators:
% 9.58/4.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.58/4.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.58/4.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.58/4.15  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.58/4.15  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.58/4.15  tff('#skF_7', type, '#skF_7': $i).
% 9.58/4.15  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i) > $i).
% 9.58/4.15  tff('#skF_10', type, '#skF_10': $i).
% 9.58/4.15  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 9.58/4.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.58/4.15  tff('#skF_6', type, '#skF_6': $i).
% 9.58/4.15  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.58/4.15  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.58/4.15  tff('#skF_9', type, '#skF_9': $i).
% 9.58/4.15  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.58/4.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.58/4.15  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.58/4.15  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 9.58/4.15  tff('#skF_8', type, '#skF_8': $i).
% 9.58/4.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.58/4.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.58/4.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.58/4.15  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 9.58/4.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.58/4.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.58/4.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.58/4.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.58/4.15  
% 9.78/4.17  tff(f_53, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.78/4.17  tff(f_143, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 9.78/4.17  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.78/4.17  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.78/4.17  tff(f_64, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 9.78/4.17  tff(f_86, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 9.78/4.17  tff(f_78, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 9.78/4.17  tff(f_44, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 9.78/4.17  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 9.78/4.17  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.78/4.17  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 9.78/4.17  tff(f_124, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k7_relset_1(C, A, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(F, E), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relset_1)).
% 9.78/4.17  tff(f_74, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 9.78/4.17  tff(c_12, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.78/4.17  tff(c_52, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 9.78/4.17  tff(c_68, plain, (![B_153, A_154]: (v1_relat_1(B_153) | ~m1_subset_1(B_153, k1_zfmisc_1(A_154)) | ~v1_relat_1(A_154))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.78/4.17  tff(c_71, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_52, c_68])).
% 9.78/4.17  tff(c_74, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_71])).
% 9.78/4.17  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.78/4.17  tff(c_104, plain, (![A_171, B_172, C_173]: (r2_hidden('#skF_2'(A_171, B_172, C_173), B_172) | ~r2_hidden(A_171, k9_relat_1(C_173, B_172)) | ~v1_relat_1(C_173))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.78/4.17  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.78/4.17  tff(c_114, plain, (![B_174, A_175, C_176]: (~v1_xboole_0(B_174) | ~r2_hidden(A_175, k9_relat_1(C_176, B_174)) | ~v1_relat_1(C_176))), inference(resolution, [status(thm)], [c_104, c_2])).
% 9.78/4.17  tff(c_124, plain, (![B_174, C_176]: (~v1_xboole_0(B_174) | ~v1_relat_1(C_176) | v1_xboole_0(k9_relat_1(C_176, B_174)))), inference(resolution, [status(thm)], [c_4, c_114])).
% 9.78/4.17  tff(c_126, plain, (![A_179, B_180, C_181, D_182]: (k7_relset_1(A_179, B_180, C_181, D_182)=k9_relat_1(C_181, D_182) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.78/4.17  tff(c_129, plain, (![D_182]: (k7_relset_1('#skF_6', '#skF_7', '#skF_9', D_182)=k9_relat_1('#skF_9', D_182))), inference(resolution, [status(thm)], [c_52, c_126])).
% 9.78/4.17  tff(c_50, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 9.78/4.17  tff(c_67, plain, (~v1_xboole_0(k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(resolution, [status(thm)], [c_50, c_2])).
% 9.78/4.17  tff(c_130, plain, (~v1_xboole_0(k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_67])).
% 9.78/4.17  tff(c_143, plain, (~v1_xboole_0('#skF_8') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_124, c_130])).
% 9.78/4.17  tff(c_146, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_143])).
% 9.78/4.17  tff(c_131, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_50])).
% 9.78/4.17  tff(c_169, plain, (![A_191, B_192, C_193, D_194]: (m1_subset_1(k7_relset_1(A_191, B_192, C_193, D_194), k1_zfmisc_1(B_192)) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(A_191, B_192))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.78/4.17  tff(c_187, plain, (![D_182]: (m1_subset_1(k9_relat_1('#skF_9', D_182), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_129, c_169])).
% 9.78/4.17  tff(c_195, plain, (![D_195]: (m1_subset_1(k9_relat_1('#skF_9', D_195), k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_187])).
% 9.78/4.17  tff(c_8, plain, (![A_8, C_10, B_9]: (m1_subset_1(A_8, C_10) | ~m1_subset_1(B_9, k1_zfmisc_1(C_10)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.78/4.17  tff(c_231, plain, (![A_201, D_202]: (m1_subset_1(A_201, '#skF_7') | ~r2_hidden(A_201, k9_relat_1('#skF_9', D_202)))), inference(resolution, [status(thm)], [c_195, c_8])).
% 9.78/4.17  tff(c_243, plain, (m1_subset_1('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_131, c_231])).
% 9.78/4.17  tff(c_6, plain, (![B_7, A_5]: (v1_xboole_0(B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_5)) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.78/4.17  tff(c_205, plain, (![D_195]: (v1_xboole_0(k9_relat_1('#skF_9', D_195)) | ~v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_195, c_6])).
% 9.78/4.17  tff(c_207, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_205])).
% 9.78/4.17  tff(c_91, plain, (![A_161, B_162, C_163]: (k1_relset_1(A_161, B_162, C_163)=k1_relat_1(C_163) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.78/4.17  tff(c_95, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_52, c_91])).
% 9.78/4.17  tff(c_522, plain, (![A_246, B_247, C_248]: (r2_hidden('#skF_3'(A_246, B_247, C_248), B_247) | k1_relset_1(B_247, A_246, C_248)=B_247 | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(B_247, A_246))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.78/4.17  tff(c_527, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_6', '#skF_9'), '#skF_6') | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6'), inference(resolution, [status(thm)], [c_52, c_522])).
% 9.78/4.17  tff(c_530, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_6', '#skF_9'), '#skF_6') | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_95, c_527])).
% 9.78/4.17  tff(c_531, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_530])).
% 9.78/4.17  tff(c_208, plain, (![A_196, B_197, C_198]: (r2_hidden('#skF_2'(A_196, B_197, C_198), k1_relat_1(C_198)) | ~r2_hidden(A_196, k9_relat_1(C_198, B_197)) | ~v1_relat_1(C_198))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.78/4.17  tff(c_246, plain, (![C_203, A_204, B_205]: (~v1_xboole_0(k1_relat_1(C_203)) | ~r2_hidden(A_204, k9_relat_1(C_203, B_205)) | ~v1_relat_1(C_203))), inference(resolution, [status(thm)], [c_208, c_2])).
% 9.78/4.17  tff(c_249, plain, (~v1_xboole_0(k1_relat_1('#skF_9')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_131, c_246])).
% 9.78/4.17  tff(c_260, plain, (~v1_xboole_0(k1_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_249])).
% 9.78/4.17  tff(c_532, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_531, c_260])).
% 9.78/4.17  tff(c_1301, plain, (![D_365, C_367, B_363, E_364, A_366]: (r2_hidden('#skF_5'(B_363, E_364, D_365, A_366, C_367), B_363) | ~r2_hidden(E_364, k7_relset_1(C_367, A_366, D_365, B_363)) | ~m1_subset_1(E_364, A_366) | ~m1_subset_1(D_365, k1_zfmisc_1(k2_zfmisc_1(C_367, A_366))) | v1_xboole_0(C_367) | v1_xboole_0(B_363) | v1_xboole_0(A_366))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.78/4.17  tff(c_1306, plain, (![B_363, E_364]: (r2_hidden('#skF_5'(B_363, E_364, '#skF_9', '#skF_7', '#skF_6'), B_363) | ~r2_hidden(E_364, k7_relset_1('#skF_6', '#skF_7', '#skF_9', B_363)) | ~m1_subset_1(E_364, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(B_363) | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_52, c_1301])).
% 9.78/4.17  tff(c_1309, plain, (![B_363, E_364]: (r2_hidden('#skF_5'(B_363, E_364, '#skF_9', '#skF_7', '#skF_6'), B_363) | ~r2_hidden(E_364, k9_relat_1('#skF_9', B_363)) | ~m1_subset_1(E_364, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(B_363) | v1_xboole_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_1306])).
% 9.78/4.17  tff(c_1311, plain, (![B_368, E_369]: (r2_hidden('#skF_5'(B_368, E_369, '#skF_9', '#skF_7', '#skF_6'), B_368) | ~r2_hidden(E_369, k9_relat_1('#skF_9', B_368)) | ~m1_subset_1(E_369, '#skF_7') | v1_xboole_0(B_368))), inference(negUnitSimplification, [status(thm)], [c_207, c_532, c_1309])).
% 9.78/4.17  tff(c_48, plain, (![F_147]: (k1_funct_1('#skF_9', F_147)!='#skF_10' | ~r2_hidden(F_147, '#skF_8') | ~m1_subset_1(F_147, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 9.78/4.17  tff(c_1404, plain, (![E_369]: (k1_funct_1('#skF_9', '#skF_5'('#skF_8', E_369, '#skF_9', '#skF_7', '#skF_6'))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_8', E_369, '#skF_9', '#skF_7', '#skF_6'), '#skF_6') | ~r2_hidden(E_369, k9_relat_1('#skF_9', '#skF_8')) | ~m1_subset_1(E_369, '#skF_7') | v1_xboole_0('#skF_8'))), inference(resolution, [status(thm)], [c_1311, c_48])).
% 9.78/4.17  tff(c_1473, plain, (![E_375]: (k1_funct_1('#skF_9', '#skF_5'('#skF_8', E_375, '#skF_9', '#skF_7', '#skF_6'))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_8', E_375, '#skF_9', '#skF_7', '#skF_6'), '#skF_6') | ~r2_hidden(E_375, k9_relat_1('#skF_9', '#skF_8')) | ~m1_subset_1(E_375, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_146, c_1404])).
% 9.78/4.17  tff(c_1492, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_8', '#skF_10', '#skF_9', '#skF_7', '#skF_6'))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_8', '#skF_10', '#skF_9', '#skF_7', '#skF_6'), '#skF_6') | ~m1_subset_1('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_131, c_1473])).
% 9.78/4.17  tff(c_1509, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_8', '#skF_10', '#skF_9', '#skF_7', '#skF_6'))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_8', '#skF_10', '#skF_9', '#skF_7', '#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_243, c_1492])).
% 9.78/4.17  tff(c_1514, plain, (~m1_subset_1('#skF_5'('#skF_8', '#skF_10', '#skF_9', '#skF_7', '#skF_6'), '#skF_6')), inference(splitLeft, [status(thm)], [c_1509])).
% 9.78/4.17  tff(c_1132, plain, (![D_335, C_337, A_336, E_334, B_333]: (m1_subset_1('#skF_5'(B_333, E_334, D_335, A_336, C_337), C_337) | ~r2_hidden(E_334, k7_relset_1(C_337, A_336, D_335, B_333)) | ~m1_subset_1(E_334, A_336) | ~m1_subset_1(D_335, k1_zfmisc_1(k2_zfmisc_1(C_337, A_336))) | v1_xboole_0(C_337) | v1_xboole_0(B_333) | v1_xboole_0(A_336))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.78/4.17  tff(c_1143, plain, (![D_182, E_334]: (m1_subset_1('#skF_5'(D_182, E_334, '#skF_9', '#skF_7', '#skF_6'), '#skF_6') | ~r2_hidden(E_334, k9_relat_1('#skF_9', D_182)) | ~m1_subset_1(E_334, '#skF_7') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | v1_xboole_0('#skF_6') | v1_xboole_0(D_182) | v1_xboole_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_1132])).
% 9.78/4.17  tff(c_1154, plain, (![D_182, E_334]: (m1_subset_1('#skF_5'(D_182, E_334, '#skF_9', '#skF_7', '#skF_6'), '#skF_6') | ~r2_hidden(E_334, k9_relat_1('#skF_9', D_182)) | ~m1_subset_1(E_334, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(D_182) | v1_xboole_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1143])).
% 9.78/4.17  tff(c_1515, plain, (![D_376, E_377]: (m1_subset_1('#skF_5'(D_376, E_377, '#skF_9', '#skF_7', '#skF_6'), '#skF_6') | ~r2_hidden(E_377, k9_relat_1('#skF_9', D_376)) | ~m1_subset_1(E_377, '#skF_7') | v1_xboole_0(D_376))), inference(negUnitSimplification, [status(thm)], [c_207, c_532, c_1154])).
% 9.78/4.17  tff(c_1538, plain, (m1_subset_1('#skF_5'('#skF_8', '#skF_10', '#skF_9', '#skF_7', '#skF_6'), '#skF_6') | ~m1_subset_1('#skF_10', '#skF_7') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_131, c_1515])).
% 9.78/4.17  tff(c_1557, plain, (m1_subset_1('#skF_5'('#skF_8', '#skF_10', '#skF_9', '#skF_7', '#skF_6'), '#skF_6') | v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_243, c_1538])).
% 9.78/4.17  tff(c_1559, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_1514, c_1557])).
% 9.78/4.17  tff(c_1560, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_8', '#skF_10', '#skF_9', '#skF_7', '#skF_6'))!='#skF_10'), inference(splitRight, [status(thm)], [c_1509])).
% 9.78/4.17  tff(c_56, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_143])).
% 9.78/4.17  tff(c_1562, plain, (![C_382, E_379, A_381, B_378, D_380]: (r2_hidden(k4_tarski('#skF_5'(B_378, E_379, D_380, A_381, C_382), E_379), D_380) | ~r2_hidden(E_379, k7_relset_1(C_382, A_381, D_380, B_378)) | ~m1_subset_1(E_379, A_381) | ~m1_subset_1(D_380, k1_zfmisc_1(k2_zfmisc_1(C_382, A_381))) | v1_xboole_0(C_382) | v1_xboole_0(B_378) | v1_xboole_0(A_381))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.78/4.17  tff(c_24, plain, (![C_24, A_22, B_23]: (k1_funct_1(C_24, A_22)=B_23 | ~r2_hidden(k4_tarski(A_22, B_23), C_24) | ~v1_funct_1(C_24) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.78/4.17  tff(c_6394, plain, (![A_831, B_833, E_834, D_832, C_835]: (k1_funct_1(D_832, '#skF_5'(B_833, E_834, D_832, A_831, C_835))=E_834 | ~v1_funct_1(D_832) | ~v1_relat_1(D_832) | ~r2_hidden(E_834, k7_relset_1(C_835, A_831, D_832, B_833)) | ~m1_subset_1(E_834, A_831) | ~m1_subset_1(D_832, k1_zfmisc_1(k2_zfmisc_1(C_835, A_831))) | v1_xboole_0(C_835) | v1_xboole_0(B_833) | v1_xboole_0(A_831))), inference(resolution, [status(thm)], [c_1562, c_24])).
% 9.78/4.17  tff(c_6416, plain, (![D_182, E_834]: (k1_funct_1('#skF_9', '#skF_5'(D_182, E_834, '#skF_9', '#skF_7', '#skF_6'))=E_834 | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(E_834, k9_relat_1('#skF_9', D_182)) | ~m1_subset_1(E_834, '#skF_7') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | v1_xboole_0('#skF_6') | v1_xboole_0(D_182) | v1_xboole_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_6394])).
% 9.78/4.17  tff(c_6433, plain, (![D_182, E_834]: (k1_funct_1('#skF_9', '#skF_5'(D_182, E_834, '#skF_9', '#skF_7', '#skF_6'))=E_834 | ~r2_hidden(E_834, k9_relat_1('#skF_9', D_182)) | ~m1_subset_1(E_834, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(D_182) | v1_xboole_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_74, c_56, c_6416])).
% 9.78/4.17  tff(c_6437, plain, (![D_836, E_837]: (k1_funct_1('#skF_9', '#skF_5'(D_836, E_837, '#skF_9', '#skF_7', '#skF_6'))=E_837 | ~r2_hidden(E_837, k9_relat_1('#skF_9', D_836)) | ~m1_subset_1(E_837, '#skF_7') | v1_xboole_0(D_836))), inference(negUnitSimplification, [status(thm)], [c_207, c_532, c_6433])).
% 9.78/4.17  tff(c_6515, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_8', '#skF_10', '#skF_9', '#skF_7', '#skF_6'))='#skF_10' | ~m1_subset_1('#skF_10', '#skF_7') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_131, c_6437])).
% 9.78/4.17  tff(c_6584, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_8', '#skF_10', '#skF_9', '#skF_7', '#skF_6'))='#skF_10' | v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_243, c_6515])).
% 9.78/4.17  tff(c_6586, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_1560, c_6584])).
% 9.78/4.17  tff(c_6587, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_6', '#skF_9'), '#skF_6')), inference(splitRight, [status(thm)], [c_530])).
% 9.78/4.17  tff(c_6592, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_6587, c_2])).
% 9.78/4.17  tff(c_7312, plain, (![B_953, E_954, D_955, C_957, A_956]: (r2_hidden('#skF_5'(B_953, E_954, D_955, A_956, C_957), B_953) | ~r2_hidden(E_954, k7_relset_1(C_957, A_956, D_955, B_953)) | ~m1_subset_1(E_954, A_956) | ~m1_subset_1(D_955, k1_zfmisc_1(k2_zfmisc_1(C_957, A_956))) | v1_xboole_0(C_957) | v1_xboole_0(B_953) | v1_xboole_0(A_956))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.78/4.17  tff(c_7317, plain, (![B_953, E_954]: (r2_hidden('#skF_5'(B_953, E_954, '#skF_9', '#skF_7', '#skF_6'), B_953) | ~r2_hidden(E_954, k7_relset_1('#skF_6', '#skF_7', '#skF_9', B_953)) | ~m1_subset_1(E_954, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(B_953) | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_52, c_7312])).
% 9.78/4.17  tff(c_7320, plain, (![B_953, E_954]: (r2_hidden('#skF_5'(B_953, E_954, '#skF_9', '#skF_7', '#skF_6'), B_953) | ~r2_hidden(E_954, k9_relat_1('#skF_9', B_953)) | ~m1_subset_1(E_954, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(B_953) | v1_xboole_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_7317])).
% 9.78/4.17  tff(c_7323, plain, (![B_960, E_961]: (r2_hidden('#skF_5'(B_960, E_961, '#skF_9', '#skF_7', '#skF_6'), B_960) | ~r2_hidden(E_961, k9_relat_1('#skF_9', B_960)) | ~m1_subset_1(E_961, '#skF_7') | v1_xboole_0(B_960))), inference(negUnitSimplification, [status(thm)], [c_207, c_6592, c_7320])).
% 9.78/4.17  tff(c_7416, plain, (![E_961]: (k1_funct_1('#skF_9', '#skF_5'('#skF_8', E_961, '#skF_9', '#skF_7', '#skF_6'))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_8', E_961, '#skF_9', '#skF_7', '#skF_6'), '#skF_6') | ~r2_hidden(E_961, k9_relat_1('#skF_9', '#skF_8')) | ~m1_subset_1(E_961, '#skF_7') | v1_xboole_0('#skF_8'))), inference(resolution, [status(thm)], [c_7323, c_48])).
% 9.78/4.17  tff(c_7484, plain, (![E_965]: (k1_funct_1('#skF_9', '#skF_5'('#skF_8', E_965, '#skF_9', '#skF_7', '#skF_6'))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_8', E_965, '#skF_9', '#skF_7', '#skF_6'), '#skF_6') | ~r2_hidden(E_965, k9_relat_1('#skF_9', '#skF_8')) | ~m1_subset_1(E_965, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_146, c_7416])).
% 9.78/4.17  tff(c_7503, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_8', '#skF_10', '#skF_9', '#skF_7', '#skF_6'))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_8', '#skF_10', '#skF_9', '#skF_7', '#skF_6'), '#skF_6') | ~m1_subset_1('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_131, c_7484])).
% 9.78/4.17  tff(c_7520, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_8', '#skF_10', '#skF_9', '#skF_7', '#skF_6'))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_8', '#skF_10', '#skF_9', '#skF_7', '#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_243, c_7503])).
% 9.78/4.17  tff(c_7526, plain, (~m1_subset_1('#skF_5'('#skF_8', '#skF_10', '#skF_9', '#skF_7', '#skF_6'), '#skF_6')), inference(splitLeft, [status(thm)], [c_7520])).
% 9.78/4.17  tff(c_7118, plain, (![C_924, A_923, E_921, D_922, B_920]: (m1_subset_1('#skF_5'(B_920, E_921, D_922, A_923, C_924), C_924) | ~r2_hidden(E_921, k7_relset_1(C_924, A_923, D_922, B_920)) | ~m1_subset_1(E_921, A_923) | ~m1_subset_1(D_922, k1_zfmisc_1(k2_zfmisc_1(C_924, A_923))) | v1_xboole_0(C_924) | v1_xboole_0(B_920) | v1_xboole_0(A_923))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.78/4.17  tff(c_7129, plain, (![D_182, E_921]: (m1_subset_1('#skF_5'(D_182, E_921, '#skF_9', '#skF_7', '#skF_6'), '#skF_6') | ~r2_hidden(E_921, k9_relat_1('#skF_9', D_182)) | ~m1_subset_1(E_921, '#skF_7') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | v1_xboole_0('#skF_6') | v1_xboole_0(D_182) | v1_xboole_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_7118])).
% 9.78/4.17  tff(c_7140, plain, (![D_182, E_921]: (m1_subset_1('#skF_5'(D_182, E_921, '#skF_9', '#skF_7', '#skF_6'), '#skF_6') | ~r2_hidden(E_921, k9_relat_1('#skF_9', D_182)) | ~m1_subset_1(E_921, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(D_182) | v1_xboole_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_7129])).
% 9.78/4.17  tff(c_7527, plain, (![D_968, E_969]: (m1_subset_1('#skF_5'(D_968, E_969, '#skF_9', '#skF_7', '#skF_6'), '#skF_6') | ~r2_hidden(E_969, k9_relat_1('#skF_9', D_968)) | ~m1_subset_1(E_969, '#skF_7') | v1_xboole_0(D_968))), inference(negUnitSimplification, [status(thm)], [c_207, c_6592, c_7140])).
% 9.78/4.17  tff(c_7550, plain, (m1_subset_1('#skF_5'('#skF_8', '#skF_10', '#skF_9', '#skF_7', '#skF_6'), '#skF_6') | ~m1_subset_1('#skF_10', '#skF_7') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_131, c_7527])).
% 9.78/4.17  tff(c_7569, plain, (m1_subset_1('#skF_5'('#skF_8', '#skF_10', '#skF_9', '#skF_7', '#skF_6'), '#skF_6') | v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_243, c_7550])).
% 9.78/4.17  tff(c_7571, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_7526, c_7569])).
% 9.78/4.17  tff(c_7572, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_8', '#skF_10', '#skF_9', '#skF_7', '#skF_6'))!='#skF_10'), inference(splitRight, [status(thm)], [c_7520])).
% 9.78/4.17  tff(c_7574, plain, (![C_974, A_973, B_970, E_971, D_972]: (r2_hidden(k4_tarski('#skF_5'(B_970, E_971, D_972, A_973, C_974), E_971), D_972) | ~r2_hidden(E_971, k7_relset_1(C_974, A_973, D_972, B_970)) | ~m1_subset_1(E_971, A_973) | ~m1_subset_1(D_972, k1_zfmisc_1(k2_zfmisc_1(C_974, A_973))) | v1_xboole_0(C_974) | v1_xboole_0(B_970) | v1_xboole_0(A_973))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.78/4.17  tff(c_12089, plain, (![A_1457, B_1458, D_1456, C_1455, E_1459]: (k1_funct_1(D_1456, '#skF_5'(B_1458, E_1459, D_1456, A_1457, C_1455))=E_1459 | ~v1_funct_1(D_1456) | ~v1_relat_1(D_1456) | ~r2_hidden(E_1459, k7_relset_1(C_1455, A_1457, D_1456, B_1458)) | ~m1_subset_1(E_1459, A_1457) | ~m1_subset_1(D_1456, k1_zfmisc_1(k2_zfmisc_1(C_1455, A_1457))) | v1_xboole_0(C_1455) | v1_xboole_0(B_1458) | v1_xboole_0(A_1457))), inference(resolution, [status(thm)], [c_7574, c_24])).
% 9.78/4.17  tff(c_12111, plain, (![D_182, E_1459]: (k1_funct_1('#skF_9', '#skF_5'(D_182, E_1459, '#skF_9', '#skF_7', '#skF_6'))=E_1459 | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(E_1459, k9_relat_1('#skF_9', D_182)) | ~m1_subset_1(E_1459, '#skF_7') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | v1_xboole_0('#skF_6') | v1_xboole_0(D_182) | v1_xboole_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_12089])).
% 9.78/4.17  tff(c_12128, plain, (![D_182, E_1459]: (k1_funct_1('#skF_9', '#skF_5'(D_182, E_1459, '#skF_9', '#skF_7', '#skF_6'))=E_1459 | ~r2_hidden(E_1459, k9_relat_1('#skF_9', D_182)) | ~m1_subset_1(E_1459, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(D_182) | v1_xboole_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_74, c_56, c_12111])).
% 9.78/4.17  tff(c_12132, plain, (![D_1460, E_1461]: (k1_funct_1('#skF_9', '#skF_5'(D_1460, E_1461, '#skF_9', '#skF_7', '#skF_6'))=E_1461 | ~r2_hidden(E_1461, k9_relat_1('#skF_9', D_1460)) | ~m1_subset_1(E_1461, '#skF_7') | v1_xboole_0(D_1460))), inference(negUnitSimplification, [status(thm)], [c_207, c_6592, c_12128])).
% 9.78/4.17  tff(c_12198, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_8', '#skF_10', '#skF_9', '#skF_7', '#skF_6'))='#skF_10' | ~m1_subset_1('#skF_10', '#skF_7') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_131, c_12132])).
% 9.78/4.17  tff(c_12254, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_8', '#skF_10', '#skF_9', '#skF_7', '#skF_6'))='#skF_10' | v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_243, c_12198])).
% 9.78/4.17  tff(c_12256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_7572, c_12254])).
% 9.78/4.17  tff(c_12257, plain, (![D_195]: (v1_xboole_0(k9_relat_1('#skF_9', D_195)))), inference(splitRight, [status(thm)], [c_205])).
% 9.78/4.17  tff(c_12261, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12257, c_130])).
% 9.78/4.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.78/4.17  
% 9.78/4.17  Inference rules
% 9.78/4.17  ----------------------
% 9.78/4.17  #Ref     : 0
% 9.78/4.17  #Sup     : 2631
% 9.78/4.17  #Fact    : 0
% 9.78/4.17  #Define  : 0
% 9.78/4.17  #Split   : 20
% 9.78/4.17  #Chain   : 0
% 9.78/4.17  #Close   : 0
% 9.78/4.17  
% 9.78/4.17  Ordering : KBO
% 9.78/4.17  
% 9.78/4.17  Simplification rules
% 9.78/4.17  ----------------------
% 9.78/4.17  #Subsume      : 731
% 9.78/4.17  #Demod        : 624
% 9.78/4.17  #Tautology    : 112
% 9.78/4.17  #SimpNegUnit  : 112
% 9.78/4.17  #BackRed      : 5
% 9.78/4.17  
% 9.78/4.17  #Partial instantiations: 0
% 9.78/4.17  #Strategies tried      : 1
% 9.78/4.17  
% 9.78/4.17  Timing (in seconds)
% 9.78/4.17  ----------------------
% 9.78/4.17  Preprocessing        : 0.34
% 9.78/4.17  Parsing              : 0.18
% 9.78/4.17  CNF conversion       : 0.03
% 9.78/4.17  Main loop            : 3.06
% 9.78/4.17  Inferencing          : 0.77
% 9.78/4.17  Reduction            : 0.59
% 9.78/4.17  Demodulation         : 0.42
% 9.78/4.17  BG Simplification    : 0.08
% 9.78/4.17  Subsumption          : 1.42
% 9.78/4.17  Abstraction          : 0.13
% 9.78/4.17  MUC search           : 0.00
% 9.78/4.17  Cooper               : 0.00
% 9.78/4.17  Total                : 3.45
% 9.78/4.17  Index Insertion      : 0.00
% 9.78/4.17  Index Deletion       : 0.00
% 9.78/4.17  Index Matching       : 0.00
% 9.78/4.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
