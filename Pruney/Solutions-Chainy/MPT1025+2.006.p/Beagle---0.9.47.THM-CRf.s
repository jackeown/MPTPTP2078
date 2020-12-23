%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:31 EST 2020

% Result     : Theorem 10.48s
% Output     : CNFRefutation 10.60s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 895 expanded)
%              Number of leaves         :   39 ( 317 expanded)
%              Depth                    :   13
%              Number of atoms          :  344 (2410 expanded)
%              Number of equality atoms :   37 ( 357 expanded)
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

tff(f_138,negated_conjecture,(
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

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_119,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_65,plain,(
    ! [C_149,A_150,B_151] :
      ( v1_relat_1(C_149)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_69,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_50,c_65])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_97,plain,(
    ! [A_162,B_163,C_164] :
      ( r2_hidden('#skF_2'(A_162,B_163,C_164),B_163)
      | ~ r2_hidden(A_162,k9_relat_1(C_164,B_163))
      | ~ v1_relat_1(C_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_107,plain,(
    ! [B_165,A_166,C_167] :
      ( ~ v1_xboole_0(B_165)
      | ~ r2_hidden(A_166,k9_relat_1(C_167,B_165))
      | ~ v1_relat_1(C_167) ) ),
    inference(resolution,[status(thm)],[c_97,c_2])).

tff(c_117,plain,(
    ! [B_165,C_167] :
      ( ~ v1_xboole_0(B_165)
      | ~ v1_relat_1(C_167)
      | v1_xboole_0(k9_relat_1(C_167,B_165)) ) ),
    inference(resolution,[status(thm)],[c_4,c_107])).

tff(c_179,plain,(
    ! [A_197,B_198,C_199,D_200] :
      ( k7_relset_1(A_197,B_198,C_199,D_200) = k9_relat_1(C_199,D_200)
      | ~ m1_subset_1(C_199,k1_zfmisc_1(k2_zfmisc_1(A_197,B_198))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_186,plain,(
    ! [D_200] : k7_relset_1('#skF_6','#skF_7','#skF_9',D_200) = k9_relat_1('#skF_9',D_200) ),
    inference(resolution,[status(thm)],[c_50,c_179])).

tff(c_48,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_64,plain,(
    ~ v1_xboole_0(k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(resolution,[status(thm)],[c_48,c_2])).

tff(c_187,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_64])).

tff(c_208,plain,
    ( ~ v1_xboole_0('#skF_8')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_117,c_187])).

tff(c_214,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_208])).

tff(c_188,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_48])).

tff(c_189,plain,(
    ! [D_201] : k7_relset_1('#skF_6','#skF_7','#skF_9',D_201) = k9_relat_1('#skF_9',D_201) ),
    inference(resolution,[status(thm)],[c_50,c_179])).

tff(c_26,plain,(
    ! [A_23,B_24,C_25,D_26] :
      ( m1_subset_1(k7_relset_1(A_23,B_24,C_25,D_26),k1_zfmisc_1(B_24))
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_195,plain,(
    ! [D_201] :
      ( m1_subset_1(k9_relat_1('#skF_9',D_201),k1_zfmisc_1('#skF_7'))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_26])).

tff(c_275,plain,(
    ! [D_205] : m1_subset_1(k9_relat_1('#skF_9',D_205),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_195])).

tff(c_8,plain,(
    ! [A_8,C_10,B_9] :
      ( m1_subset_1(A_8,C_10)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(C_10))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_285,plain,(
    ! [A_206,D_207] :
      ( m1_subset_1(A_206,'#skF_7')
      | ~ r2_hidden(A_206,k9_relat_1('#skF_9',D_207)) ) ),
    inference(resolution,[status(thm)],[c_275,c_8])).

tff(c_301,plain,(
    m1_subset_1('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_188,c_285])).

tff(c_6,plain,(
    ! [B_7,A_5] :
      ( v1_xboole_0(B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_5))
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_282,plain,(
    ! [D_205] :
      ( v1_xboole_0(k9_relat_1('#skF_9',D_205))
      | ~ v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_275,c_6])).

tff(c_284,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_282])).

tff(c_87,plain,(
    ! [A_159,B_160,C_161] :
      ( k1_relset_1(A_159,B_160,C_161) = k1_relat_1(C_161)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_91,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_50,c_87])).

tff(c_418,plain,(
    ! [A_220,B_221,C_222] :
      ( r2_hidden('#skF_3'(A_220,B_221,C_222),B_221)
      | k1_relset_1(B_221,A_220,C_222) = B_221
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(B_221,A_220))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_423,plain,
    ( r2_hidden('#skF_3'('#skF_7','#skF_6','#skF_9'),'#skF_6')
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_50,c_418])).

tff(c_426,plain,
    ( r2_hidden('#skF_3'('#skF_7','#skF_6','#skF_9'),'#skF_6')
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_423])).

tff(c_427,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_426])).

tff(c_132,plain,(
    ! [A_180,B_181,C_182] :
      ( r2_hidden('#skF_2'(A_180,B_181,C_182),k1_relat_1(C_182))
      | ~ r2_hidden(A_180,k9_relat_1(C_182,B_181))
      | ~ v1_relat_1(C_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_137,plain,(
    ! [C_183,A_184,B_185] :
      ( ~ v1_xboole_0(k1_relat_1(C_183))
      | ~ r2_hidden(A_184,k9_relat_1(C_183,B_185))
      | ~ v1_relat_1(C_183) ) ),
    inference(resolution,[status(thm)],[c_132,c_2])).

tff(c_147,plain,(
    ! [C_183,B_185] :
      ( ~ v1_xboole_0(k1_relat_1(C_183))
      | ~ v1_relat_1(C_183)
      | v1_xboole_0(k9_relat_1(C_183,B_185)) ) ),
    inference(resolution,[status(thm)],[c_4,c_137])).

tff(c_205,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_147,c_187])).

tff(c_211,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_205])).

tff(c_428,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_211])).

tff(c_1016,plain,(
    ! [A_315,E_317,C_316,B_319,D_318] :
      ( r2_hidden('#skF_5'(A_315,C_316,E_317,D_318,B_319),B_319)
      | ~ r2_hidden(E_317,k7_relset_1(C_316,A_315,D_318,B_319))
      | ~ m1_subset_1(E_317,A_315)
      | ~ m1_subset_1(D_318,k1_zfmisc_1(k2_zfmisc_1(C_316,A_315)))
      | v1_xboole_0(C_316)
      | v1_xboole_0(B_319)
      | v1_xboole_0(A_315) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1021,plain,(
    ! [E_317,B_319] :
      ( r2_hidden('#skF_5'('#skF_7','#skF_6',E_317,'#skF_9',B_319),B_319)
      | ~ r2_hidden(E_317,k7_relset_1('#skF_6','#skF_7','#skF_9',B_319))
      | ~ m1_subset_1(E_317,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(B_319)
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_50,c_1016])).

tff(c_1024,plain,(
    ! [E_317,B_319] :
      ( r2_hidden('#skF_5'('#skF_7','#skF_6',E_317,'#skF_9',B_319),B_319)
      | ~ r2_hidden(E_317,k9_relat_1('#skF_9',B_319))
      | ~ m1_subset_1(E_317,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(B_319)
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_1021])).

tff(c_1232,plain,(
    ! [E_356,B_357] :
      ( r2_hidden('#skF_5'('#skF_7','#skF_6',E_356,'#skF_9',B_357),B_357)
      | ~ r2_hidden(E_356,k9_relat_1('#skF_9',B_357))
      | ~ m1_subset_1(E_356,'#skF_7')
      | v1_xboole_0(B_357) ) ),
    inference(negUnitSimplification,[status(thm)],[c_284,c_428,c_1024])).

tff(c_46,plain,(
    ! [F_145] :
      ( k1_funct_1('#skF_9',F_145) != '#skF_10'
      | ~ r2_hidden(F_145,'#skF_8')
      | ~ m1_subset_1(F_145,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1321,plain,(
    ! [E_356] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_6',E_356,'#skF_9','#skF_8')) != '#skF_10'
      | ~ m1_subset_1('#skF_5'('#skF_7','#skF_6',E_356,'#skF_9','#skF_8'),'#skF_6')
      | ~ r2_hidden(E_356,k9_relat_1('#skF_9','#skF_8'))
      | ~ m1_subset_1(E_356,'#skF_7')
      | v1_xboole_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1232,c_46])).

tff(c_1388,plain,(
    ! [E_361] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_6',E_361,'#skF_9','#skF_8')) != '#skF_10'
      | ~ m1_subset_1('#skF_5'('#skF_7','#skF_6',E_361,'#skF_9','#skF_8'),'#skF_6')
      | ~ r2_hidden(E_361,k9_relat_1('#skF_9','#skF_8'))
      | ~ m1_subset_1(E_361,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_1321])).

tff(c_1403,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_6','#skF_10','#skF_9','#skF_8')) != '#skF_10'
    | ~ m1_subset_1('#skF_5'('#skF_7','#skF_6','#skF_10','#skF_9','#skF_8'),'#skF_6')
    | ~ m1_subset_1('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_188,c_1388])).

tff(c_1423,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_6','#skF_10','#skF_9','#skF_8')) != '#skF_10'
    | ~ m1_subset_1('#skF_5'('#skF_7','#skF_6','#skF_10','#skF_9','#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_1403])).

tff(c_1430,plain,(
    ~ m1_subset_1('#skF_5'('#skF_7','#skF_6','#skF_10','#skF_9','#skF_8'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1423])).

tff(c_1176,plain,(
    ! [C_349,B_352,D_351,A_348,E_350] :
      ( m1_subset_1('#skF_5'(A_348,C_349,E_350,D_351,B_352),C_349)
      | ~ r2_hidden(E_350,k7_relset_1(C_349,A_348,D_351,B_352))
      | ~ m1_subset_1(E_350,A_348)
      | ~ m1_subset_1(D_351,k1_zfmisc_1(k2_zfmisc_1(C_349,A_348)))
      | v1_xboole_0(C_349)
      | v1_xboole_0(B_352)
      | v1_xboole_0(A_348) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1187,plain,(
    ! [E_350,D_200] :
      ( m1_subset_1('#skF_5'('#skF_7','#skF_6',E_350,'#skF_9',D_200),'#skF_6')
      | ~ r2_hidden(E_350,k9_relat_1('#skF_9',D_200))
      | ~ m1_subset_1(E_350,'#skF_7')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_200)
      | v1_xboole_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_1176])).

tff(c_1198,plain,(
    ! [E_350,D_200] :
      ( m1_subset_1('#skF_5'('#skF_7','#skF_6',E_350,'#skF_9',D_200),'#skF_6')
      | ~ r2_hidden(E_350,k9_relat_1('#skF_9',D_200))
      | ~ m1_subset_1(E_350,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_200)
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1187])).

tff(c_1609,plain,(
    ! [E_374,D_375] :
      ( m1_subset_1('#skF_5'('#skF_7','#skF_6',E_374,'#skF_9',D_375),'#skF_6')
      | ~ r2_hidden(E_374,k9_relat_1('#skF_9',D_375))
      | ~ m1_subset_1(E_374,'#skF_7')
      | v1_xboole_0(D_375) ) ),
    inference(negUnitSimplification,[status(thm)],[c_284,c_428,c_1198])).

tff(c_1632,plain,
    ( m1_subset_1('#skF_5'('#skF_7','#skF_6','#skF_10','#skF_9','#skF_8'),'#skF_6')
    | ~ m1_subset_1('#skF_10','#skF_7')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_188,c_1609])).

tff(c_1655,plain,
    ( m1_subset_1('#skF_5'('#skF_7','#skF_6','#skF_10','#skF_9','#skF_8'),'#skF_6')
    | v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_1632])).

tff(c_1657,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_1430,c_1655])).

tff(c_1658,plain,(
    k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_6','#skF_10','#skF_9','#skF_8')) != '#skF_10' ),
    inference(splitRight,[status(thm)],[c_1423])).

tff(c_54,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1786,plain,(
    ! [D_396,B_397,C_394,E_395,A_393] :
      ( r2_hidden(k4_tarski('#skF_5'(A_393,C_394,E_395,D_396,B_397),E_395),D_396)
      | ~ r2_hidden(E_395,k7_relset_1(C_394,A_393,D_396,B_397))
      | ~ m1_subset_1(E_395,A_393)
      | ~ m1_subset_1(D_396,k1_zfmisc_1(k2_zfmisc_1(C_394,A_393)))
      | v1_xboole_0(C_394)
      | v1_xboole_0(B_397)
      | v1_xboole_0(A_393) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_20,plain,(
    ! [C_19,A_17,B_18] :
      ( k1_funct_1(C_19,A_17) = B_18
      | ~ r2_hidden(k4_tarski(A_17,B_18),C_19)
      | ~ v1_funct_1(C_19)
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_7003,plain,(
    ! [A_842,B_839,C_840,E_838,D_841] :
      ( k1_funct_1(D_841,'#skF_5'(A_842,C_840,E_838,D_841,B_839)) = E_838
      | ~ v1_funct_1(D_841)
      | ~ v1_relat_1(D_841)
      | ~ r2_hidden(E_838,k7_relset_1(C_840,A_842,D_841,B_839))
      | ~ m1_subset_1(E_838,A_842)
      | ~ m1_subset_1(D_841,k1_zfmisc_1(k2_zfmisc_1(C_840,A_842)))
      | v1_xboole_0(C_840)
      | v1_xboole_0(B_839)
      | v1_xboole_0(A_842) ) ),
    inference(resolution,[status(thm)],[c_1786,c_20])).

tff(c_7025,plain,(
    ! [E_838,D_200] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_6',E_838,'#skF_9',D_200)) = E_838
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(E_838,k9_relat_1('#skF_9',D_200))
      | ~ m1_subset_1(E_838,'#skF_7')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_200)
      | v1_xboole_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_7003])).

tff(c_7042,plain,(
    ! [E_838,D_200] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_6',E_838,'#skF_9',D_200)) = E_838
      | ~ r2_hidden(E_838,k9_relat_1('#skF_9',D_200))
      | ~ m1_subset_1(E_838,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_200)
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_69,c_54,c_7025])).

tff(c_7115,plain,(
    ! [E_844,D_845] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_6',E_844,'#skF_9',D_845)) = E_844
      | ~ r2_hidden(E_844,k9_relat_1('#skF_9',D_845))
      | ~ m1_subset_1(E_844,'#skF_7')
      | v1_xboole_0(D_845) ) ),
    inference(negUnitSimplification,[status(thm)],[c_284,c_428,c_7042])).

tff(c_7197,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_6','#skF_10','#skF_9','#skF_8')) = '#skF_10'
    | ~ m1_subset_1('#skF_10','#skF_7')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_188,c_7115])).

tff(c_7277,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_6','#skF_10','#skF_9','#skF_8')) = '#skF_10'
    | v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_7197])).

tff(c_7279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_1658,c_7277])).

tff(c_7280,plain,(
    r2_hidden('#skF_3'('#skF_7','#skF_6','#skF_9'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_426])).

tff(c_7286,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_7280,c_2])).

tff(c_8038,plain,(
    ! [C_965,E_966,B_968,D_967,A_964] :
      ( m1_subset_1('#skF_5'(A_964,C_965,E_966,D_967,B_968),C_965)
      | ~ r2_hidden(E_966,k7_relset_1(C_965,A_964,D_967,B_968))
      | ~ m1_subset_1(E_966,A_964)
      | ~ m1_subset_1(D_967,k1_zfmisc_1(k2_zfmisc_1(C_965,A_964)))
      | v1_xboole_0(C_965)
      | v1_xboole_0(B_968)
      | v1_xboole_0(A_964) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_8049,plain,(
    ! [E_966,D_200] :
      ( m1_subset_1('#skF_5'('#skF_7','#skF_6',E_966,'#skF_9',D_200),'#skF_6')
      | ~ r2_hidden(E_966,k9_relat_1('#skF_9',D_200))
      | ~ m1_subset_1(E_966,'#skF_7')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_200)
      | v1_xboole_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_8038])).

tff(c_8060,plain,(
    ! [E_966,D_200] :
      ( m1_subset_1('#skF_5'('#skF_7','#skF_6',E_966,'#skF_9',D_200),'#skF_6')
      | ~ r2_hidden(E_966,k9_relat_1('#skF_9',D_200))
      | ~ m1_subset_1(E_966,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_200)
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_8049])).

tff(c_8191,plain,(
    ! [E_993,D_994] :
      ( m1_subset_1('#skF_5'('#skF_7','#skF_6',E_993,'#skF_9',D_994),'#skF_6')
      | ~ r2_hidden(E_993,k9_relat_1('#skF_9',D_994))
      | ~ m1_subset_1(E_993,'#skF_7')
      | v1_xboole_0(D_994) ) ),
    inference(negUnitSimplification,[status(thm)],[c_284,c_7286,c_8060])).

tff(c_8206,plain,
    ( m1_subset_1('#skF_5'('#skF_7','#skF_6','#skF_10','#skF_9','#skF_8'),'#skF_6')
    | ~ m1_subset_1('#skF_10','#skF_7')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_188,c_8191])).

tff(c_8227,plain,
    ( m1_subset_1('#skF_5'('#skF_7','#skF_6','#skF_10','#skF_9','#skF_8'),'#skF_6')
    | v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_8206])).

tff(c_8228,plain,(
    m1_subset_1('#skF_5'('#skF_7','#skF_6','#skF_10','#skF_9','#skF_8'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_8227])).

tff(c_8232,plain,(
    ! [A_995,E_997,D_998,C_996,B_999] :
      ( r2_hidden('#skF_5'(A_995,C_996,E_997,D_998,B_999),B_999)
      | ~ r2_hidden(E_997,k7_relset_1(C_996,A_995,D_998,B_999))
      | ~ m1_subset_1(E_997,A_995)
      | ~ m1_subset_1(D_998,k1_zfmisc_1(k2_zfmisc_1(C_996,A_995)))
      | v1_xboole_0(C_996)
      | v1_xboole_0(B_999)
      | v1_xboole_0(A_995) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_8237,plain,(
    ! [E_997,B_999] :
      ( r2_hidden('#skF_5'('#skF_7','#skF_6',E_997,'#skF_9',B_999),B_999)
      | ~ r2_hidden(E_997,k7_relset_1('#skF_6','#skF_7','#skF_9',B_999))
      | ~ m1_subset_1(E_997,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(B_999)
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_50,c_8232])).

tff(c_8240,plain,(
    ! [E_997,B_999] :
      ( r2_hidden('#skF_5'('#skF_7','#skF_6',E_997,'#skF_9',B_999),B_999)
      | ~ r2_hidden(E_997,k9_relat_1('#skF_9',B_999))
      | ~ m1_subset_1(E_997,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(B_999)
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_8237])).

tff(c_8242,plain,(
    ! [E_1000,B_1001] :
      ( r2_hidden('#skF_5'('#skF_7','#skF_6',E_1000,'#skF_9',B_1001),B_1001)
      | ~ r2_hidden(E_1000,k9_relat_1('#skF_9',B_1001))
      | ~ m1_subset_1(E_1000,'#skF_7')
      | v1_xboole_0(B_1001) ) ),
    inference(negUnitSimplification,[status(thm)],[c_284,c_7286,c_8240])).

tff(c_8343,plain,(
    ! [E_1000] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_6',E_1000,'#skF_9','#skF_8')) != '#skF_10'
      | ~ m1_subset_1('#skF_5'('#skF_7','#skF_6',E_1000,'#skF_9','#skF_8'),'#skF_6')
      | ~ r2_hidden(E_1000,k9_relat_1('#skF_9','#skF_8'))
      | ~ m1_subset_1(E_1000,'#skF_7')
      | v1_xboole_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_8242,c_46])).

tff(c_8408,plain,(
    ! [E_1007] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_6',E_1007,'#skF_9','#skF_8')) != '#skF_10'
      | ~ m1_subset_1('#skF_5'('#skF_7','#skF_6',E_1007,'#skF_9','#skF_8'),'#skF_6')
      | ~ r2_hidden(E_1007,k9_relat_1('#skF_9','#skF_8'))
      | ~ m1_subset_1(E_1007,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_8343])).

tff(c_8423,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_6','#skF_10','#skF_9','#skF_8')) != '#skF_10'
    | ~ m1_subset_1('#skF_5'('#skF_7','#skF_6','#skF_10','#skF_9','#skF_8'),'#skF_6')
    | ~ m1_subset_1('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_188,c_8408])).

tff(c_8443,plain,(
    k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_6','#skF_10','#skF_9','#skF_8')) != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_8228,c_8423])).

tff(c_8518,plain,(
    ! [E_1024,B_1026,C_1023,A_1022,D_1025] :
      ( r2_hidden(k4_tarski('#skF_5'(A_1022,C_1023,E_1024,D_1025,B_1026),E_1024),D_1025)
      | ~ r2_hidden(E_1024,k7_relset_1(C_1023,A_1022,D_1025,B_1026))
      | ~ m1_subset_1(E_1024,A_1022)
      | ~ m1_subset_1(D_1025,k1_zfmisc_1(k2_zfmisc_1(C_1023,A_1022)))
      | v1_xboole_0(C_1023)
      | v1_xboole_0(B_1026)
      | v1_xboole_0(A_1022) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_13310,plain,(
    ! [C_1509,B_1508,D_1510,A_1507,E_1506] :
      ( k1_funct_1(D_1510,'#skF_5'(A_1507,C_1509,E_1506,D_1510,B_1508)) = E_1506
      | ~ v1_funct_1(D_1510)
      | ~ v1_relat_1(D_1510)
      | ~ r2_hidden(E_1506,k7_relset_1(C_1509,A_1507,D_1510,B_1508))
      | ~ m1_subset_1(E_1506,A_1507)
      | ~ m1_subset_1(D_1510,k1_zfmisc_1(k2_zfmisc_1(C_1509,A_1507)))
      | v1_xboole_0(C_1509)
      | v1_xboole_0(B_1508)
      | v1_xboole_0(A_1507) ) ),
    inference(resolution,[status(thm)],[c_8518,c_20])).

tff(c_13332,plain,(
    ! [E_1506,D_200] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_6',E_1506,'#skF_9',D_200)) = E_1506
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(E_1506,k9_relat_1('#skF_9',D_200))
      | ~ m1_subset_1(E_1506,'#skF_7')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_200)
      | v1_xboole_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_13310])).

tff(c_13349,plain,(
    ! [E_1506,D_200] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_6',E_1506,'#skF_9',D_200)) = E_1506
      | ~ r2_hidden(E_1506,k9_relat_1('#skF_9',D_200))
      | ~ m1_subset_1(E_1506,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_200)
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_69,c_54,c_13332])).

tff(c_13353,plain,(
    ! [E_1511,D_1512] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_6',E_1511,'#skF_9',D_1512)) = E_1511
      | ~ r2_hidden(E_1511,k9_relat_1('#skF_9',D_1512))
      | ~ m1_subset_1(E_1511,'#skF_7')
      | v1_xboole_0(D_1512) ) ),
    inference(negUnitSimplification,[status(thm)],[c_284,c_7286,c_13349])).

tff(c_13415,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_6','#skF_10','#skF_9','#skF_8')) = '#skF_10'
    | ~ m1_subset_1('#skF_10','#skF_7')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_188,c_13353])).

tff(c_13474,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_6','#skF_10','#skF_9','#skF_8')) = '#skF_10'
    | v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_13415])).

tff(c_13476,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_8443,c_13474])).

tff(c_13477,plain,(
    ! [D_205] : v1_xboole_0(k9_relat_1('#skF_9',D_205)) ),
    inference(splitRight,[status(thm)],[c_282])).

tff(c_13481,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13477,c_187])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:19:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.48/4.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.48/4.48  
% 10.48/4.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.48/4.48  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 10.48/4.48  
% 10.48/4.48  %Foreground sorts:
% 10.48/4.48  
% 10.48/4.48  
% 10.48/4.48  %Background operators:
% 10.48/4.48  
% 10.48/4.48  
% 10.48/4.48  %Foreground operators:
% 10.48/4.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.48/4.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.48/4.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.48/4.48  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.48/4.48  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.48/4.48  tff('#skF_7', type, '#skF_7': $i).
% 10.48/4.48  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i) > $i).
% 10.48/4.48  tff('#skF_10', type, '#skF_10': $i).
% 10.48/4.48  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 10.48/4.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.48/4.48  tff('#skF_6', type, '#skF_6': $i).
% 10.48/4.48  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 10.48/4.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.48/4.48  tff('#skF_9', type, '#skF_9': $i).
% 10.48/4.48  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.48/4.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.48/4.48  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.48/4.48  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 10.48/4.48  tff('#skF_8', type, '#skF_8': $i).
% 10.48/4.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.48/4.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.48/4.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.48/4.48  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.48/4.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.48/4.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.48/4.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.48/4.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.48/4.48  
% 10.60/4.50  tff(f_138, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 10.60/4.50  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.60/4.50  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 10.60/4.50  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 10.60/4.50  tff(f_81, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 10.60/4.50  tff(f_73, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 10.60/4.50  tff(f_44, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 10.60/4.50  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 10.60/4.50  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.60/4.50  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 10.60/4.50  tff(f_119, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k7_relset_1(C, A, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(F, E), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relset_1)).
% 10.60/4.50  tff(f_65, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 10.60/4.50  tff(c_50, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 10.60/4.50  tff(c_65, plain, (![C_149, A_150, B_151]: (v1_relat_1(C_149) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.60/4.50  tff(c_69, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_50, c_65])).
% 10.60/4.50  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.60/4.50  tff(c_97, plain, (![A_162, B_163, C_164]: (r2_hidden('#skF_2'(A_162, B_163, C_164), B_163) | ~r2_hidden(A_162, k9_relat_1(C_164, B_163)) | ~v1_relat_1(C_164))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.60/4.50  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.60/4.50  tff(c_107, plain, (![B_165, A_166, C_167]: (~v1_xboole_0(B_165) | ~r2_hidden(A_166, k9_relat_1(C_167, B_165)) | ~v1_relat_1(C_167))), inference(resolution, [status(thm)], [c_97, c_2])).
% 10.60/4.50  tff(c_117, plain, (![B_165, C_167]: (~v1_xboole_0(B_165) | ~v1_relat_1(C_167) | v1_xboole_0(k9_relat_1(C_167, B_165)))), inference(resolution, [status(thm)], [c_4, c_107])).
% 10.60/4.50  tff(c_179, plain, (![A_197, B_198, C_199, D_200]: (k7_relset_1(A_197, B_198, C_199, D_200)=k9_relat_1(C_199, D_200) | ~m1_subset_1(C_199, k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.60/4.50  tff(c_186, plain, (![D_200]: (k7_relset_1('#skF_6', '#skF_7', '#skF_9', D_200)=k9_relat_1('#skF_9', D_200))), inference(resolution, [status(thm)], [c_50, c_179])).
% 10.60/4.50  tff(c_48, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 10.60/4.50  tff(c_64, plain, (~v1_xboole_0(k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(resolution, [status(thm)], [c_48, c_2])).
% 10.60/4.50  tff(c_187, plain, (~v1_xboole_0(k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_64])).
% 10.60/4.50  tff(c_208, plain, (~v1_xboole_0('#skF_8') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_117, c_187])).
% 10.60/4.50  tff(c_214, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_208])).
% 10.60/4.50  tff(c_188, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_48])).
% 10.60/4.50  tff(c_189, plain, (![D_201]: (k7_relset_1('#skF_6', '#skF_7', '#skF_9', D_201)=k9_relat_1('#skF_9', D_201))), inference(resolution, [status(thm)], [c_50, c_179])).
% 10.60/4.50  tff(c_26, plain, (![A_23, B_24, C_25, D_26]: (m1_subset_1(k7_relset_1(A_23, B_24, C_25, D_26), k1_zfmisc_1(B_24)) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.60/4.50  tff(c_195, plain, (![D_201]: (m1_subset_1(k9_relat_1('#skF_9', D_201), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_189, c_26])).
% 10.60/4.50  tff(c_275, plain, (![D_205]: (m1_subset_1(k9_relat_1('#skF_9', D_205), k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_195])).
% 10.60/4.50  tff(c_8, plain, (![A_8, C_10, B_9]: (m1_subset_1(A_8, C_10) | ~m1_subset_1(B_9, k1_zfmisc_1(C_10)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.60/4.50  tff(c_285, plain, (![A_206, D_207]: (m1_subset_1(A_206, '#skF_7') | ~r2_hidden(A_206, k9_relat_1('#skF_9', D_207)))), inference(resolution, [status(thm)], [c_275, c_8])).
% 10.60/4.50  tff(c_301, plain, (m1_subset_1('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_188, c_285])).
% 10.60/4.50  tff(c_6, plain, (![B_7, A_5]: (v1_xboole_0(B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_5)) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.60/4.50  tff(c_282, plain, (![D_205]: (v1_xboole_0(k9_relat_1('#skF_9', D_205)) | ~v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_275, c_6])).
% 10.60/4.50  tff(c_284, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_282])).
% 10.60/4.50  tff(c_87, plain, (![A_159, B_160, C_161]: (k1_relset_1(A_159, B_160, C_161)=k1_relat_1(C_161) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.60/4.50  tff(c_91, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_50, c_87])).
% 10.60/4.50  tff(c_418, plain, (![A_220, B_221, C_222]: (r2_hidden('#skF_3'(A_220, B_221, C_222), B_221) | k1_relset_1(B_221, A_220, C_222)=B_221 | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(B_221, A_220))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.60/4.50  tff(c_423, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_6', '#skF_9'), '#skF_6') | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6'), inference(resolution, [status(thm)], [c_50, c_418])).
% 10.60/4.50  tff(c_426, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_6', '#skF_9'), '#skF_6') | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_91, c_423])).
% 10.60/4.50  tff(c_427, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_426])).
% 10.60/4.50  tff(c_132, plain, (![A_180, B_181, C_182]: (r2_hidden('#skF_2'(A_180, B_181, C_182), k1_relat_1(C_182)) | ~r2_hidden(A_180, k9_relat_1(C_182, B_181)) | ~v1_relat_1(C_182))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.60/4.50  tff(c_137, plain, (![C_183, A_184, B_185]: (~v1_xboole_0(k1_relat_1(C_183)) | ~r2_hidden(A_184, k9_relat_1(C_183, B_185)) | ~v1_relat_1(C_183))), inference(resolution, [status(thm)], [c_132, c_2])).
% 10.60/4.50  tff(c_147, plain, (![C_183, B_185]: (~v1_xboole_0(k1_relat_1(C_183)) | ~v1_relat_1(C_183) | v1_xboole_0(k9_relat_1(C_183, B_185)))), inference(resolution, [status(thm)], [c_4, c_137])).
% 10.60/4.50  tff(c_205, plain, (~v1_xboole_0(k1_relat_1('#skF_9')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_147, c_187])).
% 10.60/4.50  tff(c_211, plain, (~v1_xboole_0(k1_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_205])).
% 10.60/4.50  tff(c_428, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_427, c_211])).
% 10.60/4.50  tff(c_1016, plain, (![A_315, E_317, C_316, B_319, D_318]: (r2_hidden('#skF_5'(A_315, C_316, E_317, D_318, B_319), B_319) | ~r2_hidden(E_317, k7_relset_1(C_316, A_315, D_318, B_319)) | ~m1_subset_1(E_317, A_315) | ~m1_subset_1(D_318, k1_zfmisc_1(k2_zfmisc_1(C_316, A_315))) | v1_xboole_0(C_316) | v1_xboole_0(B_319) | v1_xboole_0(A_315))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.60/4.50  tff(c_1021, plain, (![E_317, B_319]: (r2_hidden('#skF_5'('#skF_7', '#skF_6', E_317, '#skF_9', B_319), B_319) | ~r2_hidden(E_317, k7_relset_1('#skF_6', '#skF_7', '#skF_9', B_319)) | ~m1_subset_1(E_317, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(B_319) | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_50, c_1016])).
% 10.60/4.50  tff(c_1024, plain, (![E_317, B_319]: (r2_hidden('#skF_5'('#skF_7', '#skF_6', E_317, '#skF_9', B_319), B_319) | ~r2_hidden(E_317, k9_relat_1('#skF_9', B_319)) | ~m1_subset_1(E_317, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(B_319) | v1_xboole_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_1021])).
% 10.60/4.50  tff(c_1232, plain, (![E_356, B_357]: (r2_hidden('#skF_5'('#skF_7', '#skF_6', E_356, '#skF_9', B_357), B_357) | ~r2_hidden(E_356, k9_relat_1('#skF_9', B_357)) | ~m1_subset_1(E_356, '#skF_7') | v1_xboole_0(B_357))), inference(negUnitSimplification, [status(thm)], [c_284, c_428, c_1024])).
% 10.60/4.50  tff(c_46, plain, (![F_145]: (k1_funct_1('#skF_9', F_145)!='#skF_10' | ~r2_hidden(F_145, '#skF_8') | ~m1_subset_1(F_145, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 10.60/4.50  tff(c_1321, plain, (![E_356]: (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_6', E_356, '#skF_9', '#skF_8'))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_7', '#skF_6', E_356, '#skF_9', '#skF_8'), '#skF_6') | ~r2_hidden(E_356, k9_relat_1('#skF_9', '#skF_8')) | ~m1_subset_1(E_356, '#skF_7') | v1_xboole_0('#skF_8'))), inference(resolution, [status(thm)], [c_1232, c_46])).
% 10.60/4.50  tff(c_1388, plain, (![E_361]: (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_6', E_361, '#skF_9', '#skF_8'))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_7', '#skF_6', E_361, '#skF_9', '#skF_8'), '#skF_6') | ~r2_hidden(E_361, k9_relat_1('#skF_9', '#skF_8')) | ~m1_subset_1(E_361, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_214, c_1321])).
% 10.60/4.50  tff(c_1403, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_6', '#skF_10', '#skF_9', '#skF_8'))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_7', '#skF_6', '#skF_10', '#skF_9', '#skF_8'), '#skF_6') | ~m1_subset_1('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_188, c_1388])).
% 10.60/4.50  tff(c_1423, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_6', '#skF_10', '#skF_9', '#skF_8'))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_7', '#skF_6', '#skF_10', '#skF_9', '#skF_8'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_301, c_1403])).
% 10.60/4.50  tff(c_1430, plain, (~m1_subset_1('#skF_5'('#skF_7', '#skF_6', '#skF_10', '#skF_9', '#skF_8'), '#skF_6')), inference(splitLeft, [status(thm)], [c_1423])).
% 10.60/4.50  tff(c_1176, plain, (![C_349, B_352, D_351, A_348, E_350]: (m1_subset_1('#skF_5'(A_348, C_349, E_350, D_351, B_352), C_349) | ~r2_hidden(E_350, k7_relset_1(C_349, A_348, D_351, B_352)) | ~m1_subset_1(E_350, A_348) | ~m1_subset_1(D_351, k1_zfmisc_1(k2_zfmisc_1(C_349, A_348))) | v1_xboole_0(C_349) | v1_xboole_0(B_352) | v1_xboole_0(A_348))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.60/4.50  tff(c_1187, plain, (![E_350, D_200]: (m1_subset_1('#skF_5'('#skF_7', '#skF_6', E_350, '#skF_9', D_200), '#skF_6') | ~r2_hidden(E_350, k9_relat_1('#skF_9', D_200)) | ~m1_subset_1(E_350, '#skF_7') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | v1_xboole_0('#skF_6') | v1_xboole_0(D_200) | v1_xboole_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_186, c_1176])).
% 10.60/4.50  tff(c_1198, plain, (![E_350, D_200]: (m1_subset_1('#skF_5'('#skF_7', '#skF_6', E_350, '#skF_9', D_200), '#skF_6') | ~r2_hidden(E_350, k9_relat_1('#skF_9', D_200)) | ~m1_subset_1(E_350, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(D_200) | v1_xboole_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1187])).
% 10.60/4.50  tff(c_1609, plain, (![E_374, D_375]: (m1_subset_1('#skF_5'('#skF_7', '#skF_6', E_374, '#skF_9', D_375), '#skF_6') | ~r2_hidden(E_374, k9_relat_1('#skF_9', D_375)) | ~m1_subset_1(E_374, '#skF_7') | v1_xboole_0(D_375))), inference(negUnitSimplification, [status(thm)], [c_284, c_428, c_1198])).
% 10.60/4.50  tff(c_1632, plain, (m1_subset_1('#skF_5'('#skF_7', '#skF_6', '#skF_10', '#skF_9', '#skF_8'), '#skF_6') | ~m1_subset_1('#skF_10', '#skF_7') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_188, c_1609])).
% 10.60/4.50  tff(c_1655, plain, (m1_subset_1('#skF_5'('#skF_7', '#skF_6', '#skF_10', '#skF_9', '#skF_8'), '#skF_6') | v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_301, c_1632])).
% 10.60/4.50  tff(c_1657, plain, $false, inference(negUnitSimplification, [status(thm)], [c_214, c_1430, c_1655])).
% 10.60/4.50  tff(c_1658, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_6', '#skF_10', '#skF_9', '#skF_8'))!='#skF_10'), inference(splitRight, [status(thm)], [c_1423])).
% 10.60/4.50  tff(c_54, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_138])).
% 10.60/4.50  tff(c_1786, plain, (![D_396, B_397, C_394, E_395, A_393]: (r2_hidden(k4_tarski('#skF_5'(A_393, C_394, E_395, D_396, B_397), E_395), D_396) | ~r2_hidden(E_395, k7_relset_1(C_394, A_393, D_396, B_397)) | ~m1_subset_1(E_395, A_393) | ~m1_subset_1(D_396, k1_zfmisc_1(k2_zfmisc_1(C_394, A_393))) | v1_xboole_0(C_394) | v1_xboole_0(B_397) | v1_xboole_0(A_393))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.60/4.50  tff(c_20, plain, (![C_19, A_17, B_18]: (k1_funct_1(C_19, A_17)=B_18 | ~r2_hidden(k4_tarski(A_17, B_18), C_19) | ~v1_funct_1(C_19) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.60/4.50  tff(c_7003, plain, (![A_842, B_839, C_840, E_838, D_841]: (k1_funct_1(D_841, '#skF_5'(A_842, C_840, E_838, D_841, B_839))=E_838 | ~v1_funct_1(D_841) | ~v1_relat_1(D_841) | ~r2_hidden(E_838, k7_relset_1(C_840, A_842, D_841, B_839)) | ~m1_subset_1(E_838, A_842) | ~m1_subset_1(D_841, k1_zfmisc_1(k2_zfmisc_1(C_840, A_842))) | v1_xboole_0(C_840) | v1_xboole_0(B_839) | v1_xboole_0(A_842))), inference(resolution, [status(thm)], [c_1786, c_20])).
% 10.60/4.50  tff(c_7025, plain, (![E_838, D_200]: (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_6', E_838, '#skF_9', D_200))=E_838 | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(E_838, k9_relat_1('#skF_9', D_200)) | ~m1_subset_1(E_838, '#skF_7') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | v1_xboole_0('#skF_6') | v1_xboole_0(D_200) | v1_xboole_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_186, c_7003])).
% 10.60/4.50  tff(c_7042, plain, (![E_838, D_200]: (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_6', E_838, '#skF_9', D_200))=E_838 | ~r2_hidden(E_838, k9_relat_1('#skF_9', D_200)) | ~m1_subset_1(E_838, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(D_200) | v1_xboole_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_69, c_54, c_7025])).
% 10.60/4.50  tff(c_7115, plain, (![E_844, D_845]: (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_6', E_844, '#skF_9', D_845))=E_844 | ~r2_hidden(E_844, k9_relat_1('#skF_9', D_845)) | ~m1_subset_1(E_844, '#skF_7') | v1_xboole_0(D_845))), inference(negUnitSimplification, [status(thm)], [c_284, c_428, c_7042])).
% 10.60/4.50  tff(c_7197, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_6', '#skF_10', '#skF_9', '#skF_8'))='#skF_10' | ~m1_subset_1('#skF_10', '#skF_7') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_188, c_7115])).
% 10.60/4.50  tff(c_7277, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_6', '#skF_10', '#skF_9', '#skF_8'))='#skF_10' | v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_301, c_7197])).
% 10.60/4.50  tff(c_7279, plain, $false, inference(negUnitSimplification, [status(thm)], [c_214, c_1658, c_7277])).
% 10.60/4.50  tff(c_7280, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_6', '#skF_9'), '#skF_6')), inference(splitRight, [status(thm)], [c_426])).
% 10.60/4.50  tff(c_7286, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_7280, c_2])).
% 10.60/4.50  tff(c_8038, plain, (![C_965, E_966, B_968, D_967, A_964]: (m1_subset_1('#skF_5'(A_964, C_965, E_966, D_967, B_968), C_965) | ~r2_hidden(E_966, k7_relset_1(C_965, A_964, D_967, B_968)) | ~m1_subset_1(E_966, A_964) | ~m1_subset_1(D_967, k1_zfmisc_1(k2_zfmisc_1(C_965, A_964))) | v1_xboole_0(C_965) | v1_xboole_0(B_968) | v1_xboole_0(A_964))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.60/4.50  tff(c_8049, plain, (![E_966, D_200]: (m1_subset_1('#skF_5'('#skF_7', '#skF_6', E_966, '#skF_9', D_200), '#skF_6') | ~r2_hidden(E_966, k9_relat_1('#skF_9', D_200)) | ~m1_subset_1(E_966, '#skF_7') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | v1_xboole_0('#skF_6') | v1_xboole_0(D_200) | v1_xboole_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_186, c_8038])).
% 10.60/4.50  tff(c_8060, plain, (![E_966, D_200]: (m1_subset_1('#skF_5'('#skF_7', '#skF_6', E_966, '#skF_9', D_200), '#skF_6') | ~r2_hidden(E_966, k9_relat_1('#skF_9', D_200)) | ~m1_subset_1(E_966, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(D_200) | v1_xboole_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_8049])).
% 10.60/4.50  tff(c_8191, plain, (![E_993, D_994]: (m1_subset_1('#skF_5'('#skF_7', '#skF_6', E_993, '#skF_9', D_994), '#skF_6') | ~r2_hidden(E_993, k9_relat_1('#skF_9', D_994)) | ~m1_subset_1(E_993, '#skF_7') | v1_xboole_0(D_994))), inference(negUnitSimplification, [status(thm)], [c_284, c_7286, c_8060])).
% 10.60/4.50  tff(c_8206, plain, (m1_subset_1('#skF_5'('#skF_7', '#skF_6', '#skF_10', '#skF_9', '#skF_8'), '#skF_6') | ~m1_subset_1('#skF_10', '#skF_7') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_188, c_8191])).
% 10.60/4.50  tff(c_8227, plain, (m1_subset_1('#skF_5'('#skF_7', '#skF_6', '#skF_10', '#skF_9', '#skF_8'), '#skF_6') | v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_301, c_8206])).
% 10.60/4.50  tff(c_8228, plain, (m1_subset_1('#skF_5'('#skF_7', '#skF_6', '#skF_10', '#skF_9', '#skF_8'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_214, c_8227])).
% 10.60/4.50  tff(c_8232, plain, (![A_995, E_997, D_998, C_996, B_999]: (r2_hidden('#skF_5'(A_995, C_996, E_997, D_998, B_999), B_999) | ~r2_hidden(E_997, k7_relset_1(C_996, A_995, D_998, B_999)) | ~m1_subset_1(E_997, A_995) | ~m1_subset_1(D_998, k1_zfmisc_1(k2_zfmisc_1(C_996, A_995))) | v1_xboole_0(C_996) | v1_xboole_0(B_999) | v1_xboole_0(A_995))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.60/4.50  tff(c_8237, plain, (![E_997, B_999]: (r2_hidden('#skF_5'('#skF_7', '#skF_6', E_997, '#skF_9', B_999), B_999) | ~r2_hidden(E_997, k7_relset_1('#skF_6', '#skF_7', '#skF_9', B_999)) | ~m1_subset_1(E_997, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(B_999) | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_50, c_8232])).
% 10.60/4.50  tff(c_8240, plain, (![E_997, B_999]: (r2_hidden('#skF_5'('#skF_7', '#skF_6', E_997, '#skF_9', B_999), B_999) | ~r2_hidden(E_997, k9_relat_1('#skF_9', B_999)) | ~m1_subset_1(E_997, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(B_999) | v1_xboole_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_8237])).
% 10.60/4.50  tff(c_8242, plain, (![E_1000, B_1001]: (r2_hidden('#skF_5'('#skF_7', '#skF_6', E_1000, '#skF_9', B_1001), B_1001) | ~r2_hidden(E_1000, k9_relat_1('#skF_9', B_1001)) | ~m1_subset_1(E_1000, '#skF_7') | v1_xboole_0(B_1001))), inference(negUnitSimplification, [status(thm)], [c_284, c_7286, c_8240])).
% 10.60/4.50  tff(c_8343, plain, (![E_1000]: (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_6', E_1000, '#skF_9', '#skF_8'))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_7', '#skF_6', E_1000, '#skF_9', '#skF_8'), '#skF_6') | ~r2_hidden(E_1000, k9_relat_1('#skF_9', '#skF_8')) | ~m1_subset_1(E_1000, '#skF_7') | v1_xboole_0('#skF_8'))), inference(resolution, [status(thm)], [c_8242, c_46])).
% 10.60/4.50  tff(c_8408, plain, (![E_1007]: (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_6', E_1007, '#skF_9', '#skF_8'))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_7', '#skF_6', E_1007, '#skF_9', '#skF_8'), '#skF_6') | ~r2_hidden(E_1007, k9_relat_1('#skF_9', '#skF_8')) | ~m1_subset_1(E_1007, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_214, c_8343])).
% 10.60/4.50  tff(c_8423, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_6', '#skF_10', '#skF_9', '#skF_8'))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_7', '#skF_6', '#skF_10', '#skF_9', '#skF_8'), '#skF_6') | ~m1_subset_1('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_188, c_8408])).
% 10.60/4.50  tff(c_8443, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_6', '#skF_10', '#skF_9', '#skF_8'))!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_301, c_8228, c_8423])).
% 10.60/4.50  tff(c_8518, plain, (![E_1024, B_1026, C_1023, A_1022, D_1025]: (r2_hidden(k4_tarski('#skF_5'(A_1022, C_1023, E_1024, D_1025, B_1026), E_1024), D_1025) | ~r2_hidden(E_1024, k7_relset_1(C_1023, A_1022, D_1025, B_1026)) | ~m1_subset_1(E_1024, A_1022) | ~m1_subset_1(D_1025, k1_zfmisc_1(k2_zfmisc_1(C_1023, A_1022))) | v1_xboole_0(C_1023) | v1_xboole_0(B_1026) | v1_xboole_0(A_1022))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.60/4.50  tff(c_13310, plain, (![C_1509, B_1508, D_1510, A_1507, E_1506]: (k1_funct_1(D_1510, '#skF_5'(A_1507, C_1509, E_1506, D_1510, B_1508))=E_1506 | ~v1_funct_1(D_1510) | ~v1_relat_1(D_1510) | ~r2_hidden(E_1506, k7_relset_1(C_1509, A_1507, D_1510, B_1508)) | ~m1_subset_1(E_1506, A_1507) | ~m1_subset_1(D_1510, k1_zfmisc_1(k2_zfmisc_1(C_1509, A_1507))) | v1_xboole_0(C_1509) | v1_xboole_0(B_1508) | v1_xboole_0(A_1507))), inference(resolution, [status(thm)], [c_8518, c_20])).
% 10.60/4.50  tff(c_13332, plain, (![E_1506, D_200]: (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_6', E_1506, '#skF_9', D_200))=E_1506 | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(E_1506, k9_relat_1('#skF_9', D_200)) | ~m1_subset_1(E_1506, '#skF_7') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | v1_xboole_0('#skF_6') | v1_xboole_0(D_200) | v1_xboole_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_186, c_13310])).
% 10.60/4.50  tff(c_13349, plain, (![E_1506, D_200]: (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_6', E_1506, '#skF_9', D_200))=E_1506 | ~r2_hidden(E_1506, k9_relat_1('#skF_9', D_200)) | ~m1_subset_1(E_1506, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(D_200) | v1_xboole_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_69, c_54, c_13332])).
% 10.60/4.50  tff(c_13353, plain, (![E_1511, D_1512]: (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_6', E_1511, '#skF_9', D_1512))=E_1511 | ~r2_hidden(E_1511, k9_relat_1('#skF_9', D_1512)) | ~m1_subset_1(E_1511, '#skF_7') | v1_xboole_0(D_1512))), inference(negUnitSimplification, [status(thm)], [c_284, c_7286, c_13349])).
% 10.60/4.50  tff(c_13415, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_6', '#skF_10', '#skF_9', '#skF_8'))='#skF_10' | ~m1_subset_1('#skF_10', '#skF_7') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_188, c_13353])).
% 10.60/4.50  tff(c_13474, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_6', '#skF_10', '#skF_9', '#skF_8'))='#skF_10' | v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_301, c_13415])).
% 10.60/4.50  tff(c_13476, plain, $false, inference(negUnitSimplification, [status(thm)], [c_214, c_8443, c_13474])).
% 10.60/4.50  tff(c_13477, plain, (![D_205]: (v1_xboole_0(k9_relat_1('#skF_9', D_205)))), inference(splitRight, [status(thm)], [c_282])).
% 10.60/4.50  tff(c_13481, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13477, c_187])).
% 10.60/4.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.60/4.50  
% 10.60/4.50  Inference rules
% 10.60/4.50  ----------------------
% 10.60/4.50  #Ref     : 0
% 10.60/4.50  #Sup     : 2896
% 10.60/4.50  #Fact    : 0
% 10.60/4.50  #Define  : 0
% 10.60/4.50  #Split   : 19
% 10.60/4.50  #Chain   : 0
% 10.60/4.50  #Close   : 0
% 10.60/4.50  
% 10.60/4.50  Ordering : KBO
% 10.60/4.50  
% 10.60/4.50  Simplification rules
% 10.60/4.50  ----------------------
% 10.60/4.50  #Subsume      : 777
% 10.60/4.50  #Demod        : 731
% 10.60/4.50  #Tautology    : 134
% 10.60/4.50  #SimpNegUnit  : 115
% 10.60/4.50  #BackRed      : 5
% 10.60/4.50  
% 10.60/4.50  #Partial instantiations: 0
% 10.60/4.50  #Strategies tried      : 1
% 10.60/4.50  
% 10.60/4.50  Timing (in seconds)
% 10.60/4.50  ----------------------
% 10.60/4.50  Preprocessing        : 0.34
% 10.60/4.50  Parsing              : 0.17
% 10.60/4.50  CNF conversion       : 0.03
% 10.60/4.50  Main loop            : 3.27
% 10.60/4.50  Inferencing          : 0.80
% 10.60/4.50  Reduction            : 0.62
% 10.60/4.50  Demodulation         : 0.44
% 10.60/4.51  BG Simplification    : 0.09
% 10.60/4.51  Subsumption          : 1.58
% 10.60/4.51  Abstraction          : 0.13
% 10.60/4.51  MUC search           : 0.00
% 10.60/4.51  Cooper               : 0.00
% 10.60/4.51  Total                : 3.66
% 10.60/4.51  Index Insertion      : 0.00
% 10.60/4.51  Index Deletion       : 0.00
% 10.60/4.51  Index Matching       : 0.00
% 10.60/4.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
