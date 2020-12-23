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
% DateTime   : Thu Dec  3 10:16:24 EST 2020

% Result     : Theorem 14.23s
% Output     : CNFRefutation 14.40s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 481 expanded)
%              Number of leaves         :   40 ( 179 expanded)
%              Depth                    :   11
%              Number of atoms          :  323 (1308 expanded)
%              Number of equality atoms :   44 ( 202 expanded)
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
                  ~ ( r2_hidden(F,A)
                    & r2_hidden(F,C)
                    & E = k1_funct_1(D,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

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

tff(c_209,plain,(
    ! [A_195,B_196,C_197,D_198] :
      ( k7_relset_1(A_195,B_196,C_197,D_198) = k9_relat_1(C_197,D_198)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_195,B_196))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_216,plain,(
    ! [D_198] : k7_relset_1('#skF_6','#skF_7','#skF_9',D_198) = k9_relat_1('#skF_9',D_198) ),
    inference(resolution,[status(thm)],[c_52,c_209])).

tff(c_50,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_218,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_50])).

tff(c_219,plain,(
    ! [D_199] : k7_relset_1('#skF_6','#skF_7','#skF_9',D_199) = k9_relat_1('#skF_9',D_199) ),
    inference(resolution,[status(thm)],[c_52,c_209])).

tff(c_28,plain,(
    ! [A_26,B_27,C_28,D_29] :
      ( m1_subset_1(k7_relset_1(A_26,B_27,C_28,D_29),k1_zfmisc_1(B_27))
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_225,plain,(
    ! [D_199] :
      ( m1_subset_1(k9_relat_1('#skF_9',D_199),k1_zfmisc_1('#skF_7'))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_28])).

tff(c_249,plain,(
    ! [D_200] : m1_subset_1(k9_relat_1('#skF_9',D_200),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_225])).

tff(c_8,plain,(
    ! [A_7,C_9,B_8] :
      ( m1_subset_1(A_7,C_9)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(C_9))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_253,plain,(
    ! [A_201,D_202] :
      ( m1_subset_1(A_201,'#skF_7')
      | ~ r2_hidden(A_201,k9_relat_1('#skF_9',D_202)) ) ),
    inference(resolution,[status(thm)],[c_249,c_8])).

tff(c_269,plain,(
    m1_subset_1('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_218,c_253])).

tff(c_135,plain,(
    ! [A_173,B_174,C_175] :
      ( r2_hidden('#skF_2'(A_173,B_174,C_175),B_174)
      | ~ r2_hidden(A_173,k9_relat_1(C_175,B_174))
      | ~ v1_relat_1(C_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_149,plain,(
    ! [B_174,A_173,C_175] :
      ( ~ v1_xboole_0(B_174)
      | ~ r2_hidden(A_173,k9_relat_1(C_175,B_174))
      | ~ v1_relat_1(C_175) ) ),
    inference(resolution,[status(thm)],[c_135,c_2])).

tff(c_235,plain,
    ( ~ v1_xboole_0('#skF_8')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_218,c_149])).

tff(c_241,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_235])).

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

tff(c_333,plain,(
    ! [A_223,B_224,C_225] :
      ( r2_hidden(k4_tarski('#skF_2'(A_223,B_224,C_225),A_223),C_225)
      | ~ r2_hidden(A_223,k9_relat_1(C_225,B_224))
      | ~ v1_relat_1(C_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_20,plain,(
    ! [C_18,A_16,B_17] :
      ( k1_funct_1(C_18,A_16) = B_17
      | ~ r2_hidden(k4_tarski(A_16,B_17),C_18)
      | ~ v1_funct_1(C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_793,plain,(
    ! [C_289,A_290,B_291] :
      ( k1_funct_1(C_289,'#skF_2'(A_290,B_291,C_289)) = A_290
      | ~ v1_funct_1(C_289)
      | ~ r2_hidden(A_290,k9_relat_1(C_289,B_291))
      | ~ v1_relat_1(C_289) ) ),
    inference(resolution,[status(thm)],[c_333,c_20])).

tff(c_801,plain,
    ( k1_funct_1('#skF_9','#skF_2'('#skF_10','#skF_8','#skF_9')) = '#skF_10'
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_218,c_793])).

tff(c_815,plain,(
    k1_funct_1('#skF_9','#skF_2'('#skF_10','#skF_8','#skF_9')) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_56,c_801])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] :
      ( r2_hidden('#skF_2'(A_10,B_11,C_12),B_11)
      | ~ r2_hidden(A_10,k9_relat_1(C_12,B_11))
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_99,plain,(
    ! [A_165,B_166,C_167] :
      ( k1_relset_1(A_165,B_166,C_167) = k1_relat_1(C_167)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_103,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_52,c_99])).

tff(c_624,plain,(
    ! [A_260,B_261,C_262] :
      ( r2_hidden('#skF_3'(A_260,B_261,C_262),B_261)
      | k1_relset_1(B_261,A_260,C_262) = B_261
      | ~ m1_subset_1(C_262,k1_zfmisc_1(k2_zfmisc_1(B_261,A_260))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_629,plain,
    ( r2_hidden('#skF_3'('#skF_7','#skF_6','#skF_9'),'#skF_6')
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_52,c_624])).

tff(c_632,plain,
    ( r2_hidden('#skF_3'('#skF_7','#skF_6','#skF_9'),'#skF_6')
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_629])).

tff(c_633,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_632])).

tff(c_16,plain,(
    ! [A_10,B_11,C_12] :
      ( r2_hidden('#skF_2'(A_10,B_11,C_12),k1_relat_1(C_12))
      | ~ r2_hidden(A_10,k9_relat_1(C_12,B_11))
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_651,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_2'(A_10,B_11,'#skF_9'),'#skF_6')
      | ~ r2_hidden(A_10,k9_relat_1('#skF_9',B_11))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_633,c_16])).

tff(c_669,plain,(
    ! [A_263,B_264] :
      ( r2_hidden('#skF_2'(A_263,B_264,'#skF_9'),'#skF_6')
      | ~ r2_hidden(A_263,k9_relat_1('#skF_9',B_264)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_651])).

tff(c_48,plain,(
    ! [F_148] :
      ( k1_funct_1('#skF_9',F_148) != '#skF_10'
      | ~ r2_hidden(F_148,'#skF_8')
      | ~ r2_hidden(F_148,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_819,plain,(
    ! [A_292,B_293] :
      ( k1_funct_1('#skF_9','#skF_2'(A_292,B_293,'#skF_9')) != '#skF_10'
      | ~ r2_hidden('#skF_2'(A_292,B_293,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_292,k9_relat_1('#skF_9',B_293)) ) ),
    inference(resolution,[status(thm)],[c_669,c_48])).

tff(c_823,plain,(
    ! [A_10] :
      ( k1_funct_1('#skF_9','#skF_2'(A_10,'#skF_8','#skF_9')) != '#skF_10'
      | ~ r2_hidden(A_10,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_12,c_819])).

tff(c_842,plain,(
    ! [A_294] :
      ( k1_funct_1('#skF_9','#skF_2'(A_294,'#skF_8','#skF_9')) != '#skF_10'
      | ~ r2_hidden(A_294,k9_relat_1('#skF_9','#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_823])).

tff(c_853,plain,(
    k1_funct_1('#skF_9','#skF_2'('#skF_10','#skF_8','#skF_9')) != '#skF_10' ),
    inference(resolution,[status(thm)],[c_218,c_842])).

tff(c_871,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_815,c_853])).

tff(c_872,plain,(
    r2_hidden('#skF_3'('#skF_7','#skF_6','#skF_9'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_632])).

tff(c_881,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_872,c_2])).

tff(c_1612,plain,(
    ! [B_380,C_381,E_382,A_379,D_378] :
      ( m1_subset_1('#skF_5'(D_378,A_379,B_380,C_381,E_382),C_381)
      | ~ r2_hidden(E_382,k7_relset_1(C_381,A_379,D_378,B_380))
      | ~ m1_subset_1(E_382,A_379)
      | ~ m1_subset_1(D_378,k1_zfmisc_1(k2_zfmisc_1(C_381,A_379)))
      | v1_xboole_0(C_381)
      | v1_xboole_0(B_380)
      | v1_xboole_0(A_379) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1623,plain,(
    ! [D_198,E_382] :
      ( m1_subset_1('#skF_5'('#skF_9','#skF_7',D_198,'#skF_6',E_382),'#skF_6')
      | ~ r2_hidden(E_382,k9_relat_1('#skF_9',D_198))
      | ~ m1_subset_1(E_382,'#skF_7')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_198)
      | v1_xboole_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_1612])).

tff(c_1637,plain,(
    ! [D_198,E_382] :
      ( m1_subset_1('#skF_5'('#skF_9','#skF_7',D_198,'#skF_6',E_382),'#skF_6')
      | ~ r2_hidden(E_382,k9_relat_1('#skF_9',D_198))
      | ~ m1_subset_1(E_382,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_198)
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1623])).

tff(c_1941,plain,(
    ! [D_419,E_420] :
      ( m1_subset_1('#skF_5'('#skF_9','#skF_7',D_419,'#skF_6',E_420),'#skF_6')
      | ~ r2_hidden(E_420,k9_relat_1('#skF_9',D_419))
      | ~ m1_subset_1(E_420,'#skF_7')
      | v1_xboole_0(D_419) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_881,c_1637])).

tff(c_1964,plain,
    ( m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6','#skF_10'),'#skF_6')
    | ~ m1_subset_1('#skF_10','#skF_7')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_218,c_1941])).

tff(c_1987,plain,
    ( m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6','#skF_10'),'#skF_6')
    | v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_1964])).

tff(c_1988,plain,(
    m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6','#skF_10'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_241,c_1987])).

tff(c_2041,plain,(
    ! [B_431,C_432,A_430,E_433,D_429] :
      ( r2_hidden(k4_tarski('#skF_5'(D_429,A_430,B_431,C_432,E_433),E_433),D_429)
      | ~ r2_hidden(E_433,k7_relset_1(C_432,A_430,D_429,B_431))
      | ~ m1_subset_1(E_433,A_430)
      | ~ m1_subset_1(D_429,k1_zfmisc_1(k2_zfmisc_1(C_432,A_430)))
      | v1_xboole_0(C_432)
      | v1_xboole_0(B_431)
      | v1_xboole_0(A_430) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_11245,plain,(
    ! [D_1176,B_1180,A_1177,E_1178,C_1179] :
      ( k1_funct_1(D_1176,'#skF_5'(D_1176,A_1177,B_1180,C_1179,E_1178)) = E_1178
      | ~ v1_funct_1(D_1176)
      | ~ v1_relat_1(D_1176)
      | ~ r2_hidden(E_1178,k7_relset_1(C_1179,A_1177,D_1176,B_1180))
      | ~ m1_subset_1(E_1178,A_1177)
      | ~ m1_subset_1(D_1176,k1_zfmisc_1(k2_zfmisc_1(C_1179,A_1177)))
      | v1_xboole_0(C_1179)
      | v1_xboole_0(B_1180)
      | v1_xboole_0(A_1177) ) ),
    inference(resolution,[status(thm)],[c_2041,c_20])).

tff(c_11265,plain,(
    ! [D_198,E_1178] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_7',D_198,'#skF_6',E_1178)) = E_1178
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(E_1178,k9_relat_1('#skF_9',D_198))
      | ~ m1_subset_1(E_1178,'#skF_7')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_198)
      | v1_xboole_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_11245])).

tff(c_11282,plain,(
    ! [D_198,E_1178] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_7',D_198,'#skF_6',E_1178)) = E_1178
      | ~ r2_hidden(E_1178,k9_relat_1('#skF_9',D_198))
      | ~ m1_subset_1(E_1178,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_198)
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_76,c_56,c_11265])).

tff(c_11287,plain,(
    ! [D_1181,E_1182] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_7',D_1181,'#skF_6',E_1182)) = E_1182
      | ~ r2_hidden(E_1182,k9_relat_1('#skF_9',D_1181))
      | ~ m1_subset_1(E_1182,'#skF_7')
      | v1_xboole_0(D_1181) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_881,c_11282])).

tff(c_11360,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6','#skF_10')) = '#skF_10'
    | ~ m1_subset_1('#skF_10','#skF_7')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_218,c_11287])).

tff(c_11426,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6','#skF_10')) = '#skF_10'
    | v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_11360])).

tff(c_11427,plain,(
    k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6','#skF_10')) = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_241,c_11426])).

tff(c_1794,plain,(
    ! [B_414,D_412,C_415,A_413,E_416] :
      ( r2_hidden('#skF_5'(D_412,A_413,B_414,C_415,E_416),B_414)
      | ~ r2_hidden(E_416,k7_relset_1(C_415,A_413,D_412,B_414))
      | ~ m1_subset_1(E_416,A_413)
      | ~ m1_subset_1(D_412,k1_zfmisc_1(k2_zfmisc_1(C_415,A_413)))
      | v1_xboole_0(C_415)
      | v1_xboole_0(B_414)
      | v1_xboole_0(A_413) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1799,plain,(
    ! [B_414,E_416] :
      ( r2_hidden('#skF_5'('#skF_9','#skF_7',B_414,'#skF_6',E_416),B_414)
      | ~ r2_hidden(E_416,k7_relset_1('#skF_6','#skF_7','#skF_9',B_414))
      | ~ m1_subset_1(E_416,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(B_414)
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_52,c_1794])).

tff(c_1802,plain,(
    ! [B_414,E_416] :
      ( r2_hidden('#skF_5'('#skF_9','#skF_7',B_414,'#skF_6',E_416),B_414)
      | ~ r2_hidden(E_416,k9_relat_1('#skF_9',B_414))
      | ~ m1_subset_1(E_416,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(B_414)
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_1799])).

tff(c_1804,plain,(
    ! [B_417,E_418] :
      ( r2_hidden('#skF_5'('#skF_9','#skF_7',B_417,'#skF_6',E_418),B_417)
      | ~ r2_hidden(E_418,k9_relat_1('#skF_9',B_417))
      | ~ m1_subset_1(E_418,'#skF_7')
      | v1_xboole_0(B_417) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_881,c_1802])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_77,plain,(
    ! [F_157] :
      ( k1_funct_1('#skF_9',F_157) != '#skF_10'
      | ~ r2_hidden(F_157,'#skF_8')
      | ~ r2_hidden(F_157,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_86,plain,(
    ! [A_5] :
      ( k1_funct_1('#skF_9',A_5) != '#skF_10'
      | ~ r2_hidden(A_5,'#skF_8')
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_5,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_6,c_77])).

tff(c_109,plain,(
    ! [A_5] :
      ( k1_funct_1('#skF_9',A_5) != '#skF_10'
      | ~ r2_hidden(A_5,'#skF_8')
      | ~ m1_subset_1(A_5,'#skF_6') ) ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_1901,plain,(
    ! [E_418] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6',E_418)) != '#skF_10'
      | ~ m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6',E_418),'#skF_6')
      | ~ r2_hidden(E_418,k9_relat_1('#skF_9','#skF_8'))
      | ~ m1_subset_1(E_418,'#skF_7')
      | v1_xboole_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1804,c_109])).

tff(c_19206,plain,(
    ! [E_1536] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6',E_1536)) != '#skF_10'
      | ~ m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6',E_1536),'#skF_6')
      | ~ r2_hidden(E_1536,k9_relat_1('#skF_9','#skF_8'))
      | ~ m1_subset_1(E_1536,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_241,c_1901])).

tff(c_19261,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6','#skF_10')) != '#skF_10'
    | ~ m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8','#skF_6','#skF_10'),'#skF_6')
    | ~ m1_subset_1('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_218,c_19206])).

tff(c_19312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_1988,c_11427,c_19261])).

tff(c_19313,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_19679,plain,(
    ! [A_1600,B_1601,C_1602] :
      ( r2_hidden('#skF_3'(A_1600,B_1601,C_1602),B_1601)
      | k1_relset_1(B_1601,A_1600,C_1602) = B_1601
      | ~ m1_subset_1(C_1602,k1_zfmisc_1(k2_zfmisc_1(B_1601,A_1600))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_19684,plain,
    ( r2_hidden('#skF_3'('#skF_7','#skF_6','#skF_9'),'#skF_6')
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_52,c_19679])).

tff(c_19687,plain,
    ( r2_hidden('#skF_3'('#skF_7','#skF_6','#skF_9'),'#skF_6')
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_19684])).

tff(c_19688,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_19687])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_19358,plain,(
    ! [A_1551,B_1552,C_1553] :
      ( r2_hidden('#skF_2'(A_1551,B_1552,C_1553),k1_relat_1(C_1553))
      | ~ r2_hidden(A_1551,k9_relat_1(C_1553,B_1552))
      | ~ v1_relat_1(C_1553) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_19363,plain,(
    ! [C_1554,A_1555,B_1556] :
      ( ~ v1_xboole_0(k1_relat_1(C_1554))
      | ~ r2_hidden(A_1555,k9_relat_1(C_1554,B_1556))
      | ~ v1_relat_1(C_1554) ) ),
    inference(resolution,[status(thm)],[c_19358,c_2])).

tff(c_19378,plain,(
    ! [C_1554,B_1556] :
      ( ~ v1_xboole_0(k1_relat_1(C_1554))
      | ~ v1_relat_1(C_1554)
      | v1_xboole_0(k9_relat_1(C_1554,B_1556)) ) ),
    inference(resolution,[status(thm)],[c_4,c_19363])).

tff(c_19421,plain,(
    ! [A_1572,B_1573,C_1574,D_1575] :
      ( k7_relset_1(A_1572,B_1573,C_1574,D_1575) = k9_relat_1(C_1574,D_1575)
      | ~ m1_subset_1(C_1574,k1_zfmisc_1(k2_zfmisc_1(A_1572,B_1573))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_19428,plain,(
    ! [D_1575] : k7_relset_1('#skF_6','#skF_7','#skF_9',D_1575) = k9_relat_1('#skF_9',D_1575) ),
    inference(resolution,[status(thm)],[c_52,c_19421])).

tff(c_66,plain,(
    ~ v1_xboole_0(k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(resolution,[status(thm)],[c_50,c_2])).

tff(c_19429,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19428,c_66])).

tff(c_19481,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_19378,c_19429])).

tff(c_19487,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_19481])).

tff(c_19689,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19688,c_19487])).

tff(c_19693,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19313,c_19689])).

tff(c_19694,plain,(
    r2_hidden('#skF_3'('#skF_7','#skF_6','#skF_9'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_19687])).

tff(c_19701,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_19694,c_2])).

tff(c_19706,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19313,c_19701])).

tff(c_19707,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_19902,plain,(
    ! [A_1649,C_1650] :
      ( r2_hidden(k4_tarski(A_1649,k1_funct_1(C_1650,A_1649)),C_1650)
      | ~ r2_hidden(A_1649,k1_relat_1(C_1650))
      | ~ v1_funct_1(C_1650)
      | ~ v1_relat_1(C_1650) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_19966,plain,(
    ! [C_1653,A_1654] :
      ( ~ v1_xboole_0(C_1653)
      | ~ r2_hidden(A_1654,k1_relat_1(C_1653))
      | ~ v1_funct_1(C_1653)
      | ~ v1_relat_1(C_1653) ) ),
    inference(resolution,[status(thm)],[c_19902,c_2])).

tff(c_19992,plain,(
    ! [C_1655] :
      ( ~ v1_xboole_0(C_1655)
      | ~ v1_funct_1(C_1655)
      | ~ v1_relat_1(C_1655)
      | v1_xboole_0(k1_relat_1(C_1655)) ) ),
    inference(resolution,[status(thm)],[c_4,c_19966])).

tff(c_19810,plain,(
    ! [A_1634,B_1635,C_1636,D_1637] :
      ( k7_relset_1(A_1634,B_1635,C_1636,D_1637) = k9_relat_1(C_1636,D_1637)
      | ~ m1_subset_1(C_1636,k1_zfmisc_1(k2_zfmisc_1(A_1634,B_1635))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_19813,plain,(
    ! [D_1637] : k7_relset_1('#skF_6','#skF_7','#skF_9',D_1637) = k9_relat_1('#skF_9',D_1637) ),
    inference(resolution,[status(thm)],[c_52,c_19810])).

tff(c_19815,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19813,c_50])).

tff(c_19805,plain,(
    ! [A_1631,B_1632,C_1633] :
      ( r2_hidden('#skF_2'(A_1631,B_1632,C_1633),k1_relat_1(C_1633))
      | ~ r2_hidden(A_1631,k9_relat_1(C_1633,B_1632))
      | ~ v1_relat_1(C_1633) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_19841,plain,(
    ! [C_1639,A_1640,B_1641] :
      ( ~ v1_xboole_0(k1_relat_1(C_1639))
      | ~ r2_hidden(A_1640,k9_relat_1(C_1639,B_1641))
      | ~ v1_relat_1(C_1639) ) ),
    inference(resolution,[status(thm)],[c_19805,c_2])).

tff(c_19844,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_19815,c_19841])).

tff(c_19859,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_19844])).

tff(c_19995,plain,
    ( ~ v1_xboole_0('#skF_9')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_19992,c_19859])).

tff(c_19999,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_56,c_19707,c_19995])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:20:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.23/6.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.23/6.75  
% 14.23/6.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.23/6.75  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 14.23/6.75  
% 14.23/6.75  %Foreground sorts:
% 14.23/6.75  
% 14.23/6.75  
% 14.23/6.75  %Background operators:
% 14.23/6.75  
% 14.23/6.75  
% 14.23/6.75  %Foreground operators:
% 14.23/6.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.23/6.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.23/6.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.23/6.75  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 14.23/6.75  tff('#skF_1', type, '#skF_1': $i > $i).
% 14.23/6.75  tff('#skF_7', type, '#skF_7': $i).
% 14.23/6.75  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i) > $i).
% 14.23/6.75  tff('#skF_10', type, '#skF_10': $i).
% 14.23/6.75  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 14.23/6.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 14.23/6.75  tff('#skF_6', type, '#skF_6': $i).
% 14.23/6.75  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 14.23/6.75  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 14.23/6.75  tff('#skF_9', type, '#skF_9': $i).
% 14.23/6.75  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 14.23/6.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.23/6.75  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 14.23/6.75  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 14.23/6.75  tff('#skF_8', type, '#skF_8': $i).
% 14.23/6.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.23/6.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.23/6.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.23/6.75  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 14.23/6.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.23/6.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.23/6.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.23/6.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.23/6.75  
% 14.40/6.77  tff(f_144, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 14.40/6.77  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 14.40/6.77  tff(f_87, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 14.40/6.77  tff(f_79, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 14.40/6.77  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 14.40/6.77  tff(f_54, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 14.40/6.77  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 14.40/6.77  tff(f_75, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 14.40/6.77  tff(f_64, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 14.40/6.77  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 14.40/6.77  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 14.40/6.77  tff(f_125, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k7_relset_1(C, A, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(F, E), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relset_1)).
% 14.40/6.77  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 14.40/6.77  tff(c_52, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 14.40/6.77  tff(c_72, plain, (![C_154, A_155, B_156]: (v1_relat_1(C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 14.40/6.77  tff(c_76, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_52, c_72])).
% 14.40/6.77  tff(c_56, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_144])).
% 14.40/6.77  tff(c_209, plain, (![A_195, B_196, C_197, D_198]: (k7_relset_1(A_195, B_196, C_197, D_198)=k9_relat_1(C_197, D_198) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_195, B_196))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.40/6.77  tff(c_216, plain, (![D_198]: (k7_relset_1('#skF_6', '#skF_7', '#skF_9', D_198)=k9_relat_1('#skF_9', D_198))), inference(resolution, [status(thm)], [c_52, c_209])).
% 14.40/6.77  tff(c_50, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 14.40/6.77  tff(c_218, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_50])).
% 14.40/6.77  tff(c_219, plain, (![D_199]: (k7_relset_1('#skF_6', '#skF_7', '#skF_9', D_199)=k9_relat_1('#skF_9', D_199))), inference(resolution, [status(thm)], [c_52, c_209])).
% 14.40/6.77  tff(c_28, plain, (![A_26, B_27, C_28, D_29]: (m1_subset_1(k7_relset_1(A_26, B_27, C_28, D_29), k1_zfmisc_1(B_27)) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.40/6.77  tff(c_225, plain, (![D_199]: (m1_subset_1(k9_relat_1('#skF_9', D_199), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_219, c_28])).
% 14.40/6.77  tff(c_249, plain, (![D_200]: (m1_subset_1(k9_relat_1('#skF_9', D_200), k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_225])).
% 14.40/6.77  tff(c_8, plain, (![A_7, C_9, B_8]: (m1_subset_1(A_7, C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(C_9)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.40/6.77  tff(c_253, plain, (![A_201, D_202]: (m1_subset_1(A_201, '#skF_7') | ~r2_hidden(A_201, k9_relat_1('#skF_9', D_202)))), inference(resolution, [status(thm)], [c_249, c_8])).
% 14.40/6.77  tff(c_269, plain, (m1_subset_1('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_218, c_253])).
% 14.40/6.77  tff(c_135, plain, (![A_173, B_174, C_175]: (r2_hidden('#skF_2'(A_173, B_174, C_175), B_174) | ~r2_hidden(A_173, k9_relat_1(C_175, B_174)) | ~v1_relat_1(C_175))), inference(cnfTransformation, [status(thm)], [f_54])).
% 14.40/6.77  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.40/6.77  tff(c_149, plain, (![B_174, A_173, C_175]: (~v1_xboole_0(B_174) | ~r2_hidden(A_173, k9_relat_1(C_175, B_174)) | ~v1_relat_1(C_175))), inference(resolution, [status(thm)], [c_135, c_2])).
% 14.40/6.77  tff(c_235, plain, (~v1_xboole_0('#skF_8') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_218, c_149])).
% 14.40/6.77  tff(c_241, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_235])).
% 14.40/6.77  tff(c_93, plain, (![C_162, B_163, A_164]: (v1_xboole_0(C_162) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(B_163, A_164))) | ~v1_xboole_0(A_164))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.40/6.77  tff(c_97, plain, (v1_xboole_0('#skF_9') | ~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_52, c_93])).
% 14.40/6.77  tff(c_98, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_97])).
% 14.40/6.77  tff(c_333, plain, (![A_223, B_224, C_225]: (r2_hidden(k4_tarski('#skF_2'(A_223, B_224, C_225), A_223), C_225) | ~r2_hidden(A_223, k9_relat_1(C_225, B_224)) | ~v1_relat_1(C_225))), inference(cnfTransformation, [status(thm)], [f_54])).
% 14.40/6.77  tff(c_20, plain, (![C_18, A_16, B_17]: (k1_funct_1(C_18, A_16)=B_17 | ~r2_hidden(k4_tarski(A_16, B_17), C_18) | ~v1_funct_1(C_18) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 14.40/6.77  tff(c_793, plain, (![C_289, A_290, B_291]: (k1_funct_1(C_289, '#skF_2'(A_290, B_291, C_289))=A_290 | ~v1_funct_1(C_289) | ~r2_hidden(A_290, k9_relat_1(C_289, B_291)) | ~v1_relat_1(C_289))), inference(resolution, [status(thm)], [c_333, c_20])).
% 14.40/6.77  tff(c_801, plain, (k1_funct_1('#skF_9', '#skF_2'('#skF_10', '#skF_8', '#skF_9'))='#skF_10' | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_218, c_793])).
% 14.40/6.77  tff(c_815, plain, (k1_funct_1('#skF_9', '#skF_2'('#skF_10', '#skF_8', '#skF_9'))='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_56, c_801])).
% 14.40/6.77  tff(c_12, plain, (![A_10, B_11, C_12]: (r2_hidden('#skF_2'(A_10, B_11, C_12), B_11) | ~r2_hidden(A_10, k9_relat_1(C_12, B_11)) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 14.40/6.77  tff(c_99, plain, (![A_165, B_166, C_167]: (k1_relset_1(A_165, B_166, C_167)=k1_relat_1(C_167) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 14.40/6.77  tff(c_103, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_52, c_99])).
% 14.40/6.77  tff(c_624, plain, (![A_260, B_261, C_262]: (r2_hidden('#skF_3'(A_260, B_261, C_262), B_261) | k1_relset_1(B_261, A_260, C_262)=B_261 | ~m1_subset_1(C_262, k1_zfmisc_1(k2_zfmisc_1(B_261, A_260))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 14.40/6.77  tff(c_629, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_6', '#skF_9'), '#skF_6') | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6'), inference(resolution, [status(thm)], [c_52, c_624])).
% 14.40/6.77  tff(c_632, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_6', '#skF_9'), '#skF_6') | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_103, c_629])).
% 14.40/6.77  tff(c_633, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_632])).
% 14.40/6.77  tff(c_16, plain, (![A_10, B_11, C_12]: (r2_hidden('#skF_2'(A_10, B_11, C_12), k1_relat_1(C_12)) | ~r2_hidden(A_10, k9_relat_1(C_12, B_11)) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 14.40/6.77  tff(c_651, plain, (![A_10, B_11]: (r2_hidden('#skF_2'(A_10, B_11, '#skF_9'), '#skF_6') | ~r2_hidden(A_10, k9_relat_1('#skF_9', B_11)) | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_633, c_16])).
% 14.40/6.78  tff(c_669, plain, (![A_263, B_264]: (r2_hidden('#skF_2'(A_263, B_264, '#skF_9'), '#skF_6') | ~r2_hidden(A_263, k9_relat_1('#skF_9', B_264)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_651])).
% 14.40/6.78  tff(c_48, plain, (![F_148]: (k1_funct_1('#skF_9', F_148)!='#skF_10' | ~r2_hidden(F_148, '#skF_8') | ~r2_hidden(F_148, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 14.40/6.78  tff(c_819, plain, (![A_292, B_293]: (k1_funct_1('#skF_9', '#skF_2'(A_292, B_293, '#skF_9'))!='#skF_10' | ~r2_hidden('#skF_2'(A_292, B_293, '#skF_9'), '#skF_8') | ~r2_hidden(A_292, k9_relat_1('#skF_9', B_293)))), inference(resolution, [status(thm)], [c_669, c_48])).
% 14.40/6.78  tff(c_823, plain, (![A_10]: (k1_funct_1('#skF_9', '#skF_2'(A_10, '#skF_8', '#skF_9'))!='#skF_10' | ~r2_hidden(A_10, k9_relat_1('#skF_9', '#skF_8')) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_12, c_819])).
% 14.40/6.78  tff(c_842, plain, (![A_294]: (k1_funct_1('#skF_9', '#skF_2'(A_294, '#skF_8', '#skF_9'))!='#skF_10' | ~r2_hidden(A_294, k9_relat_1('#skF_9', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_823])).
% 14.40/6.78  tff(c_853, plain, (k1_funct_1('#skF_9', '#skF_2'('#skF_10', '#skF_8', '#skF_9'))!='#skF_10'), inference(resolution, [status(thm)], [c_218, c_842])).
% 14.40/6.78  tff(c_871, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_815, c_853])).
% 14.40/6.78  tff(c_872, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_6', '#skF_9'), '#skF_6')), inference(splitRight, [status(thm)], [c_632])).
% 14.40/6.78  tff(c_881, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_872, c_2])).
% 14.40/6.78  tff(c_1612, plain, (![B_380, C_381, E_382, A_379, D_378]: (m1_subset_1('#skF_5'(D_378, A_379, B_380, C_381, E_382), C_381) | ~r2_hidden(E_382, k7_relset_1(C_381, A_379, D_378, B_380)) | ~m1_subset_1(E_382, A_379) | ~m1_subset_1(D_378, k1_zfmisc_1(k2_zfmisc_1(C_381, A_379))) | v1_xboole_0(C_381) | v1_xboole_0(B_380) | v1_xboole_0(A_379))), inference(cnfTransformation, [status(thm)], [f_125])).
% 14.40/6.78  tff(c_1623, plain, (![D_198, E_382]: (m1_subset_1('#skF_5'('#skF_9', '#skF_7', D_198, '#skF_6', E_382), '#skF_6') | ~r2_hidden(E_382, k9_relat_1('#skF_9', D_198)) | ~m1_subset_1(E_382, '#skF_7') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | v1_xboole_0('#skF_6') | v1_xboole_0(D_198) | v1_xboole_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_216, c_1612])).
% 14.40/6.78  tff(c_1637, plain, (![D_198, E_382]: (m1_subset_1('#skF_5'('#skF_9', '#skF_7', D_198, '#skF_6', E_382), '#skF_6') | ~r2_hidden(E_382, k9_relat_1('#skF_9', D_198)) | ~m1_subset_1(E_382, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(D_198) | v1_xboole_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1623])).
% 14.40/6.78  tff(c_1941, plain, (![D_419, E_420]: (m1_subset_1('#skF_5'('#skF_9', '#skF_7', D_419, '#skF_6', E_420), '#skF_6') | ~r2_hidden(E_420, k9_relat_1('#skF_9', D_419)) | ~m1_subset_1(E_420, '#skF_7') | v1_xboole_0(D_419))), inference(negUnitSimplification, [status(thm)], [c_98, c_881, c_1637])).
% 14.40/6.78  tff(c_1964, plain, (m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', '#skF_10'), '#skF_6') | ~m1_subset_1('#skF_10', '#skF_7') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_218, c_1941])).
% 14.40/6.78  tff(c_1987, plain, (m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', '#skF_10'), '#skF_6') | v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_269, c_1964])).
% 14.40/6.78  tff(c_1988, plain, (m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', '#skF_10'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_241, c_1987])).
% 14.40/6.78  tff(c_2041, plain, (![B_431, C_432, A_430, E_433, D_429]: (r2_hidden(k4_tarski('#skF_5'(D_429, A_430, B_431, C_432, E_433), E_433), D_429) | ~r2_hidden(E_433, k7_relset_1(C_432, A_430, D_429, B_431)) | ~m1_subset_1(E_433, A_430) | ~m1_subset_1(D_429, k1_zfmisc_1(k2_zfmisc_1(C_432, A_430))) | v1_xboole_0(C_432) | v1_xboole_0(B_431) | v1_xboole_0(A_430))), inference(cnfTransformation, [status(thm)], [f_125])).
% 14.40/6.78  tff(c_11245, plain, (![D_1176, B_1180, A_1177, E_1178, C_1179]: (k1_funct_1(D_1176, '#skF_5'(D_1176, A_1177, B_1180, C_1179, E_1178))=E_1178 | ~v1_funct_1(D_1176) | ~v1_relat_1(D_1176) | ~r2_hidden(E_1178, k7_relset_1(C_1179, A_1177, D_1176, B_1180)) | ~m1_subset_1(E_1178, A_1177) | ~m1_subset_1(D_1176, k1_zfmisc_1(k2_zfmisc_1(C_1179, A_1177))) | v1_xboole_0(C_1179) | v1_xboole_0(B_1180) | v1_xboole_0(A_1177))), inference(resolution, [status(thm)], [c_2041, c_20])).
% 14.40/6.78  tff(c_11265, plain, (![D_198, E_1178]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_7', D_198, '#skF_6', E_1178))=E_1178 | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(E_1178, k9_relat_1('#skF_9', D_198)) | ~m1_subset_1(E_1178, '#skF_7') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | v1_xboole_0('#skF_6') | v1_xboole_0(D_198) | v1_xboole_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_216, c_11245])).
% 14.40/6.78  tff(c_11282, plain, (![D_198, E_1178]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_7', D_198, '#skF_6', E_1178))=E_1178 | ~r2_hidden(E_1178, k9_relat_1('#skF_9', D_198)) | ~m1_subset_1(E_1178, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(D_198) | v1_xboole_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_76, c_56, c_11265])).
% 14.40/6.78  tff(c_11287, plain, (![D_1181, E_1182]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_7', D_1181, '#skF_6', E_1182))=E_1182 | ~r2_hidden(E_1182, k9_relat_1('#skF_9', D_1181)) | ~m1_subset_1(E_1182, '#skF_7') | v1_xboole_0(D_1181))), inference(negUnitSimplification, [status(thm)], [c_98, c_881, c_11282])).
% 14.40/6.78  tff(c_11360, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', '#skF_10'))='#skF_10' | ~m1_subset_1('#skF_10', '#skF_7') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_218, c_11287])).
% 14.40/6.78  tff(c_11426, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', '#skF_10'))='#skF_10' | v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_269, c_11360])).
% 14.40/6.78  tff(c_11427, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', '#skF_10'))='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_241, c_11426])).
% 14.40/6.78  tff(c_1794, plain, (![B_414, D_412, C_415, A_413, E_416]: (r2_hidden('#skF_5'(D_412, A_413, B_414, C_415, E_416), B_414) | ~r2_hidden(E_416, k7_relset_1(C_415, A_413, D_412, B_414)) | ~m1_subset_1(E_416, A_413) | ~m1_subset_1(D_412, k1_zfmisc_1(k2_zfmisc_1(C_415, A_413))) | v1_xboole_0(C_415) | v1_xboole_0(B_414) | v1_xboole_0(A_413))), inference(cnfTransformation, [status(thm)], [f_125])).
% 14.40/6.78  tff(c_1799, plain, (![B_414, E_416]: (r2_hidden('#skF_5'('#skF_9', '#skF_7', B_414, '#skF_6', E_416), B_414) | ~r2_hidden(E_416, k7_relset_1('#skF_6', '#skF_7', '#skF_9', B_414)) | ~m1_subset_1(E_416, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(B_414) | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_52, c_1794])).
% 14.40/6.78  tff(c_1802, plain, (![B_414, E_416]: (r2_hidden('#skF_5'('#skF_9', '#skF_7', B_414, '#skF_6', E_416), B_414) | ~r2_hidden(E_416, k9_relat_1('#skF_9', B_414)) | ~m1_subset_1(E_416, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(B_414) | v1_xboole_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_1799])).
% 14.40/6.78  tff(c_1804, plain, (![B_417, E_418]: (r2_hidden('#skF_5'('#skF_9', '#skF_7', B_417, '#skF_6', E_418), B_417) | ~r2_hidden(E_418, k9_relat_1('#skF_9', B_417)) | ~m1_subset_1(E_418, '#skF_7') | v1_xboole_0(B_417))), inference(negUnitSimplification, [status(thm)], [c_98, c_881, c_1802])).
% 14.40/6.78  tff(c_6, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.40/6.78  tff(c_77, plain, (![F_157]: (k1_funct_1('#skF_9', F_157)!='#skF_10' | ~r2_hidden(F_157, '#skF_8') | ~r2_hidden(F_157, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 14.40/6.78  tff(c_86, plain, (![A_5]: (k1_funct_1('#skF_9', A_5)!='#skF_10' | ~r2_hidden(A_5, '#skF_8') | v1_xboole_0('#skF_6') | ~m1_subset_1(A_5, '#skF_6'))), inference(resolution, [status(thm)], [c_6, c_77])).
% 14.40/6.78  tff(c_109, plain, (![A_5]: (k1_funct_1('#skF_9', A_5)!='#skF_10' | ~r2_hidden(A_5, '#skF_8') | ~m1_subset_1(A_5, '#skF_6'))), inference(splitLeft, [status(thm)], [c_86])).
% 14.40/6.78  tff(c_1901, plain, (![E_418]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', E_418))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', E_418), '#skF_6') | ~r2_hidden(E_418, k9_relat_1('#skF_9', '#skF_8')) | ~m1_subset_1(E_418, '#skF_7') | v1_xboole_0('#skF_8'))), inference(resolution, [status(thm)], [c_1804, c_109])).
% 14.40/6.78  tff(c_19206, plain, (![E_1536]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', E_1536))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', E_1536), '#skF_6') | ~r2_hidden(E_1536, k9_relat_1('#skF_9', '#skF_8')) | ~m1_subset_1(E_1536, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_241, c_1901])).
% 14.40/6.78  tff(c_19261, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', '#skF_10'))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8', '#skF_6', '#skF_10'), '#skF_6') | ~m1_subset_1('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_218, c_19206])).
% 14.40/6.78  tff(c_19312, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_269, c_1988, c_11427, c_19261])).
% 14.40/6.78  tff(c_19313, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_86])).
% 14.40/6.78  tff(c_19679, plain, (![A_1600, B_1601, C_1602]: (r2_hidden('#skF_3'(A_1600, B_1601, C_1602), B_1601) | k1_relset_1(B_1601, A_1600, C_1602)=B_1601 | ~m1_subset_1(C_1602, k1_zfmisc_1(k2_zfmisc_1(B_1601, A_1600))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 14.40/6.78  tff(c_19684, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_6', '#skF_9'), '#skF_6') | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6'), inference(resolution, [status(thm)], [c_52, c_19679])).
% 14.40/6.78  tff(c_19687, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_6', '#skF_9'), '#skF_6') | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_103, c_19684])).
% 14.40/6.78  tff(c_19688, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_19687])).
% 14.40/6.78  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.40/6.78  tff(c_19358, plain, (![A_1551, B_1552, C_1553]: (r2_hidden('#skF_2'(A_1551, B_1552, C_1553), k1_relat_1(C_1553)) | ~r2_hidden(A_1551, k9_relat_1(C_1553, B_1552)) | ~v1_relat_1(C_1553))), inference(cnfTransformation, [status(thm)], [f_54])).
% 14.40/6.78  tff(c_19363, plain, (![C_1554, A_1555, B_1556]: (~v1_xboole_0(k1_relat_1(C_1554)) | ~r2_hidden(A_1555, k9_relat_1(C_1554, B_1556)) | ~v1_relat_1(C_1554))), inference(resolution, [status(thm)], [c_19358, c_2])).
% 14.40/6.78  tff(c_19378, plain, (![C_1554, B_1556]: (~v1_xboole_0(k1_relat_1(C_1554)) | ~v1_relat_1(C_1554) | v1_xboole_0(k9_relat_1(C_1554, B_1556)))), inference(resolution, [status(thm)], [c_4, c_19363])).
% 14.40/6.78  tff(c_19421, plain, (![A_1572, B_1573, C_1574, D_1575]: (k7_relset_1(A_1572, B_1573, C_1574, D_1575)=k9_relat_1(C_1574, D_1575) | ~m1_subset_1(C_1574, k1_zfmisc_1(k2_zfmisc_1(A_1572, B_1573))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.40/6.78  tff(c_19428, plain, (![D_1575]: (k7_relset_1('#skF_6', '#skF_7', '#skF_9', D_1575)=k9_relat_1('#skF_9', D_1575))), inference(resolution, [status(thm)], [c_52, c_19421])).
% 14.40/6.78  tff(c_66, plain, (~v1_xboole_0(k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(resolution, [status(thm)], [c_50, c_2])).
% 14.40/6.78  tff(c_19429, plain, (~v1_xboole_0(k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_19428, c_66])).
% 14.40/6.78  tff(c_19481, plain, (~v1_xboole_0(k1_relat_1('#skF_9')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_19378, c_19429])).
% 14.40/6.78  tff(c_19487, plain, (~v1_xboole_0(k1_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_19481])).
% 14.40/6.78  tff(c_19689, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_19688, c_19487])).
% 14.40/6.78  tff(c_19693, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19313, c_19689])).
% 14.40/6.78  tff(c_19694, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_6', '#skF_9'), '#skF_6')), inference(splitRight, [status(thm)], [c_19687])).
% 14.40/6.78  tff(c_19701, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_19694, c_2])).
% 14.40/6.78  tff(c_19706, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19313, c_19701])).
% 14.40/6.78  tff(c_19707, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_97])).
% 14.40/6.78  tff(c_19902, plain, (![A_1649, C_1650]: (r2_hidden(k4_tarski(A_1649, k1_funct_1(C_1650, A_1649)), C_1650) | ~r2_hidden(A_1649, k1_relat_1(C_1650)) | ~v1_funct_1(C_1650) | ~v1_relat_1(C_1650))), inference(cnfTransformation, [status(thm)], [f_64])).
% 14.40/6.78  tff(c_19966, plain, (![C_1653, A_1654]: (~v1_xboole_0(C_1653) | ~r2_hidden(A_1654, k1_relat_1(C_1653)) | ~v1_funct_1(C_1653) | ~v1_relat_1(C_1653))), inference(resolution, [status(thm)], [c_19902, c_2])).
% 14.40/6.78  tff(c_19992, plain, (![C_1655]: (~v1_xboole_0(C_1655) | ~v1_funct_1(C_1655) | ~v1_relat_1(C_1655) | v1_xboole_0(k1_relat_1(C_1655)))), inference(resolution, [status(thm)], [c_4, c_19966])).
% 14.40/6.78  tff(c_19810, plain, (![A_1634, B_1635, C_1636, D_1637]: (k7_relset_1(A_1634, B_1635, C_1636, D_1637)=k9_relat_1(C_1636, D_1637) | ~m1_subset_1(C_1636, k1_zfmisc_1(k2_zfmisc_1(A_1634, B_1635))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.40/6.78  tff(c_19813, plain, (![D_1637]: (k7_relset_1('#skF_6', '#skF_7', '#skF_9', D_1637)=k9_relat_1('#skF_9', D_1637))), inference(resolution, [status(thm)], [c_52, c_19810])).
% 14.40/6.78  tff(c_19815, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_19813, c_50])).
% 14.40/6.78  tff(c_19805, plain, (![A_1631, B_1632, C_1633]: (r2_hidden('#skF_2'(A_1631, B_1632, C_1633), k1_relat_1(C_1633)) | ~r2_hidden(A_1631, k9_relat_1(C_1633, B_1632)) | ~v1_relat_1(C_1633))), inference(cnfTransformation, [status(thm)], [f_54])).
% 14.40/6.78  tff(c_19841, plain, (![C_1639, A_1640, B_1641]: (~v1_xboole_0(k1_relat_1(C_1639)) | ~r2_hidden(A_1640, k9_relat_1(C_1639, B_1641)) | ~v1_relat_1(C_1639))), inference(resolution, [status(thm)], [c_19805, c_2])).
% 14.40/6.78  tff(c_19844, plain, (~v1_xboole_0(k1_relat_1('#skF_9')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_19815, c_19841])).
% 14.40/6.78  tff(c_19859, plain, (~v1_xboole_0(k1_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_19844])).
% 14.40/6.78  tff(c_19995, plain, (~v1_xboole_0('#skF_9') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_19992, c_19859])).
% 14.40/6.78  tff(c_19999, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_56, c_19707, c_19995])).
% 14.40/6.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.40/6.78  
% 14.40/6.78  Inference rules
% 14.40/6.78  ----------------------
% 14.40/6.78  #Ref     : 0
% 14.40/6.78  #Sup     : 4252
% 14.40/6.78  #Fact    : 0
% 14.40/6.78  #Define  : 0
% 14.40/6.78  #Split   : 47
% 14.40/6.78  #Chain   : 0
% 14.40/6.78  #Close   : 0
% 14.40/6.78  
% 14.40/6.78  Ordering : KBO
% 14.40/6.78  
% 14.40/6.78  Simplification rules
% 14.40/6.78  ----------------------
% 14.40/6.78  #Subsume      : 1239
% 14.40/6.78  #Demod        : 1111
% 14.40/6.78  #Tautology    : 228
% 14.40/6.78  #SimpNegUnit  : 306
% 14.40/6.78  #BackRed      : 15
% 14.40/6.78  
% 14.40/6.78  #Partial instantiations: 0
% 14.40/6.78  #Strategies tried      : 1
% 14.40/6.78  
% 14.40/6.78  Timing (in seconds)
% 14.40/6.78  ----------------------
% 14.40/6.78  Preprocessing        : 0.56
% 14.40/6.78  Parsing              : 0.28
% 14.40/6.78  CNF conversion       : 0.06
% 14.40/6.78  Main loop            : 5.27
% 14.40/6.78  Inferencing          : 1.27
% 14.40/6.78  Reduction            : 1.11
% 14.40/6.78  Demodulation         : 0.78
% 14.40/6.78  BG Simplification    : 0.14
% 14.40/6.78  Subsumption          : 2.43
% 14.40/6.78  Abstraction          : 0.21
% 14.40/6.78  MUC search           : 0.00
% 14.40/6.78  Cooper               : 0.00
% 14.40/6.78  Total                : 5.89
% 14.40/6.78  Index Insertion      : 0.00
% 14.40/6.78  Index Deletion       : 0.00
% 14.40/6.78  Index Matching       : 0.00
% 14.40/6.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
