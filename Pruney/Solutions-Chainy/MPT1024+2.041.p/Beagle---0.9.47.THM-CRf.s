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
% DateTime   : Thu Dec  3 10:16:27 EST 2020

% Result     : Theorem 12.75s
% Output     : CNFRefutation 12.90s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 523 expanded)
%              Number of leaves         :   41 ( 193 expanded)
%              Depth                    :   11
%              Number of atoms          :  332 (1392 expanded)
%              Number of equality atoms :   45 ( 202 expanded)
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

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_149,negated_conjecture,(
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

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_84,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_130,axiom,(
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

tff(c_12,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_54,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_86,plain,(
    ! [B_159,A_160] :
      ( v1_relat_1(B_159)
      | ~ m1_subset_1(B_159,k1_zfmisc_1(A_160))
      | ~ v1_relat_1(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_89,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_54,c_86])).

tff(c_92,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_89])).

tff(c_58,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_178,plain,(
    ! [A_187,B_188,C_189,D_190] :
      ( k7_relset_1(A_187,B_188,C_189,D_190) = k9_relat_1(C_189,D_190)
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_181,plain,(
    ! [D_190] : k7_relset_1('#skF_6','#skF_7','#skF_9',D_190) = k9_relat_1('#skF_9',D_190) ),
    inference(resolution,[status(thm)],[c_54,c_178])).

tff(c_52,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_183,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_52])).

tff(c_226,plain,(
    ! [A_199,B_200,C_201,D_202] :
      ( m1_subset_1(k7_relset_1(A_199,B_200,C_201,D_202),k1_zfmisc_1(B_200))
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(A_199,B_200))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_245,plain,(
    ! [D_190] :
      ( m1_subset_1(k9_relat_1('#skF_9',D_190),k1_zfmisc_1('#skF_7'))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_226])).

tff(c_253,plain,(
    ! [D_203] : m1_subset_1(k9_relat_1('#skF_9',D_203),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_245])).

tff(c_8,plain,(
    ! [A_7,C_9,B_8] :
      ( m1_subset_1(A_7,C_9)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(C_9))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_267,plain,(
    ! [A_207,D_208] :
      ( m1_subset_1(A_207,'#skF_7')
      | ~ r2_hidden(A_207,k9_relat_1('#skF_9',D_208)) ) ),
    inference(resolution,[status(thm)],[c_253,c_8])).

tff(c_283,plain,(
    m1_subset_1('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_183,c_267])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_134,plain,(
    ! [A_173,B_174,C_175] :
      ( r2_hidden('#skF_2'(A_173,B_174,C_175),B_174)
      | ~ r2_hidden(A_173,k9_relat_1(C_175,B_174))
      | ~ v1_relat_1(C_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_149,plain,(
    ! [B_176,A_177,C_178] :
      ( ~ v1_xboole_0(B_176)
      | ~ r2_hidden(A_177,k9_relat_1(C_178,B_176))
      | ~ v1_relat_1(C_178) ) ),
    inference(resolution,[status(thm)],[c_134,c_2])).

tff(c_164,plain,(
    ! [B_176,C_178] :
      ( ~ v1_xboole_0(B_176)
      | ~ v1_relat_1(C_178)
      | v1_xboole_0(k9_relat_1(C_178,B_176)) ) ),
    inference(resolution,[status(thm)],[c_4,c_149])).

tff(c_69,plain,(
    ~ v1_xboole_0(k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(resolution,[status(thm)],[c_52,c_2])).

tff(c_182,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_69])).

tff(c_195,plain,
    ( ~ v1_xboole_0('#skF_8')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_164,c_182])).

tff(c_198,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_195])).

tff(c_93,plain,(
    ! [C_161,B_162,A_163] :
      ( v1_xboole_0(C_161)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(B_162,A_163)))
      | ~ v1_xboole_0(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_97,plain,
    ( v1_xboole_0('#skF_9')
    | ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_93])).

tff(c_98,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_16,plain,(
    ! [A_15,B_16,C_17] :
      ( r2_hidden('#skF_2'(A_15,B_16,C_17),B_16)
      | ~ r2_hidden(A_15,k9_relat_1(C_17,B_16))
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_123,plain,(
    ! [A_169,B_170,C_171] :
      ( k1_relset_1(A_169,B_170,C_171) = k1_relat_1(C_171)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_127,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_54,c_123])).

tff(c_605,plain,(
    ! [A_257,B_258,C_259] :
      ( r2_hidden('#skF_3'(A_257,B_258,C_259),B_258)
      | k1_relset_1(B_258,A_257,C_259) = B_258
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(B_258,A_257))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_610,plain,
    ( r2_hidden('#skF_3'('#skF_7','#skF_6','#skF_9'),'#skF_6')
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_54,c_605])).

tff(c_613,plain,
    ( r2_hidden('#skF_3'('#skF_7','#skF_6','#skF_9'),'#skF_6')
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_610])).

tff(c_614,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_613])).

tff(c_20,plain,(
    ! [A_15,B_16,C_17] :
      ( r2_hidden('#skF_2'(A_15,B_16,C_17),k1_relat_1(C_17))
      | ~ r2_hidden(A_15,k9_relat_1(C_17,B_16))
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_632,plain,(
    ! [A_15,B_16] :
      ( r2_hidden('#skF_2'(A_15,B_16,'#skF_9'),'#skF_6')
      | ~ r2_hidden(A_15,k9_relat_1('#skF_9',B_16))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_614,c_20])).

tff(c_650,plain,(
    ! [A_260,B_261] :
      ( r2_hidden('#skF_2'(A_260,B_261,'#skF_9'),'#skF_6')
      | ~ r2_hidden(A_260,k9_relat_1('#skF_9',B_261)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_632])).

tff(c_50,plain,(
    ! [F_150] :
      ( k1_funct_1('#skF_9',F_150) != '#skF_10'
      | ~ r2_hidden(F_150,'#skF_8')
      | ~ r2_hidden(F_150,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_775,plain,(
    ! [A_288,B_289] :
      ( k1_funct_1('#skF_9','#skF_2'(A_288,B_289,'#skF_9')) != '#skF_10'
      | ~ r2_hidden('#skF_2'(A_288,B_289,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_288,k9_relat_1('#skF_9',B_289)) ) ),
    inference(resolution,[status(thm)],[c_650,c_50])).

tff(c_779,plain,(
    ! [A_15] :
      ( k1_funct_1('#skF_9','#skF_2'(A_15,'#skF_8','#skF_9')) != '#skF_10'
      | ~ r2_hidden(A_15,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_16,c_775])).

tff(c_789,plain,(
    ! [A_290] :
      ( k1_funct_1('#skF_9','#skF_2'(A_290,'#skF_8','#skF_9')) != '#skF_10'
      | ~ r2_hidden(A_290,k9_relat_1('#skF_9','#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_779])).

tff(c_815,plain,(
    k1_funct_1('#skF_9','#skF_2'('#skF_10','#skF_8','#skF_9')) != '#skF_10' ),
    inference(resolution,[status(thm)],[c_183,c_789])).

tff(c_325,plain,(
    ! [A_219,B_220,C_221] :
      ( r2_hidden(k4_tarski('#skF_2'(A_219,B_220,C_221),A_219),C_221)
      | ~ r2_hidden(A_219,k9_relat_1(C_221,B_220))
      | ~ v1_relat_1(C_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_24,plain,(
    ! [C_23,A_21,B_22] :
      ( k1_funct_1(C_23,A_21) = B_22
      | ~ r2_hidden(k4_tarski(A_21,B_22),C_23)
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_850,plain,(
    ! [C_299,A_300,B_301] :
      ( k1_funct_1(C_299,'#skF_2'(A_300,B_301,C_299)) = A_300
      | ~ v1_funct_1(C_299)
      | ~ r2_hidden(A_300,k9_relat_1(C_299,B_301))
      | ~ v1_relat_1(C_299) ) ),
    inference(resolution,[status(thm)],[c_325,c_24])).

tff(c_858,plain,
    ( k1_funct_1('#skF_9','#skF_2'('#skF_10','#skF_8','#skF_9')) = '#skF_10'
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_183,c_850])).

tff(c_872,plain,(
    k1_funct_1('#skF_9','#skF_2'('#skF_10','#skF_8','#skF_9')) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_58,c_858])).

tff(c_874,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_815,c_872])).

tff(c_875,plain,(
    r2_hidden('#skF_3'('#skF_7','#skF_6','#skF_9'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_613])).

tff(c_884,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_875,c_2])).

tff(c_1435,plain,(
    ! [E_374,A_372,C_376,D_375,B_373] :
      ( m1_subset_1('#skF_5'(A_372,B_373,E_374,D_375,C_376),C_376)
      | ~ r2_hidden(E_374,k7_relset_1(C_376,A_372,D_375,B_373))
      | ~ m1_subset_1(E_374,A_372)
      | ~ m1_subset_1(D_375,k1_zfmisc_1(k2_zfmisc_1(C_376,A_372)))
      | v1_xboole_0(C_376)
      | v1_xboole_0(B_373)
      | v1_xboole_0(A_372) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1446,plain,(
    ! [D_190,E_374] :
      ( m1_subset_1('#skF_5'('#skF_7',D_190,E_374,'#skF_9','#skF_6'),'#skF_6')
      | ~ r2_hidden(E_374,k9_relat_1('#skF_9',D_190))
      | ~ m1_subset_1(E_374,'#skF_7')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_190)
      | v1_xboole_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_1435])).

tff(c_1460,plain,(
    ! [D_190,E_374] :
      ( m1_subset_1('#skF_5'('#skF_7',D_190,E_374,'#skF_9','#skF_6'),'#skF_6')
      | ~ r2_hidden(E_374,k9_relat_1('#skF_9',D_190))
      | ~ m1_subset_1(E_374,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_190)
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1446])).

tff(c_1887,plain,(
    ! [D_428,E_429] :
      ( m1_subset_1('#skF_5'('#skF_7',D_428,E_429,'#skF_9','#skF_6'),'#skF_6')
      | ~ r2_hidden(E_429,k9_relat_1('#skF_9',D_428))
      | ~ m1_subset_1(E_429,'#skF_7')
      | v1_xboole_0(D_428) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_884,c_1460])).

tff(c_1910,plain,
    ( m1_subset_1('#skF_5'('#skF_7','#skF_8','#skF_10','#skF_9','#skF_6'),'#skF_6')
    | ~ m1_subset_1('#skF_10','#skF_7')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_183,c_1887])).

tff(c_1933,plain,
    ( m1_subset_1('#skF_5'('#skF_7','#skF_8','#skF_10','#skF_9','#skF_6'),'#skF_6')
    | v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_1910])).

tff(c_1934,plain,(
    m1_subset_1('#skF_5'('#skF_7','#skF_8','#skF_10','#skF_9','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_198,c_1933])).

tff(c_1938,plain,(
    ! [B_431,E_432,A_430,D_433,C_434] :
      ( r2_hidden(k4_tarski('#skF_5'(A_430,B_431,E_432,D_433,C_434),E_432),D_433)
      | ~ r2_hidden(E_432,k7_relset_1(C_434,A_430,D_433,B_431))
      | ~ m1_subset_1(E_432,A_430)
      | ~ m1_subset_1(D_433,k1_zfmisc_1(k2_zfmisc_1(C_434,A_430)))
      | v1_xboole_0(C_434)
      | v1_xboole_0(B_431)
      | v1_xboole_0(A_430) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_12282,plain,(
    ! [E_1226,C_1229,A_1227,D_1225,B_1228] :
      ( k1_funct_1(D_1225,'#skF_5'(A_1227,B_1228,E_1226,D_1225,C_1229)) = E_1226
      | ~ v1_funct_1(D_1225)
      | ~ v1_relat_1(D_1225)
      | ~ r2_hidden(E_1226,k7_relset_1(C_1229,A_1227,D_1225,B_1228))
      | ~ m1_subset_1(E_1226,A_1227)
      | ~ m1_subset_1(D_1225,k1_zfmisc_1(k2_zfmisc_1(C_1229,A_1227)))
      | v1_xboole_0(C_1229)
      | v1_xboole_0(B_1228)
      | v1_xboole_0(A_1227) ) ),
    inference(resolution,[status(thm)],[c_1938,c_24])).

tff(c_12304,plain,(
    ! [D_190,E_1226] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_7',D_190,E_1226,'#skF_9','#skF_6')) = E_1226
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(E_1226,k9_relat_1('#skF_9',D_190))
      | ~ m1_subset_1(E_1226,'#skF_7')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_190)
      | v1_xboole_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_12282])).

tff(c_12324,plain,(
    ! [D_190,E_1226] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_7',D_190,E_1226,'#skF_9','#skF_6')) = E_1226
      | ~ r2_hidden(E_1226,k9_relat_1('#skF_9',D_190))
      | ~ m1_subset_1(E_1226,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_190)
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_92,c_58,c_12304])).

tff(c_12329,plain,(
    ! [D_1230,E_1231] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_7',D_1230,E_1231,'#skF_9','#skF_6')) = E_1231
      | ~ r2_hidden(E_1231,k9_relat_1('#skF_9',D_1230))
      | ~ m1_subset_1(E_1231,'#skF_7')
      | v1_xboole_0(D_1230) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_884,c_12324])).

tff(c_12410,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_8','#skF_10','#skF_9','#skF_6')) = '#skF_10'
    | ~ m1_subset_1('#skF_10','#skF_7')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_183,c_12329])).

tff(c_12484,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_8','#skF_10','#skF_9','#skF_6')) = '#skF_10'
    | v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_12410])).

tff(c_12485,plain,(
    k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_8','#skF_10','#skF_9','#skF_6')) = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_198,c_12484])).

tff(c_1654,plain,(
    ! [A_405,C_409,D_408,B_406,E_407] :
      ( r2_hidden('#skF_5'(A_405,B_406,E_407,D_408,C_409),B_406)
      | ~ r2_hidden(E_407,k7_relset_1(C_409,A_405,D_408,B_406))
      | ~ m1_subset_1(E_407,A_405)
      | ~ m1_subset_1(D_408,k1_zfmisc_1(k2_zfmisc_1(C_409,A_405)))
      | v1_xboole_0(C_409)
      | v1_xboole_0(B_406)
      | v1_xboole_0(A_405) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1659,plain,(
    ! [B_406,E_407] :
      ( r2_hidden('#skF_5'('#skF_7',B_406,E_407,'#skF_9','#skF_6'),B_406)
      | ~ r2_hidden(E_407,k7_relset_1('#skF_6','#skF_7','#skF_9',B_406))
      | ~ m1_subset_1(E_407,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(B_406)
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_54,c_1654])).

tff(c_1662,plain,(
    ! [B_406,E_407] :
      ( r2_hidden('#skF_5'('#skF_7',B_406,E_407,'#skF_9','#skF_6'),B_406)
      | ~ r2_hidden(E_407,k9_relat_1('#skF_9',B_406))
      | ~ m1_subset_1(E_407,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(B_406)
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_1659])).

tff(c_1669,plain,(
    ! [B_415,E_416] :
      ( r2_hidden('#skF_5'('#skF_7',B_415,E_416,'#skF_9','#skF_6'),B_415)
      | ~ r2_hidden(E_416,k9_relat_1('#skF_9',B_415))
      | ~ m1_subset_1(E_416,'#skF_7')
      | v1_xboole_0(B_415) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_884,c_1662])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_75,plain,(
    ! [F_158] :
      ( k1_funct_1('#skF_9',F_158) != '#skF_10'
      | ~ r2_hidden(F_158,'#skF_8')
      | ~ r2_hidden(F_158,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_84,plain,(
    ! [A_5] :
      ( k1_funct_1('#skF_9',A_5) != '#skF_10'
      | ~ r2_hidden(A_5,'#skF_8')
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_5,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_6,c_75])).

tff(c_109,plain,(
    ! [A_5] :
      ( k1_funct_1('#skF_9',A_5) != '#skF_10'
      | ~ r2_hidden(A_5,'#skF_8')
      | ~ m1_subset_1(A_5,'#skF_6') ) ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_1758,plain,(
    ! [E_416] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_8',E_416,'#skF_9','#skF_6')) != '#skF_10'
      | ~ m1_subset_1('#skF_5'('#skF_7','#skF_8',E_416,'#skF_9','#skF_6'),'#skF_6')
      | ~ r2_hidden(E_416,k9_relat_1('#skF_9','#skF_8'))
      | ~ m1_subset_1(E_416,'#skF_7')
      | v1_xboole_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1669,c_109])).

tff(c_20007,plain,(
    ! [E_1574] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_8',E_1574,'#skF_9','#skF_6')) != '#skF_10'
      | ~ m1_subset_1('#skF_5'('#skF_7','#skF_8',E_1574,'#skF_9','#skF_6'),'#skF_6')
      | ~ r2_hidden(E_1574,k9_relat_1('#skF_9','#skF_8'))
      | ~ m1_subset_1(E_1574,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_198,c_1758])).

tff(c_20062,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_8','#skF_10','#skF_9','#skF_6')) != '#skF_10'
    | ~ m1_subset_1('#skF_5'('#skF_7','#skF_8','#skF_10','#skF_9','#skF_6'),'#skF_6')
    | ~ m1_subset_1('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_183,c_20007])).

tff(c_20113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_1934,c_12485,c_20062])).

tff(c_20114,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_20116,plain,(
    ! [A_1575,B_1576,C_1577] :
      ( k1_relset_1(A_1575,B_1576,C_1577) = k1_relat_1(C_1577)
      | ~ m1_subset_1(C_1577,k1_zfmisc_1(k2_zfmisc_1(A_1575,B_1576))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_20120,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_54,c_20116])).

tff(c_20554,plain,(
    ! [A_1659,B_1660,C_1661] :
      ( r2_hidden('#skF_3'(A_1659,B_1660,C_1661),B_1660)
      | k1_relset_1(B_1660,A_1659,C_1661) = B_1660
      | ~ m1_subset_1(C_1661,k1_zfmisc_1(k2_zfmisc_1(B_1660,A_1659))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_20559,plain,
    ( r2_hidden('#skF_3'('#skF_7','#skF_6','#skF_9'),'#skF_6')
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_54,c_20554])).

tff(c_20562,plain,
    ( r2_hidden('#skF_3'('#skF_7','#skF_6','#skF_9'),'#skF_6')
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20120,c_20559])).

tff(c_20563,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_20562])).

tff(c_20186,plain,(
    ! [A_1601,B_1602,C_1603,D_1604] :
      ( k7_relset_1(A_1601,B_1602,C_1603,D_1604) = k9_relat_1(C_1603,D_1604)
      | ~ m1_subset_1(C_1603,k1_zfmisc_1(k2_zfmisc_1(A_1601,B_1602))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_20189,plain,(
    ! [D_1604] : k7_relset_1('#skF_6','#skF_7','#skF_9',D_1604) = k9_relat_1('#skF_9',D_1604) ),
    inference(resolution,[status(thm)],[c_54,c_20186])).

tff(c_20191,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20189,c_52])).

tff(c_20217,plain,(
    ! [A_1606,B_1607,C_1608] :
      ( r2_hidden('#skF_2'(A_1606,B_1607,C_1608),k1_relat_1(C_1608))
      | ~ r2_hidden(A_1606,k9_relat_1(C_1608,B_1607))
      | ~ v1_relat_1(C_1608) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_20222,plain,(
    ! [C_1609,A_1610,B_1611] :
      ( ~ v1_xboole_0(k1_relat_1(C_1609))
      | ~ r2_hidden(A_1610,k9_relat_1(C_1609,B_1611))
      | ~ v1_relat_1(C_1609) ) ),
    inference(resolution,[status(thm)],[c_20217,c_2])).

tff(c_20225,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_20191,c_20222])).

tff(c_20240,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_20225])).

tff(c_20564,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20563,c_20240])).

tff(c_20568,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20114,c_20564])).

tff(c_20569,plain,(
    r2_hidden('#skF_3'('#skF_7','#skF_6','#skF_9'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_20562])).

tff(c_20576,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_20569,c_2])).

tff(c_20581,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20114,c_20576])).

tff(c_20582,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_20834,plain,(
    ! [A_1723,C_1724] :
      ( r2_hidden(k4_tarski(A_1723,k1_funct_1(C_1724,A_1723)),C_1724)
      | ~ r2_hidden(A_1723,k1_relat_1(C_1724))
      | ~ v1_funct_1(C_1724)
      | ~ v1_relat_1(C_1724) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_20883,plain,(
    ! [C_1725,A_1726] :
      ( ~ v1_xboole_0(C_1725)
      | ~ r2_hidden(A_1726,k1_relat_1(C_1725))
      | ~ v1_funct_1(C_1725)
      | ~ v1_relat_1(C_1725) ) ),
    inference(resolution,[status(thm)],[c_20834,c_2])).

tff(c_20908,plain,(
    ! [C_1727] :
      ( ~ v1_xboole_0(C_1727)
      | ~ v1_funct_1(C_1727)
      | ~ v1_relat_1(C_1727)
      | v1_xboole_0(k1_relat_1(C_1727)) ) ),
    inference(resolution,[status(thm)],[c_4,c_20883])).

tff(c_20703,plain,(
    ! [A_1698,B_1699,C_1700,D_1701] :
      ( k7_relset_1(A_1698,B_1699,C_1700,D_1701) = k9_relat_1(C_1700,D_1701)
      | ~ m1_subset_1(C_1700,k1_zfmisc_1(k2_zfmisc_1(A_1698,B_1699))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_20710,plain,(
    ! [D_1701] : k7_relset_1('#skF_6','#skF_7','#skF_9',D_1701) = k9_relat_1('#skF_9',D_1701) ),
    inference(resolution,[status(thm)],[c_54,c_20703])).

tff(c_20712,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20710,c_52])).

tff(c_20752,plain,(
    ! [A_1704,B_1705,C_1706] :
      ( r2_hidden('#skF_2'(A_1704,B_1705,C_1706),k1_relat_1(C_1706))
      | ~ r2_hidden(A_1704,k9_relat_1(C_1706,B_1705))
      | ~ v1_relat_1(C_1706) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_20777,plain,(
    ! [C_1709,A_1710,B_1711] :
      ( ~ v1_xboole_0(k1_relat_1(C_1709))
      | ~ r2_hidden(A_1710,k9_relat_1(C_1709,B_1711))
      | ~ v1_relat_1(C_1709) ) ),
    inference(resolution,[status(thm)],[c_20752,c_2])).

tff(c_20780,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_20712,c_20777])).

tff(c_20795,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_20780])).

tff(c_20911,plain,
    ( ~ v1_xboole_0('#skF_9')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_20908,c_20795])).

tff(c_20915,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_58,c_20582,c_20911])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:31:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.75/6.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.90/6.35  
% 12.90/6.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.90/6.35  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 12.90/6.35  
% 12.90/6.35  %Foreground sorts:
% 12.90/6.35  
% 12.90/6.35  
% 12.90/6.35  %Background operators:
% 12.90/6.35  
% 12.90/6.35  
% 12.90/6.35  %Foreground operators:
% 12.90/6.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.90/6.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.90/6.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.90/6.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 12.90/6.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 12.90/6.35  tff('#skF_7', type, '#skF_7': $i).
% 12.90/6.35  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i) > $i).
% 12.90/6.35  tff('#skF_10', type, '#skF_10': $i).
% 12.90/6.35  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 12.90/6.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.90/6.35  tff('#skF_6', type, '#skF_6': $i).
% 12.90/6.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 12.90/6.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 12.90/6.35  tff('#skF_9', type, '#skF_9': $i).
% 12.90/6.35  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 12.90/6.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.90/6.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 12.90/6.35  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 12.90/6.35  tff('#skF_8', type, '#skF_8': $i).
% 12.90/6.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.90/6.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.90/6.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.90/6.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 12.90/6.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.90/6.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.90/6.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.90/6.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.90/6.35  
% 12.90/6.38  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 12.90/6.38  tff(f_149, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 12.90/6.38  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 12.90/6.38  tff(f_92, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 12.90/6.38  tff(f_84, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 12.90/6.38  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 12.90/6.38  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 12.90/6.38  tff(f_63, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 12.90/6.38  tff(f_80, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 12.90/6.38  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 12.90/6.38  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 12.90/6.38  tff(f_73, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 12.90/6.38  tff(f_130, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k7_relset_1(C, A, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(F, E), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relset_1)).
% 12.90/6.38  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 12.90/6.38  tff(c_12, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.90/6.38  tff(c_54, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 12.90/6.38  tff(c_86, plain, (![B_159, A_160]: (v1_relat_1(B_159) | ~m1_subset_1(B_159, k1_zfmisc_1(A_160)) | ~v1_relat_1(A_160))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.90/6.38  tff(c_89, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_54, c_86])).
% 12.90/6.38  tff(c_92, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_89])).
% 12.90/6.38  tff(c_58, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_149])).
% 12.90/6.38  tff(c_178, plain, (![A_187, B_188, C_189, D_190]: (k7_relset_1(A_187, B_188, C_189, D_190)=k9_relat_1(C_189, D_190) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.90/6.38  tff(c_181, plain, (![D_190]: (k7_relset_1('#skF_6', '#skF_7', '#skF_9', D_190)=k9_relat_1('#skF_9', D_190))), inference(resolution, [status(thm)], [c_54, c_178])).
% 12.90/6.38  tff(c_52, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 12.90/6.38  tff(c_183, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_52])).
% 12.90/6.38  tff(c_226, plain, (![A_199, B_200, C_201, D_202]: (m1_subset_1(k7_relset_1(A_199, B_200, C_201, D_202), k1_zfmisc_1(B_200)) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(A_199, B_200))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 12.90/6.38  tff(c_245, plain, (![D_190]: (m1_subset_1(k9_relat_1('#skF_9', D_190), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_181, c_226])).
% 12.90/6.38  tff(c_253, plain, (![D_203]: (m1_subset_1(k9_relat_1('#skF_9', D_203), k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_245])).
% 12.90/6.38  tff(c_8, plain, (![A_7, C_9, B_8]: (m1_subset_1(A_7, C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(C_9)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.90/6.38  tff(c_267, plain, (![A_207, D_208]: (m1_subset_1(A_207, '#skF_7') | ~r2_hidden(A_207, k9_relat_1('#skF_9', D_208)))), inference(resolution, [status(thm)], [c_253, c_8])).
% 12.90/6.38  tff(c_283, plain, (m1_subset_1('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_183, c_267])).
% 12.90/6.38  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.90/6.38  tff(c_134, plain, (![A_173, B_174, C_175]: (r2_hidden('#skF_2'(A_173, B_174, C_175), B_174) | ~r2_hidden(A_173, k9_relat_1(C_175, B_174)) | ~v1_relat_1(C_175))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.90/6.38  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.90/6.38  tff(c_149, plain, (![B_176, A_177, C_178]: (~v1_xboole_0(B_176) | ~r2_hidden(A_177, k9_relat_1(C_178, B_176)) | ~v1_relat_1(C_178))), inference(resolution, [status(thm)], [c_134, c_2])).
% 12.90/6.38  tff(c_164, plain, (![B_176, C_178]: (~v1_xboole_0(B_176) | ~v1_relat_1(C_178) | v1_xboole_0(k9_relat_1(C_178, B_176)))), inference(resolution, [status(thm)], [c_4, c_149])).
% 12.90/6.38  tff(c_69, plain, (~v1_xboole_0(k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(resolution, [status(thm)], [c_52, c_2])).
% 12.90/6.38  tff(c_182, plain, (~v1_xboole_0(k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_69])).
% 12.90/6.38  tff(c_195, plain, (~v1_xboole_0('#skF_8') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_164, c_182])).
% 12.90/6.38  tff(c_198, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_195])).
% 12.90/6.38  tff(c_93, plain, (![C_161, B_162, A_163]: (v1_xboole_0(C_161) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(B_162, A_163))) | ~v1_xboole_0(A_163))), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.90/6.38  tff(c_97, plain, (v1_xboole_0('#skF_9') | ~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_54, c_93])).
% 12.90/6.38  tff(c_98, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_97])).
% 12.90/6.38  tff(c_16, plain, (![A_15, B_16, C_17]: (r2_hidden('#skF_2'(A_15, B_16, C_17), B_16) | ~r2_hidden(A_15, k9_relat_1(C_17, B_16)) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.90/6.38  tff(c_123, plain, (![A_169, B_170, C_171]: (k1_relset_1(A_169, B_170, C_171)=k1_relat_1(C_171) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 12.90/6.38  tff(c_127, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_54, c_123])).
% 12.90/6.38  tff(c_605, plain, (![A_257, B_258, C_259]: (r2_hidden('#skF_3'(A_257, B_258, C_259), B_258) | k1_relset_1(B_258, A_257, C_259)=B_258 | ~m1_subset_1(C_259, k1_zfmisc_1(k2_zfmisc_1(B_258, A_257))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 12.90/6.38  tff(c_610, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_6', '#skF_9'), '#skF_6') | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6'), inference(resolution, [status(thm)], [c_54, c_605])).
% 12.90/6.38  tff(c_613, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_6', '#skF_9'), '#skF_6') | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_127, c_610])).
% 12.90/6.38  tff(c_614, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_613])).
% 12.90/6.38  tff(c_20, plain, (![A_15, B_16, C_17]: (r2_hidden('#skF_2'(A_15, B_16, C_17), k1_relat_1(C_17)) | ~r2_hidden(A_15, k9_relat_1(C_17, B_16)) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.90/6.38  tff(c_632, plain, (![A_15, B_16]: (r2_hidden('#skF_2'(A_15, B_16, '#skF_9'), '#skF_6') | ~r2_hidden(A_15, k9_relat_1('#skF_9', B_16)) | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_614, c_20])).
% 12.90/6.38  tff(c_650, plain, (![A_260, B_261]: (r2_hidden('#skF_2'(A_260, B_261, '#skF_9'), '#skF_6') | ~r2_hidden(A_260, k9_relat_1('#skF_9', B_261)))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_632])).
% 12.90/6.38  tff(c_50, plain, (![F_150]: (k1_funct_1('#skF_9', F_150)!='#skF_10' | ~r2_hidden(F_150, '#skF_8') | ~r2_hidden(F_150, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 12.90/6.38  tff(c_775, plain, (![A_288, B_289]: (k1_funct_1('#skF_9', '#skF_2'(A_288, B_289, '#skF_9'))!='#skF_10' | ~r2_hidden('#skF_2'(A_288, B_289, '#skF_9'), '#skF_8') | ~r2_hidden(A_288, k9_relat_1('#skF_9', B_289)))), inference(resolution, [status(thm)], [c_650, c_50])).
% 12.90/6.38  tff(c_779, plain, (![A_15]: (k1_funct_1('#skF_9', '#skF_2'(A_15, '#skF_8', '#skF_9'))!='#skF_10' | ~r2_hidden(A_15, k9_relat_1('#skF_9', '#skF_8')) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_16, c_775])).
% 12.90/6.38  tff(c_789, plain, (![A_290]: (k1_funct_1('#skF_9', '#skF_2'(A_290, '#skF_8', '#skF_9'))!='#skF_10' | ~r2_hidden(A_290, k9_relat_1('#skF_9', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_779])).
% 12.90/6.38  tff(c_815, plain, (k1_funct_1('#skF_9', '#skF_2'('#skF_10', '#skF_8', '#skF_9'))!='#skF_10'), inference(resolution, [status(thm)], [c_183, c_789])).
% 12.90/6.38  tff(c_325, plain, (![A_219, B_220, C_221]: (r2_hidden(k4_tarski('#skF_2'(A_219, B_220, C_221), A_219), C_221) | ~r2_hidden(A_219, k9_relat_1(C_221, B_220)) | ~v1_relat_1(C_221))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.90/6.38  tff(c_24, plain, (![C_23, A_21, B_22]: (k1_funct_1(C_23, A_21)=B_22 | ~r2_hidden(k4_tarski(A_21, B_22), C_23) | ~v1_funct_1(C_23) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.90/6.38  tff(c_850, plain, (![C_299, A_300, B_301]: (k1_funct_1(C_299, '#skF_2'(A_300, B_301, C_299))=A_300 | ~v1_funct_1(C_299) | ~r2_hidden(A_300, k9_relat_1(C_299, B_301)) | ~v1_relat_1(C_299))), inference(resolution, [status(thm)], [c_325, c_24])).
% 12.90/6.38  tff(c_858, plain, (k1_funct_1('#skF_9', '#skF_2'('#skF_10', '#skF_8', '#skF_9'))='#skF_10' | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_183, c_850])).
% 12.90/6.38  tff(c_872, plain, (k1_funct_1('#skF_9', '#skF_2'('#skF_10', '#skF_8', '#skF_9'))='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_58, c_858])).
% 12.90/6.38  tff(c_874, plain, $false, inference(negUnitSimplification, [status(thm)], [c_815, c_872])).
% 12.90/6.38  tff(c_875, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_6', '#skF_9'), '#skF_6')), inference(splitRight, [status(thm)], [c_613])).
% 12.90/6.38  tff(c_884, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_875, c_2])).
% 12.90/6.38  tff(c_1435, plain, (![E_374, A_372, C_376, D_375, B_373]: (m1_subset_1('#skF_5'(A_372, B_373, E_374, D_375, C_376), C_376) | ~r2_hidden(E_374, k7_relset_1(C_376, A_372, D_375, B_373)) | ~m1_subset_1(E_374, A_372) | ~m1_subset_1(D_375, k1_zfmisc_1(k2_zfmisc_1(C_376, A_372))) | v1_xboole_0(C_376) | v1_xboole_0(B_373) | v1_xboole_0(A_372))), inference(cnfTransformation, [status(thm)], [f_130])).
% 12.90/6.38  tff(c_1446, plain, (![D_190, E_374]: (m1_subset_1('#skF_5'('#skF_7', D_190, E_374, '#skF_9', '#skF_6'), '#skF_6') | ~r2_hidden(E_374, k9_relat_1('#skF_9', D_190)) | ~m1_subset_1(E_374, '#skF_7') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | v1_xboole_0('#skF_6') | v1_xboole_0(D_190) | v1_xboole_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_181, c_1435])).
% 12.90/6.38  tff(c_1460, plain, (![D_190, E_374]: (m1_subset_1('#skF_5'('#skF_7', D_190, E_374, '#skF_9', '#skF_6'), '#skF_6') | ~r2_hidden(E_374, k9_relat_1('#skF_9', D_190)) | ~m1_subset_1(E_374, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(D_190) | v1_xboole_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1446])).
% 12.90/6.38  tff(c_1887, plain, (![D_428, E_429]: (m1_subset_1('#skF_5'('#skF_7', D_428, E_429, '#skF_9', '#skF_6'), '#skF_6') | ~r2_hidden(E_429, k9_relat_1('#skF_9', D_428)) | ~m1_subset_1(E_429, '#skF_7') | v1_xboole_0(D_428))), inference(negUnitSimplification, [status(thm)], [c_98, c_884, c_1460])).
% 12.90/6.38  tff(c_1910, plain, (m1_subset_1('#skF_5'('#skF_7', '#skF_8', '#skF_10', '#skF_9', '#skF_6'), '#skF_6') | ~m1_subset_1('#skF_10', '#skF_7') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_183, c_1887])).
% 12.90/6.38  tff(c_1933, plain, (m1_subset_1('#skF_5'('#skF_7', '#skF_8', '#skF_10', '#skF_9', '#skF_6'), '#skF_6') | v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_283, c_1910])).
% 12.90/6.38  tff(c_1934, plain, (m1_subset_1('#skF_5'('#skF_7', '#skF_8', '#skF_10', '#skF_9', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_198, c_1933])).
% 12.90/6.38  tff(c_1938, plain, (![B_431, E_432, A_430, D_433, C_434]: (r2_hidden(k4_tarski('#skF_5'(A_430, B_431, E_432, D_433, C_434), E_432), D_433) | ~r2_hidden(E_432, k7_relset_1(C_434, A_430, D_433, B_431)) | ~m1_subset_1(E_432, A_430) | ~m1_subset_1(D_433, k1_zfmisc_1(k2_zfmisc_1(C_434, A_430))) | v1_xboole_0(C_434) | v1_xboole_0(B_431) | v1_xboole_0(A_430))), inference(cnfTransformation, [status(thm)], [f_130])).
% 12.90/6.38  tff(c_12282, plain, (![E_1226, C_1229, A_1227, D_1225, B_1228]: (k1_funct_1(D_1225, '#skF_5'(A_1227, B_1228, E_1226, D_1225, C_1229))=E_1226 | ~v1_funct_1(D_1225) | ~v1_relat_1(D_1225) | ~r2_hidden(E_1226, k7_relset_1(C_1229, A_1227, D_1225, B_1228)) | ~m1_subset_1(E_1226, A_1227) | ~m1_subset_1(D_1225, k1_zfmisc_1(k2_zfmisc_1(C_1229, A_1227))) | v1_xboole_0(C_1229) | v1_xboole_0(B_1228) | v1_xboole_0(A_1227))), inference(resolution, [status(thm)], [c_1938, c_24])).
% 12.90/6.38  tff(c_12304, plain, (![D_190, E_1226]: (k1_funct_1('#skF_9', '#skF_5'('#skF_7', D_190, E_1226, '#skF_9', '#skF_6'))=E_1226 | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(E_1226, k9_relat_1('#skF_9', D_190)) | ~m1_subset_1(E_1226, '#skF_7') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | v1_xboole_0('#skF_6') | v1_xboole_0(D_190) | v1_xboole_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_181, c_12282])).
% 12.90/6.38  tff(c_12324, plain, (![D_190, E_1226]: (k1_funct_1('#skF_9', '#skF_5'('#skF_7', D_190, E_1226, '#skF_9', '#skF_6'))=E_1226 | ~r2_hidden(E_1226, k9_relat_1('#skF_9', D_190)) | ~m1_subset_1(E_1226, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(D_190) | v1_xboole_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_92, c_58, c_12304])).
% 12.90/6.38  tff(c_12329, plain, (![D_1230, E_1231]: (k1_funct_1('#skF_9', '#skF_5'('#skF_7', D_1230, E_1231, '#skF_9', '#skF_6'))=E_1231 | ~r2_hidden(E_1231, k9_relat_1('#skF_9', D_1230)) | ~m1_subset_1(E_1231, '#skF_7') | v1_xboole_0(D_1230))), inference(negUnitSimplification, [status(thm)], [c_98, c_884, c_12324])).
% 12.90/6.38  tff(c_12410, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_8', '#skF_10', '#skF_9', '#skF_6'))='#skF_10' | ~m1_subset_1('#skF_10', '#skF_7') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_183, c_12329])).
% 12.90/6.38  tff(c_12484, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_8', '#skF_10', '#skF_9', '#skF_6'))='#skF_10' | v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_283, c_12410])).
% 12.90/6.38  tff(c_12485, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_8', '#skF_10', '#skF_9', '#skF_6'))='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_198, c_12484])).
% 12.90/6.38  tff(c_1654, plain, (![A_405, C_409, D_408, B_406, E_407]: (r2_hidden('#skF_5'(A_405, B_406, E_407, D_408, C_409), B_406) | ~r2_hidden(E_407, k7_relset_1(C_409, A_405, D_408, B_406)) | ~m1_subset_1(E_407, A_405) | ~m1_subset_1(D_408, k1_zfmisc_1(k2_zfmisc_1(C_409, A_405))) | v1_xboole_0(C_409) | v1_xboole_0(B_406) | v1_xboole_0(A_405))), inference(cnfTransformation, [status(thm)], [f_130])).
% 12.90/6.38  tff(c_1659, plain, (![B_406, E_407]: (r2_hidden('#skF_5'('#skF_7', B_406, E_407, '#skF_9', '#skF_6'), B_406) | ~r2_hidden(E_407, k7_relset_1('#skF_6', '#skF_7', '#skF_9', B_406)) | ~m1_subset_1(E_407, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(B_406) | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_54, c_1654])).
% 12.90/6.38  tff(c_1662, plain, (![B_406, E_407]: (r2_hidden('#skF_5'('#skF_7', B_406, E_407, '#skF_9', '#skF_6'), B_406) | ~r2_hidden(E_407, k9_relat_1('#skF_9', B_406)) | ~m1_subset_1(E_407, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(B_406) | v1_xboole_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_1659])).
% 12.90/6.38  tff(c_1669, plain, (![B_415, E_416]: (r2_hidden('#skF_5'('#skF_7', B_415, E_416, '#skF_9', '#skF_6'), B_415) | ~r2_hidden(E_416, k9_relat_1('#skF_9', B_415)) | ~m1_subset_1(E_416, '#skF_7') | v1_xboole_0(B_415))), inference(negUnitSimplification, [status(thm)], [c_98, c_884, c_1662])).
% 12.90/6.38  tff(c_6, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.90/6.38  tff(c_75, plain, (![F_158]: (k1_funct_1('#skF_9', F_158)!='#skF_10' | ~r2_hidden(F_158, '#skF_8') | ~r2_hidden(F_158, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 12.90/6.38  tff(c_84, plain, (![A_5]: (k1_funct_1('#skF_9', A_5)!='#skF_10' | ~r2_hidden(A_5, '#skF_8') | v1_xboole_0('#skF_6') | ~m1_subset_1(A_5, '#skF_6'))), inference(resolution, [status(thm)], [c_6, c_75])).
% 12.90/6.38  tff(c_109, plain, (![A_5]: (k1_funct_1('#skF_9', A_5)!='#skF_10' | ~r2_hidden(A_5, '#skF_8') | ~m1_subset_1(A_5, '#skF_6'))), inference(splitLeft, [status(thm)], [c_84])).
% 12.90/6.38  tff(c_1758, plain, (![E_416]: (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_8', E_416, '#skF_9', '#skF_6'))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_7', '#skF_8', E_416, '#skF_9', '#skF_6'), '#skF_6') | ~r2_hidden(E_416, k9_relat_1('#skF_9', '#skF_8')) | ~m1_subset_1(E_416, '#skF_7') | v1_xboole_0('#skF_8'))), inference(resolution, [status(thm)], [c_1669, c_109])).
% 12.90/6.38  tff(c_20007, plain, (![E_1574]: (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_8', E_1574, '#skF_9', '#skF_6'))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_7', '#skF_8', E_1574, '#skF_9', '#skF_6'), '#skF_6') | ~r2_hidden(E_1574, k9_relat_1('#skF_9', '#skF_8')) | ~m1_subset_1(E_1574, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_198, c_1758])).
% 12.90/6.38  tff(c_20062, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_8', '#skF_10', '#skF_9', '#skF_6'))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_7', '#skF_8', '#skF_10', '#skF_9', '#skF_6'), '#skF_6') | ~m1_subset_1('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_183, c_20007])).
% 12.90/6.38  tff(c_20113, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_283, c_1934, c_12485, c_20062])).
% 12.90/6.38  tff(c_20114, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_84])).
% 12.90/6.38  tff(c_20116, plain, (![A_1575, B_1576, C_1577]: (k1_relset_1(A_1575, B_1576, C_1577)=k1_relat_1(C_1577) | ~m1_subset_1(C_1577, k1_zfmisc_1(k2_zfmisc_1(A_1575, B_1576))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 12.90/6.38  tff(c_20120, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_54, c_20116])).
% 12.90/6.38  tff(c_20554, plain, (![A_1659, B_1660, C_1661]: (r2_hidden('#skF_3'(A_1659, B_1660, C_1661), B_1660) | k1_relset_1(B_1660, A_1659, C_1661)=B_1660 | ~m1_subset_1(C_1661, k1_zfmisc_1(k2_zfmisc_1(B_1660, A_1659))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 12.90/6.38  tff(c_20559, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_6', '#skF_9'), '#skF_6') | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6'), inference(resolution, [status(thm)], [c_54, c_20554])).
% 12.90/6.38  tff(c_20562, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_6', '#skF_9'), '#skF_6') | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_20120, c_20559])).
% 12.90/6.38  tff(c_20563, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_20562])).
% 12.90/6.38  tff(c_20186, plain, (![A_1601, B_1602, C_1603, D_1604]: (k7_relset_1(A_1601, B_1602, C_1603, D_1604)=k9_relat_1(C_1603, D_1604) | ~m1_subset_1(C_1603, k1_zfmisc_1(k2_zfmisc_1(A_1601, B_1602))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.90/6.38  tff(c_20189, plain, (![D_1604]: (k7_relset_1('#skF_6', '#skF_7', '#skF_9', D_1604)=k9_relat_1('#skF_9', D_1604))), inference(resolution, [status(thm)], [c_54, c_20186])).
% 12.90/6.38  tff(c_20191, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_20189, c_52])).
% 12.90/6.38  tff(c_20217, plain, (![A_1606, B_1607, C_1608]: (r2_hidden('#skF_2'(A_1606, B_1607, C_1608), k1_relat_1(C_1608)) | ~r2_hidden(A_1606, k9_relat_1(C_1608, B_1607)) | ~v1_relat_1(C_1608))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.90/6.38  tff(c_20222, plain, (![C_1609, A_1610, B_1611]: (~v1_xboole_0(k1_relat_1(C_1609)) | ~r2_hidden(A_1610, k9_relat_1(C_1609, B_1611)) | ~v1_relat_1(C_1609))), inference(resolution, [status(thm)], [c_20217, c_2])).
% 12.90/6.38  tff(c_20225, plain, (~v1_xboole_0(k1_relat_1('#skF_9')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_20191, c_20222])).
% 12.90/6.38  tff(c_20240, plain, (~v1_xboole_0(k1_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_20225])).
% 12.90/6.38  tff(c_20564, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20563, c_20240])).
% 12.90/6.38  tff(c_20568, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20114, c_20564])).
% 12.90/6.38  tff(c_20569, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_6', '#skF_9'), '#skF_6')), inference(splitRight, [status(thm)], [c_20562])).
% 12.90/6.38  tff(c_20576, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_20569, c_2])).
% 12.90/6.38  tff(c_20581, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20114, c_20576])).
% 12.90/6.38  tff(c_20582, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_97])).
% 12.90/6.38  tff(c_20834, plain, (![A_1723, C_1724]: (r2_hidden(k4_tarski(A_1723, k1_funct_1(C_1724, A_1723)), C_1724) | ~r2_hidden(A_1723, k1_relat_1(C_1724)) | ~v1_funct_1(C_1724) | ~v1_relat_1(C_1724))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.90/6.38  tff(c_20883, plain, (![C_1725, A_1726]: (~v1_xboole_0(C_1725) | ~r2_hidden(A_1726, k1_relat_1(C_1725)) | ~v1_funct_1(C_1725) | ~v1_relat_1(C_1725))), inference(resolution, [status(thm)], [c_20834, c_2])).
% 12.90/6.38  tff(c_20908, plain, (![C_1727]: (~v1_xboole_0(C_1727) | ~v1_funct_1(C_1727) | ~v1_relat_1(C_1727) | v1_xboole_0(k1_relat_1(C_1727)))), inference(resolution, [status(thm)], [c_4, c_20883])).
% 12.90/6.38  tff(c_20703, plain, (![A_1698, B_1699, C_1700, D_1701]: (k7_relset_1(A_1698, B_1699, C_1700, D_1701)=k9_relat_1(C_1700, D_1701) | ~m1_subset_1(C_1700, k1_zfmisc_1(k2_zfmisc_1(A_1698, B_1699))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.90/6.38  tff(c_20710, plain, (![D_1701]: (k7_relset_1('#skF_6', '#skF_7', '#skF_9', D_1701)=k9_relat_1('#skF_9', D_1701))), inference(resolution, [status(thm)], [c_54, c_20703])).
% 12.90/6.38  tff(c_20712, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_20710, c_52])).
% 12.90/6.38  tff(c_20752, plain, (![A_1704, B_1705, C_1706]: (r2_hidden('#skF_2'(A_1704, B_1705, C_1706), k1_relat_1(C_1706)) | ~r2_hidden(A_1704, k9_relat_1(C_1706, B_1705)) | ~v1_relat_1(C_1706))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.90/6.38  tff(c_20777, plain, (![C_1709, A_1710, B_1711]: (~v1_xboole_0(k1_relat_1(C_1709)) | ~r2_hidden(A_1710, k9_relat_1(C_1709, B_1711)) | ~v1_relat_1(C_1709))), inference(resolution, [status(thm)], [c_20752, c_2])).
% 12.90/6.38  tff(c_20780, plain, (~v1_xboole_0(k1_relat_1('#skF_9')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_20712, c_20777])).
% 12.90/6.38  tff(c_20795, plain, (~v1_xboole_0(k1_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_20780])).
% 12.90/6.38  tff(c_20911, plain, (~v1_xboole_0('#skF_9') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_20908, c_20795])).
% 12.90/6.38  tff(c_20915, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_58, c_20582, c_20911])).
% 12.90/6.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.90/6.38  
% 12.90/6.38  Inference rules
% 12.90/6.38  ----------------------
% 12.90/6.38  #Ref     : 0
% 12.90/6.38  #Sup     : 4455
% 12.90/6.38  #Fact    : 0
% 12.90/6.38  #Define  : 0
% 12.90/6.38  #Split   : 49
% 12.90/6.38  #Chain   : 0
% 12.90/6.38  #Close   : 0
% 12.90/6.38  
% 12.90/6.38  Ordering : KBO
% 12.90/6.38  
% 12.90/6.38  Simplification rules
% 12.90/6.38  ----------------------
% 12.90/6.38  #Subsume      : 1302
% 12.90/6.38  #Demod        : 1160
% 12.90/6.38  #Tautology    : 237
% 12.90/6.38  #SimpNegUnit  : 323
% 12.90/6.38  #BackRed      : 19
% 12.90/6.38  
% 12.90/6.38  #Partial instantiations: 0
% 12.90/6.38  #Strategies tried      : 1
% 12.90/6.38  
% 12.90/6.38  Timing (in seconds)
% 12.90/6.38  ----------------------
% 12.90/6.38  Preprocessing        : 0.36
% 12.90/6.38  Parsing              : 0.18
% 12.90/6.38  CNF conversion       : 0.03
% 12.90/6.38  Main loop            : 5.13
% 12.90/6.38  Inferencing          : 1.11
% 12.90/6.38  Reduction            : 1.07
% 12.90/6.38  Demodulation         : 0.76
% 12.90/6.38  BG Simplification    : 0.12
% 12.90/6.38  Subsumption          : 2.55
% 12.90/6.38  Abstraction          : 0.19
% 12.90/6.38  MUC search           : 0.00
% 12.90/6.38  Cooper               : 0.00
% 12.90/6.38  Total                : 5.54
% 12.90/6.38  Index Insertion      : 0.00
% 12.90/6.38  Index Deletion       : 0.00
% 12.90/6.38  Index Matching       : 0.00
% 12.90/6.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
