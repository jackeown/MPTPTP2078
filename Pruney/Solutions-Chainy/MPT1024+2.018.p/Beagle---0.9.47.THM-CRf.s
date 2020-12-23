%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:24 EST 2020

% Result     : Theorem 7.86s
% Output     : CNFRefutation 7.86s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 423 expanded)
%              Number of leaves         :   37 ( 153 expanded)
%              Depth                    :   12
%              Number of atoms          :  297 (1189 expanded)
%              Number of equality atoms :   30 ( 142 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

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
                  ~ ( r2_hidden(F,A)
                    & r2_hidden(F,C)
                    & E = k1_funct_1(D,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_101,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_93,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_127,axiom,(
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

tff(f_48,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_98,plain,(
    ! [C_149,A_150,B_151] :
      ( v1_relat_1(C_149)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_112,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_98])).

tff(c_10,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ v1_xboole_0(B_6)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_166,plain,(
    ! [C_165,A_166,B_167] :
      ( v1_xboole_0(C_165)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167)))
      | ~ v1_xboole_0(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_182,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_166])).

tff(c_183,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_182])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r2_hidden(B_6,A_5)
      | ~ m1_subset_1(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_124,plain,(
    ! [F_156] :
      ( k1_funct_1('#skF_7',F_156) != '#skF_8'
      | ~ r2_hidden(F_156,'#skF_6')
      | ~ r2_hidden(F_156,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_133,plain,(
    ! [B_6] :
      ( k1_funct_1('#skF_7',B_6) != '#skF_8'
      | ~ r2_hidden(B_6,'#skF_4')
      | ~ m1_subset_1(B_6,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_8,c_124])).

tff(c_222,plain,(
    ! [B_178] :
      ( k1_funct_1('#skF_7',B_178) != '#skF_8'
      | ~ r2_hidden(B_178,'#skF_4')
      | ~ m1_subset_1(B_178,'#skF_6') ) ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_230,plain,
    ( k1_funct_1('#skF_7','#skF_1'('#skF_4')) != '#skF_8'
    | ~ m1_subset_1('#skF_1'('#skF_4'),'#skF_6')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_222])).

tff(c_236,plain,
    ( k1_funct_1('#skF_7','#skF_1'('#skF_4')) != '#skF_8'
    | ~ m1_subset_1('#skF_1'('#skF_4'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_230])).

tff(c_237,plain,(
    ~ m1_subset_1('#skF_1'('#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_236])).

tff(c_241,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_4'))
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_10,c_237])).

tff(c_242,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_241])).

tff(c_433,plain,(
    ! [A_218,B_219,C_220,D_221] :
      ( k7_relset_1(A_218,B_219,C_220,D_221) = k9_relat_1(C_220,D_221)
      | ~ m1_subset_1(C_220,k1_zfmisc_1(k2_zfmisc_1(A_218,B_219))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_454,plain,(
    ! [D_221] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_221) = k9_relat_1('#skF_7',D_221) ),
    inference(resolution,[status(thm)],[c_54,c_433])).

tff(c_52,plain,(
    r2_hidden('#skF_8',k7_relset_1('#skF_4','#skF_5','#skF_7','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_457,plain,(
    r2_hidden('#skF_8',k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_52])).

tff(c_458,plain,(
    ! [D_222] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_222) = k9_relat_1('#skF_7',D_222) ),
    inference(resolution,[status(thm)],[c_54,c_433])).

tff(c_38,plain,(
    ! [A_32,B_33,C_34,D_35] :
      ( m1_subset_1(k7_relset_1(A_32,B_33,C_34,D_35),k1_zfmisc_1(B_33))
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_464,plain,(
    ! [D_222] :
      ( m1_subset_1(k9_relat_1('#skF_7',D_222),k1_zfmisc_1('#skF_5'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_38])).

tff(c_570,plain,(
    ! [D_226] : m1_subset_1(k9_relat_1('#skF_7',D_226),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_464])).

tff(c_16,plain,(
    ! [A_9,C_11,B_10] :
      ( m1_subset_1(A_9,C_11)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(C_11))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_588,plain,(
    ! [A_227,D_228] :
      ( m1_subset_1(A_227,'#skF_5')
      | ~ r2_hidden(A_227,k9_relat_1('#skF_7',D_228)) ) ),
    inference(resolution,[status(thm)],[c_570,c_16])).

tff(c_608,plain,(
    m1_subset_1('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_457,c_588])).

tff(c_135,plain,(
    ! [C_157,B_158,A_159] :
      ( v1_xboole_0(C_157)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(B_158,A_159)))
      | ~ v1_xboole_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_151,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_135])).

tff(c_152,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_1056,plain,(
    ! [C_282,E_281,D_283,A_280,B_284] :
      ( m1_subset_1('#skF_3'(A_280,E_281,C_282,D_283,B_284),C_282)
      | ~ r2_hidden(E_281,k7_relset_1(C_282,A_280,D_283,B_284))
      | ~ m1_subset_1(E_281,A_280)
      | ~ m1_subset_1(D_283,k1_zfmisc_1(k2_zfmisc_1(C_282,A_280)))
      | v1_xboole_0(C_282)
      | v1_xboole_0(B_284)
      | v1_xboole_0(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1064,plain,(
    ! [E_281,D_221] :
      ( m1_subset_1('#skF_3'('#skF_5',E_281,'#skF_4','#skF_7',D_221),'#skF_4')
      | ~ r2_hidden(E_281,k9_relat_1('#skF_7',D_221))
      | ~ m1_subset_1(E_281,'#skF_5')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(D_221)
      | v1_xboole_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_454,c_1056])).

tff(c_1077,plain,(
    ! [E_281,D_221] :
      ( m1_subset_1('#skF_3'('#skF_5',E_281,'#skF_4','#skF_7',D_221),'#skF_4')
      | ~ r2_hidden(E_281,k9_relat_1('#skF_7',D_221))
      | ~ m1_subset_1(E_281,'#skF_5')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(D_221)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1064])).

tff(c_1971,plain,(
    ! [E_373,D_374] :
      ( m1_subset_1('#skF_3'('#skF_5',E_373,'#skF_4','#skF_7',D_374),'#skF_4')
      | ~ r2_hidden(E_373,k9_relat_1('#skF_7',D_374))
      | ~ m1_subset_1(E_373,'#skF_5')
      | v1_xboole_0(D_374) ) ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_183,c_1077])).

tff(c_1990,plain,
    ( m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_4','#skF_7','#skF_6'),'#skF_4')
    | ~ m1_subset_1('#skF_8','#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_457,c_1971])).

tff(c_2016,plain,
    ( m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_4','#skF_7','#skF_6'),'#skF_4')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_1990])).

tff(c_2017,plain,(
    m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_4','#skF_7','#skF_6'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_242,c_2016])).

tff(c_935,plain,(
    ! [B_261,D_260,A_257,C_259,E_258] :
      ( r2_hidden('#skF_3'(A_257,E_258,C_259,D_260,B_261),B_261)
      | ~ r2_hidden(E_258,k7_relset_1(C_259,A_257,D_260,B_261))
      | ~ m1_subset_1(E_258,A_257)
      | ~ m1_subset_1(D_260,k1_zfmisc_1(k2_zfmisc_1(C_259,A_257)))
      | v1_xboole_0(C_259)
      | v1_xboole_0(B_261)
      | v1_xboole_0(A_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_949,plain,(
    ! [E_258,B_261] :
      ( r2_hidden('#skF_3'('#skF_5',E_258,'#skF_4','#skF_7',B_261),B_261)
      | ~ r2_hidden(E_258,k7_relset_1('#skF_4','#skF_5','#skF_7',B_261))
      | ~ m1_subset_1(E_258,'#skF_5')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(B_261)
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_935])).

tff(c_957,plain,(
    ! [E_258,B_261] :
      ( r2_hidden('#skF_3'('#skF_5',E_258,'#skF_4','#skF_7',B_261),B_261)
      | ~ r2_hidden(E_258,k9_relat_1('#skF_7',B_261))
      | ~ m1_subset_1(E_258,'#skF_5')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(B_261)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_949])).

tff(c_1119,plain,(
    ! [E_295,B_296] :
      ( r2_hidden('#skF_3'('#skF_5',E_295,'#skF_4','#skF_7',B_296),B_296)
      | ~ r2_hidden(E_295,k9_relat_1('#skF_7',B_296))
      | ~ m1_subset_1(E_295,'#skF_5')
      | v1_xboole_0(B_296) ) ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_183,c_957])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,B_8)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2439,plain,(
    ! [E_440,B_441] :
      ( m1_subset_1('#skF_3'('#skF_5',E_440,'#skF_4','#skF_7',B_441),B_441)
      | ~ r2_hidden(E_440,k9_relat_1('#skF_7',B_441))
      | ~ m1_subset_1(E_440,'#skF_5')
      | v1_xboole_0(B_441) ) ),
    inference(resolution,[status(thm)],[c_1119,c_14])).

tff(c_2453,plain,
    ( m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_4','#skF_7','#skF_6'),'#skF_6')
    | ~ m1_subset_1('#skF_8','#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_457,c_2439])).

tff(c_2475,plain,
    ( m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_4','#skF_7','#skF_6'),'#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_2453])).

tff(c_2476,plain,(
    m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_4','#skF_7','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_242,c_2475])).

tff(c_226,plain,(
    ! [B_6] :
      ( k1_funct_1('#skF_7',B_6) != '#skF_8'
      | ~ m1_subset_1(B_6,'#skF_6')
      | ~ m1_subset_1(B_6,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8,c_222])).

tff(c_233,plain,(
    ! [B_6] :
      ( k1_funct_1('#skF_7',B_6) != '#skF_8'
      | ~ m1_subset_1(B_6,'#skF_6')
      | ~ m1_subset_1(B_6,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_226])).

tff(c_2506,plain,
    ( k1_funct_1('#skF_7','#skF_3'('#skF_5','#skF_8','#skF_4','#skF_7','#skF_6')) != '#skF_8'
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_4','#skF_7','#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2476,c_233])).

tff(c_2512,plain,(
    k1_funct_1('#skF_7','#skF_3'('#skF_5','#skF_8','#skF_4','#skF_7','#skF_6')) != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2017,c_2506])).

tff(c_58,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1372,plain,(
    ! [C_312,D_313,A_310,B_314,E_311] :
      ( r2_hidden(k4_tarski('#skF_3'(A_310,E_311,C_312,D_313,B_314),E_311),D_313)
      | ~ r2_hidden(E_311,k7_relset_1(C_312,A_310,D_313,B_314))
      | ~ m1_subset_1(E_311,A_310)
      | ~ m1_subset_1(D_313,k1_zfmisc_1(k2_zfmisc_1(C_312,A_310)))
      | v1_xboole_0(C_312)
      | v1_xboole_0(B_314)
      | v1_xboole_0(A_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_28,plain,(
    ! [C_20,A_18,B_19] :
      ( k1_funct_1(C_20,A_18) = B_19
      | ~ r2_hidden(k4_tarski(A_18,B_19),C_20)
      | ~ v1_funct_1(C_20)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_5248,plain,(
    ! [E_610,B_609,C_607,A_608,D_606] :
      ( k1_funct_1(D_606,'#skF_3'(A_608,E_610,C_607,D_606,B_609)) = E_610
      | ~ v1_funct_1(D_606)
      | ~ v1_relat_1(D_606)
      | ~ r2_hidden(E_610,k7_relset_1(C_607,A_608,D_606,B_609))
      | ~ m1_subset_1(E_610,A_608)
      | ~ m1_subset_1(D_606,k1_zfmisc_1(k2_zfmisc_1(C_607,A_608)))
      | v1_xboole_0(C_607)
      | v1_xboole_0(B_609)
      | v1_xboole_0(A_608) ) ),
    inference(resolution,[status(thm)],[c_1372,c_28])).

tff(c_5264,plain,(
    ! [E_610,D_221] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_5',E_610,'#skF_4','#skF_7',D_221)) = E_610
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(E_610,k9_relat_1('#skF_7',D_221))
      | ~ m1_subset_1(E_610,'#skF_5')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(D_221)
      | v1_xboole_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_454,c_5248])).

tff(c_5281,plain,(
    ! [E_610,D_221] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_5',E_610,'#skF_4','#skF_7',D_221)) = E_610
      | ~ r2_hidden(E_610,k9_relat_1('#skF_7',D_221))
      | ~ m1_subset_1(E_610,'#skF_5')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(D_221)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_112,c_58,c_5264])).

tff(c_5288,plain,(
    ! [E_611,D_612] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_5',E_611,'#skF_4','#skF_7',D_612)) = E_611
      | ~ r2_hidden(E_611,k9_relat_1('#skF_7',D_612))
      | ~ m1_subset_1(E_611,'#skF_5')
      | v1_xboole_0(D_612) ) ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_183,c_5281])).

tff(c_5325,plain,
    ( k1_funct_1('#skF_7','#skF_3'('#skF_5','#skF_8','#skF_4','#skF_7','#skF_6')) = '#skF_8'
    | ~ m1_subset_1('#skF_8','#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_457,c_5288])).

tff(c_5368,plain,
    ( k1_funct_1('#skF_7','#skF_3'('#skF_5','#skF_8','#skF_4','#skF_7','#skF_6')) = '#skF_8'
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_5325])).

tff(c_5370,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_242,c_2512,c_5368])).

tff(c_5372,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_241])).

tff(c_5398,plain,(
    ! [A_615,B_616,C_617] :
      ( r2_hidden('#skF_2'(A_615,B_616,C_617),B_616)
      | ~ r2_hidden(A_615,k9_relat_1(C_617,B_616))
      | ~ v1_relat_1(C_617) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5422,plain,(
    ! [B_618,A_619,C_620] :
      ( ~ v1_xboole_0(B_618)
      | ~ r2_hidden(A_619,k9_relat_1(C_620,B_618))
      | ~ v1_relat_1(C_620) ) ),
    inference(resolution,[status(thm)],[c_5398,c_2])).

tff(c_5437,plain,(
    ! [B_618,C_620] :
      ( ~ v1_xboole_0(B_618)
      | ~ v1_relat_1(C_620)
      | v1_xboole_0(k9_relat_1(C_620,B_618)) ) ),
    inference(resolution,[status(thm)],[c_4,c_5422])).

tff(c_5548,plain,(
    ! [A_646,B_647,C_648,D_649] :
      ( k7_relset_1(A_646,B_647,C_648,D_649) = k9_relat_1(C_648,D_649)
      | ~ m1_subset_1(C_648,k1_zfmisc_1(k2_zfmisc_1(A_646,B_647))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_5569,plain,(
    ! [D_649] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_649) = k9_relat_1('#skF_7',D_649) ),
    inference(resolution,[status(thm)],[c_54,c_5548])).

tff(c_92,plain,(
    ~ v1_xboole_0(k7_relset_1('#skF_4','#skF_5','#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_52,c_2])).

tff(c_5571,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5569,c_92])).

tff(c_5589,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_5437,c_5571])).

tff(c_5593,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_5372,c_5589])).

tff(c_5594,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_5595,plain,(
    ! [A_651,B_652,C_653] :
      ( r2_hidden('#skF_2'(A_651,B_652,C_653),B_652)
      | ~ r2_hidden(A_651,k9_relat_1(C_653,B_652))
      | ~ v1_relat_1(C_653) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_5614,plain,(
    ! [B_654,A_655,C_656] :
      ( ~ v1_xboole_0(B_654)
      | ~ r2_hidden(A_655,k9_relat_1(C_656,B_654))
      | ~ v1_relat_1(C_656) ) ),
    inference(resolution,[status(thm)],[c_5595,c_2])).

tff(c_5629,plain,(
    ! [B_654,C_656] :
      ( ~ v1_xboole_0(B_654)
      | ~ v1_relat_1(C_656)
      | v1_xboole_0(k9_relat_1(C_656,B_654)) ) ),
    inference(resolution,[status(thm)],[c_4,c_5614])).

tff(c_5747,plain,(
    ! [A_687,B_688,C_689,D_690] :
      ( k7_relset_1(A_687,B_688,C_689,D_690) = k9_relat_1(C_689,D_690)
      | ~ m1_subset_1(C_689,k1_zfmisc_1(k2_zfmisc_1(A_687,B_688))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_5768,plain,(
    ! [D_690] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_690) = k9_relat_1('#skF_7',D_690) ),
    inference(resolution,[status(thm)],[c_54,c_5747])).

tff(c_5770,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5768,c_92])).

tff(c_5837,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_5629,c_5770])).

tff(c_5844,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_5594,c_5837])).

tff(c_5845,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_6049,plain,(
    ! [A_742,B_743,C_744,D_745] :
      ( k7_relset_1(A_742,B_743,C_744,D_745) = k9_relat_1(C_744,D_745)
      | ~ m1_subset_1(C_744,k1_zfmisc_1(k2_zfmisc_1(A_742,B_743))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_6070,plain,(
    ! [D_745] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_745) = k9_relat_1('#skF_7',D_745) ),
    inference(resolution,[status(thm)],[c_54,c_6049])).

tff(c_6124,plain,(
    r2_hidden('#skF_8',k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6070,c_52])).

tff(c_6071,plain,(
    ! [A_746,B_747,C_748] :
      ( r2_hidden(k4_tarski('#skF_2'(A_746,B_747,C_748),A_746),C_748)
      | ~ r2_hidden(A_746,k9_relat_1(C_748,B_747))
      | ~ v1_relat_1(C_748) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6281,plain,(
    ! [C_755,A_756,B_757] :
      ( ~ v1_xboole_0(C_755)
      | ~ r2_hidden(A_756,k9_relat_1(C_755,B_757))
      | ~ v1_relat_1(C_755) ) ),
    inference(resolution,[status(thm)],[c_6071,c_2])).

tff(c_6288,plain,
    ( ~ v1_xboole_0('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_6124,c_6281])).

tff(c_6309,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_5845,c_6288])).

tff(c_6310,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_6553,plain,(
    ! [A_810,B_811,C_812,D_813] :
      ( k7_relset_1(A_810,B_811,C_812,D_813) = k9_relat_1(C_812,D_813)
      | ~ m1_subset_1(C_812,k1_zfmisc_1(k2_zfmisc_1(A_810,B_811))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_6570,plain,(
    ! [D_813] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_813) = k9_relat_1('#skF_7',D_813) ),
    inference(resolution,[status(thm)],[c_54,c_6553])).

tff(c_6573,plain,(
    r2_hidden('#skF_8',k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6570,c_52])).

tff(c_6700,plain,(
    ! [A_822,B_823,C_824] :
      ( r2_hidden(k4_tarski('#skF_2'(A_822,B_823,C_824),A_822),C_824)
      | ~ r2_hidden(A_822,k9_relat_1(C_824,B_823))
      | ~ v1_relat_1(C_824) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6756,plain,(
    ! [C_825,A_826,B_827] :
      ( ~ v1_xboole_0(C_825)
      | ~ r2_hidden(A_826,k9_relat_1(C_825,B_827))
      | ~ v1_relat_1(C_825) ) ),
    inference(resolution,[status(thm)],[c_6700,c_2])).

tff(c_6763,plain,
    ( ~ v1_xboole_0('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_6573,c_6756])).

tff(c_6780,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_6310,c_6763])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:17:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.86/2.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.86/2.68  
% 7.86/2.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.86/2.68  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4
% 7.86/2.68  
% 7.86/2.68  %Foreground sorts:
% 7.86/2.68  
% 7.86/2.68  
% 7.86/2.68  %Background operators:
% 7.86/2.68  
% 7.86/2.68  
% 7.86/2.68  %Foreground operators:
% 7.86/2.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.86/2.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.86/2.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.86/2.68  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.86/2.68  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.86/2.68  tff('#skF_7', type, '#skF_7': $i).
% 7.86/2.68  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 7.86/2.68  tff('#skF_5', type, '#skF_5': $i).
% 7.86/2.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.86/2.68  tff('#skF_6', type, '#skF_6': $i).
% 7.86/2.68  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.86/2.68  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.86/2.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.86/2.68  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.86/2.68  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 7.86/2.68  tff('#skF_8', type, '#skF_8': $i).
% 7.86/2.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.86/2.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.86/2.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.86/2.68  tff('#skF_4', type, '#skF_4': $i).
% 7.86/2.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.86/2.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.86/2.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.86/2.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.86/2.68  
% 7.86/2.70  tff(f_146, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 7.86/2.70  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.86/2.70  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 7.86/2.70  tff(f_86, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 7.86/2.70  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.86/2.70  tff(f_101, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 7.86/2.70  tff(f_97, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 7.86/2.70  tff(f_54, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 7.86/2.70  tff(f_93, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 7.86/2.70  tff(f_127, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k7_relset_1(C, A, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(F, E), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relset_1)).
% 7.86/2.70  tff(f_48, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 7.86/2.70  tff(f_75, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 7.86/2.70  tff(f_65, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 7.86/2.70  tff(c_54, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.86/2.70  tff(c_98, plain, (![C_149, A_150, B_151]: (v1_relat_1(C_149) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.86/2.70  tff(c_112, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_54, c_98])).
% 7.86/2.70  tff(c_10, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~v1_xboole_0(B_6) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.86/2.70  tff(c_166, plain, (![C_165, A_166, B_167]: (v1_xboole_0(C_165) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))) | ~v1_xboole_0(A_166))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.86/2.70  tff(c_182, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_166])).
% 7.86/2.70  tff(c_183, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_182])).
% 7.86/2.70  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.86/2.70  tff(c_8, plain, (![B_6, A_5]: (r2_hidden(B_6, A_5) | ~m1_subset_1(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.86/2.70  tff(c_124, plain, (![F_156]: (k1_funct_1('#skF_7', F_156)!='#skF_8' | ~r2_hidden(F_156, '#skF_6') | ~r2_hidden(F_156, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.86/2.70  tff(c_133, plain, (![B_6]: (k1_funct_1('#skF_7', B_6)!='#skF_8' | ~r2_hidden(B_6, '#skF_4') | ~m1_subset_1(B_6, '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_8, c_124])).
% 7.86/2.70  tff(c_222, plain, (![B_178]: (k1_funct_1('#skF_7', B_178)!='#skF_8' | ~r2_hidden(B_178, '#skF_4') | ~m1_subset_1(B_178, '#skF_6'))), inference(splitLeft, [status(thm)], [c_133])).
% 7.86/2.70  tff(c_230, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_4'))!='#skF_8' | ~m1_subset_1('#skF_1'('#skF_4'), '#skF_6') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_222])).
% 7.86/2.70  tff(c_236, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_4'))!='#skF_8' | ~m1_subset_1('#skF_1'('#skF_4'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_183, c_230])).
% 7.86/2.70  tff(c_237, plain, (~m1_subset_1('#skF_1'('#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_236])).
% 7.86/2.70  tff(c_241, plain, (~v1_xboole_0('#skF_1'('#skF_4')) | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_10, c_237])).
% 7.86/2.70  tff(c_242, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_241])).
% 7.86/2.70  tff(c_433, plain, (![A_218, B_219, C_220, D_221]: (k7_relset_1(A_218, B_219, C_220, D_221)=k9_relat_1(C_220, D_221) | ~m1_subset_1(C_220, k1_zfmisc_1(k2_zfmisc_1(A_218, B_219))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.86/2.70  tff(c_454, plain, (![D_221]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_221)=k9_relat_1('#skF_7', D_221))), inference(resolution, [status(thm)], [c_54, c_433])).
% 7.86/2.70  tff(c_52, plain, (r2_hidden('#skF_8', k7_relset_1('#skF_4', '#skF_5', '#skF_7', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.86/2.70  tff(c_457, plain, (r2_hidden('#skF_8', k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_454, c_52])).
% 7.86/2.70  tff(c_458, plain, (![D_222]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_222)=k9_relat_1('#skF_7', D_222))), inference(resolution, [status(thm)], [c_54, c_433])).
% 7.86/2.70  tff(c_38, plain, (![A_32, B_33, C_34, D_35]: (m1_subset_1(k7_relset_1(A_32, B_33, C_34, D_35), k1_zfmisc_1(B_33)) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.86/2.70  tff(c_464, plain, (![D_222]: (m1_subset_1(k9_relat_1('#skF_7', D_222), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_458, c_38])).
% 7.86/2.70  tff(c_570, plain, (![D_226]: (m1_subset_1(k9_relat_1('#skF_7', D_226), k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_464])).
% 7.86/2.70  tff(c_16, plain, (![A_9, C_11, B_10]: (m1_subset_1(A_9, C_11) | ~m1_subset_1(B_10, k1_zfmisc_1(C_11)) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.86/2.70  tff(c_588, plain, (![A_227, D_228]: (m1_subset_1(A_227, '#skF_5') | ~r2_hidden(A_227, k9_relat_1('#skF_7', D_228)))), inference(resolution, [status(thm)], [c_570, c_16])).
% 7.86/2.70  tff(c_608, plain, (m1_subset_1('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_457, c_588])).
% 7.86/2.70  tff(c_135, plain, (![C_157, B_158, A_159]: (v1_xboole_0(C_157) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(B_158, A_159))) | ~v1_xboole_0(A_159))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.86/2.70  tff(c_151, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_135])).
% 7.86/2.70  tff(c_152, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_151])).
% 7.86/2.70  tff(c_1056, plain, (![C_282, E_281, D_283, A_280, B_284]: (m1_subset_1('#skF_3'(A_280, E_281, C_282, D_283, B_284), C_282) | ~r2_hidden(E_281, k7_relset_1(C_282, A_280, D_283, B_284)) | ~m1_subset_1(E_281, A_280) | ~m1_subset_1(D_283, k1_zfmisc_1(k2_zfmisc_1(C_282, A_280))) | v1_xboole_0(C_282) | v1_xboole_0(B_284) | v1_xboole_0(A_280))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.86/2.70  tff(c_1064, plain, (![E_281, D_221]: (m1_subset_1('#skF_3'('#skF_5', E_281, '#skF_4', '#skF_7', D_221), '#skF_4') | ~r2_hidden(E_281, k9_relat_1('#skF_7', D_221)) | ~m1_subset_1(E_281, '#skF_5') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | v1_xboole_0('#skF_4') | v1_xboole_0(D_221) | v1_xboole_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_454, c_1056])).
% 7.86/2.70  tff(c_1077, plain, (![E_281, D_221]: (m1_subset_1('#skF_3'('#skF_5', E_281, '#skF_4', '#skF_7', D_221), '#skF_4') | ~r2_hidden(E_281, k9_relat_1('#skF_7', D_221)) | ~m1_subset_1(E_281, '#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0(D_221) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1064])).
% 7.86/2.70  tff(c_1971, plain, (![E_373, D_374]: (m1_subset_1('#skF_3'('#skF_5', E_373, '#skF_4', '#skF_7', D_374), '#skF_4') | ~r2_hidden(E_373, k9_relat_1('#skF_7', D_374)) | ~m1_subset_1(E_373, '#skF_5') | v1_xboole_0(D_374))), inference(negUnitSimplification, [status(thm)], [c_152, c_183, c_1077])).
% 7.86/2.70  tff(c_1990, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_4', '#skF_7', '#skF_6'), '#skF_4') | ~m1_subset_1('#skF_8', '#skF_5') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_457, c_1971])).
% 7.86/2.70  tff(c_2016, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_4', '#skF_7', '#skF_6'), '#skF_4') | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_608, c_1990])).
% 7.86/2.70  tff(c_2017, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_4', '#skF_7', '#skF_6'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_242, c_2016])).
% 7.86/2.70  tff(c_935, plain, (![B_261, D_260, A_257, C_259, E_258]: (r2_hidden('#skF_3'(A_257, E_258, C_259, D_260, B_261), B_261) | ~r2_hidden(E_258, k7_relset_1(C_259, A_257, D_260, B_261)) | ~m1_subset_1(E_258, A_257) | ~m1_subset_1(D_260, k1_zfmisc_1(k2_zfmisc_1(C_259, A_257))) | v1_xboole_0(C_259) | v1_xboole_0(B_261) | v1_xboole_0(A_257))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.86/2.70  tff(c_949, plain, (![E_258, B_261]: (r2_hidden('#skF_3'('#skF_5', E_258, '#skF_4', '#skF_7', B_261), B_261) | ~r2_hidden(E_258, k7_relset_1('#skF_4', '#skF_5', '#skF_7', B_261)) | ~m1_subset_1(E_258, '#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0(B_261) | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_935])).
% 7.86/2.70  tff(c_957, plain, (![E_258, B_261]: (r2_hidden('#skF_3'('#skF_5', E_258, '#skF_4', '#skF_7', B_261), B_261) | ~r2_hidden(E_258, k9_relat_1('#skF_7', B_261)) | ~m1_subset_1(E_258, '#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0(B_261) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_454, c_949])).
% 7.86/2.70  tff(c_1119, plain, (![E_295, B_296]: (r2_hidden('#skF_3'('#skF_5', E_295, '#skF_4', '#skF_7', B_296), B_296) | ~r2_hidden(E_295, k9_relat_1('#skF_7', B_296)) | ~m1_subset_1(E_295, '#skF_5') | v1_xboole_0(B_296))), inference(negUnitSimplification, [status(thm)], [c_152, c_183, c_957])).
% 7.86/2.70  tff(c_14, plain, (![A_7, B_8]: (m1_subset_1(A_7, B_8) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.86/2.70  tff(c_2439, plain, (![E_440, B_441]: (m1_subset_1('#skF_3'('#skF_5', E_440, '#skF_4', '#skF_7', B_441), B_441) | ~r2_hidden(E_440, k9_relat_1('#skF_7', B_441)) | ~m1_subset_1(E_440, '#skF_5') | v1_xboole_0(B_441))), inference(resolution, [status(thm)], [c_1119, c_14])).
% 7.86/2.70  tff(c_2453, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_4', '#skF_7', '#skF_6'), '#skF_6') | ~m1_subset_1('#skF_8', '#skF_5') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_457, c_2439])).
% 7.86/2.70  tff(c_2475, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_4', '#skF_7', '#skF_6'), '#skF_6') | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_608, c_2453])).
% 7.86/2.70  tff(c_2476, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_4', '#skF_7', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_242, c_2475])).
% 7.86/2.70  tff(c_226, plain, (![B_6]: (k1_funct_1('#skF_7', B_6)!='#skF_8' | ~m1_subset_1(B_6, '#skF_6') | ~m1_subset_1(B_6, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_8, c_222])).
% 7.86/2.70  tff(c_233, plain, (![B_6]: (k1_funct_1('#skF_7', B_6)!='#skF_8' | ~m1_subset_1(B_6, '#skF_6') | ~m1_subset_1(B_6, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_183, c_226])).
% 7.86/2.70  tff(c_2506, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_5', '#skF_8', '#skF_4', '#skF_7', '#skF_6'))!='#skF_8' | ~m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_4', '#skF_7', '#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_2476, c_233])).
% 7.86/2.70  tff(c_2512, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_5', '#skF_8', '#skF_4', '#skF_7', '#skF_6'))!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2017, c_2506])).
% 7.86/2.70  tff(c_58, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.86/2.70  tff(c_1372, plain, (![C_312, D_313, A_310, B_314, E_311]: (r2_hidden(k4_tarski('#skF_3'(A_310, E_311, C_312, D_313, B_314), E_311), D_313) | ~r2_hidden(E_311, k7_relset_1(C_312, A_310, D_313, B_314)) | ~m1_subset_1(E_311, A_310) | ~m1_subset_1(D_313, k1_zfmisc_1(k2_zfmisc_1(C_312, A_310))) | v1_xboole_0(C_312) | v1_xboole_0(B_314) | v1_xboole_0(A_310))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.86/2.70  tff(c_28, plain, (![C_20, A_18, B_19]: (k1_funct_1(C_20, A_18)=B_19 | ~r2_hidden(k4_tarski(A_18, B_19), C_20) | ~v1_funct_1(C_20) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.86/2.70  tff(c_5248, plain, (![E_610, B_609, C_607, A_608, D_606]: (k1_funct_1(D_606, '#skF_3'(A_608, E_610, C_607, D_606, B_609))=E_610 | ~v1_funct_1(D_606) | ~v1_relat_1(D_606) | ~r2_hidden(E_610, k7_relset_1(C_607, A_608, D_606, B_609)) | ~m1_subset_1(E_610, A_608) | ~m1_subset_1(D_606, k1_zfmisc_1(k2_zfmisc_1(C_607, A_608))) | v1_xboole_0(C_607) | v1_xboole_0(B_609) | v1_xboole_0(A_608))), inference(resolution, [status(thm)], [c_1372, c_28])).
% 7.86/2.70  tff(c_5264, plain, (![E_610, D_221]: (k1_funct_1('#skF_7', '#skF_3'('#skF_5', E_610, '#skF_4', '#skF_7', D_221))=E_610 | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(E_610, k9_relat_1('#skF_7', D_221)) | ~m1_subset_1(E_610, '#skF_5') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | v1_xboole_0('#skF_4') | v1_xboole_0(D_221) | v1_xboole_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_454, c_5248])).
% 7.86/2.70  tff(c_5281, plain, (![E_610, D_221]: (k1_funct_1('#skF_7', '#skF_3'('#skF_5', E_610, '#skF_4', '#skF_7', D_221))=E_610 | ~r2_hidden(E_610, k9_relat_1('#skF_7', D_221)) | ~m1_subset_1(E_610, '#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0(D_221) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_112, c_58, c_5264])).
% 7.86/2.70  tff(c_5288, plain, (![E_611, D_612]: (k1_funct_1('#skF_7', '#skF_3'('#skF_5', E_611, '#skF_4', '#skF_7', D_612))=E_611 | ~r2_hidden(E_611, k9_relat_1('#skF_7', D_612)) | ~m1_subset_1(E_611, '#skF_5') | v1_xboole_0(D_612))), inference(negUnitSimplification, [status(thm)], [c_152, c_183, c_5281])).
% 7.86/2.70  tff(c_5325, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_5', '#skF_8', '#skF_4', '#skF_7', '#skF_6'))='#skF_8' | ~m1_subset_1('#skF_8', '#skF_5') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_457, c_5288])).
% 7.86/2.70  tff(c_5368, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_5', '#skF_8', '#skF_4', '#skF_7', '#skF_6'))='#skF_8' | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_608, c_5325])).
% 7.86/2.70  tff(c_5370, plain, $false, inference(negUnitSimplification, [status(thm)], [c_242, c_2512, c_5368])).
% 7.86/2.70  tff(c_5372, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_241])).
% 7.86/2.70  tff(c_5398, plain, (![A_615, B_616, C_617]: (r2_hidden('#skF_2'(A_615, B_616, C_617), B_616) | ~r2_hidden(A_615, k9_relat_1(C_617, B_616)) | ~v1_relat_1(C_617))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.86/2.70  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.86/2.70  tff(c_5422, plain, (![B_618, A_619, C_620]: (~v1_xboole_0(B_618) | ~r2_hidden(A_619, k9_relat_1(C_620, B_618)) | ~v1_relat_1(C_620))), inference(resolution, [status(thm)], [c_5398, c_2])).
% 7.86/2.70  tff(c_5437, plain, (![B_618, C_620]: (~v1_xboole_0(B_618) | ~v1_relat_1(C_620) | v1_xboole_0(k9_relat_1(C_620, B_618)))), inference(resolution, [status(thm)], [c_4, c_5422])).
% 7.86/2.70  tff(c_5548, plain, (![A_646, B_647, C_648, D_649]: (k7_relset_1(A_646, B_647, C_648, D_649)=k9_relat_1(C_648, D_649) | ~m1_subset_1(C_648, k1_zfmisc_1(k2_zfmisc_1(A_646, B_647))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.86/2.70  tff(c_5569, plain, (![D_649]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_649)=k9_relat_1('#skF_7', D_649))), inference(resolution, [status(thm)], [c_54, c_5548])).
% 7.86/2.70  tff(c_92, plain, (~v1_xboole_0(k7_relset_1('#skF_4', '#skF_5', '#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_52, c_2])).
% 7.86/2.70  tff(c_5571, plain, (~v1_xboole_0(k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_5569, c_92])).
% 7.86/2.70  tff(c_5589, plain, (~v1_xboole_0('#skF_6') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_5437, c_5571])).
% 7.86/2.70  tff(c_5593, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_5372, c_5589])).
% 7.86/2.70  tff(c_5594, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_133])).
% 7.86/2.70  tff(c_5595, plain, (![A_651, B_652, C_653]: (r2_hidden('#skF_2'(A_651, B_652, C_653), B_652) | ~r2_hidden(A_651, k9_relat_1(C_653, B_652)) | ~v1_relat_1(C_653))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.86/2.70  tff(c_5614, plain, (![B_654, A_655, C_656]: (~v1_xboole_0(B_654) | ~r2_hidden(A_655, k9_relat_1(C_656, B_654)) | ~v1_relat_1(C_656))), inference(resolution, [status(thm)], [c_5595, c_2])).
% 7.86/2.70  tff(c_5629, plain, (![B_654, C_656]: (~v1_xboole_0(B_654) | ~v1_relat_1(C_656) | v1_xboole_0(k9_relat_1(C_656, B_654)))), inference(resolution, [status(thm)], [c_4, c_5614])).
% 7.86/2.70  tff(c_5747, plain, (![A_687, B_688, C_689, D_690]: (k7_relset_1(A_687, B_688, C_689, D_690)=k9_relat_1(C_689, D_690) | ~m1_subset_1(C_689, k1_zfmisc_1(k2_zfmisc_1(A_687, B_688))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.86/2.70  tff(c_5768, plain, (![D_690]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_690)=k9_relat_1('#skF_7', D_690))), inference(resolution, [status(thm)], [c_54, c_5747])).
% 7.86/2.70  tff(c_5770, plain, (~v1_xboole_0(k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_5768, c_92])).
% 7.86/2.70  tff(c_5837, plain, (~v1_xboole_0('#skF_6') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_5629, c_5770])).
% 7.86/2.70  tff(c_5844, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_5594, c_5837])).
% 7.86/2.70  tff(c_5845, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_182])).
% 7.86/2.70  tff(c_6049, plain, (![A_742, B_743, C_744, D_745]: (k7_relset_1(A_742, B_743, C_744, D_745)=k9_relat_1(C_744, D_745) | ~m1_subset_1(C_744, k1_zfmisc_1(k2_zfmisc_1(A_742, B_743))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.86/2.70  tff(c_6070, plain, (![D_745]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_745)=k9_relat_1('#skF_7', D_745))), inference(resolution, [status(thm)], [c_54, c_6049])).
% 7.86/2.70  tff(c_6124, plain, (r2_hidden('#skF_8', k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6070, c_52])).
% 7.86/2.70  tff(c_6071, plain, (![A_746, B_747, C_748]: (r2_hidden(k4_tarski('#skF_2'(A_746, B_747, C_748), A_746), C_748) | ~r2_hidden(A_746, k9_relat_1(C_748, B_747)) | ~v1_relat_1(C_748))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.86/2.70  tff(c_6281, plain, (![C_755, A_756, B_757]: (~v1_xboole_0(C_755) | ~r2_hidden(A_756, k9_relat_1(C_755, B_757)) | ~v1_relat_1(C_755))), inference(resolution, [status(thm)], [c_6071, c_2])).
% 7.86/2.70  tff(c_6288, plain, (~v1_xboole_0('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_6124, c_6281])).
% 7.86/2.70  tff(c_6309, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_5845, c_6288])).
% 7.86/2.70  tff(c_6310, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_151])).
% 7.86/2.70  tff(c_6553, plain, (![A_810, B_811, C_812, D_813]: (k7_relset_1(A_810, B_811, C_812, D_813)=k9_relat_1(C_812, D_813) | ~m1_subset_1(C_812, k1_zfmisc_1(k2_zfmisc_1(A_810, B_811))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.86/2.70  tff(c_6570, plain, (![D_813]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_813)=k9_relat_1('#skF_7', D_813))), inference(resolution, [status(thm)], [c_54, c_6553])).
% 7.86/2.70  tff(c_6573, plain, (r2_hidden('#skF_8', k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6570, c_52])).
% 7.86/2.70  tff(c_6700, plain, (![A_822, B_823, C_824]: (r2_hidden(k4_tarski('#skF_2'(A_822, B_823, C_824), A_822), C_824) | ~r2_hidden(A_822, k9_relat_1(C_824, B_823)) | ~v1_relat_1(C_824))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.86/2.70  tff(c_6756, plain, (![C_825, A_826, B_827]: (~v1_xboole_0(C_825) | ~r2_hidden(A_826, k9_relat_1(C_825, B_827)) | ~v1_relat_1(C_825))), inference(resolution, [status(thm)], [c_6700, c_2])).
% 7.86/2.70  tff(c_6763, plain, (~v1_xboole_0('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_6573, c_6756])).
% 7.86/2.70  tff(c_6780, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_6310, c_6763])).
% 7.86/2.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.86/2.70  
% 7.86/2.70  Inference rules
% 7.86/2.70  ----------------------
% 7.86/2.70  #Ref     : 0
% 7.86/2.70  #Sup     : 1341
% 7.86/2.70  #Fact    : 0
% 7.86/2.70  #Define  : 0
% 7.86/2.70  #Split   : 36
% 7.86/2.70  #Chain   : 0
% 7.86/2.70  #Close   : 0
% 7.86/2.70  
% 7.86/2.70  Ordering : KBO
% 7.86/2.70  
% 7.86/2.70  Simplification rules
% 7.86/2.70  ----------------------
% 7.86/2.70  #Subsume      : 296
% 7.86/2.70  #Demod        : 368
% 7.86/2.70  #Tautology    : 108
% 7.86/2.70  #SimpNegUnit  : 155
% 7.86/2.70  #BackRed      : 17
% 7.86/2.70  
% 7.86/2.70  #Partial instantiations: 0
% 7.86/2.70  #Strategies tried      : 1
% 7.86/2.70  
% 7.86/2.70  Timing (in seconds)
% 7.86/2.70  ----------------------
% 7.86/2.71  Preprocessing        : 0.35
% 7.86/2.71  Parsing              : 0.18
% 7.86/2.71  CNF conversion       : 0.03
% 7.86/2.71  Main loop            : 1.58
% 7.86/2.71  Inferencing          : 0.52
% 7.86/2.71  Reduction            : 0.42
% 7.86/2.71  Demodulation         : 0.27
% 7.86/2.71  BG Simplification    : 0.05
% 7.86/2.71  Subsumption          : 0.46
% 7.86/2.71  Abstraction          : 0.07
% 7.86/2.71  MUC search           : 0.00
% 7.86/2.71  Cooper               : 0.00
% 7.86/2.71  Total                : 1.98
% 7.86/2.71  Index Insertion      : 0.00
% 7.86/2.71  Index Deletion       : 0.00
% 7.86/2.71  Index Matching       : 0.00
% 7.86/2.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
