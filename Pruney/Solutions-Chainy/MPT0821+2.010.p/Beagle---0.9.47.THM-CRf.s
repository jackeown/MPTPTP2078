%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:09 EST 2020

% Result     : Theorem 7.52s
% Output     : CNFRefutation 7.77s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 218 expanded)
%              Number of leaves         :   27 (  85 expanded)
%              Depth                    :   13
%              Number of atoms          :  131 ( 454 expanded)
%              Number of equality atoms :   26 ( 106 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_9 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
        <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,(
    ! [A_50,B_51] :
      ( ~ r2_hidden('#skF_1'(A_50,B_51),B_51)
      | r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_61,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_56])).

tff(c_38,plain,
    ( k1_relset_1('#skF_7','#skF_6','#skF_8') != '#skF_7'
    | r2_hidden('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_63,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_44,plain,(
    ! [D_40] :
      ( r2_hidden(k4_tarski(D_40,'#skF_9'(D_40)),'#skF_8')
      | ~ r2_hidden(D_40,'#skF_7')
      | k1_relset_1('#skF_7','#skF_6','#skF_8') = '#skF_7' ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_96,plain,(
    ! [D_73] :
      ( r2_hidden(k4_tarski(D_73,'#skF_9'(D_73)),'#skF_8')
      | ~ r2_hidden(D_73,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_44])).

tff(c_20,plain,(
    ! [C_27,A_12,D_30] :
      ( r2_hidden(C_27,k1_relat_1(A_12))
      | ~ r2_hidden(k4_tarski(C_27,D_30),A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_104,plain,(
    ! [D_74] :
      ( r2_hidden(D_74,k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_74,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_96,c_20])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_119,plain,(
    ! [A_75] :
      ( r1_tarski(A_75,k1_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_75,k1_relat_1('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_104,c_4])).

tff(c_129,plain,(
    r1_tarski('#skF_7',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6,c_119])).

tff(c_32,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_135,plain,(
    ! [A_76,B_77,C_78] :
      ( k1_relset_1(A_76,B_77,C_78) = k1_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_144,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_32,c_135])).

tff(c_148,plain,(
    k1_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_63])).

tff(c_967,plain,(
    ! [A_165,B_166] :
      ( r2_hidden(k4_tarski('#skF_2'(A_165,B_166),'#skF_3'(A_165,B_166)),A_165)
      | r2_hidden('#skF_4'(A_165,B_166),B_166)
      | k1_relat_1(A_165) = B_166 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1006,plain,(
    ! [A_165,B_166] :
      ( r2_hidden('#skF_2'(A_165,B_166),k1_relat_1(A_165))
      | r2_hidden('#skF_4'(A_165,B_166),B_166)
      | k1_relat_1(A_165) = B_166 ) ),
    inference(resolution,[status(thm)],[c_967,c_20])).

tff(c_46,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_54,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_32,c_46])).

tff(c_497,plain,(
    ! [C_129,A_130] :
      ( r2_hidden(k4_tarski(C_129,'#skF_5'(A_130,k1_relat_1(A_130),C_129)),A_130)
      | ~ r2_hidden(C_129,k1_relat_1(A_130)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1881,plain,(
    ! [C_217,A_218,B_219] :
      ( r2_hidden(k4_tarski(C_217,'#skF_5'(A_218,k1_relat_1(A_218),C_217)),B_219)
      | ~ r1_tarski(A_218,B_219)
      | ~ r2_hidden(C_217,k1_relat_1(A_218)) ) ),
    inference(resolution,[status(thm)],[c_497,c_2])).

tff(c_1940,plain,(
    ! [C_220,B_221,A_222] :
      ( r2_hidden(C_220,k1_relat_1(B_221))
      | ~ r1_tarski(A_222,B_221)
      | ~ r2_hidden(C_220,k1_relat_1(A_222)) ) ),
    inference(resolution,[status(thm)],[c_1881,c_20])).

tff(c_1971,plain,(
    ! [C_223] :
      ( r2_hidden(C_223,k1_relat_1(k2_zfmisc_1('#skF_7','#skF_6')))
      | ~ r2_hidden(C_223,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_54,c_1940])).

tff(c_12,plain,(
    ! [A_6,C_8,B_7,D_9] :
      ( r2_hidden(A_6,C_8)
      | ~ r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(C_8,D_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_521,plain,(
    ! [C_129,C_8,D_9] :
      ( r2_hidden(C_129,C_8)
      | ~ r2_hidden(C_129,k1_relat_1(k2_zfmisc_1(C_8,D_9))) ) ),
    inference(resolution,[status(thm)],[c_497,c_12])).

tff(c_2020,plain,(
    ! [C_224] :
      ( r2_hidden(C_224,'#skF_7')
      | ~ r2_hidden(C_224,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_1971,c_521])).

tff(c_3391,plain,(
    ! [B_276] :
      ( r2_hidden('#skF_2'('#skF_8',B_276),'#skF_7')
      | r2_hidden('#skF_4'('#skF_8',B_276),B_276)
      | k1_relat_1('#skF_8') = B_276 ) ),
    inference(resolution,[status(thm)],[c_1006,c_2020])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( ~ r2_hidden('#skF_2'(A_12,B_13),B_13)
      | r2_hidden('#skF_4'(A_12,B_13),B_13)
      | k1_relat_1(A_12) = B_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3404,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k1_relat_1('#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_3391,c_26])).

tff(c_3441,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_148,c_3404])).

tff(c_3465,plain,(
    ! [B_277] :
      ( r2_hidden('#skF_4'('#skF_8','#skF_7'),B_277)
      | ~ r1_tarski('#skF_7',B_277) ) ),
    inference(resolution,[status(thm)],[c_3441,c_2])).

tff(c_3601,plain,(
    ! [B_285,B_286] :
      ( r2_hidden('#skF_4'('#skF_8','#skF_7'),B_285)
      | ~ r1_tarski(B_286,B_285)
      | ~ r1_tarski('#skF_7',B_286) ) ),
    inference(resolution,[status(thm)],[c_3465,c_2])).

tff(c_3621,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),k1_relat_1('#skF_8'))
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_129,c_3601])).

tff(c_3643,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_7'),k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_3621])).

tff(c_18,plain,(
    ! [C_27,A_12] :
      ( r2_hidden(k4_tarski(C_27,'#skF_5'(A_12,k1_relat_1(A_12),C_27)),A_12)
      | ~ r2_hidden(C_27,k1_relat_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_95,plain,(
    ! [D_40] :
      ( r2_hidden(k4_tarski(D_40,'#skF_9'(D_40)),'#skF_8')
      | ~ r2_hidden(D_40,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_44])).

tff(c_1424,plain,(
    ! [A_191,B_192,D_193] :
      ( r2_hidden(k4_tarski('#skF_2'(A_191,B_192),'#skF_3'(A_191,B_192)),A_191)
      | ~ r2_hidden(k4_tarski('#skF_4'(A_191,B_192),D_193),A_191)
      | k1_relat_1(A_191) = B_192 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1553,plain,(
    ! [B_198] :
      ( r2_hidden(k4_tarski('#skF_2'('#skF_8',B_198),'#skF_3'('#skF_8',B_198)),'#skF_8')
      | k1_relat_1('#skF_8') = B_198
      | ~ r2_hidden('#skF_4'('#skF_8',B_198),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_95,c_1424])).

tff(c_5316,plain,(
    ! [B_347] :
      ( r2_hidden('#skF_2'('#skF_8',B_347),k1_relat_1('#skF_8'))
      | k1_relat_1('#skF_8') = B_347
      | ~ r2_hidden('#skF_4'('#skF_8',B_347),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1553,c_20])).

tff(c_2013,plain,(
    ! [C_223] :
      ( r2_hidden(C_223,'#skF_7')
      | ~ r2_hidden(C_223,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_1971,c_521])).

tff(c_7096,plain,(
    ! [B_410] :
      ( r2_hidden('#skF_2'('#skF_8',B_410),'#skF_7')
      | k1_relat_1('#skF_8') = B_410
      | ~ r2_hidden('#skF_4'('#skF_8',B_410),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_5316,c_2013])).

tff(c_22,plain,(
    ! [A_12,B_13,D_26] :
      ( ~ r2_hidden('#skF_2'(A_12,B_13),B_13)
      | ~ r2_hidden(k4_tarski('#skF_4'(A_12,B_13),D_26),A_12)
      | k1_relat_1(A_12) = B_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_7105,plain,(
    ! [D_26] :
      ( ~ r2_hidden(k4_tarski('#skF_4'('#skF_8','#skF_7'),D_26),'#skF_8')
      | k1_relat_1('#skF_8') = '#skF_7'
      | ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_7096,c_22])).

tff(c_7123,plain,(
    ! [D_26] :
      ( ~ r2_hidden(k4_tarski('#skF_4'('#skF_8','#skF_7'),D_26),'#skF_8')
      | k1_relat_1('#skF_8') = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3441,c_7105])).

tff(c_7131,plain,(
    ! [D_411] : ~ r2_hidden(k4_tarski('#skF_4'('#skF_8','#skF_7'),D_411),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_7123])).

tff(c_7139,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_18,c_7131])).

tff(c_7152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3643,c_7139])).

tff(c_7153,plain,(
    r2_hidden('#skF_10','#skF_7') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_7154,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_7193,plain,(
    ! [A_433,B_434,C_435] :
      ( k1_relset_1(A_433,B_434,C_435) = k1_relat_1(C_435)
      | ~ m1_subset_1(C_435,k1_zfmisc_1(k2_zfmisc_1(A_433,B_434))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_7200,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_32,c_7193])).

tff(c_7203,plain,(
    k1_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7154,c_7200])).

tff(c_7230,plain,(
    ! [C_443,A_444] :
      ( r2_hidden(k4_tarski(C_443,'#skF_5'(A_444,k1_relat_1(A_444),C_443)),A_444)
      | ~ r2_hidden(C_443,k1_relat_1(A_444)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_34,plain,(
    ! [E_43] :
      ( k1_relset_1('#skF_7','#skF_6','#skF_8') != '#skF_7'
      | ~ r2_hidden(k4_tarski('#skF_10',E_43),'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_7179,plain,(
    ! [E_43] : ~ r2_hidden(k4_tarski('#skF_10',E_43),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7154,c_34])).

tff(c_7242,plain,(
    ~ r2_hidden('#skF_10',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_7230,c_7179])).

tff(c_7256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7153,c_7203,c_7242])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:52:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.52/2.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.77/2.59  
% 7.77/2.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.77/2.59  %$ r2_hidden > r1_tarski > m1_subset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_9 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 7.77/2.59  
% 7.77/2.59  %Foreground sorts:
% 7.77/2.59  
% 7.77/2.59  
% 7.77/2.59  %Background operators:
% 7.77/2.59  
% 7.77/2.59  
% 7.77/2.59  %Foreground operators:
% 7.77/2.59  tff('#skF_9', type, '#skF_9': $i > $i).
% 7.77/2.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.77/2.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.77/2.59  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.77/2.59  tff('#skF_7', type, '#skF_7': $i).
% 7.77/2.59  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.77/2.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.77/2.59  tff('#skF_10', type, '#skF_10': $i).
% 7.77/2.59  tff('#skF_6', type, '#skF_6': $i).
% 7.77/2.59  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 7.77/2.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.77/2.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.77/2.59  tff('#skF_8', type, '#skF_8': $i).
% 7.77/2.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.77/2.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.77/2.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.77/2.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.77/2.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.77/2.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.77/2.59  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.77/2.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.77/2.59  
% 7.77/2.61  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.77/2.61  tff(f_67, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 7.77/2.61  tff(f_50, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 7.77/2.61  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.77/2.61  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.77/2.61  tff(f_38, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 7.77/2.61  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.77/2.61  tff(c_56, plain, (![A_50, B_51]: (~r2_hidden('#skF_1'(A_50, B_51), B_51) | r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.77/2.61  tff(c_61, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_56])).
% 7.77/2.61  tff(c_38, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')!='#skF_7' | r2_hidden('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.77/2.61  tff(c_63, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')!='#skF_7'), inference(splitLeft, [status(thm)], [c_38])).
% 7.77/2.61  tff(c_44, plain, (![D_40]: (r2_hidden(k4_tarski(D_40, '#skF_9'(D_40)), '#skF_8') | ~r2_hidden(D_40, '#skF_7') | k1_relset_1('#skF_7', '#skF_6', '#skF_8')='#skF_7')), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.77/2.61  tff(c_96, plain, (![D_73]: (r2_hidden(k4_tarski(D_73, '#skF_9'(D_73)), '#skF_8') | ~r2_hidden(D_73, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_63, c_44])).
% 7.77/2.61  tff(c_20, plain, (![C_27, A_12, D_30]: (r2_hidden(C_27, k1_relat_1(A_12)) | ~r2_hidden(k4_tarski(C_27, D_30), A_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.77/2.61  tff(c_104, plain, (![D_74]: (r2_hidden(D_74, k1_relat_1('#skF_8')) | ~r2_hidden(D_74, '#skF_7'))), inference(resolution, [status(thm)], [c_96, c_20])).
% 7.77/2.61  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.77/2.61  tff(c_119, plain, (![A_75]: (r1_tarski(A_75, k1_relat_1('#skF_8')) | ~r2_hidden('#skF_1'(A_75, k1_relat_1('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_104, c_4])).
% 7.77/2.61  tff(c_129, plain, (r1_tarski('#skF_7', k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6, c_119])).
% 7.77/2.61  tff(c_32, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.77/2.61  tff(c_135, plain, (![A_76, B_77, C_78]: (k1_relset_1(A_76, B_77, C_78)=k1_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.77/2.61  tff(c_144, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_32, c_135])).
% 7.77/2.61  tff(c_148, plain, (k1_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_144, c_63])).
% 7.77/2.61  tff(c_967, plain, (![A_165, B_166]: (r2_hidden(k4_tarski('#skF_2'(A_165, B_166), '#skF_3'(A_165, B_166)), A_165) | r2_hidden('#skF_4'(A_165, B_166), B_166) | k1_relat_1(A_165)=B_166)), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.77/2.61  tff(c_1006, plain, (![A_165, B_166]: (r2_hidden('#skF_2'(A_165, B_166), k1_relat_1(A_165)) | r2_hidden('#skF_4'(A_165, B_166), B_166) | k1_relat_1(A_165)=B_166)), inference(resolution, [status(thm)], [c_967, c_20])).
% 7.77/2.61  tff(c_46, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~m1_subset_1(A_46, k1_zfmisc_1(B_47)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.77/2.61  tff(c_54, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_32, c_46])).
% 7.77/2.61  tff(c_497, plain, (![C_129, A_130]: (r2_hidden(k4_tarski(C_129, '#skF_5'(A_130, k1_relat_1(A_130), C_129)), A_130) | ~r2_hidden(C_129, k1_relat_1(A_130)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.77/2.61  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.77/2.61  tff(c_1881, plain, (![C_217, A_218, B_219]: (r2_hidden(k4_tarski(C_217, '#skF_5'(A_218, k1_relat_1(A_218), C_217)), B_219) | ~r1_tarski(A_218, B_219) | ~r2_hidden(C_217, k1_relat_1(A_218)))), inference(resolution, [status(thm)], [c_497, c_2])).
% 7.77/2.61  tff(c_1940, plain, (![C_220, B_221, A_222]: (r2_hidden(C_220, k1_relat_1(B_221)) | ~r1_tarski(A_222, B_221) | ~r2_hidden(C_220, k1_relat_1(A_222)))), inference(resolution, [status(thm)], [c_1881, c_20])).
% 7.77/2.61  tff(c_1971, plain, (![C_223]: (r2_hidden(C_223, k1_relat_1(k2_zfmisc_1('#skF_7', '#skF_6'))) | ~r2_hidden(C_223, k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_54, c_1940])).
% 7.77/2.61  tff(c_12, plain, (![A_6, C_8, B_7, D_9]: (r2_hidden(A_6, C_8) | ~r2_hidden(k4_tarski(A_6, B_7), k2_zfmisc_1(C_8, D_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.77/2.61  tff(c_521, plain, (![C_129, C_8, D_9]: (r2_hidden(C_129, C_8) | ~r2_hidden(C_129, k1_relat_1(k2_zfmisc_1(C_8, D_9))))), inference(resolution, [status(thm)], [c_497, c_12])).
% 7.77/2.61  tff(c_2020, plain, (![C_224]: (r2_hidden(C_224, '#skF_7') | ~r2_hidden(C_224, k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_1971, c_521])).
% 7.77/2.61  tff(c_3391, plain, (![B_276]: (r2_hidden('#skF_2'('#skF_8', B_276), '#skF_7') | r2_hidden('#skF_4'('#skF_8', B_276), B_276) | k1_relat_1('#skF_8')=B_276)), inference(resolution, [status(thm)], [c_1006, c_2020])).
% 7.77/2.61  tff(c_26, plain, (![A_12, B_13]: (~r2_hidden('#skF_2'(A_12, B_13), B_13) | r2_hidden('#skF_4'(A_12, B_13), B_13) | k1_relat_1(A_12)=B_13)), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.77/2.61  tff(c_3404, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k1_relat_1('#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_3391, c_26])).
% 7.77/2.61  tff(c_3441, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_148, c_148, c_3404])).
% 7.77/2.61  tff(c_3465, plain, (![B_277]: (r2_hidden('#skF_4'('#skF_8', '#skF_7'), B_277) | ~r1_tarski('#skF_7', B_277))), inference(resolution, [status(thm)], [c_3441, c_2])).
% 7.77/2.61  tff(c_3601, plain, (![B_285, B_286]: (r2_hidden('#skF_4'('#skF_8', '#skF_7'), B_285) | ~r1_tarski(B_286, B_285) | ~r1_tarski('#skF_7', B_286))), inference(resolution, [status(thm)], [c_3465, c_2])).
% 7.77/2.61  tff(c_3621, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), k1_relat_1('#skF_8')) | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_129, c_3601])).
% 7.77/2.61  tff(c_3643, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_3621])).
% 7.77/2.61  tff(c_18, plain, (![C_27, A_12]: (r2_hidden(k4_tarski(C_27, '#skF_5'(A_12, k1_relat_1(A_12), C_27)), A_12) | ~r2_hidden(C_27, k1_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.77/2.61  tff(c_95, plain, (![D_40]: (r2_hidden(k4_tarski(D_40, '#skF_9'(D_40)), '#skF_8') | ~r2_hidden(D_40, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_63, c_44])).
% 7.77/2.61  tff(c_1424, plain, (![A_191, B_192, D_193]: (r2_hidden(k4_tarski('#skF_2'(A_191, B_192), '#skF_3'(A_191, B_192)), A_191) | ~r2_hidden(k4_tarski('#skF_4'(A_191, B_192), D_193), A_191) | k1_relat_1(A_191)=B_192)), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.77/2.61  tff(c_1553, plain, (![B_198]: (r2_hidden(k4_tarski('#skF_2'('#skF_8', B_198), '#skF_3'('#skF_8', B_198)), '#skF_8') | k1_relat_1('#skF_8')=B_198 | ~r2_hidden('#skF_4'('#skF_8', B_198), '#skF_7'))), inference(resolution, [status(thm)], [c_95, c_1424])).
% 7.77/2.61  tff(c_5316, plain, (![B_347]: (r2_hidden('#skF_2'('#skF_8', B_347), k1_relat_1('#skF_8')) | k1_relat_1('#skF_8')=B_347 | ~r2_hidden('#skF_4'('#skF_8', B_347), '#skF_7'))), inference(resolution, [status(thm)], [c_1553, c_20])).
% 7.77/2.61  tff(c_2013, plain, (![C_223]: (r2_hidden(C_223, '#skF_7') | ~r2_hidden(C_223, k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_1971, c_521])).
% 7.77/2.61  tff(c_7096, plain, (![B_410]: (r2_hidden('#skF_2'('#skF_8', B_410), '#skF_7') | k1_relat_1('#skF_8')=B_410 | ~r2_hidden('#skF_4'('#skF_8', B_410), '#skF_7'))), inference(resolution, [status(thm)], [c_5316, c_2013])).
% 7.77/2.61  tff(c_22, plain, (![A_12, B_13, D_26]: (~r2_hidden('#skF_2'(A_12, B_13), B_13) | ~r2_hidden(k4_tarski('#skF_4'(A_12, B_13), D_26), A_12) | k1_relat_1(A_12)=B_13)), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.77/2.61  tff(c_7105, plain, (![D_26]: (~r2_hidden(k4_tarski('#skF_4'('#skF_8', '#skF_7'), D_26), '#skF_8') | k1_relat_1('#skF_8')='#skF_7' | ~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7'))), inference(resolution, [status(thm)], [c_7096, c_22])).
% 7.77/2.61  tff(c_7123, plain, (![D_26]: (~r2_hidden(k4_tarski('#skF_4'('#skF_8', '#skF_7'), D_26), '#skF_8') | k1_relat_1('#skF_8')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3441, c_7105])).
% 7.77/2.61  tff(c_7131, plain, (![D_411]: (~r2_hidden(k4_tarski('#skF_4'('#skF_8', '#skF_7'), D_411), '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_148, c_7123])).
% 7.77/2.61  tff(c_7139, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_7'), k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_18, c_7131])).
% 7.77/2.61  tff(c_7152, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3643, c_7139])).
% 7.77/2.61  tff(c_7153, plain, (r2_hidden('#skF_10', '#skF_7')), inference(splitRight, [status(thm)], [c_38])).
% 7.77/2.61  tff(c_7154, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')='#skF_7'), inference(splitRight, [status(thm)], [c_38])).
% 7.77/2.61  tff(c_7193, plain, (![A_433, B_434, C_435]: (k1_relset_1(A_433, B_434, C_435)=k1_relat_1(C_435) | ~m1_subset_1(C_435, k1_zfmisc_1(k2_zfmisc_1(A_433, B_434))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.77/2.61  tff(c_7200, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_32, c_7193])).
% 7.77/2.61  tff(c_7203, plain, (k1_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_7154, c_7200])).
% 7.77/2.61  tff(c_7230, plain, (![C_443, A_444]: (r2_hidden(k4_tarski(C_443, '#skF_5'(A_444, k1_relat_1(A_444), C_443)), A_444) | ~r2_hidden(C_443, k1_relat_1(A_444)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.77/2.61  tff(c_34, plain, (![E_43]: (k1_relset_1('#skF_7', '#skF_6', '#skF_8')!='#skF_7' | ~r2_hidden(k4_tarski('#skF_10', E_43), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.77/2.61  tff(c_7179, plain, (![E_43]: (~r2_hidden(k4_tarski('#skF_10', E_43), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_7154, c_34])).
% 7.77/2.61  tff(c_7242, plain, (~r2_hidden('#skF_10', k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_7230, c_7179])).
% 7.77/2.61  tff(c_7256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7153, c_7203, c_7242])).
% 7.77/2.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.77/2.61  
% 7.77/2.61  Inference rules
% 7.77/2.61  ----------------------
% 7.77/2.61  #Ref     : 0
% 7.77/2.61  #Sup     : 1739
% 7.77/2.61  #Fact    : 0
% 7.77/2.61  #Define  : 0
% 7.77/2.61  #Split   : 28
% 7.77/2.61  #Chain   : 0
% 7.77/2.61  #Close   : 0
% 7.77/2.61  
% 7.77/2.61  Ordering : KBO
% 7.77/2.61  
% 7.77/2.61  Simplification rules
% 7.77/2.61  ----------------------
% 7.77/2.61  #Subsume      : 415
% 7.77/2.61  #Demod        : 188
% 7.77/2.61  #Tautology    : 161
% 7.77/2.61  #SimpNegUnit  : 13
% 7.77/2.61  #BackRed      : 9
% 7.77/2.61  
% 7.77/2.61  #Partial instantiations: 0
% 7.77/2.61  #Strategies tried      : 1
% 7.77/2.61  
% 7.77/2.61  Timing (in seconds)
% 7.77/2.61  ----------------------
% 7.77/2.61  Preprocessing        : 0.30
% 7.77/2.61  Parsing              : 0.15
% 7.77/2.61  CNF conversion       : 0.03
% 7.77/2.61  Main loop            : 1.64
% 7.77/2.61  Inferencing          : 0.44
% 7.77/2.61  Reduction            : 0.40
% 7.77/2.61  Demodulation         : 0.25
% 7.77/2.61  BG Simplification    : 0.06
% 7.77/2.61  Subsumption          : 0.60
% 7.77/2.61  Abstraction          : 0.07
% 7.77/2.61  MUC search           : 0.00
% 7.77/2.61  Cooper               : 0.00
% 7.77/2.61  Total                : 1.97
% 7.77/2.61  Index Insertion      : 0.00
% 7.77/2.61  Index Deletion       : 0.00
% 7.77/2.61  Index Matching       : 0.00
% 7.77/2.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
