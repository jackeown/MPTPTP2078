%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:04 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 222 expanded)
%              Number of leaves         :   36 (  92 expanded)
%              Depth                    :    8
%              Number of atoms          :  140 ( 518 expanded)
%              Number of equality atoms :   21 (  60 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ! [D] :
                    ( m1_subset_1(D,A)
                   => ( r2_hidden(D,k1_relset_1(A,B,C))
                    <=> ? [E] :
                          ( m1_subset_1(E,B)
                          & r2_hidden(k4_tarski(D,E),C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_38,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_556,plain,(
    ! [A_203,B_204,C_205] :
      ( k1_relset_1(A_203,B_204,C_205) = k1_relat_1(C_205)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_203,B_204))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_560,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_556])).

tff(c_158,plain,(
    ! [A_113,B_114,C_115] :
      ( k1_relset_1(A_113,B_114,C_115) = k1_relat_1(C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_162,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_158])).

tff(c_54,plain,
    ( r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8'))
    | m1_subset_1('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_64,plain,(
    m1_subset_1('#skF_10','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_50,plain,
    ( r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8'))
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_65,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_70,plain,(
    ! [C_91,A_92,D_93] :
      ( r2_hidden(C_91,k1_relat_1(A_92))
      | ~ r2_hidden(k4_tarski(C_91,D_93),A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_74,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_65,c_70])).

tff(c_80,plain,(
    ! [A_94,B_95,C_96] :
      ( k1_relset_1(A_94,B_95,C_96) = k1_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_84,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_80])).

tff(c_44,plain,(
    ! [E_84] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_84),'#skF_8')
      | ~ m1_subset_1(E_84,'#skF_7')
      | ~ r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8')) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_135,plain,(
    ! [E_109] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_109),'#skF_8')
      | ~ m1_subset_1(E_109,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_84,c_44])).

tff(c_142,plain,(
    ~ m1_subset_1('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_65,c_135])).

tff(c_149,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_142])).

tff(c_150,plain,(
    r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_164,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_150])).

tff(c_234,plain,(
    ! [A_134,B_135,C_136,D_137] :
      ( k8_relset_1(A_134,B_135,C_136,D_137) = k10_relat_1(C_136,D_137)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_241,plain,(
    ! [D_137] : k8_relset_1('#skF_6','#skF_7','#skF_8',D_137) = k10_relat_1('#skF_8',D_137) ),
    inference(resolution,[status(thm)],[c_38,c_234])).

tff(c_294,plain,(
    ! [A_149,B_150,C_151] :
      ( k8_relset_1(A_149,B_150,C_151,B_150) = k1_relset_1(A_149,B_150,C_151)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_299,plain,(
    k8_relset_1('#skF_6','#skF_7','#skF_8','#skF_7') = k1_relset_1('#skF_6','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_294])).

tff(c_302,plain,(
    k10_relat_1('#skF_8','#skF_7') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_162,c_299])).

tff(c_18,plain,(
    ! [A_25,B_26] : v1_relat_1(k2_zfmisc_1(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_57,plain,(
    ! [B_89,A_90] :
      ( v1_relat_1(B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_90))
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_60,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_38,c_57])).

tff(c_63,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_60])).

tff(c_252,plain,(
    ! [A_142,B_143,C_144] :
      ( r2_hidden(k4_tarski(A_142,'#skF_5'(A_142,B_143,C_144)),C_144)
      | ~ r2_hidden(A_142,k10_relat_1(C_144,B_143))
      | ~ v1_relat_1(C_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_151,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,(
    ! [E_84] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_84),'#skF_8')
      | ~ m1_subset_1(E_84,'#skF_7')
      | r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_179,plain,(
    ! [E_84] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_84),'#skF_8')
      | ~ m1_subset_1(E_84,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_48])).

tff(c_259,plain,(
    ! [B_143] :
      ( ~ m1_subset_1('#skF_5'('#skF_9',B_143,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_143))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_252,c_179])).

tff(c_269,plain,(
    ! [B_143] :
      ( ~ m1_subset_1('#skF_5'('#skF_9',B_143,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_143)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_259])).

tff(c_306,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_269])).

tff(c_315,plain,(
    ~ m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_306])).

tff(c_169,plain,(
    ! [A_116,B_117,C_118] :
      ( r2_hidden('#skF_5'(A_116,B_117,C_118),B_117)
      | ~ r2_hidden(A_116,k10_relat_1(C_118,B_117))
      | ~ v1_relat_1(C_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_173,plain,(
    ! [A_116,B_117,C_118] :
      ( m1_subset_1('#skF_5'(A_116,B_117,C_118),B_117)
      | ~ r2_hidden(A_116,k10_relat_1(C_118,B_117))
      | ~ v1_relat_1(C_118) ) ),
    inference(resolution,[status(thm)],[c_169,c_2])).

tff(c_311,plain,(
    ! [A_116] :
      ( m1_subset_1('#skF_5'(A_116,'#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_116,k1_relat_1('#skF_8'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_173])).

tff(c_333,plain,(
    ! [A_155] :
      ( m1_subset_1('#skF_5'(A_155,'#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_155,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_311])).

tff(c_348,plain,(
    m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_164,c_333])).

tff(c_359,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_315,c_348])).

tff(c_360,plain,(
    r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_562,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_360])).

tff(c_599,plain,(
    ! [A_213,B_214,C_215,D_216] :
      ( k8_relset_1(A_213,B_214,C_215,D_216) = k10_relat_1(C_215,D_216)
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1(A_213,B_214))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_602,plain,(
    ! [D_216] : k8_relset_1('#skF_6','#skF_7','#skF_8',D_216) = k10_relat_1('#skF_8',D_216) ),
    inference(resolution,[status(thm)],[c_38,c_599])).

tff(c_649,plain,(
    ! [A_231,B_232,C_233] :
      ( k8_relset_1(A_231,B_232,C_233,B_232) = k1_relset_1(A_231,B_232,C_233)
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(A_231,B_232))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_654,plain,(
    k8_relset_1('#skF_6','#skF_7','#skF_8','#skF_7') = k1_relset_1('#skF_6','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_649])).

tff(c_657,plain,(
    k10_relat_1('#skF_8','#skF_7') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_560,c_654])).

tff(c_594,plain,(
    ! [A_210,B_211,C_212] :
      ( r2_hidden('#skF_5'(A_210,B_211,C_212),B_211)
      | ~ r2_hidden(A_210,k10_relat_1(C_212,B_211))
      | ~ v1_relat_1(C_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_598,plain,(
    ! [A_210,B_211,C_212] :
      ( m1_subset_1('#skF_5'(A_210,B_211,C_212),B_211)
      | ~ r2_hidden(A_210,k10_relat_1(C_212,B_211))
      | ~ v1_relat_1(C_212) ) ),
    inference(resolution,[status(thm)],[c_594,c_2])).

tff(c_660,plain,(
    ! [A_210] :
      ( m1_subset_1('#skF_5'(A_210,'#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_210,k1_relat_1('#skF_8'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_657,c_598])).

tff(c_678,plain,(
    ! [A_237] :
      ( m1_subset_1('#skF_5'(A_237,'#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_237,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_660])).

tff(c_697,plain,(
    m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_562,c_678])).

tff(c_700,plain,(
    ! [A_243,B_244,C_245] :
      ( r2_hidden(k4_tarski(A_243,'#skF_5'(A_243,B_244,C_245)),C_245)
      | ~ r2_hidden(A_243,k10_relat_1(C_245,B_244))
      | ~ v1_relat_1(C_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_361,plain,(
    ~ m1_subset_1('#skF_10','#skF_7') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,(
    ! [E_84] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_84),'#skF_8')
      | ~ m1_subset_1(E_84,'#skF_7')
      | m1_subset_1('#skF_10','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_554,plain,(
    ! [E_84] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_84),'#skF_8')
      | ~ m1_subset_1(E_84,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_361,c_52])).

tff(c_711,plain,(
    ! [B_244] :
      ( ~ m1_subset_1('#skF_5'('#skF_9',B_244,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_244))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_700,c_554])).

tff(c_725,plain,(
    ! [B_246] :
      ( ~ m1_subset_1('#skF_5'('#skF_9',B_246,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_246)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_711])).

tff(c_728,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_657,c_725])).

tff(c_731,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_562,c_697,c_728])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n002.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 13:44:51 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.18/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.41  
% 2.82/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.42  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1
% 2.82/1.42  
% 2.82/1.42  %Foreground sorts:
% 2.82/1.42  
% 2.82/1.42  
% 2.82/1.42  %Background operators:
% 2.82/1.42  
% 2.82/1.42  
% 2.82/1.42  %Foreground operators:
% 2.82/1.42  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.82/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.82/1.42  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.82/1.42  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.82/1.42  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.82/1.42  tff('#skF_7', type, '#skF_7': $i).
% 2.82/1.42  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.82/1.42  tff('#skF_10', type, '#skF_10': $i).
% 2.82/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.82/1.42  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.82/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.82/1.42  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.82/1.42  tff('#skF_9', type, '#skF_9': $i).
% 2.82/1.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.82/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.82/1.42  tff('#skF_8', type, '#skF_8': $i).
% 2.82/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.42  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.82/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.82/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.82/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.82/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.82/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.82/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.82/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.82/1.42  
% 2.82/1.44  tff(f_92, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (![D]: (m1_subset_1(D, A) => (r2_hidden(D, k1_relset_1(A, B, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(D, E), C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relset_1)).
% 2.82/1.44  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.82/1.44  tff(f_44, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 2.82/1.44  tff(f_65, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.82/1.44  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 2.82/1.44  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.82/1.44  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.82/1.44  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.82/1.44  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.82/1.44  tff(c_38, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.82/1.44  tff(c_556, plain, (![A_203, B_204, C_205]: (k1_relset_1(A_203, B_204, C_205)=k1_relat_1(C_205) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_203, B_204))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.82/1.44  tff(c_560, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_556])).
% 2.82/1.44  tff(c_158, plain, (![A_113, B_114, C_115]: (k1_relset_1(A_113, B_114, C_115)=k1_relat_1(C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.82/1.44  tff(c_162, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_158])).
% 2.82/1.44  tff(c_54, plain, (r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8')) | m1_subset_1('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.82/1.44  tff(c_64, plain, (m1_subset_1('#skF_10', '#skF_7')), inference(splitLeft, [status(thm)], [c_54])).
% 2.82/1.44  tff(c_50, plain, (r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8')) | r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.82/1.44  tff(c_65, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8')), inference(splitLeft, [status(thm)], [c_50])).
% 2.82/1.44  tff(c_70, plain, (![C_91, A_92, D_93]: (r2_hidden(C_91, k1_relat_1(A_92)) | ~r2_hidden(k4_tarski(C_91, D_93), A_92))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.82/1.44  tff(c_74, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_65, c_70])).
% 2.82/1.44  tff(c_80, plain, (![A_94, B_95, C_96]: (k1_relset_1(A_94, B_95, C_96)=k1_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.82/1.44  tff(c_84, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_80])).
% 2.82/1.44  tff(c_44, plain, (![E_84]: (~r2_hidden(k4_tarski('#skF_9', E_84), '#skF_8') | ~m1_subset_1(E_84, '#skF_7') | ~r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.82/1.44  tff(c_135, plain, (![E_109]: (~r2_hidden(k4_tarski('#skF_9', E_109), '#skF_8') | ~m1_subset_1(E_109, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_84, c_44])).
% 2.82/1.44  tff(c_142, plain, (~m1_subset_1('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_65, c_135])).
% 2.82/1.44  tff(c_149, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_142])).
% 2.82/1.44  tff(c_150, plain, (r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_50])).
% 2.82/1.44  tff(c_164, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_150])).
% 2.82/1.44  tff(c_234, plain, (![A_134, B_135, C_136, D_137]: (k8_relset_1(A_134, B_135, C_136, D_137)=k10_relat_1(C_136, D_137) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.82/1.44  tff(c_241, plain, (![D_137]: (k8_relset_1('#skF_6', '#skF_7', '#skF_8', D_137)=k10_relat_1('#skF_8', D_137))), inference(resolution, [status(thm)], [c_38, c_234])).
% 2.82/1.44  tff(c_294, plain, (![A_149, B_150, C_151]: (k8_relset_1(A_149, B_150, C_151, B_150)=k1_relset_1(A_149, B_150, C_151) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.82/1.44  tff(c_299, plain, (k8_relset_1('#skF_6', '#skF_7', '#skF_8', '#skF_7')=k1_relset_1('#skF_6', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_38, c_294])).
% 2.82/1.44  tff(c_302, plain, (k10_relat_1('#skF_8', '#skF_7')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_241, c_162, c_299])).
% 2.82/1.44  tff(c_18, plain, (![A_25, B_26]: (v1_relat_1(k2_zfmisc_1(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.82/1.44  tff(c_57, plain, (![B_89, A_90]: (v1_relat_1(B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(A_90)) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.82/1.44  tff(c_60, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_38, c_57])).
% 2.82/1.44  tff(c_63, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_60])).
% 2.82/1.44  tff(c_252, plain, (![A_142, B_143, C_144]: (r2_hidden(k4_tarski(A_142, '#skF_5'(A_142, B_143, C_144)), C_144) | ~r2_hidden(A_142, k10_relat_1(C_144, B_143)) | ~v1_relat_1(C_144))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.82/1.44  tff(c_151, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8')), inference(splitRight, [status(thm)], [c_50])).
% 2.82/1.44  tff(c_48, plain, (![E_84]: (~r2_hidden(k4_tarski('#skF_9', E_84), '#skF_8') | ~m1_subset_1(E_84, '#skF_7') | r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.82/1.44  tff(c_179, plain, (![E_84]: (~r2_hidden(k4_tarski('#skF_9', E_84), '#skF_8') | ~m1_subset_1(E_84, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_151, c_48])).
% 2.82/1.44  tff(c_259, plain, (![B_143]: (~m1_subset_1('#skF_5'('#skF_9', B_143, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_143)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_252, c_179])).
% 2.82/1.44  tff(c_269, plain, (![B_143]: (~m1_subset_1('#skF_5'('#skF_9', B_143, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_143)))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_259])).
% 2.82/1.44  tff(c_306, plain, (~m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_302, c_269])).
% 2.82/1.44  tff(c_315, plain, (~m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_306])).
% 2.82/1.44  tff(c_169, plain, (![A_116, B_117, C_118]: (r2_hidden('#skF_5'(A_116, B_117, C_118), B_117) | ~r2_hidden(A_116, k10_relat_1(C_118, B_117)) | ~v1_relat_1(C_118))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.82/1.44  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.82/1.44  tff(c_173, plain, (![A_116, B_117, C_118]: (m1_subset_1('#skF_5'(A_116, B_117, C_118), B_117) | ~r2_hidden(A_116, k10_relat_1(C_118, B_117)) | ~v1_relat_1(C_118))), inference(resolution, [status(thm)], [c_169, c_2])).
% 2.82/1.44  tff(c_311, plain, (![A_116]: (m1_subset_1('#skF_5'(A_116, '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_116, k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_302, c_173])).
% 2.82/1.44  tff(c_333, plain, (![A_155]: (m1_subset_1('#skF_5'(A_155, '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_155, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_311])).
% 2.82/1.44  tff(c_348, plain, (m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_164, c_333])).
% 2.82/1.44  tff(c_359, plain, $false, inference(negUnitSimplification, [status(thm)], [c_315, c_348])).
% 2.82/1.44  tff(c_360, plain, (r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_54])).
% 2.82/1.44  tff(c_562, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_560, c_360])).
% 2.82/1.44  tff(c_599, plain, (![A_213, B_214, C_215, D_216]: (k8_relset_1(A_213, B_214, C_215, D_216)=k10_relat_1(C_215, D_216) | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1(A_213, B_214))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.82/1.44  tff(c_602, plain, (![D_216]: (k8_relset_1('#skF_6', '#skF_7', '#skF_8', D_216)=k10_relat_1('#skF_8', D_216))), inference(resolution, [status(thm)], [c_38, c_599])).
% 2.82/1.44  tff(c_649, plain, (![A_231, B_232, C_233]: (k8_relset_1(A_231, B_232, C_233, B_232)=k1_relset_1(A_231, B_232, C_233) | ~m1_subset_1(C_233, k1_zfmisc_1(k2_zfmisc_1(A_231, B_232))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.82/1.44  tff(c_654, plain, (k8_relset_1('#skF_6', '#skF_7', '#skF_8', '#skF_7')=k1_relset_1('#skF_6', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_38, c_649])).
% 2.82/1.44  tff(c_657, plain, (k10_relat_1('#skF_8', '#skF_7')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_602, c_560, c_654])).
% 2.82/1.44  tff(c_594, plain, (![A_210, B_211, C_212]: (r2_hidden('#skF_5'(A_210, B_211, C_212), B_211) | ~r2_hidden(A_210, k10_relat_1(C_212, B_211)) | ~v1_relat_1(C_212))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.82/1.44  tff(c_598, plain, (![A_210, B_211, C_212]: (m1_subset_1('#skF_5'(A_210, B_211, C_212), B_211) | ~r2_hidden(A_210, k10_relat_1(C_212, B_211)) | ~v1_relat_1(C_212))), inference(resolution, [status(thm)], [c_594, c_2])).
% 2.82/1.44  tff(c_660, plain, (![A_210]: (m1_subset_1('#skF_5'(A_210, '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_210, k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_657, c_598])).
% 2.82/1.44  tff(c_678, plain, (![A_237]: (m1_subset_1('#skF_5'(A_237, '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_237, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_660])).
% 2.82/1.44  tff(c_697, plain, (m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_562, c_678])).
% 2.82/1.44  tff(c_700, plain, (![A_243, B_244, C_245]: (r2_hidden(k4_tarski(A_243, '#skF_5'(A_243, B_244, C_245)), C_245) | ~r2_hidden(A_243, k10_relat_1(C_245, B_244)) | ~v1_relat_1(C_245))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.82/1.44  tff(c_361, plain, (~m1_subset_1('#skF_10', '#skF_7')), inference(splitRight, [status(thm)], [c_54])).
% 2.82/1.44  tff(c_52, plain, (![E_84]: (~r2_hidden(k4_tarski('#skF_9', E_84), '#skF_8') | ~m1_subset_1(E_84, '#skF_7') | m1_subset_1('#skF_10', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.82/1.44  tff(c_554, plain, (![E_84]: (~r2_hidden(k4_tarski('#skF_9', E_84), '#skF_8') | ~m1_subset_1(E_84, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_361, c_52])).
% 2.82/1.44  tff(c_711, plain, (![B_244]: (~m1_subset_1('#skF_5'('#skF_9', B_244, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_244)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_700, c_554])).
% 2.82/1.44  tff(c_725, plain, (![B_246]: (~m1_subset_1('#skF_5'('#skF_9', B_246, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_246)))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_711])).
% 2.82/1.44  tff(c_728, plain, (~m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_657, c_725])).
% 2.82/1.44  tff(c_731, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_562, c_697, c_728])).
% 2.82/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.44  
% 2.82/1.44  Inference rules
% 2.82/1.44  ----------------------
% 2.82/1.44  #Ref     : 0
% 2.82/1.44  #Sup     : 139
% 2.82/1.44  #Fact    : 0
% 2.82/1.44  #Define  : 0
% 2.82/1.44  #Split   : 3
% 2.82/1.44  #Chain   : 0
% 2.82/1.44  #Close   : 0
% 2.82/1.44  
% 2.82/1.44  Ordering : KBO
% 2.82/1.44  
% 2.82/1.44  Simplification rules
% 2.82/1.44  ----------------------
% 2.82/1.44  #Subsume      : 6
% 2.82/1.44  #Demod        : 47
% 2.82/1.44  #Tautology    : 38
% 2.82/1.44  #SimpNegUnit  : 5
% 2.82/1.44  #BackRed      : 6
% 2.82/1.44  
% 2.82/1.44  #Partial instantiations: 0
% 2.82/1.44  #Strategies tried      : 1
% 2.82/1.44  
% 2.82/1.44  Timing (in seconds)
% 2.82/1.44  ----------------------
% 2.82/1.44  Preprocessing        : 0.33
% 2.82/1.44  Parsing              : 0.17
% 2.82/1.44  CNF conversion       : 0.03
% 2.82/1.44  Main loop            : 0.35
% 2.82/1.44  Inferencing          : 0.13
% 2.82/1.44  Reduction            : 0.10
% 2.82/1.44  Demodulation         : 0.07
% 2.82/1.44  BG Simplification    : 0.02
% 2.82/1.44  Subsumption          : 0.06
% 2.82/1.44  Abstraction          : 0.02
% 2.82/1.44  MUC search           : 0.00
% 2.82/1.44  Cooper               : 0.00
% 2.82/1.44  Total                : 0.72
% 2.82/1.44  Index Insertion      : 0.00
% 2.82/1.44  Index Deletion       : 0.00
% 2.82/1.44  Index Matching       : 0.00
% 2.82/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
