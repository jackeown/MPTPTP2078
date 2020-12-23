%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:03 EST 2020

% Result     : Theorem 7.37s
% Output     : CNFRefutation 7.47s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 212 expanded)
%              Number of leaves         :   39 (  90 expanded)
%              Depth                    :    9
%              Number of atoms          :  188 ( 505 expanded)
%              Number of equality atoms :   10 (  24 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_11 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_59,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_105,negated_conjecture,(
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

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_57,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_28,plain,(
    ! [A_32,B_33] : v1_relat_1(k2_zfmisc_1(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_48,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2939,plain,(
    ! [B_463,A_464] :
      ( v1_relat_1(B_463)
      | ~ m1_subset_1(B_463,k1_zfmisc_1(A_464))
      | ~ v1_relat_1(A_464) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2942,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_48,c_2939])).

tff(c_2945,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2942])).

tff(c_2962,plain,(
    ! [C_475,B_476,A_477] :
      ( v5_relat_1(C_475,B_476)
      | ~ m1_subset_1(C_475,k1_zfmisc_1(k2_zfmisc_1(A_477,B_476))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2971,plain,(
    v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_2962])).

tff(c_3016,plain,(
    ! [A_491,B_492,C_493] :
      ( k1_relset_1(A_491,B_492,C_493) = k1_relat_1(C_493)
      | ~ m1_subset_1(C_493,k1_zfmisc_1(k2_zfmisc_1(A_491,B_492))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3025,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_48,c_3016])).

tff(c_89,plain,(
    ! [B_99,A_100] :
      ( v1_relat_1(B_99)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_100))
      | ~ v1_relat_1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_92,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_48,c_89])).

tff(c_95,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_92])).

tff(c_335,plain,(
    ! [C_159,B_160,A_161] :
      ( v5_relat_1(C_159,B_160)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_161,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_344,plain,(
    v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_335])).

tff(c_383,plain,(
    ! [A_171,B_172,C_173] :
      ( k1_relset_1(A_171,B_172,C_173) = k1_relat_1(C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_397,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_48,c_383])).

tff(c_68,plain,(
    ! [A_95,B_96] :
      ( r2_hidden('#skF_1'(A_95,B_96),A_95)
      | r1_tarski(A_95,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_76,plain,(
    ! [A_95] : r1_tarski(A_95,A_95) ),
    inference(resolution,[status(thm)],[c_68,c_4])).

tff(c_64,plain,
    ( r2_hidden('#skF_10',k1_relset_1('#skF_7','#skF_8','#skF_9'))
    | m1_subset_1('#skF_11','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_79,plain,(
    m1_subset_1('#skF_11','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_60,plain,
    ( r2_hidden('#skF_10',k1_relset_1('#skF_7','#skF_8','#skF_9'))
    | r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_119,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_148,plain,(
    ! [C_117,B_118,A_119] :
      ( r2_hidden(C_117,B_118)
      | ~ r2_hidden(C_117,A_119)
      | ~ r1_tarski(A_119,B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_156,plain,(
    ! [B_118] :
      ( r2_hidden(k4_tarski('#skF_10','#skF_11'),B_118)
      | ~ r1_tarski('#skF_9',B_118) ) ),
    inference(resolution,[status(thm)],[c_119,c_148])).

tff(c_134,plain,(
    ! [C_112,A_113,D_114] :
      ( r2_hidden(C_112,k1_relat_1(A_113))
      | ~ r2_hidden(k4_tarski(C_112,D_114),A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_138,plain,(
    r2_hidden('#skF_10',k1_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_119,c_134])).

tff(c_203,plain,(
    ! [A_125,B_126,C_127] :
      ( k1_relset_1(A_125,B_126,C_127) = k1_relat_1(C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_217,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_48,c_203])).

tff(c_54,plain,(
    ! [E_88] :
      ( ~ r2_hidden(k4_tarski('#skF_10',E_88),'#skF_9')
      | ~ m1_subset_1(E_88,'#skF_8')
      | ~ r2_hidden('#skF_10',k1_relset_1('#skF_7','#skF_8','#skF_9')) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_297,plain,(
    ! [E_150] :
      ( ~ r2_hidden(k4_tarski('#skF_10',E_150),'#skF_9')
      | ~ m1_subset_1(E_150,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_217,c_54])).

tff(c_305,plain,
    ( ~ m1_subset_1('#skF_11','#skF_8')
    | ~ r1_tarski('#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_156,c_297])).

tff(c_315,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_79,c_305])).

tff(c_316,plain,(
    r2_hidden('#skF_10',k1_relset_1('#skF_7','#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_400,plain,(
    r2_hidden('#skF_10',k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_316])).

tff(c_38,plain,(
    ! [A_40] :
      ( k10_relat_1(A_40,k2_relat_1(A_40)) = k1_relat_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_452,plain,(
    ! [A_183,B_184,C_185] :
      ( r2_hidden('#skF_6'(A_183,B_184,C_185),k2_relat_1(C_185))
      | ~ r2_hidden(A_183,k10_relat_1(C_185,B_184))
      | ~ v1_relat_1(C_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1162,plain,(
    ! [A_287,B_288,C_289,B_290] :
      ( r2_hidden('#skF_6'(A_287,B_288,C_289),B_290)
      | ~ r1_tarski(k2_relat_1(C_289),B_290)
      | ~ r2_hidden(A_287,k10_relat_1(C_289,B_288))
      | ~ v1_relat_1(C_289) ) ),
    inference(resolution,[status(thm)],[c_452,c_2])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1220,plain,(
    ! [A_296,B_297,C_298,B_299] :
      ( m1_subset_1('#skF_6'(A_296,B_297,C_298),B_299)
      | ~ r1_tarski(k2_relat_1(C_298),B_299)
      | ~ r2_hidden(A_296,k10_relat_1(C_298,B_297))
      | ~ v1_relat_1(C_298) ) ),
    inference(resolution,[status(thm)],[c_1162,c_8])).

tff(c_1228,plain,(
    ! [A_300,B_301,B_302,A_303] :
      ( m1_subset_1('#skF_6'(A_300,B_301,B_302),A_303)
      | ~ r2_hidden(A_300,k10_relat_1(B_302,B_301))
      | ~ v5_relat_1(B_302,A_303)
      | ~ v1_relat_1(B_302) ) ),
    inference(resolution,[status(thm)],[c_14,c_1220])).

tff(c_2895,plain,(
    ! [A_459,A_460,A_461] :
      ( m1_subset_1('#skF_6'(A_459,k2_relat_1(A_460),A_460),A_461)
      | ~ r2_hidden(A_459,k1_relat_1(A_460))
      | ~ v5_relat_1(A_460,A_461)
      | ~ v1_relat_1(A_460)
      | ~ v1_relat_1(A_460) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1228])).

tff(c_529,plain,(
    ! [A_214,B_215,C_216] :
      ( r2_hidden(k4_tarski(A_214,'#skF_6'(A_214,B_215,C_216)),C_216)
      | ~ r2_hidden(A_214,k10_relat_1(C_216,B_215))
      | ~ v1_relat_1(C_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_317,plain,(
    ~ r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_58,plain,(
    ! [E_88] :
      ( ~ r2_hidden(k4_tarski('#skF_10',E_88),'#skF_9')
      | ~ m1_subset_1(E_88,'#skF_8')
      | r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_405,plain,(
    ! [E_88] :
      ( ~ r2_hidden(k4_tarski('#skF_10',E_88),'#skF_9')
      | ~ m1_subset_1(E_88,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_317,c_58])).

tff(c_536,plain,(
    ! [B_215] :
      ( ~ m1_subset_1('#skF_6'('#skF_10',B_215,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_215))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_529,c_405])).

tff(c_581,plain,(
    ! [B_220] :
      ( ~ m1_subset_1('#skF_6'('#skF_10',B_220,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_220)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_536])).

tff(c_585,plain,
    ( ~ m1_subset_1('#skF_6'('#skF_10',k2_relat_1('#skF_9'),'#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k1_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_581])).

tff(c_587,plain,(
    ~ m1_subset_1('#skF_6'('#skF_10',k2_relat_1('#skF_9'),'#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_400,c_585])).

tff(c_2902,plain,
    ( ~ r2_hidden('#skF_10',k1_relat_1('#skF_9'))
    | ~ v5_relat_1('#skF_9','#skF_8')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_2895,c_587])).

tff(c_2923,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_344,c_400,c_2902])).

tff(c_2924,plain,(
    r2_hidden('#skF_10',k1_relset_1('#skF_7','#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_3028,plain,(
    r2_hidden('#skF_10',k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3025,c_2924])).

tff(c_3148,plain,(
    ! [A_513,B_514,C_515] :
      ( r2_hidden('#skF_6'(A_513,B_514,C_515),k2_relat_1(C_515))
      | ~ r2_hidden(A_513,k10_relat_1(C_515,B_514))
      | ~ v1_relat_1(C_515) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3741,plain,(
    ! [A_603,B_604,C_605,B_606] :
      ( r2_hidden('#skF_6'(A_603,B_604,C_605),B_606)
      | ~ r1_tarski(k2_relat_1(C_605),B_606)
      | ~ r2_hidden(A_603,k10_relat_1(C_605,B_604))
      | ~ v1_relat_1(C_605) ) ),
    inference(resolution,[status(thm)],[c_3148,c_2])).

tff(c_4092,plain,(
    ! [A_636,B_637,C_638,B_639] :
      ( m1_subset_1('#skF_6'(A_636,B_637,C_638),B_639)
      | ~ r1_tarski(k2_relat_1(C_638),B_639)
      | ~ r2_hidden(A_636,k10_relat_1(C_638,B_637))
      | ~ v1_relat_1(C_638) ) ),
    inference(resolution,[status(thm)],[c_3741,c_8])).

tff(c_4100,plain,(
    ! [A_640,B_641,B_642,A_643] :
      ( m1_subset_1('#skF_6'(A_640,B_641,B_642),A_643)
      | ~ r2_hidden(A_640,k10_relat_1(B_642,B_641))
      | ~ v5_relat_1(B_642,A_643)
      | ~ v1_relat_1(B_642) ) ),
    inference(resolution,[status(thm)],[c_14,c_4092])).

tff(c_6056,plain,(
    ! [A_820,A_821,A_822] :
      ( m1_subset_1('#skF_6'(A_820,k2_relat_1(A_821),A_821),A_822)
      | ~ r2_hidden(A_820,k1_relat_1(A_821))
      | ~ v5_relat_1(A_821,A_822)
      | ~ v1_relat_1(A_821)
      | ~ v1_relat_1(A_821) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_4100])).

tff(c_3165,plain,(
    ! [A_526,B_527,C_528] :
      ( r2_hidden(k4_tarski(A_526,'#skF_6'(A_526,B_527,C_528)),C_528)
      | ~ r2_hidden(A_526,k10_relat_1(C_528,B_527))
      | ~ v1_relat_1(C_528) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2925,plain,(
    ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_62,plain,(
    ! [E_88] :
      ( ~ r2_hidden(k4_tarski('#skF_10',E_88),'#skF_9')
      | ~ m1_subset_1(E_88,'#skF_8')
      | m1_subset_1('#skF_11','#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2982,plain,(
    ! [E_88] :
      ( ~ r2_hidden(k4_tarski('#skF_10',E_88),'#skF_9')
      | ~ m1_subset_1(E_88,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2925,c_62])).

tff(c_3172,plain,(
    ! [B_527] :
      ( ~ m1_subset_1('#skF_6'('#skF_10',B_527,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_527))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_3165,c_2982])).

tff(c_3188,plain,(
    ! [B_529] :
      ( ~ m1_subset_1('#skF_6'('#skF_10',B_529,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_529)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2945,c_3172])).

tff(c_3192,plain,
    ( ~ m1_subset_1('#skF_6'('#skF_10',k2_relat_1('#skF_9'),'#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k1_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_3188])).

tff(c_3194,plain,(
    ~ m1_subset_1('#skF_6'('#skF_10',k2_relat_1('#skF_9'),'#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2945,c_3028,c_3192])).

tff(c_6063,plain,
    ( ~ r2_hidden('#skF_10',k1_relat_1('#skF_9'))
    | ~ v5_relat_1('#skF_9','#skF_8')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_6056,c_3194])).

tff(c_6084,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2945,c_2971,c_3028,c_6063])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:21:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.37/2.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.37/2.58  
% 7.37/2.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.37/2.58  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_11 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 7.37/2.58  
% 7.37/2.58  %Foreground sorts:
% 7.37/2.58  
% 7.37/2.58  
% 7.37/2.58  %Background operators:
% 7.37/2.58  
% 7.37/2.58  
% 7.37/2.58  %Foreground operators:
% 7.37/2.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.37/2.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.37/2.58  tff('#skF_11', type, '#skF_11': $i).
% 7.37/2.58  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 7.37/2.58  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.37/2.58  tff('#skF_7', type, '#skF_7': $i).
% 7.37/2.58  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.37/2.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.37/2.58  tff('#skF_10', type, '#skF_10': $i).
% 7.37/2.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.37/2.58  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 7.37/2.58  tff('#skF_9', type, '#skF_9': $i).
% 7.37/2.58  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.37/2.58  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.37/2.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.37/2.58  tff('#skF_8', type, '#skF_8': $i).
% 7.37/2.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.37/2.58  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.37/2.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.37/2.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.37/2.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.37/2.58  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.37/2.58  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.37/2.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.37/2.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.37/2.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.37/2.58  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.37/2.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.37/2.58  
% 7.47/2.60  tff(f_59, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.47/2.60  tff(f_105, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (![D]: (m1_subset_1(D, A) => (r2_hidden(D, k1_relset_1(A, B, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(D, E), C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relset_1)).
% 7.47/2.60  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.47/2.60  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.47/2.60  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.47/2.60  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.47/2.60  tff(f_57, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 7.47/2.60  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 7.47/2.60  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 7.47/2.60  tff(f_70, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 7.47/2.60  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 7.47/2.60  tff(c_28, plain, (![A_32, B_33]: (v1_relat_1(k2_zfmisc_1(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.47/2.60  tff(c_48, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.47/2.60  tff(c_2939, plain, (![B_463, A_464]: (v1_relat_1(B_463) | ~m1_subset_1(B_463, k1_zfmisc_1(A_464)) | ~v1_relat_1(A_464))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.47/2.60  tff(c_2942, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_48, c_2939])).
% 7.47/2.60  tff(c_2945, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2942])).
% 7.47/2.60  tff(c_2962, plain, (![C_475, B_476, A_477]: (v5_relat_1(C_475, B_476) | ~m1_subset_1(C_475, k1_zfmisc_1(k2_zfmisc_1(A_477, B_476))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.47/2.60  tff(c_2971, plain, (v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_48, c_2962])).
% 7.47/2.60  tff(c_3016, plain, (![A_491, B_492, C_493]: (k1_relset_1(A_491, B_492, C_493)=k1_relat_1(C_493) | ~m1_subset_1(C_493, k1_zfmisc_1(k2_zfmisc_1(A_491, B_492))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.47/2.60  tff(c_3025, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_48, c_3016])).
% 7.47/2.60  tff(c_89, plain, (![B_99, A_100]: (v1_relat_1(B_99) | ~m1_subset_1(B_99, k1_zfmisc_1(A_100)) | ~v1_relat_1(A_100))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.47/2.60  tff(c_92, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_48, c_89])).
% 7.47/2.60  tff(c_95, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_92])).
% 7.47/2.60  tff(c_335, plain, (![C_159, B_160, A_161]: (v5_relat_1(C_159, B_160) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_161, B_160))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.47/2.60  tff(c_344, plain, (v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_48, c_335])).
% 7.47/2.60  tff(c_383, plain, (![A_171, B_172, C_173]: (k1_relset_1(A_171, B_172, C_173)=k1_relat_1(C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.47/2.60  tff(c_397, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_48, c_383])).
% 7.47/2.60  tff(c_68, plain, (![A_95, B_96]: (r2_hidden('#skF_1'(A_95, B_96), A_95) | r1_tarski(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.47/2.60  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.47/2.60  tff(c_76, plain, (![A_95]: (r1_tarski(A_95, A_95))), inference(resolution, [status(thm)], [c_68, c_4])).
% 7.47/2.60  tff(c_64, plain, (r2_hidden('#skF_10', k1_relset_1('#skF_7', '#skF_8', '#skF_9')) | m1_subset_1('#skF_11', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.47/2.60  tff(c_79, plain, (m1_subset_1('#skF_11', '#skF_8')), inference(splitLeft, [status(thm)], [c_64])).
% 7.47/2.60  tff(c_60, plain, (r2_hidden('#skF_10', k1_relset_1('#skF_7', '#skF_8', '#skF_9')) | r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.47/2.60  tff(c_119, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(splitLeft, [status(thm)], [c_60])).
% 7.47/2.60  tff(c_148, plain, (![C_117, B_118, A_119]: (r2_hidden(C_117, B_118) | ~r2_hidden(C_117, A_119) | ~r1_tarski(A_119, B_118))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.47/2.60  tff(c_156, plain, (![B_118]: (r2_hidden(k4_tarski('#skF_10', '#skF_11'), B_118) | ~r1_tarski('#skF_9', B_118))), inference(resolution, [status(thm)], [c_119, c_148])).
% 7.47/2.60  tff(c_134, plain, (![C_112, A_113, D_114]: (r2_hidden(C_112, k1_relat_1(A_113)) | ~r2_hidden(k4_tarski(C_112, D_114), A_113))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.47/2.60  tff(c_138, plain, (r2_hidden('#skF_10', k1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_119, c_134])).
% 7.47/2.60  tff(c_203, plain, (![A_125, B_126, C_127]: (k1_relset_1(A_125, B_126, C_127)=k1_relat_1(C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.47/2.60  tff(c_217, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_48, c_203])).
% 7.47/2.60  tff(c_54, plain, (![E_88]: (~r2_hidden(k4_tarski('#skF_10', E_88), '#skF_9') | ~m1_subset_1(E_88, '#skF_8') | ~r2_hidden('#skF_10', k1_relset_1('#skF_7', '#skF_8', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.47/2.60  tff(c_297, plain, (![E_150]: (~r2_hidden(k4_tarski('#skF_10', E_150), '#skF_9') | ~m1_subset_1(E_150, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_217, c_54])).
% 7.47/2.60  tff(c_305, plain, (~m1_subset_1('#skF_11', '#skF_8') | ~r1_tarski('#skF_9', '#skF_9')), inference(resolution, [status(thm)], [c_156, c_297])).
% 7.47/2.60  tff(c_315, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_79, c_305])).
% 7.47/2.60  tff(c_316, plain, (r2_hidden('#skF_10', k1_relset_1('#skF_7', '#skF_8', '#skF_9'))), inference(splitRight, [status(thm)], [c_60])).
% 7.47/2.60  tff(c_400, plain, (r2_hidden('#skF_10', k1_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_397, c_316])).
% 7.47/2.60  tff(c_38, plain, (![A_40]: (k10_relat_1(A_40, k2_relat_1(A_40))=k1_relat_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.47/2.60  tff(c_14, plain, (![B_12, A_11]: (r1_tarski(k2_relat_1(B_12), A_11) | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.47/2.60  tff(c_452, plain, (![A_183, B_184, C_185]: (r2_hidden('#skF_6'(A_183, B_184, C_185), k2_relat_1(C_185)) | ~r2_hidden(A_183, k10_relat_1(C_185, B_184)) | ~v1_relat_1(C_185))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.47/2.60  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.47/2.60  tff(c_1162, plain, (![A_287, B_288, C_289, B_290]: (r2_hidden('#skF_6'(A_287, B_288, C_289), B_290) | ~r1_tarski(k2_relat_1(C_289), B_290) | ~r2_hidden(A_287, k10_relat_1(C_289, B_288)) | ~v1_relat_1(C_289))), inference(resolution, [status(thm)], [c_452, c_2])).
% 7.47/2.60  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.47/2.60  tff(c_1220, plain, (![A_296, B_297, C_298, B_299]: (m1_subset_1('#skF_6'(A_296, B_297, C_298), B_299) | ~r1_tarski(k2_relat_1(C_298), B_299) | ~r2_hidden(A_296, k10_relat_1(C_298, B_297)) | ~v1_relat_1(C_298))), inference(resolution, [status(thm)], [c_1162, c_8])).
% 7.47/2.60  tff(c_1228, plain, (![A_300, B_301, B_302, A_303]: (m1_subset_1('#skF_6'(A_300, B_301, B_302), A_303) | ~r2_hidden(A_300, k10_relat_1(B_302, B_301)) | ~v5_relat_1(B_302, A_303) | ~v1_relat_1(B_302))), inference(resolution, [status(thm)], [c_14, c_1220])).
% 7.47/2.60  tff(c_2895, plain, (![A_459, A_460, A_461]: (m1_subset_1('#skF_6'(A_459, k2_relat_1(A_460), A_460), A_461) | ~r2_hidden(A_459, k1_relat_1(A_460)) | ~v5_relat_1(A_460, A_461) | ~v1_relat_1(A_460) | ~v1_relat_1(A_460))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1228])).
% 7.47/2.60  tff(c_529, plain, (![A_214, B_215, C_216]: (r2_hidden(k4_tarski(A_214, '#skF_6'(A_214, B_215, C_216)), C_216) | ~r2_hidden(A_214, k10_relat_1(C_216, B_215)) | ~v1_relat_1(C_216))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.47/2.60  tff(c_317, plain, (~r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(splitRight, [status(thm)], [c_60])).
% 7.47/2.60  tff(c_58, plain, (![E_88]: (~r2_hidden(k4_tarski('#skF_10', E_88), '#skF_9') | ~m1_subset_1(E_88, '#skF_8') | r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.47/2.60  tff(c_405, plain, (![E_88]: (~r2_hidden(k4_tarski('#skF_10', E_88), '#skF_9') | ~m1_subset_1(E_88, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_317, c_58])).
% 7.47/2.60  tff(c_536, plain, (![B_215]: (~m1_subset_1('#skF_6'('#skF_10', B_215, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_215)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_529, c_405])).
% 7.47/2.60  tff(c_581, plain, (![B_220]: (~m1_subset_1('#skF_6'('#skF_10', B_220, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_220)))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_536])).
% 7.47/2.60  tff(c_585, plain, (~m1_subset_1('#skF_6'('#skF_10', k2_relat_1('#skF_9'), '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k1_relat_1('#skF_9')) | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_38, c_581])).
% 7.47/2.60  tff(c_587, plain, (~m1_subset_1('#skF_6'('#skF_10', k2_relat_1('#skF_9'), '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_400, c_585])).
% 7.47/2.60  tff(c_2902, plain, (~r2_hidden('#skF_10', k1_relat_1('#skF_9')) | ~v5_relat_1('#skF_9', '#skF_8') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_2895, c_587])).
% 7.47/2.60  tff(c_2923, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95, c_344, c_400, c_2902])).
% 7.47/2.60  tff(c_2924, plain, (r2_hidden('#skF_10', k1_relset_1('#skF_7', '#skF_8', '#skF_9'))), inference(splitRight, [status(thm)], [c_64])).
% 7.47/2.60  tff(c_3028, plain, (r2_hidden('#skF_10', k1_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_3025, c_2924])).
% 7.47/2.60  tff(c_3148, plain, (![A_513, B_514, C_515]: (r2_hidden('#skF_6'(A_513, B_514, C_515), k2_relat_1(C_515)) | ~r2_hidden(A_513, k10_relat_1(C_515, B_514)) | ~v1_relat_1(C_515))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.47/2.60  tff(c_3741, plain, (![A_603, B_604, C_605, B_606]: (r2_hidden('#skF_6'(A_603, B_604, C_605), B_606) | ~r1_tarski(k2_relat_1(C_605), B_606) | ~r2_hidden(A_603, k10_relat_1(C_605, B_604)) | ~v1_relat_1(C_605))), inference(resolution, [status(thm)], [c_3148, c_2])).
% 7.47/2.60  tff(c_4092, plain, (![A_636, B_637, C_638, B_639]: (m1_subset_1('#skF_6'(A_636, B_637, C_638), B_639) | ~r1_tarski(k2_relat_1(C_638), B_639) | ~r2_hidden(A_636, k10_relat_1(C_638, B_637)) | ~v1_relat_1(C_638))), inference(resolution, [status(thm)], [c_3741, c_8])).
% 7.47/2.60  tff(c_4100, plain, (![A_640, B_641, B_642, A_643]: (m1_subset_1('#skF_6'(A_640, B_641, B_642), A_643) | ~r2_hidden(A_640, k10_relat_1(B_642, B_641)) | ~v5_relat_1(B_642, A_643) | ~v1_relat_1(B_642))), inference(resolution, [status(thm)], [c_14, c_4092])).
% 7.47/2.60  tff(c_6056, plain, (![A_820, A_821, A_822]: (m1_subset_1('#skF_6'(A_820, k2_relat_1(A_821), A_821), A_822) | ~r2_hidden(A_820, k1_relat_1(A_821)) | ~v5_relat_1(A_821, A_822) | ~v1_relat_1(A_821) | ~v1_relat_1(A_821))), inference(superposition, [status(thm), theory('equality')], [c_38, c_4100])).
% 7.47/2.60  tff(c_3165, plain, (![A_526, B_527, C_528]: (r2_hidden(k4_tarski(A_526, '#skF_6'(A_526, B_527, C_528)), C_528) | ~r2_hidden(A_526, k10_relat_1(C_528, B_527)) | ~v1_relat_1(C_528))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.47/2.60  tff(c_2925, plain, (~m1_subset_1('#skF_11', '#skF_8')), inference(splitRight, [status(thm)], [c_64])).
% 7.47/2.60  tff(c_62, plain, (![E_88]: (~r2_hidden(k4_tarski('#skF_10', E_88), '#skF_9') | ~m1_subset_1(E_88, '#skF_8') | m1_subset_1('#skF_11', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.47/2.60  tff(c_2982, plain, (![E_88]: (~r2_hidden(k4_tarski('#skF_10', E_88), '#skF_9') | ~m1_subset_1(E_88, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_2925, c_62])).
% 7.47/2.60  tff(c_3172, plain, (![B_527]: (~m1_subset_1('#skF_6'('#skF_10', B_527, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_527)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_3165, c_2982])).
% 7.47/2.60  tff(c_3188, plain, (![B_529]: (~m1_subset_1('#skF_6'('#skF_10', B_529, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_529)))), inference(demodulation, [status(thm), theory('equality')], [c_2945, c_3172])).
% 7.47/2.60  tff(c_3192, plain, (~m1_subset_1('#skF_6'('#skF_10', k2_relat_1('#skF_9'), '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k1_relat_1('#skF_9')) | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_38, c_3188])).
% 7.47/2.60  tff(c_3194, plain, (~m1_subset_1('#skF_6'('#skF_10', k2_relat_1('#skF_9'), '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2945, c_3028, c_3192])).
% 7.47/2.60  tff(c_6063, plain, (~r2_hidden('#skF_10', k1_relat_1('#skF_9')) | ~v5_relat_1('#skF_9', '#skF_8') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_6056, c_3194])).
% 7.47/2.60  tff(c_6084, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2945, c_2971, c_3028, c_6063])).
% 7.47/2.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.47/2.60  
% 7.47/2.60  Inference rules
% 7.47/2.60  ----------------------
% 7.47/2.60  #Ref     : 0
% 7.47/2.60  #Sup     : 1365
% 7.47/2.60  #Fact    : 0
% 7.47/2.60  #Define  : 0
% 7.47/2.60  #Split   : 6
% 7.47/2.60  #Chain   : 0
% 7.47/2.60  #Close   : 0
% 7.47/2.60  
% 7.47/2.60  Ordering : KBO
% 7.47/2.60  
% 7.47/2.60  Simplification rules
% 7.47/2.60  ----------------------
% 7.47/2.60  #Subsume      : 83
% 7.47/2.60  #Demod        : 56
% 7.47/2.60  #Tautology    : 89
% 7.47/2.60  #SimpNegUnit  : 2
% 7.47/2.60  #BackRed      : 6
% 7.47/2.60  
% 7.47/2.60  #Partial instantiations: 0
% 7.47/2.60  #Strategies tried      : 1
% 7.47/2.60  
% 7.47/2.60  Timing (in seconds)
% 7.47/2.60  ----------------------
% 7.47/2.60  Preprocessing        : 0.35
% 7.47/2.60  Parsing              : 0.18
% 7.47/2.60  CNF conversion       : 0.03
% 7.47/2.60  Main loop            : 1.43
% 7.47/2.60  Inferencing          : 0.52
% 7.47/2.60  Reduction            : 0.33
% 7.47/2.60  Demodulation         : 0.21
% 7.47/2.60  BG Simplification    : 0.07
% 7.47/2.60  Subsumption          : 0.39
% 7.47/2.60  Abstraction          : 0.08
% 7.47/2.60  MUC search           : 0.00
% 7.47/2.60  Cooper               : 0.00
% 7.47/2.60  Total                : 1.81
% 7.47/2.60  Index Insertion      : 0.00
% 7.47/2.60  Index Deletion       : 0.00
% 7.47/2.60  Index Matching       : 0.00
% 7.47/2.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
