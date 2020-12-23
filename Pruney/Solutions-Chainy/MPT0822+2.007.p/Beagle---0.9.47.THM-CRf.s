%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:11 EST 2020

% Result     : Theorem 7.95s
% Output     : CNFRefutation 8.16s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 482 expanded)
%              Number of leaves         :   32 ( 173 expanded)
%              Depth                    :   15
%              Number of atoms          :  238 (1060 expanded)
%              Number of equality atoms :   40 ( 191 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_9 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] : ~ r2_hidden(k4_tarski(E,D),C) )
        <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( r2_hidden(C,k2_relat_1(B))
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,(
    ! [A_57,B_58] :
      ( ~ r2_hidden('#skF_1'(A_57,B_58),B_58)
      | r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_65,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_60])).

tff(c_42,plain,(
    ! [D_45] :
      ( r2_hidden(k4_tarski('#skF_9'(D_45),D_45),'#skF_8')
      | ~ r2_hidden(D_45,'#skF_7')
      | r2_hidden('#skF_10','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_114,plain,(
    r2_hidden('#skF_10','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_34,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_131,plain,(
    ! [A_85,B_86,C_87] :
      ( k2_relset_1(A_85,B_86,C_87) = k2_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_140,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_131])).

tff(c_40,plain,
    ( k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7'
    | r2_hidden('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_59,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_141,plain,(
    k2_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_59])).

tff(c_46,plain,(
    ! [D_45] :
      ( r2_hidden(k4_tarski('#skF_9'(D_45),D_45),'#skF_8')
      | ~ r2_hidden(D_45,'#skF_7')
      | k2_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_7' ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_219,plain,(
    ! [D_45] :
      ( r2_hidden(k4_tarski('#skF_9'(D_45),D_45),'#skF_8')
      | ~ r2_hidden(D_45,'#skF_7')
      | k2_relat_1('#skF_8') = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_46])).

tff(c_221,plain,(
    ! [D_106] :
      ( r2_hidden(k4_tarski('#skF_9'(D_106),D_106),'#skF_8')
      | ~ r2_hidden(D_106,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_219])).

tff(c_38,plain,(
    ! [D_45,E_48] :
      ( r2_hidden(k4_tarski('#skF_9'(D_45),D_45),'#skF_8')
      | ~ r2_hidden(D_45,'#skF_7')
      | ~ r2_hidden(k4_tarski(E_48,'#skF_10'),'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_147,plain,(
    ! [E_48] : ~ r2_hidden(k4_tarski(E_48,'#skF_10'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_225,plain,(
    ~ r2_hidden('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_221,c_147])).

tff(c_234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_225])).

tff(c_236,plain,(
    ! [D_107] :
      ( r2_hidden(k4_tarski('#skF_9'(D_107),D_107),'#skF_8')
      | ~ r2_hidden(D_107,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_14,plain,(
    ! [C_23,A_8,D_26] :
      ( r2_hidden(C_23,k2_relat_1(A_8))
      | ~ r2_hidden(k4_tarski(D_26,C_23),A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_244,plain,(
    ! [D_108] :
      ( r2_hidden(D_108,k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_108,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_236,c_14])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_276,plain,(
    ! [A_116] :
      ( r1_tarski(A_116,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_116,k2_relat_1('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_244,c_4])).

tff(c_281,plain,(
    r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6,c_276])).

tff(c_675,plain,(
    ! [A_169,B_170] :
      ( r2_hidden(k4_tarski('#skF_3'(A_169,B_170),'#skF_2'(A_169,B_170)),A_169)
      | r2_hidden('#skF_4'(A_169,B_170),B_170)
      | k2_relat_1(A_169) = B_170 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_697,plain,(
    ! [A_169,B_170] :
      ( r2_hidden('#skF_2'(A_169,B_170),k2_relat_1(A_169))
      | r2_hidden('#skF_4'(A_169,B_170),B_170)
      | k2_relat_1(A_169) = B_170 ) ),
    inference(resolution,[status(thm)],[c_675,c_14])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_67,plain,(
    ! [C_60,B_61,A_62] :
      ( v5_relat_1(C_60,B_61)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_62,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_77,plain,(
    ! [A_63,B_64,A_65] :
      ( v5_relat_1(A_63,B_64)
      | ~ r1_tarski(A_63,k2_zfmisc_1(A_65,B_64)) ) ),
    inference(resolution,[status(thm)],[c_10,c_67])).

tff(c_85,plain,(
    ! [A_65,B_64] : v5_relat_1(k2_zfmisc_1(A_65,B_64),B_64) ),
    inference(resolution,[status(thm)],[c_65,c_77])).

tff(c_24,plain,(
    ! [A_27,B_28] : v1_relat_1(k2_zfmisc_1(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_49,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(A_53,B_54)
      | ~ m1_subset_1(A_53,k1_zfmisc_1(B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_57,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_34,c_49])).

tff(c_413,plain,(
    ! [A_137,C_138] :
      ( r2_hidden(k4_tarski('#skF_5'(A_137,k2_relat_1(A_137),C_138),C_138),A_137)
      | ~ r2_hidden(C_138,k2_relat_1(A_137)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1266,plain,(
    ! [A_215,C_216,B_217] :
      ( r2_hidden(k4_tarski('#skF_5'(A_215,k2_relat_1(A_215),C_216),C_216),B_217)
      | ~ r1_tarski(A_215,B_217)
      | ~ r2_hidden(C_216,k2_relat_1(A_215)) ) ),
    inference(resolution,[status(thm)],[c_413,c_2])).

tff(c_1372,plain,(
    ! [C_225,B_226,A_227] :
      ( r2_hidden(C_225,k2_relat_1(B_226))
      | ~ r1_tarski(A_227,B_226)
      | ~ r2_hidden(C_225,k2_relat_1(A_227)) ) ),
    inference(resolution,[status(thm)],[c_1266,c_14])).

tff(c_1406,plain,(
    ! [C_228] :
      ( r2_hidden(C_228,k2_relat_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ r2_hidden(C_228,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_57,c_1372])).

tff(c_26,plain,(
    ! [C_32,A_29,B_30] :
      ( r2_hidden(C_32,A_29)
      | ~ r2_hidden(C_32,k2_relat_1(B_30))
      | ~ v5_relat_1(B_30,A_29)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1418,plain,(
    ! [C_228,A_29] :
      ( r2_hidden(C_228,A_29)
      | ~ v5_relat_1(k2_zfmisc_1('#skF_6','#skF_7'),A_29)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ r2_hidden(C_228,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_1406,c_26])).

tff(c_1794,plain,(
    ! [C_259,A_260] :
      ( r2_hidden(C_259,A_260)
      | ~ v5_relat_1(k2_zfmisc_1('#skF_6','#skF_7'),A_260)
      | ~ r2_hidden(C_259,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1418])).

tff(c_1803,plain,(
    ! [C_261] :
      ( r2_hidden(C_261,'#skF_7')
      | ~ r2_hidden(C_261,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_85,c_1794])).

tff(c_3687,plain,(
    ! [B_330] :
      ( r2_hidden('#skF_2'('#skF_8',B_330),'#skF_7')
      | r2_hidden('#skF_4'('#skF_8',B_330),B_330)
      | k2_relat_1('#skF_8') = B_330 ) ),
    inference(resolution,[status(thm)],[c_697,c_1803])).

tff(c_20,plain,(
    ! [A_8,B_9] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9),B_9)
      | r2_hidden('#skF_4'(A_8,B_9),B_9)
      | k2_relat_1(A_8) = B_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3694,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_3687,c_20])).

tff(c_3729,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_141,c_3694])).

tff(c_3823,plain,(
    ! [B_334] :
      ( r2_hidden('#skF_4'('#skF_8','#skF_7'),B_334)
      | ~ r1_tarski('#skF_7',B_334) ) ),
    inference(resolution,[status(thm)],[c_3729,c_2])).

tff(c_3861,plain,(
    ! [B_335,B_336] :
      ( r2_hidden('#skF_4'('#skF_8','#skF_7'),B_335)
      | ~ r1_tarski(B_336,B_335)
      | ~ r1_tarski('#skF_7',B_336) ) ),
    inference(resolution,[status(thm)],[c_3823,c_2])).

tff(c_3901,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),k2_relat_1('#skF_8'))
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_281,c_3861])).

tff(c_3938,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_7'),k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_3901])).

tff(c_12,plain,(
    ! [A_8,C_23] :
      ( r2_hidden(k4_tarski('#skF_5'(A_8,k2_relat_1(A_8),C_23),C_23),A_8)
      | ~ r2_hidden(C_23,k2_relat_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_235,plain,(
    ! [D_45] :
      ( r2_hidden(k4_tarski('#skF_9'(D_45),D_45),'#skF_8')
      | ~ r2_hidden(D_45,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_858,plain,(
    ! [A_185,B_186,D_187] :
      ( r2_hidden(k4_tarski('#skF_3'(A_185,B_186),'#skF_2'(A_185,B_186)),A_185)
      | ~ r2_hidden(k4_tarski(D_187,'#skF_4'(A_185,B_186)),A_185)
      | k2_relat_1(A_185) = B_186 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_915,plain,(
    ! [B_188] :
      ( r2_hidden(k4_tarski('#skF_3'('#skF_8',B_188),'#skF_2'('#skF_8',B_188)),'#skF_8')
      | k2_relat_1('#skF_8') = B_188
      | ~ r2_hidden('#skF_4'('#skF_8',B_188),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_235,c_858])).

tff(c_921,plain,(
    ! [B_188] :
      ( r2_hidden('#skF_2'('#skF_8',B_188),k2_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_188
      | ~ r2_hidden('#skF_4'('#skF_8',B_188),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_915,c_14])).

tff(c_4760,plain,(
    ! [B_365] :
      ( r2_hidden('#skF_2'('#skF_8',B_365),'#skF_7')
      | k2_relat_1('#skF_8') = B_365
      | ~ r2_hidden('#skF_4'('#skF_8',B_365),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_921,c_1803])).

tff(c_16,plain,(
    ! [A_8,B_9,D_22] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9),B_9)
      | ~ r2_hidden(k4_tarski(D_22,'#skF_4'(A_8,B_9)),A_8)
      | k2_relat_1(A_8) = B_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4763,plain,(
    ! [D_22] :
      ( ~ r2_hidden(k4_tarski(D_22,'#skF_4'('#skF_8','#skF_7')),'#skF_8')
      | k2_relat_1('#skF_8') = '#skF_7'
      | ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_4760,c_16])).

tff(c_4772,plain,(
    ! [D_22] :
      ( ~ r2_hidden(k4_tarski(D_22,'#skF_4'('#skF_8','#skF_7')),'#skF_8')
      | k2_relat_1('#skF_8') = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3729,c_4763])).

tff(c_4849,plain,(
    ! [D_370] : ~ r2_hidden(k4_tarski(D_370,'#skF_4'('#skF_8','#skF_7')),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_4772])).

tff(c_4861,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_12,c_4849])).

tff(c_4875,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3938,c_4861])).

tff(c_4882,plain,(
    ! [D_377] :
      ( r2_hidden(k4_tarski('#skF_9'(D_377),D_377),'#skF_8')
      | ~ r2_hidden(D_377,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_4895,plain,(
    ! [D_378] :
      ( r2_hidden(D_378,k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_378,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_4882,c_14])).

tff(c_4925,plain,(
    ! [A_384] :
      ( r1_tarski(A_384,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_384,k2_relat_1('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_4895,c_4])).

tff(c_4930,plain,(
    r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6,c_4925])).

tff(c_4910,plain,(
    ! [A_381,B_382,C_383] :
      ( k2_relset_1(A_381,B_382,C_383) = k2_relat_1(C_383)
      | ~ m1_subset_1(C_383,k1_zfmisc_1(k2_zfmisc_1(A_381,B_382))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4919,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_4910])).

tff(c_4920,plain,(
    k2_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4919,c_59])).

tff(c_5327,plain,(
    ! [A_439,B_440] :
      ( r2_hidden(k4_tarski('#skF_3'(A_439,B_440),'#skF_2'(A_439,B_440)),A_439)
      | r2_hidden('#skF_4'(A_439,B_440),B_440)
      | k2_relat_1(A_439) = B_440 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_5353,plain,(
    ! [A_439,B_440] :
      ( r2_hidden('#skF_2'(A_439,B_440),k2_relat_1(A_439))
      | r2_hidden('#skF_4'(A_439,B_440),B_440)
      | k2_relat_1(A_439) = B_440 ) ),
    inference(resolution,[status(thm)],[c_5327,c_14])).

tff(c_5031,plain,(
    ! [A_403,C_404] :
      ( r2_hidden(k4_tarski('#skF_5'(A_403,k2_relat_1(A_403),C_404),C_404),A_403)
      | ~ r2_hidden(C_404,k2_relat_1(A_403)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_5730,plain,(
    ! [A_479,C_480,B_481] :
      ( r2_hidden(k4_tarski('#skF_5'(A_479,k2_relat_1(A_479),C_480),C_480),B_481)
      | ~ r1_tarski(A_479,B_481)
      | ~ r2_hidden(C_480,k2_relat_1(A_479)) ) ),
    inference(resolution,[status(thm)],[c_5031,c_2])).

tff(c_5820,plain,(
    ! [C_486,B_487,A_488] :
      ( r2_hidden(C_486,k2_relat_1(B_487))
      | ~ r1_tarski(A_488,B_487)
      | ~ r2_hidden(C_486,k2_relat_1(A_488)) ) ),
    inference(resolution,[status(thm)],[c_5730,c_14])).

tff(c_5854,plain,(
    ! [C_489] :
      ( r2_hidden(C_489,k2_relat_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ r2_hidden(C_489,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_57,c_5820])).

tff(c_5870,plain,(
    ! [C_489,A_29] :
      ( r2_hidden(C_489,A_29)
      | ~ v5_relat_1(k2_zfmisc_1('#skF_6','#skF_7'),A_29)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ r2_hidden(C_489,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_5854,c_26])).

tff(c_5989,plain,(
    ! [C_494,A_495] :
      ( r2_hidden(C_494,A_495)
      | ~ v5_relat_1(k2_zfmisc_1('#skF_6','#skF_7'),A_495)
      | ~ r2_hidden(C_494,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_5870])).

tff(c_5998,plain,(
    ! [C_496] :
      ( r2_hidden(C_496,'#skF_7')
      | ~ r2_hidden(C_496,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_85,c_5989])).

tff(c_6891,plain,(
    ! [B_530] :
      ( r2_hidden('#skF_2'('#skF_8',B_530),'#skF_7')
      | r2_hidden('#skF_4'('#skF_8',B_530),B_530)
      | k2_relat_1('#skF_8') = B_530 ) ),
    inference(resolution,[status(thm)],[c_5353,c_5998])).

tff(c_6898,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_6891,c_20])).

tff(c_6929,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_4920,c_4920,c_6898])).

tff(c_6942,plain,(
    ! [B_531] :
      ( r2_hidden('#skF_4'('#skF_8','#skF_7'),B_531)
      | ~ r1_tarski('#skF_7',B_531) ) ),
    inference(resolution,[status(thm)],[c_6929,c_2])).

tff(c_7109,plain,(
    ! [B_538,B_539] :
      ( r2_hidden('#skF_4'('#skF_8','#skF_7'),B_538)
      | ~ r1_tarski(B_539,B_538)
      | ~ r1_tarski('#skF_7',B_539) ) ),
    inference(resolution,[status(thm)],[c_6942,c_2])).

tff(c_7137,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),k2_relat_1('#skF_8'))
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_4930,c_7109])).

tff(c_7164,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_7'),k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_7137])).

tff(c_4876,plain,(
    ! [D_45] :
      ( r2_hidden(k4_tarski('#skF_9'(D_45),D_45),'#skF_8')
      | ~ r2_hidden(D_45,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_5422,plain,(
    ! [A_446,B_447,D_448] :
      ( r2_hidden(k4_tarski('#skF_3'(A_446,B_447),'#skF_2'(A_446,B_447)),A_446)
      | ~ r2_hidden(k4_tarski(D_448,'#skF_4'(A_446,B_447)),A_446)
      | k2_relat_1(A_446) = B_447 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_5671,plain,(
    ! [B_468] :
      ( r2_hidden(k4_tarski('#skF_3'('#skF_8',B_468),'#skF_2'('#skF_8',B_468)),'#skF_8')
      | k2_relat_1('#skF_8') = B_468
      | ~ r2_hidden('#skF_4'('#skF_8',B_468),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_4876,c_5422])).

tff(c_7238,plain,(
    ! [B_541] :
      ( r2_hidden('#skF_2'('#skF_8',B_541),k2_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_541
      | ~ r2_hidden('#skF_4'('#skF_8',B_541),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_5671,c_14])).

tff(c_5997,plain,(
    ! [C_494] :
      ( r2_hidden(C_494,'#skF_7')
      | ~ r2_hidden(C_494,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_85,c_5989])).

tff(c_7582,plain,(
    ! [B_559] :
      ( r2_hidden('#skF_2'('#skF_8',B_559),'#skF_7')
      | k2_relat_1('#skF_8') = B_559
      | ~ r2_hidden('#skF_4'('#skF_8',B_559),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_7238,c_5997])).

tff(c_7585,plain,(
    ! [D_22] :
      ( ~ r2_hidden(k4_tarski(D_22,'#skF_4'('#skF_8','#skF_7')),'#skF_8')
      | k2_relat_1('#skF_8') = '#skF_7'
      | ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_7582,c_16])).

tff(c_7594,plain,(
    ! [D_22] :
      ( ~ r2_hidden(k4_tarski(D_22,'#skF_4'('#skF_8','#skF_7')),'#skF_8')
      | k2_relat_1('#skF_8') = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6929,c_7585])).

tff(c_7601,plain,(
    ! [D_560] : ~ r2_hidden(k4_tarski(D_560,'#skF_4'('#skF_8','#skF_7')),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_4920,c_7594])).

tff(c_7613,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_12,c_7601])).

tff(c_7627,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7164,c_7613])).

tff(c_7628,plain,(
    r2_hidden('#skF_10','#skF_7') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_7629,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_7731,plain,(
    ! [A_596,B_597,C_598] :
      ( k2_relset_1(A_596,B_597,C_598) = k2_relat_1(C_598)
      | ~ m1_subset_1(C_598,k1_zfmisc_1(k2_zfmisc_1(A_596,B_597))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_7738,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_7731])).

tff(c_7741,plain,(
    k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7629,c_7738])).

tff(c_7742,plain,(
    ! [A_599,C_600] :
      ( r2_hidden(k4_tarski('#skF_5'(A_599,k2_relat_1(A_599),C_600),C_600),A_599)
      | ~ r2_hidden(C_600,k2_relat_1(A_599)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_36,plain,(
    ! [E_48] :
      ( k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7'
      | ~ r2_hidden(k4_tarski(E_48,'#skF_10'),'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_7654,plain,(
    ! [E_48] : ~ r2_hidden(k4_tarski(E_48,'#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7629,c_36])).

tff(c_7756,plain,(
    ~ r2_hidden('#skF_10',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_7742,c_7654])).

tff(c_7770,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7628,c_7741,c_7756])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:17:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.95/2.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.95/2.74  
% 7.95/2.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.95/2.74  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_9 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 7.95/2.74  
% 7.95/2.74  %Foreground sorts:
% 7.95/2.74  
% 7.95/2.74  
% 7.95/2.74  %Background operators:
% 7.95/2.74  
% 7.95/2.74  
% 7.95/2.74  %Foreground operators:
% 7.95/2.74  tff('#skF_9', type, '#skF_9': $i > $i).
% 7.95/2.74  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.95/2.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.95/2.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.95/2.74  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.95/2.74  tff('#skF_7', type, '#skF_7': $i).
% 7.95/2.74  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.95/2.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.95/2.74  tff('#skF_10', type, '#skF_10': $i).
% 7.95/2.74  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.95/2.74  tff('#skF_6', type, '#skF_6': $i).
% 7.95/2.74  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 7.95/2.74  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.95/2.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.95/2.74  tff('#skF_8', type, '#skF_8': $i).
% 7.95/2.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.95/2.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.95/2.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.95/2.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.95/2.74  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.95/2.74  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.95/2.74  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.95/2.74  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.95/2.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.95/2.74  
% 8.16/2.76  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.16/2.76  tff(f_78, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(E, D), C)))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_relset_1)).
% 8.16/2.76  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.16/2.76  tff(f_44, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 8.16/2.76  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.16/2.76  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.16/2.76  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.16/2.76  tff(f_55, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t202_relat_1)).
% 8.16/2.76  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.16/2.76  tff(c_60, plain, (![A_57, B_58]: (~r2_hidden('#skF_1'(A_57, B_58), B_58) | r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.16/2.76  tff(c_65, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_60])).
% 8.16/2.76  tff(c_42, plain, (![D_45]: (r2_hidden(k4_tarski('#skF_9'(D_45), D_45), '#skF_8') | ~r2_hidden(D_45, '#skF_7') | r2_hidden('#skF_10', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.16/2.76  tff(c_114, plain, (r2_hidden('#skF_10', '#skF_7')), inference(splitLeft, [status(thm)], [c_42])).
% 8.16/2.76  tff(c_34, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.16/2.76  tff(c_131, plain, (![A_85, B_86, C_87]: (k2_relset_1(A_85, B_86, C_87)=k2_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.16/2.76  tff(c_140, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_34, c_131])).
% 8.16/2.76  tff(c_40, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7' | r2_hidden('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.16/2.76  tff(c_59, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7'), inference(splitLeft, [status(thm)], [c_40])).
% 8.16/2.76  tff(c_141, plain, (k2_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_140, c_59])).
% 8.16/2.76  tff(c_46, plain, (![D_45]: (r2_hidden(k4_tarski('#skF_9'(D_45), D_45), '#skF_8') | ~r2_hidden(D_45, '#skF_7') | k2_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_7')), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.16/2.76  tff(c_219, plain, (![D_45]: (r2_hidden(k4_tarski('#skF_9'(D_45), D_45), '#skF_8') | ~r2_hidden(D_45, '#skF_7') | k2_relat_1('#skF_8')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_46])).
% 8.16/2.76  tff(c_221, plain, (![D_106]: (r2_hidden(k4_tarski('#skF_9'(D_106), D_106), '#skF_8') | ~r2_hidden(D_106, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_141, c_219])).
% 8.16/2.76  tff(c_38, plain, (![D_45, E_48]: (r2_hidden(k4_tarski('#skF_9'(D_45), D_45), '#skF_8') | ~r2_hidden(D_45, '#skF_7') | ~r2_hidden(k4_tarski(E_48, '#skF_10'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.16/2.76  tff(c_147, plain, (![E_48]: (~r2_hidden(k4_tarski(E_48, '#skF_10'), '#skF_8'))), inference(splitLeft, [status(thm)], [c_38])).
% 8.16/2.76  tff(c_225, plain, (~r2_hidden('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_221, c_147])).
% 8.16/2.76  tff(c_234, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_225])).
% 8.16/2.76  tff(c_236, plain, (![D_107]: (r2_hidden(k4_tarski('#skF_9'(D_107), D_107), '#skF_8') | ~r2_hidden(D_107, '#skF_7'))), inference(splitRight, [status(thm)], [c_38])).
% 8.16/2.76  tff(c_14, plain, (![C_23, A_8, D_26]: (r2_hidden(C_23, k2_relat_1(A_8)) | ~r2_hidden(k4_tarski(D_26, C_23), A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.16/2.76  tff(c_244, plain, (![D_108]: (r2_hidden(D_108, k2_relat_1('#skF_8')) | ~r2_hidden(D_108, '#skF_7'))), inference(resolution, [status(thm)], [c_236, c_14])).
% 8.16/2.76  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.16/2.76  tff(c_276, plain, (![A_116]: (r1_tarski(A_116, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_1'(A_116, k2_relat_1('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_244, c_4])).
% 8.16/2.76  tff(c_281, plain, (r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6, c_276])).
% 8.16/2.76  tff(c_675, plain, (![A_169, B_170]: (r2_hidden(k4_tarski('#skF_3'(A_169, B_170), '#skF_2'(A_169, B_170)), A_169) | r2_hidden('#skF_4'(A_169, B_170), B_170) | k2_relat_1(A_169)=B_170)), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.16/2.76  tff(c_697, plain, (![A_169, B_170]: (r2_hidden('#skF_2'(A_169, B_170), k2_relat_1(A_169)) | r2_hidden('#skF_4'(A_169, B_170), B_170) | k2_relat_1(A_169)=B_170)), inference(resolution, [status(thm)], [c_675, c_14])).
% 8.16/2.76  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.16/2.76  tff(c_67, plain, (![C_60, B_61, A_62]: (v5_relat_1(C_60, B_61) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_62, B_61))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.16/2.76  tff(c_77, plain, (![A_63, B_64, A_65]: (v5_relat_1(A_63, B_64) | ~r1_tarski(A_63, k2_zfmisc_1(A_65, B_64)))), inference(resolution, [status(thm)], [c_10, c_67])).
% 8.16/2.76  tff(c_85, plain, (![A_65, B_64]: (v5_relat_1(k2_zfmisc_1(A_65, B_64), B_64))), inference(resolution, [status(thm)], [c_65, c_77])).
% 8.16/2.76  tff(c_24, plain, (![A_27, B_28]: (v1_relat_1(k2_zfmisc_1(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.16/2.76  tff(c_49, plain, (![A_53, B_54]: (r1_tarski(A_53, B_54) | ~m1_subset_1(A_53, k1_zfmisc_1(B_54)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.16/2.76  tff(c_57, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_34, c_49])).
% 8.16/2.76  tff(c_413, plain, (![A_137, C_138]: (r2_hidden(k4_tarski('#skF_5'(A_137, k2_relat_1(A_137), C_138), C_138), A_137) | ~r2_hidden(C_138, k2_relat_1(A_137)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.16/2.76  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.16/2.76  tff(c_1266, plain, (![A_215, C_216, B_217]: (r2_hidden(k4_tarski('#skF_5'(A_215, k2_relat_1(A_215), C_216), C_216), B_217) | ~r1_tarski(A_215, B_217) | ~r2_hidden(C_216, k2_relat_1(A_215)))), inference(resolution, [status(thm)], [c_413, c_2])).
% 8.16/2.76  tff(c_1372, plain, (![C_225, B_226, A_227]: (r2_hidden(C_225, k2_relat_1(B_226)) | ~r1_tarski(A_227, B_226) | ~r2_hidden(C_225, k2_relat_1(A_227)))), inference(resolution, [status(thm)], [c_1266, c_14])).
% 8.16/2.76  tff(c_1406, plain, (![C_228]: (r2_hidden(C_228, k2_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~r2_hidden(C_228, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_57, c_1372])).
% 8.16/2.76  tff(c_26, plain, (![C_32, A_29, B_30]: (r2_hidden(C_32, A_29) | ~r2_hidden(C_32, k2_relat_1(B_30)) | ~v5_relat_1(B_30, A_29) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.16/2.76  tff(c_1418, plain, (![C_228, A_29]: (r2_hidden(C_228, A_29) | ~v5_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'), A_29) | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7')) | ~r2_hidden(C_228, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_1406, c_26])).
% 8.16/2.76  tff(c_1794, plain, (![C_259, A_260]: (r2_hidden(C_259, A_260) | ~v5_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'), A_260) | ~r2_hidden(C_259, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1418])).
% 8.16/2.76  tff(c_1803, plain, (![C_261]: (r2_hidden(C_261, '#skF_7') | ~r2_hidden(C_261, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_85, c_1794])).
% 8.16/2.76  tff(c_3687, plain, (![B_330]: (r2_hidden('#skF_2'('#skF_8', B_330), '#skF_7') | r2_hidden('#skF_4'('#skF_8', B_330), B_330) | k2_relat_1('#skF_8')=B_330)), inference(resolution, [status(thm)], [c_697, c_1803])).
% 8.16/2.76  tff(c_20, plain, (![A_8, B_9]: (~r2_hidden('#skF_2'(A_8, B_9), B_9) | r2_hidden('#skF_4'(A_8, B_9), B_9) | k2_relat_1(A_8)=B_9)), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.16/2.76  tff(c_3694, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_3687, c_20])).
% 8.16/2.76  tff(c_3729, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_141, c_141, c_3694])).
% 8.16/2.76  tff(c_3823, plain, (![B_334]: (r2_hidden('#skF_4'('#skF_8', '#skF_7'), B_334) | ~r1_tarski('#skF_7', B_334))), inference(resolution, [status(thm)], [c_3729, c_2])).
% 8.16/2.76  tff(c_3861, plain, (![B_335, B_336]: (r2_hidden('#skF_4'('#skF_8', '#skF_7'), B_335) | ~r1_tarski(B_336, B_335) | ~r1_tarski('#skF_7', B_336))), inference(resolution, [status(thm)], [c_3823, c_2])).
% 8.16/2.76  tff(c_3901, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), k2_relat_1('#skF_8')) | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_281, c_3861])).
% 8.16/2.76  tff(c_3938, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_3901])).
% 8.16/2.76  tff(c_12, plain, (![A_8, C_23]: (r2_hidden(k4_tarski('#skF_5'(A_8, k2_relat_1(A_8), C_23), C_23), A_8) | ~r2_hidden(C_23, k2_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.16/2.76  tff(c_235, plain, (![D_45]: (r2_hidden(k4_tarski('#skF_9'(D_45), D_45), '#skF_8') | ~r2_hidden(D_45, '#skF_7'))), inference(splitRight, [status(thm)], [c_38])).
% 8.16/2.76  tff(c_858, plain, (![A_185, B_186, D_187]: (r2_hidden(k4_tarski('#skF_3'(A_185, B_186), '#skF_2'(A_185, B_186)), A_185) | ~r2_hidden(k4_tarski(D_187, '#skF_4'(A_185, B_186)), A_185) | k2_relat_1(A_185)=B_186)), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.16/2.76  tff(c_915, plain, (![B_188]: (r2_hidden(k4_tarski('#skF_3'('#skF_8', B_188), '#skF_2'('#skF_8', B_188)), '#skF_8') | k2_relat_1('#skF_8')=B_188 | ~r2_hidden('#skF_4'('#skF_8', B_188), '#skF_7'))), inference(resolution, [status(thm)], [c_235, c_858])).
% 8.16/2.76  tff(c_921, plain, (![B_188]: (r2_hidden('#skF_2'('#skF_8', B_188), k2_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_188 | ~r2_hidden('#skF_4'('#skF_8', B_188), '#skF_7'))), inference(resolution, [status(thm)], [c_915, c_14])).
% 8.16/2.76  tff(c_4760, plain, (![B_365]: (r2_hidden('#skF_2'('#skF_8', B_365), '#skF_7') | k2_relat_1('#skF_8')=B_365 | ~r2_hidden('#skF_4'('#skF_8', B_365), '#skF_7'))), inference(resolution, [status(thm)], [c_921, c_1803])).
% 8.16/2.76  tff(c_16, plain, (![A_8, B_9, D_22]: (~r2_hidden('#skF_2'(A_8, B_9), B_9) | ~r2_hidden(k4_tarski(D_22, '#skF_4'(A_8, B_9)), A_8) | k2_relat_1(A_8)=B_9)), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.16/2.76  tff(c_4763, plain, (![D_22]: (~r2_hidden(k4_tarski(D_22, '#skF_4'('#skF_8', '#skF_7')), '#skF_8') | k2_relat_1('#skF_8')='#skF_7' | ~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7'))), inference(resolution, [status(thm)], [c_4760, c_16])).
% 8.16/2.76  tff(c_4772, plain, (![D_22]: (~r2_hidden(k4_tarski(D_22, '#skF_4'('#skF_8', '#skF_7')), '#skF_8') | k2_relat_1('#skF_8')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3729, c_4763])).
% 8.16/2.76  tff(c_4849, plain, (![D_370]: (~r2_hidden(k4_tarski(D_370, '#skF_4'('#skF_8', '#skF_7')), '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_141, c_4772])).
% 8.16/2.76  tff(c_4861, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_7'), k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_12, c_4849])).
% 8.16/2.76  tff(c_4875, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3938, c_4861])).
% 8.16/2.76  tff(c_4882, plain, (![D_377]: (r2_hidden(k4_tarski('#skF_9'(D_377), D_377), '#skF_8') | ~r2_hidden(D_377, '#skF_7'))), inference(splitRight, [status(thm)], [c_42])).
% 8.16/2.76  tff(c_4895, plain, (![D_378]: (r2_hidden(D_378, k2_relat_1('#skF_8')) | ~r2_hidden(D_378, '#skF_7'))), inference(resolution, [status(thm)], [c_4882, c_14])).
% 8.16/2.76  tff(c_4925, plain, (![A_384]: (r1_tarski(A_384, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_1'(A_384, k2_relat_1('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_4895, c_4])).
% 8.16/2.76  tff(c_4930, plain, (r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6, c_4925])).
% 8.16/2.76  tff(c_4910, plain, (![A_381, B_382, C_383]: (k2_relset_1(A_381, B_382, C_383)=k2_relat_1(C_383) | ~m1_subset_1(C_383, k1_zfmisc_1(k2_zfmisc_1(A_381, B_382))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.16/2.76  tff(c_4919, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_34, c_4910])).
% 8.16/2.76  tff(c_4920, plain, (k2_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_4919, c_59])).
% 8.16/2.76  tff(c_5327, plain, (![A_439, B_440]: (r2_hidden(k4_tarski('#skF_3'(A_439, B_440), '#skF_2'(A_439, B_440)), A_439) | r2_hidden('#skF_4'(A_439, B_440), B_440) | k2_relat_1(A_439)=B_440)), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.16/2.76  tff(c_5353, plain, (![A_439, B_440]: (r2_hidden('#skF_2'(A_439, B_440), k2_relat_1(A_439)) | r2_hidden('#skF_4'(A_439, B_440), B_440) | k2_relat_1(A_439)=B_440)), inference(resolution, [status(thm)], [c_5327, c_14])).
% 8.16/2.76  tff(c_5031, plain, (![A_403, C_404]: (r2_hidden(k4_tarski('#skF_5'(A_403, k2_relat_1(A_403), C_404), C_404), A_403) | ~r2_hidden(C_404, k2_relat_1(A_403)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.16/2.76  tff(c_5730, plain, (![A_479, C_480, B_481]: (r2_hidden(k4_tarski('#skF_5'(A_479, k2_relat_1(A_479), C_480), C_480), B_481) | ~r1_tarski(A_479, B_481) | ~r2_hidden(C_480, k2_relat_1(A_479)))), inference(resolution, [status(thm)], [c_5031, c_2])).
% 8.16/2.76  tff(c_5820, plain, (![C_486, B_487, A_488]: (r2_hidden(C_486, k2_relat_1(B_487)) | ~r1_tarski(A_488, B_487) | ~r2_hidden(C_486, k2_relat_1(A_488)))), inference(resolution, [status(thm)], [c_5730, c_14])).
% 8.16/2.76  tff(c_5854, plain, (![C_489]: (r2_hidden(C_489, k2_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~r2_hidden(C_489, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_57, c_5820])).
% 8.16/2.76  tff(c_5870, plain, (![C_489, A_29]: (r2_hidden(C_489, A_29) | ~v5_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'), A_29) | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7')) | ~r2_hidden(C_489, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_5854, c_26])).
% 8.16/2.76  tff(c_5989, plain, (![C_494, A_495]: (r2_hidden(C_494, A_495) | ~v5_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'), A_495) | ~r2_hidden(C_494, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_5870])).
% 8.16/2.76  tff(c_5998, plain, (![C_496]: (r2_hidden(C_496, '#skF_7') | ~r2_hidden(C_496, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_85, c_5989])).
% 8.16/2.76  tff(c_6891, plain, (![B_530]: (r2_hidden('#skF_2'('#skF_8', B_530), '#skF_7') | r2_hidden('#skF_4'('#skF_8', B_530), B_530) | k2_relat_1('#skF_8')=B_530)), inference(resolution, [status(thm)], [c_5353, c_5998])).
% 8.16/2.76  tff(c_6898, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_6891, c_20])).
% 8.16/2.76  tff(c_6929, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_4920, c_4920, c_6898])).
% 8.16/2.76  tff(c_6942, plain, (![B_531]: (r2_hidden('#skF_4'('#skF_8', '#skF_7'), B_531) | ~r1_tarski('#skF_7', B_531))), inference(resolution, [status(thm)], [c_6929, c_2])).
% 8.16/2.76  tff(c_7109, plain, (![B_538, B_539]: (r2_hidden('#skF_4'('#skF_8', '#skF_7'), B_538) | ~r1_tarski(B_539, B_538) | ~r1_tarski('#skF_7', B_539))), inference(resolution, [status(thm)], [c_6942, c_2])).
% 8.16/2.76  tff(c_7137, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), k2_relat_1('#skF_8')) | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_4930, c_7109])).
% 8.16/2.76  tff(c_7164, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_7137])).
% 8.16/2.76  tff(c_4876, plain, (![D_45]: (r2_hidden(k4_tarski('#skF_9'(D_45), D_45), '#skF_8') | ~r2_hidden(D_45, '#skF_7'))), inference(splitRight, [status(thm)], [c_42])).
% 8.16/2.76  tff(c_5422, plain, (![A_446, B_447, D_448]: (r2_hidden(k4_tarski('#skF_3'(A_446, B_447), '#skF_2'(A_446, B_447)), A_446) | ~r2_hidden(k4_tarski(D_448, '#skF_4'(A_446, B_447)), A_446) | k2_relat_1(A_446)=B_447)), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.16/2.76  tff(c_5671, plain, (![B_468]: (r2_hidden(k4_tarski('#skF_3'('#skF_8', B_468), '#skF_2'('#skF_8', B_468)), '#skF_8') | k2_relat_1('#skF_8')=B_468 | ~r2_hidden('#skF_4'('#skF_8', B_468), '#skF_7'))), inference(resolution, [status(thm)], [c_4876, c_5422])).
% 8.16/2.76  tff(c_7238, plain, (![B_541]: (r2_hidden('#skF_2'('#skF_8', B_541), k2_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_541 | ~r2_hidden('#skF_4'('#skF_8', B_541), '#skF_7'))), inference(resolution, [status(thm)], [c_5671, c_14])).
% 8.16/2.76  tff(c_5997, plain, (![C_494]: (r2_hidden(C_494, '#skF_7') | ~r2_hidden(C_494, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_85, c_5989])).
% 8.16/2.76  tff(c_7582, plain, (![B_559]: (r2_hidden('#skF_2'('#skF_8', B_559), '#skF_7') | k2_relat_1('#skF_8')=B_559 | ~r2_hidden('#skF_4'('#skF_8', B_559), '#skF_7'))), inference(resolution, [status(thm)], [c_7238, c_5997])).
% 8.16/2.76  tff(c_7585, plain, (![D_22]: (~r2_hidden(k4_tarski(D_22, '#skF_4'('#skF_8', '#skF_7')), '#skF_8') | k2_relat_1('#skF_8')='#skF_7' | ~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7'))), inference(resolution, [status(thm)], [c_7582, c_16])).
% 8.16/2.76  tff(c_7594, plain, (![D_22]: (~r2_hidden(k4_tarski(D_22, '#skF_4'('#skF_8', '#skF_7')), '#skF_8') | k2_relat_1('#skF_8')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6929, c_7585])).
% 8.16/2.76  tff(c_7601, plain, (![D_560]: (~r2_hidden(k4_tarski(D_560, '#skF_4'('#skF_8', '#skF_7')), '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_4920, c_7594])).
% 8.16/2.76  tff(c_7613, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_7'), k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_12, c_7601])).
% 8.16/2.76  tff(c_7627, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7164, c_7613])).
% 8.16/2.76  tff(c_7628, plain, (r2_hidden('#skF_10', '#skF_7')), inference(splitRight, [status(thm)], [c_40])).
% 8.16/2.76  tff(c_7629, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_7'), inference(splitRight, [status(thm)], [c_40])).
% 8.16/2.76  tff(c_7731, plain, (![A_596, B_597, C_598]: (k2_relset_1(A_596, B_597, C_598)=k2_relat_1(C_598) | ~m1_subset_1(C_598, k1_zfmisc_1(k2_zfmisc_1(A_596, B_597))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.16/2.76  tff(c_7738, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_34, c_7731])).
% 8.16/2.76  tff(c_7741, plain, (k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_7629, c_7738])).
% 8.16/2.76  tff(c_7742, plain, (![A_599, C_600]: (r2_hidden(k4_tarski('#skF_5'(A_599, k2_relat_1(A_599), C_600), C_600), A_599) | ~r2_hidden(C_600, k2_relat_1(A_599)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.16/2.76  tff(c_36, plain, (![E_48]: (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7' | ~r2_hidden(k4_tarski(E_48, '#skF_10'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.16/2.76  tff(c_7654, plain, (![E_48]: (~r2_hidden(k4_tarski(E_48, '#skF_10'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_7629, c_36])).
% 8.16/2.76  tff(c_7756, plain, (~r2_hidden('#skF_10', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_7742, c_7654])).
% 8.16/2.76  tff(c_7770, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7628, c_7741, c_7756])).
% 8.16/2.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.16/2.76  
% 8.16/2.76  Inference rules
% 8.16/2.76  ----------------------
% 8.16/2.76  #Ref     : 0
% 8.16/2.76  #Sup     : 1723
% 8.16/2.76  #Fact    : 0
% 8.16/2.76  #Define  : 0
% 8.16/2.76  #Split   : 41
% 8.16/2.76  #Chain   : 0
% 8.16/2.76  #Close   : 0
% 8.16/2.76  
% 8.16/2.76  Ordering : KBO
% 8.16/2.76  
% 8.16/2.76  Simplification rules
% 8.16/2.76  ----------------------
% 8.16/2.76  #Subsume      : 436
% 8.16/2.76  #Demod        : 387
% 8.16/2.76  #Tautology    : 221
% 8.16/2.76  #SimpNegUnit  : 11
% 8.16/2.76  #BackRed      : 2
% 8.16/2.76  
% 8.16/2.76  #Partial instantiations: 0
% 8.16/2.76  #Strategies tried      : 1
% 8.16/2.76  
% 8.16/2.76  Timing (in seconds)
% 8.16/2.76  ----------------------
% 8.16/2.77  Preprocessing        : 0.32
% 8.16/2.77  Parsing              : 0.17
% 8.16/2.77  CNF conversion       : 0.03
% 8.16/2.77  Main loop            : 1.65
% 8.16/2.77  Inferencing          : 0.48
% 8.16/2.77  Reduction            : 0.45
% 8.16/2.77  Demodulation         : 0.28
% 8.16/2.77  BG Simplification    : 0.05
% 8.16/2.77  Subsumption          : 0.53
% 8.16/2.77  Abstraction          : 0.07
% 8.16/2.77  MUC search           : 0.00
% 8.16/2.77  Cooper               : 0.00
% 8.16/2.77  Total                : 2.02
% 8.16/2.77  Index Insertion      : 0.00
% 8.16/2.77  Index Deletion       : 0.00
% 8.16/2.77  Index Matching       : 0.00
% 8.16/2.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
