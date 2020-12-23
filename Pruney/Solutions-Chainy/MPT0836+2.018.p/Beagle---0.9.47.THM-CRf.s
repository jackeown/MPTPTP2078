%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:05 EST 2020

% Result     : Theorem 3.98s
% Output     : CNFRefutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 198 expanded)
%              Number of leaves         :   28 (  76 expanded)
%              Depth                    :    8
%              Number of atoms          :  160 ( 477 expanded)
%              Number of equality atoms :   12 (  28 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_62,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_87,negated_conjecture,(
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

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_2077,plain,(
    ! [C_381,A_382] :
      ( r2_hidden(k4_tarski(C_381,'#skF_4'(A_382,k1_relat_1(A_382),C_381)),A_382)
      | ~ r2_hidden(C_381,k1_relat_1(A_382)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_32,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1181,plain,(
    ! [A_267,B_268,C_269] :
      ( k1_relset_1(A_267,B_268,C_269) = k1_relat_1(C_269)
      | ~ m1_subset_1(C_269,k1_zfmisc_1(k2_zfmisc_1(A_267,B_268))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1185,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_1181])).

tff(c_1105,plain,(
    ! [C_243,A_244] :
      ( r2_hidden(k4_tarski(C_243,'#skF_4'(A_244,k1_relat_1(A_244),C_243)),A_244)
      | ~ r2_hidden(C_243,k1_relat_1(A_244)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_153,plain,(
    ! [A_110,B_111,C_112] :
      ( k1_relset_1(A_110,B_111,C_112) = k1_relat_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_157,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_153])).

tff(c_48,plain,
    ( r2_hidden('#skF_8',k1_relset_1('#skF_5','#skF_6','#skF_7'))
    | m1_subset_1('#skF_9','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_61,plain,(
    m1_subset_1('#skF_9','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_44,plain,
    ( r2_hidden('#skF_8',k1_relset_1('#skF_5','#skF_6','#skF_7'))
    | r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_83,plain,(
    r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_18,plain,(
    ! [C_30,A_15,D_33] :
      ( r2_hidden(C_30,k1_relat_1(A_15))
      | ~ r2_hidden(k4_tarski(C_30,D_33),A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_90,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_83,c_18])).

tff(c_116,plain,(
    ! [A_106,B_107,C_108] :
      ( k1_relset_1(A_106,B_107,C_108) = k1_relat_1(C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_120,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_116])).

tff(c_38,plain,(
    ! [E_78] :
      ( ~ r2_hidden(k4_tarski('#skF_8',E_78),'#skF_7')
      | ~ m1_subset_1(E_78,'#skF_6')
      | ~ r2_hidden('#skF_8',k1_relset_1('#skF_5','#skF_6','#skF_7')) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_131,plain,(
    ! [E_109] :
      ( ~ r2_hidden(k4_tarski('#skF_8',E_109),'#skF_7')
      | ~ m1_subset_1(E_109,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_120,c_38])).

tff(c_134,plain,(
    ~ m1_subset_1('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_83,c_131])).

tff(c_141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_134])).

tff(c_142,plain,(
    r2_hidden('#skF_8',k1_relset_1('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_159,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_142])).

tff(c_16,plain,(
    ! [C_30,A_15] :
      ( r2_hidden(k4_tarski(C_30,'#skF_4'(A_15,k1_relat_1(A_15),C_30)),A_15)
      | ~ r2_hidden(C_30,k1_relat_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_63,plain,(
    ! [C_86,B_87,A_88] :
      ( ~ v1_xboole_0(C_86)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(C_86))
      | ~ r2_hidden(A_88,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_66,plain,(
    ! [A_88] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(A_88,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_32,c_63])).

tff(c_67,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_68,plain,(
    ! [A_89,C_90,B_91] :
      ( m1_subset_1(A_89,C_90)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(C_90))
      | ~ r2_hidden(A_89,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_71,plain,(
    ! [A_89] :
      ( m1_subset_1(A_89,k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(A_89,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_32,c_68])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_78,plain,(
    ! [B_97,D_98,A_99,C_100] :
      ( r2_hidden(B_97,D_98)
      | ~ r2_hidden(k4_tarski(A_99,B_97),k2_zfmisc_1(C_100,D_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_937,plain,(
    ! [B_201,D_202,C_203,A_204] :
      ( r2_hidden(B_201,D_202)
      | v1_xboole_0(k2_zfmisc_1(C_203,D_202))
      | ~ m1_subset_1(k4_tarski(A_204,B_201),k2_zfmisc_1(C_203,D_202)) ) ),
    inference(resolution,[status(thm)],[c_10,c_78])).

tff(c_948,plain,(
    ! [B_201,A_204] :
      ( r2_hidden(B_201,'#skF_6')
      | v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(k4_tarski(A_204,B_201),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_71,c_937])).

tff(c_954,plain,(
    ! [B_205,A_206] :
      ( r2_hidden(B_205,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_206,B_205),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_948])).

tff(c_970,plain,(
    ! [C_207] :
      ( r2_hidden('#skF_4'('#skF_7',k1_relat_1('#skF_7'),C_207),'#skF_6')
      | ~ r2_hidden(C_207,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_16,c_954])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_981,plain,(
    ! [C_208] :
      ( m1_subset_1('#skF_4'('#skF_7',k1_relat_1('#skF_7'),C_208),'#skF_6')
      | ~ r2_hidden(C_208,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_970,c_8])).

tff(c_244,plain,(
    ! [C_134,A_135] :
      ( r2_hidden(k4_tarski(C_134,'#skF_4'(A_135,k1_relat_1(A_135),C_134)),A_135)
      | ~ r2_hidden(C_134,k1_relat_1(A_135)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_143,plain,(
    ~ r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,(
    ! [E_78] :
      ( ~ r2_hidden(k4_tarski('#skF_8',E_78),'#skF_7')
      | ~ m1_subset_1(E_78,'#skF_6')
      | r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_169,plain,(
    ! [E_78] :
      ( ~ r2_hidden(k4_tarski('#skF_8',E_78),'#skF_7')
      | ~ m1_subset_1(E_78,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_42])).

tff(c_253,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_7',k1_relat_1('#skF_7'),'#skF_8'),'#skF_6')
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_244,c_169])).

tff(c_272,plain,(
    ~ m1_subset_1('#skF_4'('#skF_7',k1_relat_1('#skF_7'),'#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_253])).

tff(c_984,plain,(
    ~ r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_981,c_272])).

tff(c_988,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_984])).

tff(c_989,plain,(
    ! [A_88] : ~ r2_hidden(A_88,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_1129,plain,(
    ! [C_243] : ~ r2_hidden(C_243,k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_1105,c_989])).

tff(c_1029,plain,(
    ! [A_226,B_227,C_228] :
      ( k1_relset_1(A_226,B_227,C_228) = k1_relat_1(C_228)
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(A_226,B_227))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1033,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_1029])).

tff(c_991,plain,(
    r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_998,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_989,c_991])).

tff(c_999,plain,(
    r2_hidden('#skF_8',k1_relset_1('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1035,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1033,c_999])).

tff(c_1133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1129,c_1035])).

tff(c_1134,plain,(
    r2_hidden('#skF_8',k1_relset_1('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1187,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1185,c_1134])).

tff(c_1146,plain,(
    ! [C_246,B_247,A_248] :
      ( ~ v1_xboole_0(C_246)
      | ~ m1_subset_1(B_247,k1_zfmisc_1(C_246))
      | ~ r2_hidden(A_248,B_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1149,plain,(
    ! [A_248] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(A_248,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_32,c_1146])).

tff(c_1150,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1149])).

tff(c_1151,plain,(
    ! [A_249,C_250,B_251] :
      ( m1_subset_1(A_249,C_250)
      | ~ m1_subset_1(B_251,k1_zfmisc_1(C_250))
      | ~ r2_hidden(A_249,B_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1154,plain,(
    ! [A_249] :
      ( m1_subset_1(A_249,k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(A_249,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_32,c_1151])).

tff(c_1161,plain,(
    ! [B_257,D_258,A_259,C_260] :
      ( r2_hidden(B_257,D_258)
      | ~ r2_hidden(k4_tarski(A_259,B_257),k2_zfmisc_1(C_260,D_258)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1984,plain,(
    ! [B_354,D_355,C_356,A_357] :
      ( r2_hidden(B_354,D_355)
      | v1_xboole_0(k2_zfmisc_1(C_356,D_355))
      | ~ m1_subset_1(k4_tarski(A_357,B_354),k2_zfmisc_1(C_356,D_355)) ) ),
    inference(resolution,[status(thm)],[c_10,c_1161])).

tff(c_1995,plain,(
    ! [B_354,A_357] :
      ( r2_hidden(B_354,'#skF_6')
      | v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(k4_tarski(A_357,B_354),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1154,c_1984])).

tff(c_2001,plain,(
    ! [B_358,A_359] :
      ( r2_hidden(B_358,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_359,B_358),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1150,c_1995])).

tff(c_2017,plain,(
    ! [C_360] :
      ( r2_hidden('#skF_4'('#skF_7',k1_relat_1('#skF_7'),C_360),'#skF_6')
      | ~ r2_hidden(C_360,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_16,c_2001])).

tff(c_2025,plain,(
    ! [C_361] :
      ( m1_subset_1('#skF_4'('#skF_7',k1_relat_1('#skF_7'),C_361),'#skF_6')
      | ~ r2_hidden(C_361,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_2017,c_8])).

tff(c_1197,plain,(
    ! [C_270,A_271] :
      ( r2_hidden(k4_tarski(C_270,'#skF_4'(A_271,k1_relat_1(A_271),C_270)),A_271)
      | ~ r2_hidden(C_270,k1_relat_1(A_271)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1135,plain,(
    ~ m1_subset_1('#skF_9','#skF_6') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,(
    ! [E_78] :
      ( ~ r2_hidden(k4_tarski('#skF_8',E_78),'#skF_7')
      | ~ m1_subset_1(E_78,'#skF_6')
      | m1_subset_1('#skF_9','#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1140,plain,(
    ! [E_78] :
      ( ~ r2_hidden(k4_tarski('#skF_8',E_78),'#skF_7')
      | ~ m1_subset_1(E_78,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1135,c_46])).

tff(c_1212,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_7',k1_relat_1('#skF_7'),'#skF_8'),'#skF_6')
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_1197,c_1140])).

tff(c_1224,plain,(
    ~ m1_subset_1('#skF_4'('#skF_7',k1_relat_1('#skF_7'),'#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1187,c_1212])).

tff(c_2028,plain,(
    ~ r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_2025,c_1224])).

tff(c_2032,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1187,c_2028])).

tff(c_2033,plain,(
    ! [A_248] : ~ r2_hidden(A_248,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_1149])).

tff(c_2098,plain,(
    ! [C_381] : ~ r2_hidden(C_381,k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_2077,c_2033])).

tff(c_2060,plain,(
    ! [A_378,B_379,C_380] :
      ( k1_relset_1(A_378,B_379,C_380) = k1_relat_1(C_380)
      | ~ m1_subset_1(C_380,k1_zfmisc_1(k2_zfmisc_1(A_378,B_379))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2064,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_2060])).

tff(c_2066,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2064,c_1134])).

tff(c_2102,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2098,c_2066])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:36:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.98/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/1.65  
% 3.98/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/1.65  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1
% 3.98/1.65  
% 3.98/1.65  %Foreground sorts:
% 3.98/1.65  
% 3.98/1.65  
% 3.98/1.65  %Background operators:
% 3.98/1.65  
% 3.98/1.65  
% 3.98/1.65  %Foreground operators:
% 3.98/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.98/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.98/1.65  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.98/1.65  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.98/1.65  tff('#skF_7', type, '#skF_7': $i).
% 3.98/1.65  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.98/1.65  tff('#skF_5', type, '#skF_5': $i).
% 3.98/1.65  tff('#skF_6', type, '#skF_6': $i).
% 3.98/1.65  tff('#skF_9', type, '#skF_9': $i).
% 3.98/1.65  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.98/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.98/1.65  tff('#skF_8', type, '#skF_8': $i).
% 3.98/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.98/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.98/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.98/1.65  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.98/1.65  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.98/1.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.98/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.98/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.98/1.65  
% 3.98/1.67  tff(f_62, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.98/1.67  tff(f_87, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (![D]: (m1_subset_1(D, A) => (r2_hidden(D, k1_relset_1(A, B, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(D, E), C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relset_1)).
% 3.98/1.67  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.98/1.67  tff(f_54, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.98/1.67  tff(f_47, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.98/1.67  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.98/1.67  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.98/1.67  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.98/1.67  tff(c_2077, plain, (![C_381, A_382]: (r2_hidden(k4_tarski(C_381, '#skF_4'(A_382, k1_relat_1(A_382), C_381)), A_382) | ~r2_hidden(C_381, k1_relat_1(A_382)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.98/1.67  tff(c_32, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.98/1.67  tff(c_1181, plain, (![A_267, B_268, C_269]: (k1_relset_1(A_267, B_268, C_269)=k1_relat_1(C_269) | ~m1_subset_1(C_269, k1_zfmisc_1(k2_zfmisc_1(A_267, B_268))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.98/1.67  tff(c_1185, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_32, c_1181])).
% 3.98/1.67  tff(c_1105, plain, (![C_243, A_244]: (r2_hidden(k4_tarski(C_243, '#skF_4'(A_244, k1_relat_1(A_244), C_243)), A_244) | ~r2_hidden(C_243, k1_relat_1(A_244)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.98/1.67  tff(c_153, plain, (![A_110, B_111, C_112]: (k1_relset_1(A_110, B_111, C_112)=k1_relat_1(C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.98/1.67  tff(c_157, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_32, c_153])).
% 3.98/1.67  tff(c_48, plain, (r2_hidden('#skF_8', k1_relset_1('#skF_5', '#skF_6', '#skF_7')) | m1_subset_1('#skF_9', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.98/1.67  tff(c_61, plain, (m1_subset_1('#skF_9', '#skF_6')), inference(splitLeft, [status(thm)], [c_48])).
% 3.98/1.67  tff(c_44, plain, (r2_hidden('#skF_8', k1_relset_1('#skF_5', '#skF_6', '#skF_7')) | r2_hidden(k4_tarski('#skF_8', '#skF_9'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.98/1.67  tff(c_83, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_9'), '#skF_7')), inference(splitLeft, [status(thm)], [c_44])).
% 3.98/1.67  tff(c_18, plain, (![C_30, A_15, D_33]: (r2_hidden(C_30, k1_relat_1(A_15)) | ~r2_hidden(k4_tarski(C_30, D_33), A_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.98/1.67  tff(c_90, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_83, c_18])).
% 3.98/1.67  tff(c_116, plain, (![A_106, B_107, C_108]: (k1_relset_1(A_106, B_107, C_108)=k1_relat_1(C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.98/1.67  tff(c_120, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_32, c_116])).
% 3.98/1.67  tff(c_38, plain, (![E_78]: (~r2_hidden(k4_tarski('#skF_8', E_78), '#skF_7') | ~m1_subset_1(E_78, '#skF_6') | ~r2_hidden('#skF_8', k1_relset_1('#skF_5', '#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.98/1.67  tff(c_131, plain, (![E_109]: (~r2_hidden(k4_tarski('#skF_8', E_109), '#skF_7') | ~m1_subset_1(E_109, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_120, c_38])).
% 3.98/1.67  tff(c_134, plain, (~m1_subset_1('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_83, c_131])).
% 3.98/1.67  tff(c_141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_134])).
% 3.98/1.67  tff(c_142, plain, (r2_hidden('#skF_8', k1_relset_1('#skF_5', '#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_44])).
% 3.98/1.67  tff(c_159, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_142])).
% 3.98/1.67  tff(c_16, plain, (![C_30, A_15]: (r2_hidden(k4_tarski(C_30, '#skF_4'(A_15, k1_relat_1(A_15), C_30)), A_15) | ~r2_hidden(C_30, k1_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.98/1.67  tff(c_63, plain, (![C_86, B_87, A_88]: (~v1_xboole_0(C_86) | ~m1_subset_1(B_87, k1_zfmisc_1(C_86)) | ~r2_hidden(A_88, B_87))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.98/1.67  tff(c_66, plain, (![A_88]: (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6')) | ~r2_hidden(A_88, '#skF_7'))), inference(resolution, [status(thm)], [c_32, c_63])).
% 3.98/1.67  tff(c_67, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_66])).
% 3.98/1.67  tff(c_68, plain, (![A_89, C_90, B_91]: (m1_subset_1(A_89, C_90) | ~m1_subset_1(B_91, k1_zfmisc_1(C_90)) | ~r2_hidden(A_89, B_91))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.98/1.67  tff(c_71, plain, (![A_89]: (m1_subset_1(A_89, k2_zfmisc_1('#skF_5', '#skF_6')) | ~r2_hidden(A_89, '#skF_7'))), inference(resolution, [status(thm)], [c_32, c_68])).
% 3.98/1.67  tff(c_10, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.98/1.67  tff(c_78, plain, (![B_97, D_98, A_99, C_100]: (r2_hidden(B_97, D_98) | ~r2_hidden(k4_tarski(A_99, B_97), k2_zfmisc_1(C_100, D_98)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.98/1.67  tff(c_937, plain, (![B_201, D_202, C_203, A_204]: (r2_hidden(B_201, D_202) | v1_xboole_0(k2_zfmisc_1(C_203, D_202)) | ~m1_subset_1(k4_tarski(A_204, B_201), k2_zfmisc_1(C_203, D_202)))), inference(resolution, [status(thm)], [c_10, c_78])).
% 3.98/1.67  tff(c_948, plain, (![B_201, A_204]: (r2_hidden(B_201, '#skF_6') | v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6')) | ~r2_hidden(k4_tarski(A_204, B_201), '#skF_7'))), inference(resolution, [status(thm)], [c_71, c_937])).
% 3.98/1.67  tff(c_954, plain, (![B_205, A_206]: (r2_hidden(B_205, '#skF_6') | ~r2_hidden(k4_tarski(A_206, B_205), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_67, c_948])).
% 3.98/1.67  tff(c_970, plain, (![C_207]: (r2_hidden('#skF_4'('#skF_7', k1_relat_1('#skF_7'), C_207), '#skF_6') | ~r2_hidden(C_207, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_16, c_954])).
% 3.98/1.67  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(A_5, B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.98/1.67  tff(c_981, plain, (![C_208]: (m1_subset_1('#skF_4'('#skF_7', k1_relat_1('#skF_7'), C_208), '#skF_6') | ~r2_hidden(C_208, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_970, c_8])).
% 3.98/1.67  tff(c_244, plain, (![C_134, A_135]: (r2_hidden(k4_tarski(C_134, '#skF_4'(A_135, k1_relat_1(A_135), C_134)), A_135) | ~r2_hidden(C_134, k1_relat_1(A_135)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.98/1.67  tff(c_143, plain, (~r2_hidden(k4_tarski('#skF_8', '#skF_9'), '#skF_7')), inference(splitRight, [status(thm)], [c_44])).
% 3.98/1.67  tff(c_42, plain, (![E_78]: (~r2_hidden(k4_tarski('#skF_8', E_78), '#skF_7') | ~m1_subset_1(E_78, '#skF_6') | r2_hidden(k4_tarski('#skF_8', '#skF_9'), '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.98/1.67  tff(c_169, plain, (![E_78]: (~r2_hidden(k4_tarski('#skF_8', E_78), '#skF_7') | ~m1_subset_1(E_78, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_143, c_42])).
% 3.98/1.67  tff(c_253, plain, (~m1_subset_1('#skF_4'('#skF_7', k1_relat_1('#skF_7'), '#skF_8'), '#skF_6') | ~r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_244, c_169])).
% 3.98/1.67  tff(c_272, plain, (~m1_subset_1('#skF_4'('#skF_7', k1_relat_1('#skF_7'), '#skF_8'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_253])).
% 3.98/1.67  tff(c_984, plain, (~r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_981, c_272])).
% 3.98/1.67  tff(c_988, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_159, c_984])).
% 3.98/1.67  tff(c_989, plain, (![A_88]: (~r2_hidden(A_88, '#skF_7'))), inference(splitRight, [status(thm)], [c_66])).
% 3.98/1.67  tff(c_1129, plain, (![C_243]: (~r2_hidden(C_243, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_1105, c_989])).
% 3.98/1.67  tff(c_1029, plain, (![A_226, B_227, C_228]: (k1_relset_1(A_226, B_227, C_228)=k1_relat_1(C_228) | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(A_226, B_227))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.98/1.67  tff(c_1033, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_32, c_1029])).
% 3.98/1.67  tff(c_991, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_9'), '#skF_7')), inference(splitLeft, [status(thm)], [c_44])).
% 3.98/1.67  tff(c_998, plain, $false, inference(negUnitSimplification, [status(thm)], [c_989, c_991])).
% 3.98/1.67  tff(c_999, plain, (r2_hidden('#skF_8', k1_relset_1('#skF_5', '#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_44])).
% 3.98/1.67  tff(c_1035, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1033, c_999])).
% 3.98/1.67  tff(c_1133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1129, c_1035])).
% 3.98/1.67  tff(c_1134, plain, (r2_hidden('#skF_8', k1_relset_1('#skF_5', '#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_48])).
% 3.98/1.67  tff(c_1187, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1185, c_1134])).
% 3.98/1.67  tff(c_1146, plain, (![C_246, B_247, A_248]: (~v1_xboole_0(C_246) | ~m1_subset_1(B_247, k1_zfmisc_1(C_246)) | ~r2_hidden(A_248, B_247))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.98/1.67  tff(c_1149, plain, (![A_248]: (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6')) | ~r2_hidden(A_248, '#skF_7'))), inference(resolution, [status(thm)], [c_32, c_1146])).
% 3.98/1.67  tff(c_1150, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_1149])).
% 3.98/1.67  tff(c_1151, plain, (![A_249, C_250, B_251]: (m1_subset_1(A_249, C_250) | ~m1_subset_1(B_251, k1_zfmisc_1(C_250)) | ~r2_hidden(A_249, B_251))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.98/1.67  tff(c_1154, plain, (![A_249]: (m1_subset_1(A_249, k2_zfmisc_1('#skF_5', '#skF_6')) | ~r2_hidden(A_249, '#skF_7'))), inference(resolution, [status(thm)], [c_32, c_1151])).
% 3.98/1.67  tff(c_1161, plain, (![B_257, D_258, A_259, C_260]: (r2_hidden(B_257, D_258) | ~r2_hidden(k4_tarski(A_259, B_257), k2_zfmisc_1(C_260, D_258)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.98/1.67  tff(c_1984, plain, (![B_354, D_355, C_356, A_357]: (r2_hidden(B_354, D_355) | v1_xboole_0(k2_zfmisc_1(C_356, D_355)) | ~m1_subset_1(k4_tarski(A_357, B_354), k2_zfmisc_1(C_356, D_355)))), inference(resolution, [status(thm)], [c_10, c_1161])).
% 3.98/1.67  tff(c_1995, plain, (![B_354, A_357]: (r2_hidden(B_354, '#skF_6') | v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6')) | ~r2_hidden(k4_tarski(A_357, B_354), '#skF_7'))), inference(resolution, [status(thm)], [c_1154, c_1984])).
% 3.98/1.67  tff(c_2001, plain, (![B_358, A_359]: (r2_hidden(B_358, '#skF_6') | ~r2_hidden(k4_tarski(A_359, B_358), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_1150, c_1995])).
% 3.98/1.67  tff(c_2017, plain, (![C_360]: (r2_hidden('#skF_4'('#skF_7', k1_relat_1('#skF_7'), C_360), '#skF_6') | ~r2_hidden(C_360, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_16, c_2001])).
% 3.98/1.67  tff(c_2025, plain, (![C_361]: (m1_subset_1('#skF_4'('#skF_7', k1_relat_1('#skF_7'), C_361), '#skF_6') | ~r2_hidden(C_361, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_2017, c_8])).
% 3.98/1.67  tff(c_1197, plain, (![C_270, A_271]: (r2_hidden(k4_tarski(C_270, '#skF_4'(A_271, k1_relat_1(A_271), C_270)), A_271) | ~r2_hidden(C_270, k1_relat_1(A_271)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.98/1.67  tff(c_1135, plain, (~m1_subset_1('#skF_9', '#skF_6')), inference(splitRight, [status(thm)], [c_48])).
% 3.98/1.67  tff(c_46, plain, (![E_78]: (~r2_hidden(k4_tarski('#skF_8', E_78), '#skF_7') | ~m1_subset_1(E_78, '#skF_6') | m1_subset_1('#skF_9', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.98/1.67  tff(c_1140, plain, (![E_78]: (~r2_hidden(k4_tarski('#skF_8', E_78), '#skF_7') | ~m1_subset_1(E_78, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_1135, c_46])).
% 3.98/1.67  tff(c_1212, plain, (~m1_subset_1('#skF_4'('#skF_7', k1_relat_1('#skF_7'), '#skF_8'), '#skF_6') | ~r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_1197, c_1140])).
% 3.98/1.67  tff(c_1224, plain, (~m1_subset_1('#skF_4'('#skF_7', k1_relat_1('#skF_7'), '#skF_8'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1187, c_1212])).
% 3.98/1.67  tff(c_2028, plain, (~r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_2025, c_1224])).
% 3.98/1.67  tff(c_2032, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1187, c_2028])).
% 3.98/1.67  tff(c_2033, plain, (![A_248]: (~r2_hidden(A_248, '#skF_7'))), inference(splitRight, [status(thm)], [c_1149])).
% 3.98/1.67  tff(c_2098, plain, (![C_381]: (~r2_hidden(C_381, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_2077, c_2033])).
% 3.98/1.67  tff(c_2060, plain, (![A_378, B_379, C_380]: (k1_relset_1(A_378, B_379, C_380)=k1_relat_1(C_380) | ~m1_subset_1(C_380, k1_zfmisc_1(k2_zfmisc_1(A_378, B_379))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.98/1.67  tff(c_2064, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_32, c_2060])).
% 3.98/1.67  tff(c_2066, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2064, c_1134])).
% 3.98/1.67  tff(c_2102, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2098, c_2066])).
% 3.98/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/1.67  
% 3.98/1.67  Inference rules
% 3.98/1.67  ----------------------
% 3.98/1.67  #Ref     : 0
% 3.98/1.67  #Sup     : 460
% 3.98/1.67  #Fact    : 0
% 3.98/1.67  #Define  : 0
% 3.98/1.67  #Split   : 15
% 3.98/1.67  #Chain   : 0
% 3.98/1.67  #Close   : 0
% 3.98/1.67  
% 3.98/1.67  Ordering : KBO
% 3.98/1.67  
% 3.98/1.67  Simplification rules
% 3.98/1.67  ----------------------
% 3.98/1.67  #Subsume      : 30
% 3.98/1.67  #Demod        : 56
% 3.98/1.67  #Tautology    : 52
% 3.98/1.67  #SimpNegUnit  : 15
% 3.98/1.67  #BackRed      : 27
% 3.98/1.67  
% 3.98/1.67  #Partial instantiations: 0
% 3.98/1.67  #Strategies tried      : 1
% 3.98/1.67  
% 3.98/1.67  Timing (in seconds)
% 3.98/1.67  ----------------------
% 3.98/1.68  Preprocessing        : 0.32
% 3.98/1.68  Parsing              : 0.17
% 3.98/1.68  CNF conversion       : 0.03
% 3.98/1.68  Main loop            : 0.65
% 3.98/1.68  Inferencing          : 0.24
% 3.98/1.68  Reduction            : 0.18
% 3.98/1.68  Demodulation         : 0.11
% 3.98/1.68  BG Simplification    : 0.03
% 3.98/1.68  Subsumption          : 0.15
% 3.98/1.68  Abstraction          : 0.03
% 3.98/1.68  MUC search           : 0.00
% 3.98/1.68  Cooper               : 0.00
% 3.98/1.68  Total                : 1.01
% 3.98/1.68  Index Insertion      : 0.00
% 3.98/1.68  Index Deletion       : 0.00
% 3.98/1.68  Index Matching       : 0.00
% 3.98/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
