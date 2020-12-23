%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0836+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:55 EST 2020

% Result     : Theorem 4.74s
% Output     : CNFRefutation 5.08s
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

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_86,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relset_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(c_3026,plain,(
    ! [C_433,A_434] :
      ( r2_hidden(k4_tarski(C_433,'#skF_4'(A_434,k1_relat_1(A_434),C_433)),A_434)
      | ~ r2_hidden(C_433,k1_relat_1(A_434)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1673,plain,(
    ! [A_290,B_291,C_292] :
      ( k1_relset_1(A_290,B_291,C_292) = k1_relat_1(C_292)
      | ~ m1_subset_1(C_292,k1_zfmisc_1(k2_zfmisc_1(A_290,B_291))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1677,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_1673])).

tff(c_1594,plain,(
    ! [C_263,A_264] :
      ( r2_hidden(k4_tarski(C_263,'#skF_4'(A_264,k1_relat_1(A_264),C_263)),A_264)
      | ~ r2_hidden(C_263,k1_relat_1(A_264)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_153,plain,(
    ! [A_110,B_111,C_112] :
      ( k1_relset_1(A_110,B_111,C_112) = k1_relat_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_157,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_153])).

tff(c_48,plain,
    ( r2_hidden('#skF_8',k1_relset_1('#skF_5','#skF_6','#skF_7'))
    | m1_subset_1('#skF_9','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_55,plain,(
    m1_subset_1('#skF_9','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_44,plain,
    ( r2_hidden('#skF_8',k1_relset_1('#skF_5','#skF_6','#skF_7'))
    | r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_83,plain,(
    r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_4,plain,(
    ! [C_16,A_1,D_19] :
      ( r2_hidden(C_16,k1_relat_1(A_1))
      | ~ r2_hidden(k4_tarski(C_16,D_19),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_90,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_83,c_4])).

tff(c_116,plain,(
    ! [A_106,B_107,C_108] :
      ( k1_relset_1(A_106,B_107,C_108) = k1_relat_1(C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_120,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_116])).

tff(c_38,plain,(
    ! [E_78] :
      ( ~ r2_hidden(k4_tarski('#skF_8',E_78),'#skF_7')
      | ~ m1_subset_1(E_78,'#skF_6')
      | ~ r2_hidden('#skF_8',k1_relset_1('#skF_5','#skF_6','#skF_7')) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

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
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_134])).

tff(c_142,plain,(
    r2_hidden('#skF_8',k1_relset_1('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_159,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_142])).

tff(c_2,plain,(
    ! [C_16,A_1] :
      ( r2_hidden(k4_tarski(C_16,'#skF_4'(A_1,k1_relat_1(A_1),C_16)),A_1)
      | ~ r2_hidden(C_16,k1_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_63,plain,(
    ! [C_86,B_87,A_88] :
      ( ~ v1_xboole_0(C_86)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(C_86))
      | ~ r2_hidden(A_88,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

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
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_71,plain,(
    ! [A_89] :
      ( m1_subset_1(A_89,k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(A_89,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_32,c_68])).

tff(c_24,plain,(
    ! [A_29,B_30] :
      ( r2_hidden(A_29,B_30)
      | v1_xboole_0(B_30)
      | ~ m1_subset_1(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_78,plain,(
    ! [B_97,D_98,A_99,C_100] :
      ( r2_hidden(B_97,D_98)
      | ~ r2_hidden(k4_tarski(A_99,B_97),k2_zfmisc_1(C_100,D_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1478,plain,(
    ! [B_235,D_236,C_237,A_238] :
      ( r2_hidden(B_235,D_236)
      | v1_xboole_0(k2_zfmisc_1(C_237,D_236))
      | ~ m1_subset_1(k4_tarski(A_238,B_235),k2_zfmisc_1(C_237,D_236)) ) ),
    inference(resolution,[status(thm)],[c_24,c_78])).

tff(c_1489,plain,(
    ! [B_235,A_238] :
      ( r2_hidden(B_235,'#skF_6')
      | v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(k4_tarski(A_238,B_235),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_71,c_1478])).

tff(c_1495,plain,(
    ! [B_239,A_240] :
      ( r2_hidden(B_239,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_240,B_239),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_1489])).

tff(c_1511,plain,(
    ! [C_241] :
      ( r2_hidden('#skF_4'('#skF_7',k1_relat_1('#skF_7'),C_241),'#skF_6')
      | ~ r2_hidden(C_241,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_2,c_1495])).

tff(c_22,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(A_27,B_28)
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1528,plain,(
    ! [C_242] :
      ( m1_subset_1('#skF_4'('#skF_7',k1_relat_1('#skF_7'),C_242),'#skF_6')
      | ~ r2_hidden(C_242,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_1511,c_22])).

tff(c_206,plain,(
    ! [C_124,A_125] :
      ( r2_hidden(k4_tarski(C_124,'#skF_4'(A_125,k1_relat_1(A_125),C_124)),A_125)
      | ~ r2_hidden(C_124,k1_relat_1(A_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_143,plain,(
    ~ r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,(
    ! [E_78] :
      ( ~ r2_hidden(k4_tarski('#skF_8',E_78),'#skF_7')
      | ~ m1_subset_1(E_78,'#skF_6')
      | r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_169,plain,(
    ! [E_78] :
      ( ~ r2_hidden(k4_tarski('#skF_8',E_78),'#skF_7')
      | ~ m1_subset_1(E_78,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_42])).

tff(c_213,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_7',k1_relat_1('#skF_7'),'#skF_8'),'#skF_6')
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_206,c_169])).

tff(c_231,plain,(
    ~ m1_subset_1('#skF_4'('#skF_7',k1_relat_1('#skF_7'),'#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_213])).

tff(c_1531,plain,(
    ~ r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_1528,c_231])).

tff(c_1535,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_1531])).

tff(c_1536,plain,(
    ! [A_88] : ~ r2_hidden(A_88,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_1615,plain,(
    ! [C_263] : ~ r2_hidden(C_263,k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_1594,c_1536])).

tff(c_1576,plain,(
    ! [A_260,B_261,C_262] :
      ( k1_relset_1(A_260,B_261,C_262) = k1_relat_1(C_262)
      | ~ m1_subset_1(C_262,k1_zfmisc_1(k2_zfmisc_1(A_260,B_261))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1580,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_1576])).

tff(c_1538,plain,(
    r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_1545,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1536,c_1538])).

tff(c_1546,plain,(
    r2_hidden('#skF_8',k1_relset_1('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1582,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1580,c_1546])).

tff(c_1619,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1615,c_1582])).

tff(c_1620,plain,(
    r2_hidden('#skF_8',k1_relset_1('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1679,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1677,c_1620])).

tff(c_1632,plain,(
    ! [C_268,B_269,A_270] :
      ( ~ v1_xboole_0(C_268)
      | ~ m1_subset_1(B_269,k1_zfmisc_1(C_268))
      | ~ r2_hidden(A_270,B_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1635,plain,(
    ! [A_270] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(A_270,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_32,c_1632])).

tff(c_1636,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1635])).

tff(c_1648,plain,(
    ! [A_276,C_277,B_278] :
      ( m1_subset_1(A_276,C_277)
      | ~ m1_subset_1(B_278,k1_zfmisc_1(C_277))
      | ~ r2_hidden(A_276,B_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1651,plain,(
    ! [A_276] :
      ( m1_subset_1(A_276,k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(A_276,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_32,c_1648])).

tff(c_1653,plain,(
    ! [B_280,D_281,A_282,C_283] :
      ( r2_hidden(B_280,D_281)
      | ~ r2_hidden(k4_tarski(A_282,B_280),k2_zfmisc_1(C_283,D_281)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2864,plain,(
    ! [B_403,D_404,C_405,A_406] :
      ( r2_hidden(B_403,D_404)
      | v1_xboole_0(k2_zfmisc_1(C_405,D_404))
      | ~ m1_subset_1(k4_tarski(A_406,B_403),k2_zfmisc_1(C_405,D_404)) ) ),
    inference(resolution,[status(thm)],[c_24,c_1653])).

tff(c_2875,plain,(
    ! [B_403,A_406] :
      ( r2_hidden(B_403,'#skF_6')
      | v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(k4_tarski(A_406,B_403),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1651,c_2864])).

tff(c_2938,plain,(
    ! [B_409,A_410] :
      ( r2_hidden(B_409,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_410,B_409),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1636,c_2875])).

tff(c_2954,plain,(
    ! [C_411] :
      ( r2_hidden('#skF_4'('#skF_7',k1_relat_1('#skF_7'),C_411),'#skF_6')
      | ~ r2_hidden(C_411,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_2,c_2938])).

tff(c_2968,plain,(
    ! [C_412] :
      ( m1_subset_1('#skF_4'('#skF_7',k1_relat_1('#skF_7'),C_412),'#skF_6')
      | ~ r2_hidden(C_412,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_2954,c_22])).

tff(c_1744,plain,(
    ! [C_307,A_308] :
      ( r2_hidden(k4_tarski(C_307,'#skF_4'(A_308,k1_relat_1(A_308),C_307)),A_308)
      | ~ r2_hidden(C_307,k1_relat_1(A_308)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1621,plain,(
    ~ m1_subset_1('#skF_9','#skF_6') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,(
    ! [E_78] :
      ( ~ r2_hidden(k4_tarski('#skF_8',E_78),'#skF_7')
      | ~ m1_subset_1(E_78,'#skF_6')
      | m1_subset_1('#skF_9','#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1637,plain,(
    ! [E_78] :
      ( ~ r2_hidden(k4_tarski('#skF_8',E_78),'#skF_7')
      | ~ m1_subset_1(E_78,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1621,c_46])).

tff(c_1761,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_7',k1_relat_1('#skF_7'),'#skF_8'),'#skF_6')
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_1744,c_1637])).

tff(c_1774,plain,(
    ~ m1_subset_1('#skF_4'('#skF_7',k1_relat_1('#skF_7'),'#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1679,c_1761])).

tff(c_2971,plain,(
    ~ r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_2968,c_1774])).

tff(c_2975,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1679,c_2971])).

tff(c_2976,plain,(
    ! [A_270] : ~ r2_hidden(A_270,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_1635])).

tff(c_3047,plain,(
    ! [C_433] : ~ r2_hidden(C_433,k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_3026,c_2976])).

tff(c_3010,plain,(
    ! [A_430,B_431,C_432] :
      ( k1_relset_1(A_430,B_431,C_432) = k1_relat_1(C_432)
      | ~ m1_subset_1(C_432,k1_zfmisc_1(k2_zfmisc_1(A_430,B_431))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3014,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_3010])).

tff(c_3016,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3014,c_1620])).

tff(c_3051,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3047,c_3016])).

%------------------------------------------------------------------------------
