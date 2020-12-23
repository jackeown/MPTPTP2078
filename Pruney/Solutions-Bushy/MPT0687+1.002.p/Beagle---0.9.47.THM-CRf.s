%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0687+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:42 EST 2020

% Result     : Theorem 24.32s
% Output     : CNFRefutation 24.32s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 160 expanded)
%              Number of leaves         :   32 (  69 expanded)
%              Depth                    :   11
%              Number of atoms          :  135 ( 273 expanded)
%              Number of equality atoms :   36 (  74 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_1 > #skF_13 > #skF_10 > #skF_2 > #skF_8 > #skF_11 > #skF_4 > #skF_3 > #skF_9 > #skF_5 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_59,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_60,plain,
    ( r2_hidden('#skF_12',k2_relat_1('#skF_13'))
    | k10_relat_1('#skF_13',k1_tarski('#skF_12')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_89,plain,(
    k10_relat_1('#skF_13',k1_tarski('#skF_12')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_48,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_62,plain,(
    ! [A_73] :
      ( k1_xboole_0 = A_73
      | ~ v1_xboole_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_66,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_62])).

tff(c_67,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_48])).

tff(c_54,plain,
    ( k10_relat_1('#skF_13',k1_tarski('#skF_12')) = k1_xboole_0
    | ~ r2_hidden('#skF_12',k2_relat_1('#skF_13')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_116,plain,(
    ~ r2_hidden('#skF_12',k2_relat_1('#skF_13')) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_54])).

tff(c_52,plain,(
    v1_relat_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_878,plain,(
    ! [A_141,B_142,C_143] :
      ( r2_hidden('#skF_2'(A_141,B_142,C_143),B_142)
      | r2_hidden('#skF_3'(A_141,B_142,C_143),C_143)
      | k10_relat_1(A_141,B_142) = C_143
      | ~ v1_relat_1(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32,plain,(
    ! [B_51,A_48] :
      ( ~ r2_hidden(B_51,A_48)
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_5975,plain,(
    ! [C_268,A_269,B_270] :
      ( ~ v1_xboole_0(C_268)
      | r2_hidden('#skF_2'(A_269,B_270,C_268),B_270)
      | k10_relat_1(A_269,B_270) = C_268
      | ~ v1_relat_1(A_269) ) ),
    inference(resolution,[status(thm)],[c_878,c_32])).

tff(c_20,plain,(
    ! [C_47,A_43] :
      ( C_47 = A_43
      | ~ r2_hidden(C_47,k1_tarski(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_52968,plain,(
    ! [A_808,A_809,C_810] :
      ( '#skF_2'(A_808,k1_tarski(A_809),C_810) = A_809
      | ~ v1_xboole_0(C_810)
      | k10_relat_1(A_808,k1_tarski(A_809)) = C_810
      | ~ v1_relat_1(A_808) ) ),
    inference(resolution,[status(thm)],[c_5975,c_20])).

tff(c_58594,plain,(
    ! [C_810] :
      ( k1_xboole_0 != C_810
      | '#skF_2'('#skF_13',k1_tarski('#skF_12'),C_810) = '#skF_12'
      | ~ v1_xboole_0(C_810)
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52968,c_89])).

tff(c_58817,plain,(
    ! [C_11087] :
      ( k1_xboole_0 != C_11087
      | '#skF_2'('#skF_13',k1_tarski('#skF_12'),C_11087) = '#skF_12'
      | ~ v1_xboole_0(C_11087) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_58594])).

tff(c_1591,plain,(
    ! [A_174,B_175,C_176] :
      ( r2_hidden(k4_tarski('#skF_1'(A_174,B_175,C_176),'#skF_2'(A_174,B_175,C_176)),A_174)
      | r2_hidden('#skF_3'(A_174,B_175,C_176),C_176)
      | k10_relat_1(A_174,B_175) = C_176
      | ~ v1_relat_1(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_38,plain,(
    ! [C_67,A_52,D_70] :
      ( r2_hidden(C_67,k2_relat_1(A_52))
      | ~ r2_hidden(k4_tarski(D_70,C_67),A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1645,plain,(
    ! [A_174,B_175,C_176] :
      ( r2_hidden('#skF_2'(A_174,B_175,C_176),k2_relat_1(A_174))
      | r2_hidden('#skF_3'(A_174,B_175,C_176),C_176)
      | k10_relat_1(A_174,B_175) = C_176
      | ~ v1_relat_1(A_174) ) ),
    inference(resolution,[status(thm)],[c_1591,c_38])).

tff(c_58835,plain,(
    ! [C_11087] :
      ( r2_hidden('#skF_12',k2_relat_1('#skF_13'))
      | r2_hidden('#skF_3'('#skF_13',k1_tarski('#skF_12'),C_11087),C_11087)
      | k10_relat_1('#skF_13',k1_tarski('#skF_12')) = C_11087
      | ~ v1_relat_1('#skF_13')
      | k1_xboole_0 != C_11087
      | ~ v1_xboole_0(C_11087) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58817,c_1645])).

tff(c_58864,plain,(
    ! [C_11087] :
      ( r2_hidden('#skF_12',k2_relat_1('#skF_13'))
      | r2_hidden('#skF_3'('#skF_13',k1_tarski('#skF_12'),C_11087),C_11087)
      | k10_relat_1('#skF_13',k1_tarski('#skF_12')) = C_11087
      | k1_xboole_0 != C_11087
      | ~ v1_xboole_0(C_11087) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_58835])).

tff(c_60446,plain,(
    ! [C_11156] :
      ( r2_hidden('#skF_3'('#skF_13',k1_tarski('#skF_12'),C_11156),C_11156)
      | k10_relat_1('#skF_13',k1_tarski('#skF_12')) = C_11156
      | k1_xboole_0 != C_11156
      | ~ v1_xboole_0(C_11156) ) ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_58864])).

tff(c_34,plain,(
    ! [A_48] :
      ( v1_xboole_0(A_48)
      | r2_hidden('#skF_7'(A_48),A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_259,plain,(
    ! [A_109,C_110] :
      ( r2_hidden(k4_tarski('#skF_11'(A_109,k2_relat_1(A_109),C_110),C_110),A_109)
      | ~ r2_hidden(C_110,k2_relat_1(A_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_279,plain,(
    ! [A_114,C_115] :
      ( ~ v1_xboole_0(A_114)
      | ~ r2_hidden(C_115,k2_relat_1(A_114)) ) ),
    inference(resolution,[status(thm)],[c_259,c_32])).

tff(c_313,plain,(
    ! [A_116] :
      ( ~ v1_xboole_0(A_116)
      | v1_xboole_0(k2_relat_1(A_116)) ) ),
    inference(resolution,[status(thm)],[c_34,c_279])).

tff(c_50,plain,(
    ! [A_71] :
      ( k1_xboole_0 = A_71
      | ~ v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_329,plain,(
    ! [A_117] :
      ( k2_relat_1(A_117) = k1_xboole_0
      | ~ v1_xboole_0(A_117) ) ),
    inference(resolution,[status(thm)],[c_313,c_50])).

tff(c_337,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_67,c_329])).

tff(c_277,plain,(
    ! [A_109,C_110] :
      ( ~ v1_xboole_0(A_109)
      | ~ r2_hidden(C_110,k2_relat_1(A_109)) ) ),
    inference(resolution,[status(thm)],[c_259,c_32])).

tff(c_369,plain,(
    ! [C_110] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_110,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_277])).

tff(c_378,plain,(
    ! [C_110] : ~ r2_hidden(C_110,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_369])).

tff(c_60612,plain,
    ( k10_relat_1('#skF_13',k1_tarski('#skF_12')) = k1_xboole_0
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_60446,c_378])).

tff(c_60689,plain,(
    k10_relat_1('#skF_13',k1_tarski('#skF_12')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_60612])).

tff(c_60691,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_60689])).

tff(c_60692,plain,(
    r2_hidden('#skF_12',k2_relat_1('#skF_13')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_36,plain,(
    ! [A_52,C_67] :
      ( r2_hidden(k4_tarski('#skF_11'(A_52,k2_relat_1(A_52),C_67),C_67),A_52)
      | ~ r2_hidden(C_67,k2_relat_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_60774,plain,(
    ! [A_11213,C_11214] :
      ( r2_hidden(k4_tarski('#skF_11'(A_11213,k2_relat_1(A_11213),C_11214),C_11214),A_11213)
      | ~ r2_hidden(C_11214,k2_relat_1(A_11213)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_60788,plain,(
    ! [A_11215,C_11216] :
      ( ~ v1_xboole_0(A_11215)
      | ~ r2_hidden(C_11216,k2_relat_1(A_11215)) ) ),
    inference(resolution,[status(thm)],[c_60774,c_32])).

tff(c_60816,plain,(
    ! [A_11217] :
      ( ~ v1_xboole_0(A_11217)
      | v1_xboole_0(k2_relat_1(A_11217)) ) ),
    inference(resolution,[status(thm)],[c_34,c_60788])).

tff(c_60851,plain,(
    ! [A_11220] :
      ( k2_relat_1(A_11220) = k1_xboole_0
      | ~ v1_xboole_0(A_11220) ) ),
    inference(resolution,[status(thm)],[c_60816,c_50])).

tff(c_60859,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_67,c_60851])).

tff(c_60787,plain,(
    ! [A_11213,C_11214] :
      ( ~ v1_xboole_0(A_11213)
      | ~ r2_hidden(C_11214,k2_relat_1(A_11213)) ) ),
    inference(resolution,[status(thm)],[c_60774,c_32])).

tff(c_60866,plain,(
    ! [C_11214] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_11214,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60859,c_60787])).

tff(c_60875,plain,(
    ! [C_11214] : ~ r2_hidden(C_11214,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_60866])).

tff(c_60693,plain,(
    k10_relat_1('#skF_13',k1_tarski('#skF_12')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_22,plain,(
    ! [C_47] : r2_hidden(C_47,k1_tarski(C_47)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_61269,plain,(
    ! [D_11237,A_11238,B_11239,E_11240] :
      ( r2_hidden(D_11237,k10_relat_1(A_11238,B_11239))
      | ~ r2_hidden(E_11240,B_11239)
      | ~ r2_hidden(k4_tarski(D_11237,E_11240),A_11238)
      | ~ v1_relat_1(A_11238) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_69740,plain,(
    ! [D_11439,A_11440,C_11441] :
      ( r2_hidden(D_11439,k10_relat_1(A_11440,k1_tarski(C_11441)))
      | ~ r2_hidden(k4_tarski(D_11439,C_11441),A_11440)
      | ~ v1_relat_1(A_11440) ) ),
    inference(resolution,[status(thm)],[c_22,c_61269])).

tff(c_69804,plain,(
    ! [D_11439] :
      ( r2_hidden(D_11439,k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_11439,'#skF_12'),'#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60693,c_69740])).

tff(c_69825,plain,(
    ! [D_11439] :
      ( r2_hidden(D_11439,k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_11439,'#skF_12'),'#skF_13') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_69804])).

tff(c_69827,plain,(
    ! [D_11442] : ~ r2_hidden(k4_tarski(D_11442,'#skF_12'),'#skF_13') ),
    inference(negUnitSimplification,[status(thm)],[c_60875,c_69825])).

tff(c_69831,plain,(
    ~ r2_hidden('#skF_12',k2_relat_1('#skF_13')) ),
    inference(resolution,[status(thm)],[c_36,c_69827])).

tff(c_69835,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60692,c_69831])).

%------------------------------------------------------------------------------
