%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:39 EST 2020

% Result     : Theorem 4.36s
% Output     : CNFRefutation 4.36s
% Verified   : 
% Statistics : Number of formulae       :  166 (1734 expanded)
%              Number of leaves         :   27 ( 559 expanded)
%              Depth                    :   14
%              Number of atoms          :  248 (3997 expanded)
%              Number of equality atoms :   57 ( 450 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_10 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_55,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ! [E,F] :
            ( r2_hidden(k4_tarski(E,F),k2_zfmisc_1(A,B))
          <=> r2_hidden(k4_tarski(E,F),k2_zfmisc_1(C,D)) )
       => k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ~ ( r1_tarski(A,k2_zfmisc_1(B,C))
        & r2_hidden(D,A)
        & ! [E,F] :
            ~ ( r2_hidden(E,B)
              & r2_hidden(F,C)
              & D = k4_tarski(E,F) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).

tff(f_61,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_38,plain,(
    ! [B_16] : r1_tarski(B_16,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_32,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_4'(A_12,B_13),B_13)
      | r2_hidden('#skF_5'(A_12,B_13),A_12)
      | B_13 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_285,plain,(
    ! [A_87,B_88,C_89,D_90] :
      ( r2_hidden(k4_tarski(A_87,B_88),k2_zfmisc_1(C_89,D_90))
      | ~ r2_hidden(B_88,D_90)
      | ~ r2_hidden(A_87,C_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_58,plain,(
    ! [E_31,F_32] :
      ( r2_hidden(k4_tarski(E_31,F_32),k2_zfmisc_1('#skF_10','#skF_11'))
      | ~ r2_hidden(k4_tarski(E_31,F_32),k2_zfmisc_1('#skF_8','#skF_9')) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_115,plain,(
    ! [B_53,D_54,A_55,C_56] :
      ( r2_hidden(B_53,D_54)
      | ~ r2_hidden(k4_tarski(A_55,B_53),k2_zfmisc_1(C_56,D_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_119,plain,(
    ! [F_32,E_31] :
      ( r2_hidden(F_32,'#skF_11')
      | ~ r2_hidden(k4_tarski(E_31,F_32),k2_zfmisc_1('#skF_8','#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_58,c_115])).

tff(c_308,plain,(
    ! [B_88,A_87] :
      ( r2_hidden(B_88,'#skF_11')
      | ~ r2_hidden(B_88,'#skF_9')
      | ~ r2_hidden(A_87,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_285,c_119])).

tff(c_3006,plain,(
    ! [A_285] : ~ r2_hidden(A_285,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_308])).

tff(c_3040,plain,(
    ! [B_13] :
      ( r2_hidden('#skF_4'('#skF_8',B_13),B_13)
      | B_13 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_32,c_3006])).

tff(c_54,plain,(
    ! [A_23,B_24,C_25,D_26] :
      ( r2_hidden('#skF_6'(A_23,B_24,C_25,D_26),B_24)
      | ~ r2_hidden(D_26,A_23)
      | ~ r1_tarski(A_23,k2_zfmisc_1(B_24,C_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3223,plain,(
    ! [D_302,A_303,C_304] :
      ( ~ r2_hidden(D_302,A_303)
      | ~ r1_tarski(A_303,k2_zfmisc_1('#skF_8',C_304)) ) ),
    inference(resolution,[status(thm)],[c_54,c_3006])).

tff(c_3263,plain,(
    ! [B_305,C_306] :
      ( ~ r1_tarski(B_305,k2_zfmisc_1('#skF_8',C_306))
      | B_305 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_3040,c_3223])).

tff(c_3279,plain,(
    ! [C_306] : k2_zfmisc_1('#skF_8',C_306) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_38,c_3263])).

tff(c_120,plain,(
    ! [A_57,C_58,B_59,D_60] :
      ( r2_hidden(A_57,C_58)
      | ~ r2_hidden(k4_tarski(A_57,B_59),k2_zfmisc_1(C_58,D_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_124,plain,(
    ! [E_31,F_32] :
      ( r2_hidden(E_31,'#skF_10')
      | ~ r2_hidden(k4_tarski(E_31,F_32),k2_zfmisc_1('#skF_8','#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_58,c_120])).

tff(c_307,plain,(
    ! [A_87,B_88] :
      ( r2_hidden(A_87,'#skF_10')
      | ~ r2_hidden(B_88,'#skF_9')
      | ~ r2_hidden(A_87,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_285,c_124])).

tff(c_381,plain,(
    ! [B_99] : ~ r2_hidden(B_99,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_307])).

tff(c_405,plain,(
    ! [B_13] :
      ( r2_hidden('#skF_4'('#skF_9',B_13),B_13)
      | B_13 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_32,c_381])).

tff(c_462,plain,(
    ! [A_102,B_103,C_104,D_105] :
      ( r2_hidden('#skF_7'(A_102,B_103,C_104,D_105),C_104)
      | ~ r2_hidden(D_105,A_102)
      | ~ r1_tarski(A_102,k2_zfmisc_1(B_103,C_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_380,plain,(
    ! [B_88] : ~ r2_hidden(B_88,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_307])).

tff(c_772,plain,(
    ! [D_131,A_132,B_133] :
      ( ~ r2_hidden(D_131,A_132)
      | ~ r1_tarski(A_132,k2_zfmisc_1(B_133,'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_462,c_380])).

tff(c_806,plain,(
    ! [B_134,B_135] :
      ( ~ r1_tarski(B_134,k2_zfmisc_1(B_135,'#skF_9'))
      | B_134 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_405,c_772])).

tff(c_825,plain,(
    ! [B_135] : k2_zfmisc_1(B_135,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_38,c_806])).

tff(c_578,plain,(
    ! [A_111,B_112,C_113,D_114] :
      ( r2_hidden('#skF_6'(A_111,B_112,C_113,D_114),B_112)
      | ~ r2_hidden(D_114,A_111)
      | ~ r1_tarski(A_111,k2_zfmisc_1(B_112,C_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_646,plain,(
    ! [D_120,A_121,C_122] :
      ( ~ r2_hidden(D_120,A_121)
      | ~ r1_tarski(A_121,k2_zfmisc_1('#skF_9',C_122)) ) ),
    inference(resolution,[status(thm)],[c_578,c_380])).

tff(c_686,plain,(
    ! [B_126,C_127] :
      ( ~ r1_tarski(B_126,k2_zfmisc_1('#skF_9',C_127))
      | B_126 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_405,c_646])).

tff(c_702,plain,(
    ! [C_127] : k2_zfmisc_1('#skF_9',C_127) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_38,c_686])).

tff(c_60,plain,(
    ! [E_31,F_32] :
      ( r2_hidden(k4_tarski(E_31,F_32),k2_zfmisc_1('#skF_8','#skF_9'))
      | ~ r2_hidden(k4_tarski(E_31,F_32),k2_zfmisc_1('#skF_10','#skF_11')) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_501,plain,(
    ! [A_107,B_108] :
      ( r2_hidden(k4_tarski(A_107,B_108),k2_zfmisc_1('#skF_8','#skF_9'))
      | ~ r2_hidden(B_108,'#skF_11')
      | ~ r2_hidden(A_107,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_285,c_60])).

tff(c_46,plain,(
    ! [B_20,D_22,A_19,C_21] :
      ( r2_hidden(B_20,D_22)
      | ~ r2_hidden(k4_tarski(A_19,B_20),k2_zfmisc_1(C_21,D_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_513,plain,(
    ! [B_108,A_107] :
      ( r2_hidden(B_108,'#skF_9')
      | ~ r2_hidden(B_108,'#skF_11')
      | ~ r2_hidden(A_107,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_501,c_46])).

tff(c_521,plain,(
    ! [B_108,A_107] :
      ( ~ r2_hidden(B_108,'#skF_11')
      | ~ r2_hidden(A_107,'#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_380,c_513])).

tff(c_525,plain,(
    ! [A_109] : ~ r2_hidden(A_109,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_521])).

tff(c_558,plain,(
    ! [B_110] : r1_tarski('#skF_10',B_110) ),
    inference(resolution,[status(thm)],[c_6,c_525])).

tff(c_409,plain,(
    ! [B_100] : r1_tarski('#skF_9',B_100) ),
    inference(resolution,[status(thm)],[c_6,c_381])).

tff(c_42,plain,(
    ! [A_18] :
      ( k1_xboole_0 = A_18
      | ~ r1_tarski(A_18,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_422,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_409,c_42])).

tff(c_428,plain,(
    ! [A_18] :
      ( A_18 = '#skF_9'
      | ~ r1_tarski(A_18,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_422,c_42])).

tff(c_565,plain,(
    '#skF_10' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_558,c_428])).

tff(c_56,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != k2_zfmisc_1('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_571,plain,(
    k2_zfmisc_1('#skF_9','#skF_11') != k2_zfmisc_1('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_565,c_56])).

tff(c_705,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_702,c_571])).

tff(c_831,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_825,c_705])).

tff(c_853,plain,(
    ! [B_140] : ~ r2_hidden(B_140,'#skF_11') ),
    inference(splitRight,[status(thm)],[c_521])).

tff(c_891,plain,(
    ! [B_141] : r1_tarski('#skF_11',B_141) ),
    inference(resolution,[status(thm)],[c_6,c_853])).

tff(c_898,plain,(
    '#skF_11' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_891,c_428])).

tff(c_887,plain,(
    ! [B_13] :
      ( r2_hidden('#skF_4'('#skF_11',B_13),B_13)
      | B_13 = '#skF_11' ) ),
    inference(resolution,[status(thm)],[c_32,c_853])).

tff(c_970,plain,(
    ! [B_13] :
      ( r2_hidden('#skF_4'('#skF_9',B_13),B_13)
      | B_13 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_898,c_898,c_887])).

tff(c_52,plain,(
    ! [A_23,B_24,C_25,D_26] :
      ( r2_hidden('#skF_7'(A_23,B_24,C_25,D_26),C_25)
      | ~ r2_hidden(D_26,A_23)
      | ~ r1_tarski(A_23,k2_zfmisc_1(B_24,C_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_885,plain,(
    ! [D_26,A_23,B_24] :
      ( ~ r2_hidden(D_26,A_23)
      | ~ r1_tarski(A_23,k2_zfmisc_1(B_24,'#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_52,c_853])).

tff(c_1145,plain,(
    ! [D_163,A_164,B_165] :
      ( ~ r2_hidden(D_163,A_164)
      | ~ r1_tarski(A_164,k2_zfmisc_1(B_165,'#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_898,c_885])).

tff(c_1185,plain,(
    ! [B_166,B_167] :
      ( ~ r1_tarski(B_166,k2_zfmisc_1(B_167,'#skF_9'))
      | B_166 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_970,c_1145])).

tff(c_1204,plain,(
    ! [B_167] : k2_zfmisc_1(B_167,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_38,c_1185])).

tff(c_904,plain,(
    k2_zfmisc_1('#skF_10','#skF_9') != k2_zfmisc_1('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_898,c_56])).

tff(c_1211,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1204,c_1204,c_904])).

tff(c_1240,plain,(
    ! [A_170] :
      ( r2_hidden(A_170,'#skF_10')
      | ~ r2_hidden(A_170,'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_307])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1291,plain,(
    ! [A_172] :
      ( r1_tarski(A_172,'#skF_10')
      | ~ r2_hidden('#skF_1'(A_172,'#skF_10'),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1240,c_4])).

tff(c_1306,plain,(
    r1_tarski('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_6,c_1291])).

tff(c_34,plain,(
    ! [B_16,A_15] :
      ( B_16 = A_15
      | ~ r1_tarski(B_16,A_15)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1309,plain,
    ( '#skF_10' = '#skF_8'
    | ~ r1_tarski('#skF_10','#skF_8') ),
    inference(resolution,[status(thm)],[c_1306,c_34])).

tff(c_1336,plain,(
    ~ r1_tarski('#skF_10','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1309])).

tff(c_1213,plain,(
    ! [A_168,B_169] :
      ( r2_hidden(k4_tarski(A_168,B_169),k2_zfmisc_1('#skF_8','#skF_9'))
      | ~ r2_hidden(B_169,'#skF_11')
      | ~ r2_hidden(A_168,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_285,c_60])).

tff(c_48,plain,(
    ! [A_19,C_21,B_20,D_22] :
      ( r2_hidden(A_19,C_21)
      | ~ r2_hidden(k4_tarski(A_19,B_20),k2_zfmisc_1(C_21,D_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1237,plain,(
    ! [A_168,B_169] :
      ( r2_hidden(A_168,'#skF_8')
      | ~ r2_hidden(B_169,'#skF_11')
      | ~ r2_hidden(A_168,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_1213,c_48])).

tff(c_2165,plain,(
    ! [B_169] : ~ r2_hidden(B_169,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_1237])).

tff(c_1359,plain,(
    ! [A_183] : ~ r2_hidden(A_183,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_308])).

tff(c_1388,plain,(
    ! [B_13] :
      ( r2_hidden('#skF_4'('#skF_8',B_13),B_13)
      | B_13 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_32,c_1359])).

tff(c_1898,plain,(
    ! [D_218,A_219,B_220] :
      ( ~ r2_hidden(D_218,A_219)
      | ~ r1_tarski(A_219,k2_zfmisc_1(B_220,'#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_52,c_1359])).

tff(c_1938,plain,(
    ! [B_221,B_222] :
      ( ~ r1_tarski(B_221,k2_zfmisc_1(B_222,'#skF_8'))
      | B_221 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_1388,c_1898])).

tff(c_1957,plain,(
    ! [B_222] : k2_zfmisc_1(B_222,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_38,c_1938])).

tff(c_1419,plain,(
    ! [A_185,B_186,C_187,D_188] :
      ( r2_hidden('#skF_6'(A_185,B_186,C_187,D_188),B_186)
      | ~ r2_hidden(D_188,A_185)
      | ~ r1_tarski(A_185,k2_zfmisc_1(B_186,C_187)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1358,plain,(
    ! [A_87] : ~ r2_hidden(A_87,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_308])).

tff(c_1749,plain,(
    ! [D_205,A_206,C_207] :
      ( ~ r2_hidden(D_205,A_206)
      | ~ r1_tarski(A_206,k2_zfmisc_1('#skF_8',C_207)) ) ),
    inference(resolution,[status(thm)],[c_1419,c_1358])).

tff(c_1796,plain,(
    ! [B_210,C_211] :
      ( ~ r1_tarski(B_210,k2_zfmisc_1('#skF_8',C_211))
      | B_210 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_1388,c_1749])).

tff(c_1812,plain,(
    ! [C_211] : k2_zfmisc_1('#skF_8',C_211) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_38,c_1796])).

tff(c_1593,plain,(
    ! [B_198] :
      ( r2_hidden('#skF_4'('#skF_8',B_198),B_198)
      | B_198 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_32,c_1359])).

tff(c_1238,plain,(
    ! [B_169,A_168] :
      ( r2_hidden(B_169,'#skF_9')
      | ~ r2_hidden(B_169,'#skF_11')
      | ~ r2_hidden(A_168,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_1213,c_46])).

tff(c_1489,plain,(
    ! [A_191] : ~ r2_hidden(A_191,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_1238])).

tff(c_1526,plain,(
    ! [B_2] : r1_tarski('#skF_10',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_1489])).

tff(c_1531,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1526,c_1336])).

tff(c_1532,plain,(
    ! [B_169] :
      ( r2_hidden(B_169,'#skF_9')
      | ~ r2_hidden(B_169,'#skF_11') ) ),
    inference(splitRight,[status(thm)],[c_1238])).

tff(c_1615,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_11'),'#skF_9')
    | '#skF_11' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1593,c_1532])).

tff(c_1622,plain,(
    '#skF_11' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1615])).

tff(c_1696,plain,(
    k2_zfmisc_1('#skF_10','#skF_8') != k2_zfmisc_1('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1622,c_56])).

tff(c_1816,plain,(
    k2_zfmisc_1('#skF_10','#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1812,c_1696])).

tff(c_1963,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1957,c_1816])).

tff(c_1965,plain,(
    '#skF_11' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1615])).

tff(c_1391,plain,(
    ! [B_2] : r1_tarski('#skF_8',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_1359])).

tff(c_1966,plain,(
    ! [B_169,A_168] :
      ( ~ r2_hidden(B_169,'#skF_11')
      | ~ r2_hidden(A_168,'#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1358,c_1237])).

tff(c_1969,plain,(
    ! [A_223] : ~ r2_hidden(A_223,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_1966])).

tff(c_2004,plain,(
    '#skF_10' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1388,c_1969])).

tff(c_2015,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2004,c_1336])).

tff(c_2023,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1391,c_2015])).

tff(c_2026,plain,(
    ! [B_224] : ~ r2_hidden(B_224,'#skF_11') ),
    inference(splitRight,[status(thm)],[c_1966])).

tff(c_2030,plain,(
    '#skF_11' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1388,c_2026])).

tff(c_2064,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1965,c_2030])).

tff(c_2065,plain,(
    ! [B_88] :
      ( r2_hidden(B_88,'#skF_11')
      | ~ r2_hidden(B_88,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_308])).

tff(c_2206,plain,(
    ! [B_233] : ~ r2_hidden(B_233,'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_2165,c_2065])).

tff(c_2243,plain,(
    ! [B_2] : r1_tarski('#skF_9',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_2206])).

tff(c_2168,plain,(
    ! [B_232] : ~ r2_hidden(B_232,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_1237])).

tff(c_2244,plain,(
    ! [B_234] : r1_tarski('#skF_11',B_234) ),
    inference(resolution,[status(thm)],[c_6,c_2168])).

tff(c_2257,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_2244,c_42])).

tff(c_2326,plain,(
    ! [A_244] :
      ( A_244 = '#skF_11'
      | ~ r1_tarski(A_244,'#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2257,c_2257,c_42])).

tff(c_2348,plain,(
    '#skF_11' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_2243,c_2326])).

tff(c_2202,plain,(
    ! [B_13] :
      ( r2_hidden('#skF_4'('#skF_11',B_13),B_13)
      | B_13 = '#skF_11' ) ),
    inference(resolution,[status(thm)],[c_32,c_2168])).

tff(c_2488,plain,(
    ! [B_13] :
      ( r2_hidden('#skF_4'('#skF_9',B_13),B_13)
      | B_13 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2348,c_2348,c_2202])).

tff(c_2200,plain,(
    ! [D_26,A_23,B_24] :
      ( ~ r2_hidden(D_26,A_23)
      | ~ r1_tarski(A_23,k2_zfmisc_1(B_24,'#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_52,c_2168])).

tff(c_2669,plain,(
    ! [D_266,A_267,B_268] :
      ( ~ r2_hidden(D_266,A_267)
      | ~ r1_tarski(A_267,k2_zfmisc_1(B_268,'#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2348,c_2200])).

tff(c_2713,plain,(
    ! [B_269,B_270] :
      ( ~ r1_tarski(B_269,k2_zfmisc_1(B_270,'#skF_9'))
      | B_269 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_2488,c_2669])).

tff(c_2732,plain,(
    ! [B_270] : k2_zfmisc_1(B_270,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_38,c_2713])).

tff(c_2360,plain,(
    k2_zfmisc_1('#skF_10','#skF_9') != k2_zfmisc_1('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2348,c_56])).

tff(c_2739,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2732,c_2732,c_2360])).

tff(c_2765,plain,(
    ! [A_275] :
      ( r2_hidden(A_275,'#skF_8')
      | ~ r2_hidden(A_275,'#skF_10') ) ),
    inference(splitRight,[status(thm)],[c_1237])).

tff(c_2942,plain,(
    ! [B_280] :
      ( r2_hidden('#skF_1'('#skF_10',B_280),'#skF_8')
      | r1_tarski('#skF_10',B_280) ) ),
    inference(resolution,[status(thm)],[c_6,c_2765])).

tff(c_2954,plain,(
    r1_tarski('#skF_10','#skF_8') ),
    inference(resolution,[status(thm)],[c_2942,c_4])).

tff(c_2962,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1336,c_1336,c_2954])).

tff(c_2963,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1309])).

tff(c_2995,plain,(
    k2_zfmisc_1('#skF_8','#skF_11') != k2_zfmisc_1('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2963,c_56])).

tff(c_3285,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3279,c_3279,c_2995])).

tff(c_3293,plain,(
    ! [B_309] :
      ( r2_hidden(B_309,'#skF_11')
      | ~ r2_hidden(B_309,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_308])).

tff(c_3354,plain,(
    ! [A_311] :
      ( r1_tarski(A_311,'#skF_11')
      | ~ r2_hidden('#skF_1'(A_311,'#skF_11'),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_3293,c_4])).

tff(c_3369,plain,(
    r1_tarski('#skF_9','#skF_11') ),
    inference(resolution,[status(thm)],[c_6,c_3354])).

tff(c_3372,plain,
    ( '#skF_11' = '#skF_9'
    | ~ r1_tarski('#skF_11','#skF_9') ),
    inference(resolution,[status(thm)],[c_3369,c_34])).

tff(c_3426,plain,(
    ~ r1_tarski('#skF_11','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_3372])).

tff(c_3459,plain,(
    ! [B_169,A_168] :
      ( r2_hidden(B_169,'#skF_9')
      | ~ r2_hidden(B_169,'#skF_11')
      | ~ r2_hidden(A_168,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2963,c_1238])).

tff(c_3461,plain,(
    ! [A_320] : ~ r2_hidden(A_320,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_3459])).

tff(c_3502,plain,(
    ! [B_13] :
      ( r2_hidden('#skF_4'('#skF_8',B_13),B_13)
      | B_13 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_32,c_3461])).

tff(c_3802,plain,(
    ! [D_344,A_345,C_346] :
      ( ~ r2_hidden(D_344,A_345)
      | ~ r1_tarski(A_345,k2_zfmisc_1('#skF_8',C_346)) ) ),
    inference(resolution,[status(thm)],[c_54,c_3461])).

tff(c_3848,plain,(
    ! [B_347,C_348] :
      ( ~ r1_tarski(B_347,k2_zfmisc_1('#skF_8',C_348))
      | B_347 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_3502,c_3802])).

tff(c_3867,plain,(
    ! [C_348] : k2_zfmisc_1('#skF_8',C_348) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_38,c_3848])).

tff(c_3907,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3867,c_3867,c_2995])).

tff(c_3909,plain,(
    ! [B_353] :
      ( r2_hidden(B_353,'#skF_9')
      | ~ r2_hidden(B_353,'#skF_11') ) ),
    inference(splitRight,[status(thm)],[c_3459])).

tff(c_3958,plain,(
    ! [B_354] :
      ( r2_hidden('#skF_1'('#skF_11',B_354),'#skF_9')
      | r1_tarski('#skF_11',B_354) ) ),
    inference(resolution,[status(thm)],[c_6,c_3909])).

tff(c_3970,plain,(
    r1_tarski('#skF_11','#skF_9') ),
    inference(resolution,[status(thm)],[c_3958,c_4])).

tff(c_3978,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3426,c_3426,c_3970])).

tff(c_3979,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_3372])).

tff(c_4011,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3979,c_2995])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:31:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.36/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.36/1.80  
% 4.36/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.36/1.80  %$ r2_hidden > r1_tarski > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_10 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 4.36/1.80  
% 4.36/1.80  %Foreground sorts:
% 4.36/1.80  
% 4.36/1.80  
% 4.36/1.80  %Background operators:
% 4.36/1.80  
% 4.36/1.80  
% 4.36/1.80  %Foreground operators:
% 4.36/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.36/1.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.36/1.80  tff('#skF_11', type, '#skF_11': $i).
% 4.36/1.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.36/1.80  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.36/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.36/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.36/1.80  tff('#skF_10', type, '#skF_10': $i).
% 4.36/1.80  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.36/1.80  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 4.36/1.80  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 4.36/1.80  tff('#skF_9', type, '#skF_9': $i).
% 4.36/1.80  tff('#skF_8', type, '#skF_8': $i).
% 4.36/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.36/1.80  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.36/1.80  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.36/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.36/1.80  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.36/1.80  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.36/1.80  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.36/1.80  
% 4.36/1.83  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.36/1.83  tff(f_55, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.36/1.83  tff(f_49, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 4.36/1.83  tff(f_67, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 4.36/1.83  tff(f_88, negated_conjecture, ~(![A, B, C, D]: ((![E, F]: (r2_hidden(k4_tarski(E, F), k2_zfmisc_1(A, B)) <=> r2_hidden(k4_tarski(E, F), k2_zfmisc_1(C, D)))) => (k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_zfmisc_1)).
% 4.36/1.83  tff(f_80, axiom, (![A, B, C, D]: ~((r1_tarski(A, k2_zfmisc_1(B, C)) & r2_hidden(D, A)) & (![E, F]: ~((r2_hidden(E, B) & r2_hidden(F, C)) & (D = k4_tarski(E, F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_zfmisc_1)).
% 4.36/1.83  tff(f_61, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 4.36/1.83  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.36/1.83  tff(c_38, plain, (![B_16]: (r1_tarski(B_16, B_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.36/1.83  tff(c_32, plain, (![A_12, B_13]: (r2_hidden('#skF_4'(A_12, B_13), B_13) | r2_hidden('#skF_5'(A_12, B_13), A_12) | B_13=A_12)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.36/1.83  tff(c_285, plain, (![A_87, B_88, C_89, D_90]: (r2_hidden(k4_tarski(A_87, B_88), k2_zfmisc_1(C_89, D_90)) | ~r2_hidden(B_88, D_90) | ~r2_hidden(A_87, C_89))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.36/1.83  tff(c_58, plain, (![E_31, F_32]: (r2_hidden(k4_tarski(E_31, F_32), k2_zfmisc_1('#skF_10', '#skF_11')) | ~r2_hidden(k4_tarski(E_31, F_32), k2_zfmisc_1('#skF_8', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.36/1.83  tff(c_115, plain, (![B_53, D_54, A_55, C_56]: (r2_hidden(B_53, D_54) | ~r2_hidden(k4_tarski(A_55, B_53), k2_zfmisc_1(C_56, D_54)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.36/1.83  tff(c_119, plain, (![F_32, E_31]: (r2_hidden(F_32, '#skF_11') | ~r2_hidden(k4_tarski(E_31, F_32), k2_zfmisc_1('#skF_8', '#skF_9')))), inference(resolution, [status(thm)], [c_58, c_115])).
% 4.36/1.83  tff(c_308, plain, (![B_88, A_87]: (r2_hidden(B_88, '#skF_11') | ~r2_hidden(B_88, '#skF_9') | ~r2_hidden(A_87, '#skF_8'))), inference(resolution, [status(thm)], [c_285, c_119])).
% 4.36/1.83  tff(c_3006, plain, (![A_285]: (~r2_hidden(A_285, '#skF_8'))), inference(splitLeft, [status(thm)], [c_308])).
% 4.36/1.83  tff(c_3040, plain, (![B_13]: (r2_hidden('#skF_4'('#skF_8', B_13), B_13) | B_13='#skF_8')), inference(resolution, [status(thm)], [c_32, c_3006])).
% 4.36/1.83  tff(c_54, plain, (![A_23, B_24, C_25, D_26]: (r2_hidden('#skF_6'(A_23, B_24, C_25, D_26), B_24) | ~r2_hidden(D_26, A_23) | ~r1_tarski(A_23, k2_zfmisc_1(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.36/1.83  tff(c_3223, plain, (![D_302, A_303, C_304]: (~r2_hidden(D_302, A_303) | ~r1_tarski(A_303, k2_zfmisc_1('#skF_8', C_304)))), inference(resolution, [status(thm)], [c_54, c_3006])).
% 4.36/1.83  tff(c_3263, plain, (![B_305, C_306]: (~r1_tarski(B_305, k2_zfmisc_1('#skF_8', C_306)) | B_305='#skF_8')), inference(resolution, [status(thm)], [c_3040, c_3223])).
% 4.36/1.83  tff(c_3279, plain, (![C_306]: (k2_zfmisc_1('#skF_8', C_306)='#skF_8')), inference(resolution, [status(thm)], [c_38, c_3263])).
% 4.36/1.83  tff(c_120, plain, (![A_57, C_58, B_59, D_60]: (r2_hidden(A_57, C_58) | ~r2_hidden(k4_tarski(A_57, B_59), k2_zfmisc_1(C_58, D_60)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.36/1.83  tff(c_124, plain, (![E_31, F_32]: (r2_hidden(E_31, '#skF_10') | ~r2_hidden(k4_tarski(E_31, F_32), k2_zfmisc_1('#skF_8', '#skF_9')))), inference(resolution, [status(thm)], [c_58, c_120])).
% 4.36/1.83  tff(c_307, plain, (![A_87, B_88]: (r2_hidden(A_87, '#skF_10') | ~r2_hidden(B_88, '#skF_9') | ~r2_hidden(A_87, '#skF_8'))), inference(resolution, [status(thm)], [c_285, c_124])).
% 4.36/1.83  tff(c_381, plain, (![B_99]: (~r2_hidden(B_99, '#skF_9'))), inference(splitLeft, [status(thm)], [c_307])).
% 4.36/1.83  tff(c_405, plain, (![B_13]: (r2_hidden('#skF_4'('#skF_9', B_13), B_13) | B_13='#skF_9')), inference(resolution, [status(thm)], [c_32, c_381])).
% 4.36/1.83  tff(c_462, plain, (![A_102, B_103, C_104, D_105]: (r2_hidden('#skF_7'(A_102, B_103, C_104, D_105), C_104) | ~r2_hidden(D_105, A_102) | ~r1_tarski(A_102, k2_zfmisc_1(B_103, C_104)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.36/1.83  tff(c_380, plain, (![B_88]: (~r2_hidden(B_88, '#skF_9'))), inference(splitLeft, [status(thm)], [c_307])).
% 4.36/1.83  tff(c_772, plain, (![D_131, A_132, B_133]: (~r2_hidden(D_131, A_132) | ~r1_tarski(A_132, k2_zfmisc_1(B_133, '#skF_9')))), inference(resolution, [status(thm)], [c_462, c_380])).
% 4.36/1.83  tff(c_806, plain, (![B_134, B_135]: (~r1_tarski(B_134, k2_zfmisc_1(B_135, '#skF_9')) | B_134='#skF_9')), inference(resolution, [status(thm)], [c_405, c_772])).
% 4.36/1.83  tff(c_825, plain, (![B_135]: (k2_zfmisc_1(B_135, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_38, c_806])).
% 4.36/1.83  tff(c_578, plain, (![A_111, B_112, C_113, D_114]: (r2_hidden('#skF_6'(A_111, B_112, C_113, D_114), B_112) | ~r2_hidden(D_114, A_111) | ~r1_tarski(A_111, k2_zfmisc_1(B_112, C_113)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.36/1.83  tff(c_646, plain, (![D_120, A_121, C_122]: (~r2_hidden(D_120, A_121) | ~r1_tarski(A_121, k2_zfmisc_1('#skF_9', C_122)))), inference(resolution, [status(thm)], [c_578, c_380])).
% 4.36/1.83  tff(c_686, plain, (![B_126, C_127]: (~r1_tarski(B_126, k2_zfmisc_1('#skF_9', C_127)) | B_126='#skF_9')), inference(resolution, [status(thm)], [c_405, c_646])).
% 4.36/1.83  tff(c_702, plain, (![C_127]: (k2_zfmisc_1('#skF_9', C_127)='#skF_9')), inference(resolution, [status(thm)], [c_38, c_686])).
% 4.36/1.83  tff(c_60, plain, (![E_31, F_32]: (r2_hidden(k4_tarski(E_31, F_32), k2_zfmisc_1('#skF_8', '#skF_9')) | ~r2_hidden(k4_tarski(E_31, F_32), k2_zfmisc_1('#skF_10', '#skF_11')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.36/1.83  tff(c_501, plain, (![A_107, B_108]: (r2_hidden(k4_tarski(A_107, B_108), k2_zfmisc_1('#skF_8', '#skF_9')) | ~r2_hidden(B_108, '#skF_11') | ~r2_hidden(A_107, '#skF_10'))), inference(resolution, [status(thm)], [c_285, c_60])).
% 4.36/1.83  tff(c_46, plain, (![B_20, D_22, A_19, C_21]: (r2_hidden(B_20, D_22) | ~r2_hidden(k4_tarski(A_19, B_20), k2_zfmisc_1(C_21, D_22)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.36/1.83  tff(c_513, plain, (![B_108, A_107]: (r2_hidden(B_108, '#skF_9') | ~r2_hidden(B_108, '#skF_11') | ~r2_hidden(A_107, '#skF_10'))), inference(resolution, [status(thm)], [c_501, c_46])).
% 4.36/1.83  tff(c_521, plain, (![B_108, A_107]: (~r2_hidden(B_108, '#skF_11') | ~r2_hidden(A_107, '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_380, c_513])).
% 4.36/1.83  tff(c_525, plain, (![A_109]: (~r2_hidden(A_109, '#skF_10'))), inference(splitLeft, [status(thm)], [c_521])).
% 4.36/1.83  tff(c_558, plain, (![B_110]: (r1_tarski('#skF_10', B_110))), inference(resolution, [status(thm)], [c_6, c_525])).
% 4.36/1.83  tff(c_409, plain, (![B_100]: (r1_tarski('#skF_9', B_100))), inference(resolution, [status(thm)], [c_6, c_381])).
% 4.36/1.83  tff(c_42, plain, (![A_18]: (k1_xboole_0=A_18 | ~r1_tarski(A_18, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.36/1.83  tff(c_422, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_409, c_42])).
% 4.36/1.83  tff(c_428, plain, (![A_18]: (A_18='#skF_9' | ~r1_tarski(A_18, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_422, c_422, c_42])).
% 4.36/1.83  tff(c_565, plain, ('#skF_10'='#skF_9'), inference(resolution, [status(thm)], [c_558, c_428])).
% 4.36/1.83  tff(c_56, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!=k2_zfmisc_1('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.36/1.83  tff(c_571, plain, (k2_zfmisc_1('#skF_9', '#skF_11')!=k2_zfmisc_1('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_565, c_56])).
% 4.36/1.83  tff(c_705, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_702, c_571])).
% 4.36/1.83  tff(c_831, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_825, c_705])).
% 4.36/1.83  tff(c_853, plain, (![B_140]: (~r2_hidden(B_140, '#skF_11'))), inference(splitRight, [status(thm)], [c_521])).
% 4.36/1.83  tff(c_891, plain, (![B_141]: (r1_tarski('#skF_11', B_141))), inference(resolution, [status(thm)], [c_6, c_853])).
% 4.36/1.83  tff(c_898, plain, ('#skF_11'='#skF_9'), inference(resolution, [status(thm)], [c_891, c_428])).
% 4.36/1.83  tff(c_887, plain, (![B_13]: (r2_hidden('#skF_4'('#skF_11', B_13), B_13) | B_13='#skF_11')), inference(resolution, [status(thm)], [c_32, c_853])).
% 4.36/1.83  tff(c_970, plain, (![B_13]: (r2_hidden('#skF_4'('#skF_9', B_13), B_13) | B_13='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_898, c_898, c_887])).
% 4.36/1.83  tff(c_52, plain, (![A_23, B_24, C_25, D_26]: (r2_hidden('#skF_7'(A_23, B_24, C_25, D_26), C_25) | ~r2_hidden(D_26, A_23) | ~r1_tarski(A_23, k2_zfmisc_1(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.36/1.83  tff(c_885, plain, (![D_26, A_23, B_24]: (~r2_hidden(D_26, A_23) | ~r1_tarski(A_23, k2_zfmisc_1(B_24, '#skF_11')))), inference(resolution, [status(thm)], [c_52, c_853])).
% 4.36/1.83  tff(c_1145, plain, (![D_163, A_164, B_165]: (~r2_hidden(D_163, A_164) | ~r1_tarski(A_164, k2_zfmisc_1(B_165, '#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_898, c_885])).
% 4.36/1.83  tff(c_1185, plain, (![B_166, B_167]: (~r1_tarski(B_166, k2_zfmisc_1(B_167, '#skF_9')) | B_166='#skF_9')), inference(resolution, [status(thm)], [c_970, c_1145])).
% 4.36/1.83  tff(c_1204, plain, (![B_167]: (k2_zfmisc_1(B_167, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_38, c_1185])).
% 4.36/1.83  tff(c_904, plain, (k2_zfmisc_1('#skF_10', '#skF_9')!=k2_zfmisc_1('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_898, c_56])).
% 4.36/1.83  tff(c_1211, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1204, c_1204, c_904])).
% 4.36/1.83  tff(c_1240, plain, (![A_170]: (r2_hidden(A_170, '#skF_10') | ~r2_hidden(A_170, '#skF_8'))), inference(splitRight, [status(thm)], [c_307])).
% 4.36/1.83  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.36/1.83  tff(c_1291, plain, (![A_172]: (r1_tarski(A_172, '#skF_10') | ~r2_hidden('#skF_1'(A_172, '#skF_10'), '#skF_8'))), inference(resolution, [status(thm)], [c_1240, c_4])).
% 4.36/1.83  tff(c_1306, plain, (r1_tarski('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_6, c_1291])).
% 4.36/1.83  tff(c_34, plain, (![B_16, A_15]: (B_16=A_15 | ~r1_tarski(B_16, A_15) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.36/1.83  tff(c_1309, plain, ('#skF_10'='#skF_8' | ~r1_tarski('#skF_10', '#skF_8')), inference(resolution, [status(thm)], [c_1306, c_34])).
% 4.36/1.83  tff(c_1336, plain, (~r1_tarski('#skF_10', '#skF_8')), inference(splitLeft, [status(thm)], [c_1309])).
% 4.36/1.83  tff(c_1213, plain, (![A_168, B_169]: (r2_hidden(k4_tarski(A_168, B_169), k2_zfmisc_1('#skF_8', '#skF_9')) | ~r2_hidden(B_169, '#skF_11') | ~r2_hidden(A_168, '#skF_10'))), inference(resolution, [status(thm)], [c_285, c_60])).
% 4.36/1.83  tff(c_48, plain, (![A_19, C_21, B_20, D_22]: (r2_hidden(A_19, C_21) | ~r2_hidden(k4_tarski(A_19, B_20), k2_zfmisc_1(C_21, D_22)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.36/1.83  tff(c_1237, plain, (![A_168, B_169]: (r2_hidden(A_168, '#skF_8') | ~r2_hidden(B_169, '#skF_11') | ~r2_hidden(A_168, '#skF_10'))), inference(resolution, [status(thm)], [c_1213, c_48])).
% 4.36/1.83  tff(c_2165, plain, (![B_169]: (~r2_hidden(B_169, '#skF_11'))), inference(splitLeft, [status(thm)], [c_1237])).
% 4.36/1.83  tff(c_1359, plain, (![A_183]: (~r2_hidden(A_183, '#skF_8'))), inference(splitLeft, [status(thm)], [c_308])).
% 4.36/1.83  tff(c_1388, plain, (![B_13]: (r2_hidden('#skF_4'('#skF_8', B_13), B_13) | B_13='#skF_8')), inference(resolution, [status(thm)], [c_32, c_1359])).
% 4.36/1.83  tff(c_1898, plain, (![D_218, A_219, B_220]: (~r2_hidden(D_218, A_219) | ~r1_tarski(A_219, k2_zfmisc_1(B_220, '#skF_8')))), inference(resolution, [status(thm)], [c_52, c_1359])).
% 4.36/1.83  tff(c_1938, plain, (![B_221, B_222]: (~r1_tarski(B_221, k2_zfmisc_1(B_222, '#skF_8')) | B_221='#skF_8')), inference(resolution, [status(thm)], [c_1388, c_1898])).
% 4.36/1.83  tff(c_1957, plain, (![B_222]: (k2_zfmisc_1(B_222, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_38, c_1938])).
% 4.36/1.83  tff(c_1419, plain, (![A_185, B_186, C_187, D_188]: (r2_hidden('#skF_6'(A_185, B_186, C_187, D_188), B_186) | ~r2_hidden(D_188, A_185) | ~r1_tarski(A_185, k2_zfmisc_1(B_186, C_187)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.36/1.83  tff(c_1358, plain, (![A_87]: (~r2_hidden(A_87, '#skF_8'))), inference(splitLeft, [status(thm)], [c_308])).
% 4.36/1.83  tff(c_1749, plain, (![D_205, A_206, C_207]: (~r2_hidden(D_205, A_206) | ~r1_tarski(A_206, k2_zfmisc_1('#skF_8', C_207)))), inference(resolution, [status(thm)], [c_1419, c_1358])).
% 4.36/1.83  tff(c_1796, plain, (![B_210, C_211]: (~r1_tarski(B_210, k2_zfmisc_1('#skF_8', C_211)) | B_210='#skF_8')), inference(resolution, [status(thm)], [c_1388, c_1749])).
% 4.36/1.83  tff(c_1812, plain, (![C_211]: (k2_zfmisc_1('#skF_8', C_211)='#skF_8')), inference(resolution, [status(thm)], [c_38, c_1796])).
% 4.36/1.83  tff(c_1593, plain, (![B_198]: (r2_hidden('#skF_4'('#skF_8', B_198), B_198) | B_198='#skF_8')), inference(resolution, [status(thm)], [c_32, c_1359])).
% 4.36/1.83  tff(c_1238, plain, (![B_169, A_168]: (r2_hidden(B_169, '#skF_9') | ~r2_hidden(B_169, '#skF_11') | ~r2_hidden(A_168, '#skF_10'))), inference(resolution, [status(thm)], [c_1213, c_46])).
% 4.36/1.83  tff(c_1489, plain, (![A_191]: (~r2_hidden(A_191, '#skF_10'))), inference(splitLeft, [status(thm)], [c_1238])).
% 4.36/1.83  tff(c_1526, plain, (![B_2]: (r1_tarski('#skF_10', B_2))), inference(resolution, [status(thm)], [c_6, c_1489])).
% 4.36/1.83  tff(c_1531, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1526, c_1336])).
% 4.36/1.83  tff(c_1532, plain, (![B_169]: (r2_hidden(B_169, '#skF_9') | ~r2_hidden(B_169, '#skF_11'))), inference(splitRight, [status(thm)], [c_1238])).
% 4.36/1.83  tff(c_1615, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_11'), '#skF_9') | '#skF_11'='#skF_8'), inference(resolution, [status(thm)], [c_1593, c_1532])).
% 4.36/1.83  tff(c_1622, plain, ('#skF_11'='#skF_8'), inference(splitLeft, [status(thm)], [c_1615])).
% 4.36/1.83  tff(c_1696, plain, (k2_zfmisc_1('#skF_10', '#skF_8')!=k2_zfmisc_1('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1622, c_56])).
% 4.36/1.83  tff(c_1816, plain, (k2_zfmisc_1('#skF_10', '#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1812, c_1696])).
% 4.36/1.83  tff(c_1963, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1957, c_1816])).
% 4.36/1.83  tff(c_1965, plain, ('#skF_11'!='#skF_8'), inference(splitRight, [status(thm)], [c_1615])).
% 4.36/1.83  tff(c_1391, plain, (![B_2]: (r1_tarski('#skF_8', B_2))), inference(resolution, [status(thm)], [c_6, c_1359])).
% 4.36/1.83  tff(c_1966, plain, (![B_169, A_168]: (~r2_hidden(B_169, '#skF_11') | ~r2_hidden(A_168, '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_1358, c_1237])).
% 4.36/1.83  tff(c_1969, plain, (![A_223]: (~r2_hidden(A_223, '#skF_10'))), inference(splitLeft, [status(thm)], [c_1966])).
% 4.36/1.83  tff(c_2004, plain, ('#skF_10'='#skF_8'), inference(resolution, [status(thm)], [c_1388, c_1969])).
% 4.36/1.83  tff(c_2015, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2004, c_1336])).
% 4.36/1.83  tff(c_2023, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1391, c_2015])).
% 4.36/1.83  tff(c_2026, plain, (![B_224]: (~r2_hidden(B_224, '#skF_11'))), inference(splitRight, [status(thm)], [c_1966])).
% 4.36/1.83  tff(c_2030, plain, ('#skF_11'='#skF_8'), inference(resolution, [status(thm)], [c_1388, c_2026])).
% 4.36/1.83  tff(c_2064, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1965, c_2030])).
% 4.36/1.83  tff(c_2065, plain, (![B_88]: (r2_hidden(B_88, '#skF_11') | ~r2_hidden(B_88, '#skF_9'))), inference(splitRight, [status(thm)], [c_308])).
% 4.36/1.83  tff(c_2206, plain, (![B_233]: (~r2_hidden(B_233, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_2165, c_2065])).
% 4.36/1.83  tff(c_2243, plain, (![B_2]: (r1_tarski('#skF_9', B_2))), inference(resolution, [status(thm)], [c_6, c_2206])).
% 4.36/1.83  tff(c_2168, plain, (![B_232]: (~r2_hidden(B_232, '#skF_11'))), inference(splitLeft, [status(thm)], [c_1237])).
% 4.36/1.83  tff(c_2244, plain, (![B_234]: (r1_tarski('#skF_11', B_234))), inference(resolution, [status(thm)], [c_6, c_2168])).
% 4.36/1.83  tff(c_2257, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_2244, c_42])).
% 4.36/1.83  tff(c_2326, plain, (![A_244]: (A_244='#skF_11' | ~r1_tarski(A_244, '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_2257, c_2257, c_42])).
% 4.36/1.83  tff(c_2348, plain, ('#skF_11'='#skF_9'), inference(resolution, [status(thm)], [c_2243, c_2326])).
% 4.36/1.83  tff(c_2202, plain, (![B_13]: (r2_hidden('#skF_4'('#skF_11', B_13), B_13) | B_13='#skF_11')), inference(resolution, [status(thm)], [c_32, c_2168])).
% 4.36/1.83  tff(c_2488, plain, (![B_13]: (r2_hidden('#skF_4'('#skF_9', B_13), B_13) | B_13='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2348, c_2348, c_2202])).
% 4.36/1.83  tff(c_2200, plain, (![D_26, A_23, B_24]: (~r2_hidden(D_26, A_23) | ~r1_tarski(A_23, k2_zfmisc_1(B_24, '#skF_11')))), inference(resolution, [status(thm)], [c_52, c_2168])).
% 4.36/1.83  tff(c_2669, plain, (![D_266, A_267, B_268]: (~r2_hidden(D_266, A_267) | ~r1_tarski(A_267, k2_zfmisc_1(B_268, '#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_2348, c_2200])).
% 4.36/1.83  tff(c_2713, plain, (![B_269, B_270]: (~r1_tarski(B_269, k2_zfmisc_1(B_270, '#skF_9')) | B_269='#skF_9')), inference(resolution, [status(thm)], [c_2488, c_2669])).
% 4.36/1.83  tff(c_2732, plain, (![B_270]: (k2_zfmisc_1(B_270, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_38, c_2713])).
% 4.36/1.83  tff(c_2360, plain, (k2_zfmisc_1('#skF_10', '#skF_9')!=k2_zfmisc_1('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2348, c_56])).
% 4.36/1.83  tff(c_2739, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2732, c_2732, c_2360])).
% 4.36/1.83  tff(c_2765, plain, (![A_275]: (r2_hidden(A_275, '#skF_8') | ~r2_hidden(A_275, '#skF_10'))), inference(splitRight, [status(thm)], [c_1237])).
% 4.36/1.83  tff(c_2942, plain, (![B_280]: (r2_hidden('#skF_1'('#skF_10', B_280), '#skF_8') | r1_tarski('#skF_10', B_280))), inference(resolution, [status(thm)], [c_6, c_2765])).
% 4.36/1.83  tff(c_2954, plain, (r1_tarski('#skF_10', '#skF_8')), inference(resolution, [status(thm)], [c_2942, c_4])).
% 4.36/1.83  tff(c_2962, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1336, c_1336, c_2954])).
% 4.36/1.83  tff(c_2963, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_1309])).
% 4.36/1.83  tff(c_2995, plain, (k2_zfmisc_1('#skF_8', '#skF_11')!=k2_zfmisc_1('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2963, c_56])).
% 4.36/1.83  tff(c_3285, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3279, c_3279, c_2995])).
% 4.36/1.83  tff(c_3293, plain, (![B_309]: (r2_hidden(B_309, '#skF_11') | ~r2_hidden(B_309, '#skF_9'))), inference(splitRight, [status(thm)], [c_308])).
% 4.36/1.83  tff(c_3354, plain, (![A_311]: (r1_tarski(A_311, '#skF_11') | ~r2_hidden('#skF_1'(A_311, '#skF_11'), '#skF_9'))), inference(resolution, [status(thm)], [c_3293, c_4])).
% 4.36/1.83  tff(c_3369, plain, (r1_tarski('#skF_9', '#skF_11')), inference(resolution, [status(thm)], [c_6, c_3354])).
% 4.36/1.83  tff(c_3372, plain, ('#skF_11'='#skF_9' | ~r1_tarski('#skF_11', '#skF_9')), inference(resolution, [status(thm)], [c_3369, c_34])).
% 4.36/1.83  tff(c_3426, plain, (~r1_tarski('#skF_11', '#skF_9')), inference(splitLeft, [status(thm)], [c_3372])).
% 4.36/1.83  tff(c_3459, plain, (![B_169, A_168]: (r2_hidden(B_169, '#skF_9') | ~r2_hidden(B_169, '#skF_11') | ~r2_hidden(A_168, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2963, c_1238])).
% 4.36/1.83  tff(c_3461, plain, (![A_320]: (~r2_hidden(A_320, '#skF_8'))), inference(splitLeft, [status(thm)], [c_3459])).
% 4.36/1.83  tff(c_3502, plain, (![B_13]: (r2_hidden('#skF_4'('#skF_8', B_13), B_13) | B_13='#skF_8')), inference(resolution, [status(thm)], [c_32, c_3461])).
% 4.36/1.83  tff(c_3802, plain, (![D_344, A_345, C_346]: (~r2_hidden(D_344, A_345) | ~r1_tarski(A_345, k2_zfmisc_1('#skF_8', C_346)))), inference(resolution, [status(thm)], [c_54, c_3461])).
% 4.36/1.83  tff(c_3848, plain, (![B_347, C_348]: (~r1_tarski(B_347, k2_zfmisc_1('#skF_8', C_348)) | B_347='#skF_8')), inference(resolution, [status(thm)], [c_3502, c_3802])).
% 4.36/1.83  tff(c_3867, plain, (![C_348]: (k2_zfmisc_1('#skF_8', C_348)='#skF_8')), inference(resolution, [status(thm)], [c_38, c_3848])).
% 4.36/1.83  tff(c_3907, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3867, c_3867, c_2995])).
% 4.36/1.83  tff(c_3909, plain, (![B_353]: (r2_hidden(B_353, '#skF_9') | ~r2_hidden(B_353, '#skF_11'))), inference(splitRight, [status(thm)], [c_3459])).
% 4.36/1.83  tff(c_3958, plain, (![B_354]: (r2_hidden('#skF_1'('#skF_11', B_354), '#skF_9') | r1_tarski('#skF_11', B_354))), inference(resolution, [status(thm)], [c_6, c_3909])).
% 4.36/1.83  tff(c_3970, plain, (r1_tarski('#skF_11', '#skF_9')), inference(resolution, [status(thm)], [c_3958, c_4])).
% 4.36/1.83  tff(c_3978, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3426, c_3426, c_3970])).
% 4.36/1.83  tff(c_3979, plain, ('#skF_11'='#skF_9'), inference(splitRight, [status(thm)], [c_3372])).
% 4.36/1.83  tff(c_4011, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3979, c_2995])).
% 4.36/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.36/1.83  
% 4.36/1.83  Inference rules
% 4.36/1.83  ----------------------
% 4.36/1.83  #Ref     : 0
% 4.36/1.83  #Sup     : 832
% 4.36/1.83  #Fact    : 0
% 4.36/1.83  #Define  : 0
% 4.36/1.83  #Split   : 16
% 4.36/1.83  #Chain   : 0
% 4.36/1.83  #Close   : 0
% 4.36/1.83  
% 4.36/1.83  Ordering : KBO
% 4.36/1.83  
% 4.36/1.83  Simplification rules
% 4.36/1.83  ----------------------
% 4.36/1.83  #Subsume      : 214
% 4.36/1.83  #Demod        : 336
% 4.36/1.83  #Tautology    : 198
% 4.36/1.83  #SimpNegUnit  : 52
% 4.36/1.83  #BackRed      : 147
% 4.36/1.83  
% 4.36/1.83  #Partial instantiations: 0
% 4.36/1.83  #Strategies tried      : 1
% 4.58/1.83  
% 4.58/1.83  Timing (in seconds)
% 4.58/1.83  ----------------------
% 4.58/1.83  Preprocessing        : 0.31
% 4.58/1.83  Parsing              : 0.16
% 4.58/1.83  CNF conversion       : 0.03
% 4.58/1.83  Main loop            : 0.73
% 4.58/1.83  Inferencing          : 0.25
% 4.58/1.83  Reduction            : 0.20
% 4.58/1.83  Demodulation         : 0.13
% 4.58/1.83  BG Simplification    : 0.04
% 4.58/1.83  Subsumption          : 0.16
% 4.58/1.83  Abstraction          : 0.03
% 4.58/1.83  MUC search           : 0.00
% 4.58/1.83  Cooper               : 0.00
% 4.58/1.83  Total                : 1.09
% 4.58/1.83  Index Insertion      : 0.00
% 4.58/1.83  Index Deletion       : 0.00
% 4.58/1.83  Index Matching       : 0.00
% 4.58/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
