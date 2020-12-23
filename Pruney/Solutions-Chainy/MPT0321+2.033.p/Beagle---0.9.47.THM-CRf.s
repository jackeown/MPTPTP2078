%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:17 EST 2020

% Result     : Theorem 5.37s
% Output     : CNFRefutation 5.65s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 720 expanded)
%              Number of leaves         :   29 ( 243 expanded)
%              Depth                    :   13
%              Number of atoms          :  227 (1577 expanded)
%              Number of equality atoms :   54 ( 468 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k3_tarski > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_74,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_54,plain,
    ( '#skF_10' != '#skF_8'
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_68,plain,(
    '#skF_7' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_60,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') = k2_zfmisc_1('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_126,plain,(
    ! [A_66,C_67,B_68] :
      ( r1_tarski(k2_zfmisc_1(A_66,C_67),k2_zfmisc_1(B_68,C_67))
      | ~ r1_tarski(A_66,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_131,plain,(
    ! [B_68] :
      ( r1_tarski(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1(B_68,'#skF_8'))
      | ~ r1_tarski('#skF_7',B_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_126])).

tff(c_303,plain,(
    ! [A_102,B_103,C_104] :
      ( ~ r1_tarski(k2_zfmisc_1(A_102,B_103),k2_zfmisc_1(A_102,C_104))
      | r1_tarski(B_103,C_104)
      | k1_xboole_0 = A_102 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_329,plain,
    ( r1_tarski('#skF_10','#skF_8')
    | k1_xboole_0 = '#skF_9'
    | ~ r1_tarski('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_131,c_303])).

tff(c_375,plain,(
    ~ r1_tarski('#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_329])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_48,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_30,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),A_9)
      | r2_hidden('#skF_4'(A_9,B_10),B_10)
      | k3_tarski(A_9) = B_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_214,plain,(
    ! [A_90,C_91] :
      ( r2_hidden('#skF_5'(A_90,k3_tarski(A_90),C_91),A_90)
      | ~ r2_hidden(C_91,k3_tarski(A_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_225,plain,(
    ! [C_91] :
      ( r2_hidden('#skF_5'(k1_xboole_0,k1_xboole_0,C_91),k1_xboole_0)
      | ~ r2_hidden(C_91,k3_tarski(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_214])).

tff(c_252,plain,(
    ! [C_93] :
      ( r2_hidden('#skF_5'(k1_xboole_0,k1_xboole_0,C_93),k1_xboole_0)
      | ~ r2_hidden(C_93,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_225])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_256,plain,(
    ! [C_93,B_2] :
      ( r2_hidden('#skF_5'(k1_xboole_0,k1_xboole_0,C_93),B_2)
      | ~ r1_tarski(k1_xboole_0,B_2)
      | ~ r2_hidden(C_93,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_252,c_2])).

tff(c_261,plain,(
    ! [C_93,B_2] :
      ( r2_hidden('#skF_5'(k1_xboole_0,k1_xboole_0,C_93),B_2)
      | ~ r2_hidden(C_93,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_256])).

tff(c_262,plain,(
    ! [C_94,B_95] :
      ( r2_hidden('#skF_5'(k1_xboole_0,k1_xboole_0,C_94),B_95)
      | ~ r2_hidden(C_94,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_256])).

tff(c_50,plain,(
    ! [D_44,A_38,B_39] :
      ( ~ r2_hidden(D_44,'#skF_6'(A_38,B_39))
      | ~ r2_hidden(D_44,B_39)
      | ~ r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1638,plain,(
    ! [C_190,B_191,A_192] :
      ( ~ r2_hidden('#skF_5'(k1_xboole_0,k1_xboole_0,C_190),B_191)
      | ~ r2_hidden(A_192,B_191)
      | ~ r2_hidden(C_190,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_262,c_50])).

tff(c_1647,plain,(
    ! [A_192,B_2,C_93] :
      ( ~ r2_hidden(A_192,B_2)
      | ~ r2_hidden(C_93,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_261,c_1638])).

tff(c_1652,plain,(
    ! [C_193] : ~ r2_hidden(C_193,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1647])).

tff(c_1656,plain,(
    ! [B_10] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_10),B_10)
      | k3_tarski(k1_xboole_0) = B_10 ) ),
    inference(resolution,[status(thm)],[c_30,c_1652])).

tff(c_1680,plain,(
    ! [B_10] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_10),B_10)
      | k1_xboole_0 = B_10 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1656])).

tff(c_1688,plain,(
    ! [A_194,B_195,C_196,D_197] :
      ( r2_hidden(k4_tarski(A_194,B_195),k2_zfmisc_1(C_196,D_197))
      | ~ r2_hidden(B_195,D_197)
      | ~ r2_hidden(A_194,C_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1764,plain,(
    ! [A_202,B_203] :
      ( r2_hidden(k4_tarski(A_202,B_203),k2_zfmisc_1('#skF_9','#skF_10'))
      | ~ r2_hidden(B_203,'#skF_8')
      | ~ r2_hidden(A_202,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_1688])).

tff(c_38,plain,(
    ! [A_28,C_30,B_29,D_31] :
      ( r2_hidden(A_28,C_30)
      | ~ r2_hidden(k4_tarski(A_28,B_29),k2_zfmisc_1(C_30,D_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1789,plain,(
    ! [A_202,B_203] :
      ( r2_hidden(A_202,'#skF_9')
      | ~ r2_hidden(B_203,'#skF_8')
      | ~ r2_hidden(A_202,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1764,c_38])).

tff(c_2629,plain,(
    ! [B_246] : ~ r2_hidden(B_246,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1789])).

tff(c_2633,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1680,c_2629])).

tff(c_2663,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2633])).

tff(c_2665,plain,(
    ! [A_247] :
      ( r2_hidden(A_247,'#skF_9')
      | ~ r2_hidden(A_247,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_1789])).

tff(c_2877,plain,(
    ! [B_254] :
      ( r2_hidden('#skF_1'('#skF_7',B_254),'#skF_9')
      | r1_tarski('#skF_7',B_254) ) ),
    inference(resolution,[status(thm)],[c_6,c_2665])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2892,plain,(
    r1_tarski('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_2877,c_4])).

tff(c_2901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_375,c_375,c_2892])).

tff(c_2902,plain,(
    ! [A_192,B_2] : ~ r2_hidden(A_192,B_2) ),
    inference(splitRight,[status(thm)],[c_1647])).

tff(c_2964,plain,(
    ! [A_261] : k3_tarski(A_261) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_2902,c_2902,c_30])).

tff(c_2936,plain,(
    ! [A_9,B_10] : k3_tarski(A_9) = B_10 ),
    inference(negUnitSimplification,[status(thm)],[c_2902,c_2902,c_30])).

tff(c_3124,plain,(
    ! [B_816] : B_816 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_2964,c_2936])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3256,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_3124,c_58])).

tff(c_3258,plain,(
    r1_tarski('#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_329])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3282,plain,
    ( '#skF_7' = '#skF_9'
    | ~ r1_tarski('#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_3258,c_8])).

tff(c_3285,plain,(
    ~ r1_tarski('#skF_9','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3282])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3520,plain,(
    ! [C_1394,B_1395,A_1396] :
      ( ~ r2_hidden('#skF_5'(k1_xboole_0,k1_xboole_0,C_1394),B_1395)
      | ~ r2_hidden(A_1396,B_1395)
      | ~ r2_hidden(C_1394,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_262,c_50])).

tff(c_3529,plain,(
    ! [A_1396,B_2,C_93] :
      ( ~ r2_hidden(A_1396,B_2)
      | ~ r2_hidden(C_93,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_261,c_3520])).

tff(c_3534,plain,(
    ! [C_1397] : ~ r2_hidden(C_1397,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_3529])).

tff(c_3538,plain,(
    ! [B_10] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_10),B_10)
      | k3_tarski(k1_xboole_0) = B_10 ) ),
    inference(resolution,[status(thm)],[c_30,c_3534])).

tff(c_3562,plain,(
    ! [B_10] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_10),B_10)
      | k1_xboole_0 = B_10 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3538])).

tff(c_3603,plain,(
    ! [A_1400,B_1401,C_1402,D_1403] :
      ( r2_hidden(k4_tarski(A_1400,B_1401),k2_zfmisc_1(C_1402,D_1403))
      | ~ r2_hidden(B_1401,D_1403)
      | ~ r2_hidden(A_1400,C_1402) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_112,plain,(
    ! [A_59,C_60,B_61,D_62] :
      ( r2_hidden(A_59,C_60)
      | ~ r2_hidden(k4_tarski(A_59,B_61),k2_zfmisc_1(C_60,D_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_115,plain,(
    ! [A_59,B_61] :
      ( r2_hidden(A_59,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_59,B_61),k2_zfmisc_1('#skF_9','#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_112])).

tff(c_3629,plain,(
    ! [A_1400,B_1401] :
      ( r2_hidden(A_1400,'#skF_7')
      | ~ r2_hidden(B_1401,'#skF_10')
      | ~ r2_hidden(A_1400,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_3603,c_115])).

tff(c_4098,plain,(
    ! [B_1428] : ~ r2_hidden(B_1428,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_3629])).

tff(c_4129,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_3562,c_4098])).

tff(c_4223,plain,(
    '#skF_7' != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4129,c_58])).

tff(c_3993,plain,(
    ! [B_1401] : ~ r2_hidden(B_1401,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_3629])).

tff(c_3676,plain,(
    ! [A_1407,B_1408] :
      ( r2_hidden(k4_tarski(A_1407,B_1408),k2_zfmisc_1('#skF_9','#skF_10'))
      | ~ r2_hidden(B_1408,'#skF_8')
      | ~ r2_hidden(A_1407,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_3603])).

tff(c_36,plain,(
    ! [B_29,D_31,A_28,C_30] :
      ( r2_hidden(B_29,D_31)
      | ~ r2_hidden(k4_tarski(A_28,B_29),k2_zfmisc_1(C_30,D_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3699,plain,(
    ! [B_1408,A_1407] :
      ( r2_hidden(B_1408,'#skF_10')
      | ~ r2_hidden(B_1408,'#skF_8')
      | ~ r2_hidden(A_1407,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_3676,c_36])).

tff(c_4302,plain,(
    ! [B_1408,A_1407] :
      ( ~ r2_hidden(B_1408,'#skF_8')
      | ~ r2_hidden(A_1407,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_3993,c_3699])).

tff(c_4305,plain,(
    ! [A_1440] : ~ r2_hidden(A_1440,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_4302])).

tff(c_4346,plain,(
    ! [B_1441] : r1_tarski('#skF_7',B_1441) ),
    inference(resolution,[status(thm)],[c_6,c_4305])).

tff(c_4229,plain,(
    ! [B_1434] : r1_tarski('#skF_10',B_1434) ),
    inference(resolution,[status(thm)],[c_6,c_4098])).

tff(c_4232,plain,(
    ! [B_1434] :
      ( B_1434 = '#skF_10'
      | ~ r1_tarski(B_1434,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_4229,c_8])).

tff(c_4350,plain,(
    '#skF_7' = '#skF_10' ),
    inference(resolution,[status(thm)],[c_4346,c_4232])).

tff(c_4356,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4223,c_4350])).

tff(c_4359,plain,(
    ! [B_1442] : ~ r2_hidden(B_1442,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_4302])).

tff(c_4390,plain,(
    ! [B_2] : r1_tarski('#skF_8',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_4359])).

tff(c_3257,plain,
    ( k1_xboole_0 = '#skF_9'
    | r1_tarski('#skF_10','#skF_8') ),
    inference(splitRight,[status(thm)],[c_329])).

tff(c_3286,plain,(
    r1_tarski('#skF_10','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_3257])).

tff(c_3289,plain,
    ( '#skF_10' = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_3286,c_8])).

tff(c_3290,plain,(
    ~ r1_tarski('#skF_8','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_3289])).

tff(c_4397,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4390,c_3290])).

tff(c_4399,plain,(
    ! [A_1443] :
      ( r2_hidden(A_1443,'#skF_7')
      | ~ r2_hidden(A_1443,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_3629])).

tff(c_4426,plain,(
    ! [A_1447] :
      ( r1_tarski(A_1447,'#skF_7')
      | ~ r2_hidden('#skF_1'(A_1447,'#skF_7'),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_4399,c_4])).

tff(c_4434,plain,(
    r1_tarski('#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_4426])).

tff(c_4439,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3285,c_3285,c_4434])).

tff(c_4440,plain,(
    ! [A_1396,B_2] : ~ r2_hidden(A_1396,B_2) ),
    inference(splitRight,[status(thm)],[c_3529])).

tff(c_4497,plain,(
    ! [A_1451] : k3_tarski(A_1451) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_4440,c_4440,c_30])).

tff(c_4468,plain,(
    ! [A_9,B_10] : k3_tarski(A_9) = B_10 ),
    inference(negUnitSimplification,[status(thm)],[c_4440,c_4440,c_30])).

tff(c_4917,plain,(
    ! [B_3129] : B_3129 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_4497,c_4468])).

tff(c_4965,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_4917,c_3290])).

tff(c_5053,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4965])).

tff(c_5054,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_3289])).

tff(c_116,plain,(
    ! [C_63,A_64,B_65] :
      ( r1_tarski(k2_zfmisc_1(C_63,A_64),k2_zfmisc_1(C_63,B_65))
      | ~ r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_121,plain,(
    ! [B_65] :
      ( r1_tarski(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1('#skF_7',B_65))
      | ~ r1_tarski('#skF_8',B_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_116])).

tff(c_339,plain,(
    ! [B_105,A_106,C_107] :
      ( ~ r1_tarski(k2_zfmisc_1(B_105,A_106),k2_zfmisc_1(C_107,A_106))
      | r1_tarski(B_105,C_107)
      | k1_xboole_0 = A_106 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_365,plain,
    ( r1_tarski('#skF_9','#skF_7')
    | k1_xboole_0 = '#skF_10'
    | ~ r1_tarski('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_121,c_339])).

tff(c_5114,plain,
    ( r1_tarski('#skF_9','#skF_7')
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_5054,c_5054,c_365])).

tff(c_5115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_3285,c_5114])).

tff(c_5116,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_3257])).

tff(c_5124,plain,(
    ! [A_8] : r1_tarski('#skF_9',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5116,c_14])).

tff(c_5146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5124,c_3285])).

tff(c_5147,plain,(
    '#skF_10' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_5148,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_5154,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5148,c_58])).

tff(c_5153,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = k2_zfmisc_1('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5148,c_60])).

tff(c_5227,plain,(
    ! [A_3754,C_3755,B_3756] :
      ( r1_tarski(k2_zfmisc_1(A_3754,C_3755),k2_zfmisc_1(B_3756,C_3755))
      | ~ r1_tarski(A_3754,B_3756) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_5232,plain,(
    ! [B_3756] :
      ( r1_tarski(k2_zfmisc_1('#skF_9','#skF_8'),k2_zfmisc_1(B_3756,'#skF_10'))
      | ~ r1_tarski('#skF_9',B_3756) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5153,c_5227])).

tff(c_5341,plain,(
    ! [A_3774,B_3775,C_3776] :
      ( ~ r1_tarski(k2_zfmisc_1(A_3774,B_3775),k2_zfmisc_1(A_3774,C_3776))
      | r1_tarski(B_3775,C_3776)
      | k1_xboole_0 = A_3774 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_5351,plain,
    ( r1_tarski('#skF_8','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | ~ r1_tarski('#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_5232,c_5341])).

tff(c_5381,plain,
    ( r1_tarski('#skF_8','#skF_10')
    | k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_5351])).

tff(c_5382,plain,(
    r1_tarski('#skF_8','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_5154,c_5381])).

tff(c_5235,plain,(
    ! [A_3754] :
      ( r1_tarski(k2_zfmisc_1(A_3754,'#skF_10'),k2_zfmisc_1('#skF_9','#skF_8'))
      | ~ r1_tarski(A_3754,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5153,c_5227])).

tff(c_5355,plain,
    ( r1_tarski('#skF_10','#skF_8')
    | k1_xboole_0 = '#skF_9'
    | ~ r1_tarski('#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_5235,c_5341])).

tff(c_5385,plain,
    ( r1_tarski('#skF_10','#skF_8')
    | k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_5355])).

tff(c_5386,plain,(
    r1_tarski('#skF_10','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_5154,c_5385])).

tff(c_5401,plain,
    ( '#skF_10' = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_5386,c_8])).

tff(c_5404,plain,(
    '#skF_10' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5382,c_5401])).

tff(c_5406,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5147,c_5404])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:00:41 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.37/2.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.37/2.02  
% 5.37/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.37/2.02  %$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k3_tarski > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 5.37/2.02  
% 5.37/2.02  %Foreground sorts:
% 5.37/2.02  
% 5.37/2.02  
% 5.37/2.02  %Background operators:
% 5.37/2.02  
% 5.37/2.02  
% 5.37/2.02  %Foreground operators:
% 5.37/2.02  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.37/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.37/2.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.37/2.02  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.37/2.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.37/2.02  tff('#skF_7', type, '#skF_7': $i).
% 5.37/2.02  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.37/2.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.37/2.02  tff('#skF_10', type, '#skF_10': $i).
% 5.37/2.02  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.37/2.02  tff('#skF_9', type, '#skF_9': $i).
% 5.37/2.02  tff('#skF_8', type, '#skF_8': $i).
% 5.37/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.37/2.02  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.37/2.02  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.37/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.37/2.02  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.37/2.02  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.37/2.02  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.37/2.02  
% 5.65/2.04  tff(f_98, negated_conjecture, ~(![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 5.65/2.04  tff(f_73, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 5.65/2.04  tff(f_67, axiom, (![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 5.65/2.04  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.65/2.04  tff(f_74, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 5.65/2.04  tff(f_50, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 5.65/2.04  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.65/2.04  tff(f_87, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 5.65/2.04  tff(f_56, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 5.65/2.04  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.65/2.04  tff(c_56, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.65/2.04  tff(c_54, plain, ('#skF_10'!='#skF_8' | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.65/2.04  tff(c_68, plain, ('#skF_7'!='#skF_9'), inference(splitLeft, [status(thm)], [c_54])).
% 5.65/2.04  tff(c_60, plain, (k2_zfmisc_1('#skF_7', '#skF_8')=k2_zfmisc_1('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.65/2.04  tff(c_126, plain, (![A_66, C_67, B_68]: (r1_tarski(k2_zfmisc_1(A_66, C_67), k2_zfmisc_1(B_68, C_67)) | ~r1_tarski(A_66, B_68))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.65/2.04  tff(c_131, plain, (![B_68]: (r1_tarski(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1(B_68, '#skF_8')) | ~r1_tarski('#skF_7', B_68))), inference(superposition, [status(thm), theory('equality')], [c_60, c_126])).
% 5.65/2.04  tff(c_303, plain, (![A_102, B_103, C_104]: (~r1_tarski(k2_zfmisc_1(A_102, B_103), k2_zfmisc_1(A_102, C_104)) | r1_tarski(B_103, C_104) | k1_xboole_0=A_102)), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.65/2.04  tff(c_329, plain, (r1_tarski('#skF_10', '#skF_8') | k1_xboole_0='#skF_9' | ~r1_tarski('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_131, c_303])).
% 5.65/2.04  tff(c_375, plain, (~r1_tarski('#skF_7', '#skF_9')), inference(splitLeft, [status(thm)], [c_329])).
% 5.65/2.04  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.65/2.04  tff(c_48, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.65/2.04  tff(c_30, plain, (![A_9, B_10]: (r2_hidden('#skF_3'(A_9, B_10), A_9) | r2_hidden('#skF_4'(A_9, B_10), B_10) | k3_tarski(A_9)=B_10)), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.65/2.04  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.65/2.04  tff(c_214, plain, (![A_90, C_91]: (r2_hidden('#skF_5'(A_90, k3_tarski(A_90), C_91), A_90) | ~r2_hidden(C_91, k3_tarski(A_90)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.65/2.04  tff(c_225, plain, (![C_91]: (r2_hidden('#skF_5'(k1_xboole_0, k1_xboole_0, C_91), k1_xboole_0) | ~r2_hidden(C_91, k3_tarski(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_214])).
% 5.65/2.04  tff(c_252, plain, (![C_93]: (r2_hidden('#skF_5'(k1_xboole_0, k1_xboole_0, C_93), k1_xboole_0) | ~r2_hidden(C_93, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_225])).
% 5.65/2.04  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.65/2.04  tff(c_256, plain, (![C_93, B_2]: (r2_hidden('#skF_5'(k1_xboole_0, k1_xboole_0, C_93), B_2) | ~r1_tarski(k1_xboole_0, B_2) | ~r2_hidden(C_93, k1_xboole_0))), inference(resolution, [status(thm)], [c_252, c_2])).
% 5.65/2.04  tff(c_261, plain, (![C_93, B_2]: (r2_hidden('#skF_5'(k1_xboole_0, k1_xboole_0, C_93), B_2) | ~r2_hidden(C_93, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_256])).
% 5.65/2.04  tff(c_262, plain, (![C_94, B_95]: (r2_hidden('#skF_5'(k1_xboole_0, k1_xboole_0, C_94), B_95) | ~r2_hidden(C_94, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_256])).
% 5.65/2.04  tff(c_50, plain, (![D_44, A_38, B_39]: (~r2_hidden(D_44, '#skF_6'(A_38, B_39)) | ~r2_hidden(D_44, B_39) | ~r2_hidden(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.65/2.04  tff(c_1638, plain, (![C_190, B_191, A_192]: (~r2_hidden('#skF_5'(k1_xboole_0, k1_xboole_0, C_190), B_191) | ~r2_hidden(A_192, B_191) | ~r2_hidden(C_190, k1_xboole_0))), inference(resolution, [status(thm)], [c_262, c_50])).
% 5.65/2.04  tff(c_1647, plain, (![A_192, B_2, C_93]: (~r2_hidden(A_192, B_2) | ~r2_hidden(C_93, k1_xboole_0))), inference(resolution, [status(thm)], [c_261, c_1638])).
% 5.65/2.04  tff(c_1652, plain, (![C_193]: (~r2_hidden(C_193, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_1647])).
% 5.65/2.04  tff(c_1656, plain, (![B_10]: (r2_hidden('#skF_4'(k1_xboole_0, B_10), B_10) | k3_tarski(k1_xboole_0)=B_10)), inference(resolution, [status(thm)], [c_30, c_1652])).
% 5.65/2.04  tff(c_1680, plain, (![B_10]: (r2_hidden('#skF_4'(k1_xboole_0, B_10), B_10) | k1_xboole_0=B_10)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1656])).
% 5.65/2.04  tff(c_1688, plain, (![A_194, B_195, C_196, D_197]: (r2_hidden(k4_tarski(A_194, B_195), k2_zfmisc_1(C_196, D_197)) | ~r2_hidden(B_195, D_197) | ~r2_hidden(A_194, C_196))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.65/2.04  tff(c_1764, plain, (![A_202, B_203]: (r2_hidden(k4_tarski(A_202, B_203), k2_zfmisc_1('#skF_9', '#skF_10')) | ~r2_hidden(B_203, '#skF_8') | ~r2_hidden(A_202, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_1688])).
% 5.65/2.04  tff(c_38, plain, (![A_28, C_30, B_29, D_31]: (r2_hidden(A_28, C_30) | ~r2_hidden(k4_tarski(A_28, B_29), k2_zfmisc_1(C_30, D_31)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.65/2.04  tff(c_1789, plain, (![A_202, B_203]: (r2_hidden(A_202, '#skF_9') | ~r2_hidden(B_203, '#skF_8') | ~r2_hidden(A_202, '#skF_7'))), inference(resolution, [status(thm)], [c_1764, c_38])).
% 5.65/2.04  tff(c_2629, plain, (![B_246]: (~r2_hidden(B_246, '#skF_8'))), inference(splitLeft, [status(thm)], [c_1789])).
% 5.65/2.04  tff(c_2633, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_1680, c_2629])).
% 5.65/2.04  tff(c_2663, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_2633])).
% 5.65/2.04  tff(c_2665, plain, (![A_247]: (r2_hidden(A_247, '#skF_9') | ~r2_hidden(A_247, '#skF_7'))), inference(splitRight, [status(thm)], [c_1789])).
% 5.65/2.04  tff(c_2877, plain, (![B_254]: (r2_hidden('#skF_1'('#skF_7', B_254), '#skF_9') | r1_tarski('#skF_7', B_254))), inference(resolution, [status(thm)], [c_6, c_2665])).
% 5.65/2.04  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.65/2.04  tff(c_2892, plain, (r1_tarski('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_2877, c_4])).
% 5.65/2.04  tff(c_2901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_375, c_375, c_2892])).
% 5.65/2.04  tff(c_2902, plain, (![A_192, B_2]: (~r2_hidden(A_192, B_2))), inference(splitRight, [status(thm)], [c_1647])).
% 5.65/2.04  tff(c_2964, plain, (![A_261]: (k3_tarski(A_261)='#skF_7')), inference(negUnitSimplification, [status(thm)], [c_2902, c_2902, c_30])).
% 5.65/2.04  tff(c_2936, plain, (![A_9, B_10]: (k3_tarski(A_9)=B_10)), inference(negUnitSimplification, [status(thm)], [c_2902, c_2902, c_30])).
% 5.65/2.04  tff(c_3124, plain, (![B_816]: (B_816='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2964, c_2936])).
% 5.65/2.04  tff(c_58, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.65/2.04  tff(c_3256, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_3124, c_58])).
% 5.65/2.04  tff(c_3258, plain, (r1_tarski('#skF_7', '#skF_9')), inference(splitRight, [status(thm)], [c_329])).
% 5.65/2.04  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.65/2.04  tff(c_3282, plain, ('#skF_7'='#skF_9' | ~r1_tarski('#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_3258, c_8])).
% 5.65/2.04  tff(c_3285, plain, (~r1_tarski('#skF_9', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_68, c_3282])).
% 5.65/2.04  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.65/2.04  tff(c_3520, plain, (![C_1394, B_1395, A_1396]: (~r2_hidden('#skF_5'(k1_xboole_0, k1_xboole_0, C_1394), B_1395) | ~r2_hidden(A_1396, B_1395) | ~r2_hidden(C_1394, k1_xboole_0))), inference(resolution, [status(thm)], [c_262, c_50])).
% 5.65/2.04  tff(c_3529, plain, (![A_1396, B_2, C_93]: (~r2_hidden(A_1396, B_2) | ~r2_hidden(C_93, k1_xboole_0))), inference(resolution, [status(thm)], [c_261, c_3520])).
% 5.65/2.04  tff(c_3534, plain, (![C_1397]: (~r2_hidden(C_1397, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_3529])).
% 5.65/2.04  tff(c_3538, plain, (![B_10]: (r2_hidden('#skF_4'(k1_xboole_0, B_10), B_10) | k3_tarski(k1_xboole_0)=B_10)), inference(resolution, [status(thm)], [c_30, c_3534])).
% 5.65/2.04  tff(c_3562, plain, (![B_10]: (r2_hidden('#skF_4'(k1_xboole_0, B_10), B_10) | k1_xboole_0=B_10)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_3538])).
% 5.65/2.04  tff(c_3603, plain, (![A_1400, B_1401, C_1402, D_1403]: (r2_hidden(k4_tarski(A_1400, B_1401), k2_zfmisc_1(C_1402, D_1403)) | ~r2_hidden(B_1401, D_1403) | ~r2_hidden(A_1400, C_1402))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.65/2.04  tff(c_112, plain, (![A_59, C_60, B_61, D_62]: (r2_hidden(A_59, C_60) | ~r2_hidden(k4_tarski(A_59, B_61), k2_zfmisc_1(C_60, D_62)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.65/2.04  tff(c_115, plain, (![A_59, B_61]: (r2_hidden(A_59, '#skF_7') | ~r2_hidden(k4_tarski(A_59, B_61), k2_zfmisc_1('#skF_9', '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_60, c_112])).
% 5.65/2.04  tff(c_3629, plain, (![A_1400, B_1401]: (r2_hidden(A_1400, '#skF_7') | ~r2_hidden(B_1401, '#skF_10') | ~r2_hidden(A_1400, '#skF_9'))), inference(resolution, [status(thm)], [c_3603, c_115])).
% 5.65/2.04  tff(c_4098, plain, (![B_1428]: (~r2_hidden(B_1428, '#skF_10'))), inference(splitLeft, [status(thm)], [c_3629])).
% 5.65/2.04  tff(c_4129, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_3562, c_4098])).
% 5.65/2.04  tff(c_4223, plain, ('#skF_7'!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_4129, c_58])).
% 5.65/2.04  tff(c_3993, plain, (![B_1401]: (~r2_hidden(B_1401, '#skF_10'))), inference(splitLeft, [status(thm)], [c_3629])).
% 5.65/2.04  tff(c_3676, plain, (![A_1407, B_1408]: (r2_hidden(k4_tarski(A_1407, B_1408), k2_zfmisc_1('#skF_9', '#skF_10')) | ~r2_hidden(B_1408, '#skF_8') | ~r2_hidden(A_1407, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_3603])).
% 5.65/2.04  tff(c_36, plain, (![B_29, D_31, A_28, C_30]: (r2_hidden(B_29, D_31) | ~r2_hidden(k4_tarski(A_28, B_29), k2_zfmisc_1(C_30, D_31)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.65/2.04  tff(c_3699, plain, (![B_1408, A_1407]: (r2_hidden(B_1408, '#skF_10') | ~r2_hidden(B_1408, '#skF_8') | ~r2_hidden(A_1407, '#skF_7'))), inference(resolution, [status(thm)], [c_3676, c_36])).
% 5.65/2.04  tff(c_4302, plain, (![B_1408, A_1407]: (~r2_hidden(B_1408, '#skF_8') | ~r2_hidden(A_1407, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_3993, c_3699])).
% 5.65/2.04  tff(c_4305, plain, (![A_1440]: (~r2_hidden(A_1440, '#skF_7'))), inference(splitLeft, [status(thm)], [c_4302])).
% 5.65/2.04  tff(c_4346, plain, (![B_1441]: (r1_tarski('#skF_7', B_1441))), inference(resolution, [status(thm)], [c_6, c_4305])).
% 5.65/2.04  tff(c_4229, plain, (![B_1434]: (r1_tarski('#skF_10', B_1434))), inference(resolution, [status(thm)], [c_6, c_4098])).
% 5.65/2.04  tff(c_4232, plain, (![B_1434]: (B_1434='#skF_10' | ~r1_tarski(B_1434, '#skF_10'))), inference(resolution, [status(thm)], [c_4229, c_8])).
% 5.65/2.04  tff(c_4350, plain, ('#skF_7'='#skF_10'), inference(resolution, [status(thm)], [c_4346, c_4232])).
% 5.65/2.04  tff(c_4356, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4223, c_4350])).
% 5.65/2.04  tff(c_4359, plain, (![B_1442]: (~r2_hidden(B_1442, '#skF_8'))), inference(splitRight, [status(thm)], [c_4302])).
% 5.65/2.04  tff(c_4390, plain, (![B_2]: (r1_tarski('#skF_8', B_2))), inference(resolution, [status(thm)], [c_6, c_4359])).
% 5.65/2.04  tff(c_3257, plain, (k1_xboole_0='#skF_9' | r1_tarski('#skF_10', '#skF_8')), inference(splitRight, [status(thm)], [c_329])).
% 5.65/2.04  tff(c_3286, plain, (r1_tarski('#skF_10', '#skF_8')), inference(splitLeft, [status(thm)], [c_3257])).
% 5.65/2.04  tff(c_3289, plain, ('#skF_10'='#skF_8' | ~r1_tarski('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_3286, c_8])).
% 5.65/2.04  tff(c_3290, plain, (~r1_tarski('#skF_8', '#skF_10')), inference(splitLeft, [status(thm)], [c_3289])).
% 5.65/2.04  tff(c_4397, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4390, c_3290])).
% 5.65/2.04  tff(c_4399, plain, (![A_1443]: (r2_hidden(A_1443, '#skF_7') | ~r2_hidden(A_1443, '#skF_9'))), inference(splitRight, [status(thm)], [c_3629])).
% 5.65/2.04  tff(c_4426, plain, (![A_1447]: (r1_tarski(A_1447, '#skF_7') | ~r2_hidden('#skF_1'(A_1447, '#skF_7'), '#skF_9'))), inference(resolution, [status(thm)], [c_4399, c_4])).
% 5.65/2.04  tff(c_4434, plain, (r1_tarski('#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_6, c_4426])).
% 5.65/2.04  tff(c_4439, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3285, c_3285, c_4434])).
% 5.65/2.04  tff(c_4440, plain, (![A_1396, B_2]: (~r2_hidden(A_1396, B_2))), inference(splitRight, [status(thm)], [c_3529])).
% 5.65/2.04  tff(c_4497, plain, (![A_1451]: (k3_tarski(A_1451)='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_4440, c_4440, c_30])).
% 5.65/2.04  tff(c_4468, plain, (![A_9, B_10]: (k3_tarski(A_9)=B_10)), inference(negUnitSimplification, [status(thm)], [c_4440, c_4440, c_30])).
% 5.65/2.04  tff(c_4917, plain, (![B_3129]: (B_3129='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_4497, c_4468])).
% 5.65/2.04  tff(c_4965, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_4917, c_3290])).
% 5.65/2.04  tff(c_5053, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_4965])).
% 5.65/2.04  tff(c_5054, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_3289])).
% 5.65/2.04  tff(c_116, plain, (![C_63, A_64, B_65]: (r1_tarski(k2_zfmisc_1(C_63, A_64), k2_zfmisc_1(C_63, B_65)) | ~r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.65/2.04  tff(c_121, plain, (![B_65]: (r1_tarski(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_7', B_65)) | ~r1_tarski('#skF_8', B_65))), inference(superposition, [status(thm), theory('equality')], [c_60, c_116])).
% 5.65/2.04  tff(c_339, plain, (![B_105, A_106, C_107]: (~r1_tarski(k2_zfmisc_1(B_105, A_106), k2_zfmisc_1(C_107, A_106)) | r1_tarski(B_105, C_107) | k1_xboole_0=A_106)), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.65/2.04  tff(c_365, plain, (r1_tarski('#skF_9', '#skF_7') | k1_xboole_0='#skF_10' | ~r1_tarski('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_121, c_339])).
% 5.65/2.04  tff(c_5114, plain, (r1_tarski('#skF_9', '#skF_7') | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_5054, c_5054, c_365])).
% 5.65/2.04  tff(c_5115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_3285, c_5114])).
% 5.65/2.04  tff(c_5116, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_3257])).
% 5.65/2.04  tff(c_5124, plain, (![A_8]: (r1_tarski('#skF_9', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_5116, c_14])).
% 5.65/2.04  tff(c_5146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5124, c_3285])).
% 5.65/2.04  tff(c_5147, plain, ('#skF_10'!='#skF_8'), inference(splitRight, [status(thm)], [c_54])).
% 5.65/2.04  tff(c_5148, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_54])).
% 5.65/2.04  tff(c_5154, plain, (k1_xboole_0!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_5148, c_58])).
% 5.65/2.04  tff(c_5153, plain, (k2_zfmisc_1('#skF_9', '#skF_10')=k2_zfmisc_1('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_5148, c_60])).
% 5.65/2.04  tff(c_5227, plain, (![A_3754, C_3755, B_3756]: (r1_tarski(k2_zfmisc_1(A_3754, C_3755), k2_zfmisc_1(B_3756, C_3755)) | ~r1_tarski(A_3754, B_3756))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.65/2.04  tff(c_5232, plain, (![B_3756]: (r1_tarski(k2_zfmisc_1('#skF_9', '#skF_8'), k2_zfmisc_1(B_3756, '#skF_10')) | ~r1_tarski('#skF_9', B_3756))), inference(superposition, [status(thm), theory('equality')], [c_5153, c_5227])).
% 5.65/2.04  tff(c_5341, plain, (![A_3774, B_3775, C_3776]: (~r1_tarski(k2_zfmisc_1(A_3774, B_3775), k2_zfmisc_1(A_3774, C_3776)) | r1_tarski(B_3775, C_3776) | k1_xboole_0=A_3774)), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.65/2.04  tff(c_5351, plain, (r1_tarski('#skF_8', '#skF_10') | k1_xboole_0='#skF_9' | ~r1_tarski('#skF_9', '#skF_9')), inference(resolution, [status(thm)], [c_5232, c_5341])).
% 5.65/2.04  tff(c_5381, plain, (r1_tarski('#skF_8', '#skF_10') | k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_5351])).
% 5.65/2.04  tff(c_5382, plain, (r1_tarski('#skF_8', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_5154, c_5381])).
% 5.65/2.04  tff(c_5235, plain, (![A_3754]: (r1_tarski(k2_zfmisc_1(A_3754, '#skF_10'), k2_zfmisc_1('#skF_9', '#skF_8')) | ~r1_tarski(A_3754, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_5153, c_5227])).
% 5.65/2.04  tff(c_5355, plain, (r1_tarski('#skF_10', '#skF_8') | k1_xboole_0='#skF_9' | ~r1_tarski('#skF_9', '#skF_9')), inference(resolution, [status(thm)], [c_5235, c_5341])).
% 5.65/2.04  tff(c_5385, plain, (r1_tarski('#skF_10', '#skF_8') | k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_5355])).
% 5.65/2.04  tff(c_5386, plain, (r1_tarski('#skF_10', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_5154, c_5385])).
% 5.65/2.04  tff(c_5401, plain, ('#skF_10'='#skF_8' | ~r1_tarski('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_5386, c_8])).
% 5.65/2.04  tff(c_5404, plain, ('#skF_10'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_5382, c_5401])).
% 5.65/2.04  tff(c_5406, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5147, c_5404])).
% 5.65/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.65/2.04  
% 5.65/2.04  Inference rules
% 5.65/2.04  ----------------------
% 5.65/2.04  #Ref     : 0
% 5.65/2.04  #Sup     : 1245
% 5.65/2.04  #Fact    : 0
% 5.65/2.04  #Define  : 0
% 5.65/2.04  #Split   : 28
% 5.65/2.04  #Chain   : 0
% 5.65/2.04  #Close   : 0
% 5.65/2.04  
% 5.65/2.04  Ordering : KBO
% 5.65/2.04  
% 5.65/2.04  Simplification rules
% 5.65/2.04  ----------------------
% 5.65/2.04  #Subsume      : 251
% 5.65/2.04  #Demod        : 557
% 5.65/2.04  #Tautology    : 266
% 5.65/2.04  #SimpNegUnit  : 106
% 5.65/2.04  #BackRed      : 194
% 5.65/2.04  
% 5.65/2.04  #Partial instantiations: 1158
% 5.65/2.04  #Strategies tried      : 1
% 5.65/2.04  
% 5.65/2.04  Timing (in seconds)
% 5.65/2.04  ----------------------
% 5.65/2.04  Preprocessing        : 0.31
% 5.65/2.04  Parsing              : 0.16
% 5.65/2.05  CNF conversion       : 0.03
% 5.65/2.05  Main loop            : 0.95
% 5.65/2.05  Inferencing          : 0.34
% 5.65/2.05  Reduction            : 0.28
% 5.65/2.05  Demodulation         : 0.18
% 5.65/2.05  BG Simplification    : 0.04
% 5.65/2.05  Subsumption          : 0.21
% 5.65/2.05  Abstraction          : 0.04
% 5.65/2.05  MUC search           : 0.00
% 5.65/2.05  Cooper               : 0.00
% 5.65/2.05  Total                : 1.31
% 5.65/2.05  Index Insertion      : 0.00
% 5.65/2.05  Index Deletion       : 0.00
% 5.65/2.05  Index Matching       : 0.00
% 5.65/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
