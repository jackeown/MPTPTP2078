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
% DateTime   : Thu Dec  3 10:01:45 EST 2020

% Result     : Theorem 49.72s
% Output     : CNFRefutation 49.72s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 175 expanded)
%              Number of leaves         :   30 (  71 expanded)
%              Depth                    :   11
%              Number of atoms          :  162 ( 443 expanded)
%              Number of equality atoms :   14 (  54 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_50,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_112,plain,(
    ! [A_43,B_44] :
      ( r2_hidden('#skF_2'(A_43,B_44),A_43)
      | r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_124,plain,(
    ! [A_43] : r1_tarski(A_43,A_43) ),
    inference(resolution,[status(thm)],[c_112,c_8])).

tff(c_46,plain,(
    r1_tarski('#skF_5',k2_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_141,plain,(
    ! [C_51,B_52,A_53] :
      ( r2_hidden(C_51,B_52)
      | ~ r2_hidden(C_51,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_148,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_1'(A_54),B_55)
      | ~ r1_tarski(A_54,B_55)
      | v1_xboole_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_4,c_141])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_7292,plain,(
    ! [A_408,B_409,B_410] :
      ( r2_hidden('#skF_1'(A_408),B_409)
      | ~ r1_tarski(B_410,B_409)
      | ~ r1_tarski(A_408,B_410)
      | v1_xboole_0(A_408) ) ),
    inference(resolution,[status(thm)],[c_148,c_6])).

tff(c_7370,plain,(
    ! [A_408] :
      ( r2_hidden('#skF_1'(A_408),k2_relat_1('#skF_6'))
      | ~ r1_tarski(A_408,'#skF_5')
      | v1_xboole_0(A_408) ) ),
    inference(resolution,[status(thm)],[c_46,c_7292])).

tff(c_16,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_79,plain,(
    ! [A_36,B_37] : ~ r2_hidden(A_36,k2_zfmisc_1(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_82,plain,(
    ! [A_11] : ~ r2_hidden(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_79])).

tff(c_44,plain,(
    k10_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_26,plain,(
    ! [A_15,B_16,C_17] :
      ( r2_hidden(k4_tarski('#skF_3'(A_15,B_16,C_17),A_15),C_17)
      | ~ r2_hidden(A_15,k9_relat_1(C_17,B_16))
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_994,plain,(
    ! [A_140,C_141,B_142,D_143] :
      ( r2_hidden(A_140,k10_relat_1(C_141,B_142))
      | ~ r2_hidden(D_143,B_142)
      | ~ r2_hidden(k4_tarski(A_140,D_143),C_141)
      | ~ r2_hidden(D_143,k2_relat_1(C_141))
      | ~ v1_relat_1(C_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6165,plain,(
    ! [A_360,C_361,A_362] :
      ( r2_hidden(A_360,k10_relat_1(C_361,A_362))
      | ~ r2_hidden(k4_tarski(A_360,'#skF_1'(A_362)),C_361)
      | ~ r2_hidden('#skF_1'(A_362),k2_relat_1(C_361))
      | ~ v1_relat_1(C_361)
      | v1_xboole_0(A_362) ) ),
    inference(resolution,[status(thm)],[c_4,c_994])).

tff(c_178239,plain,(
    ! [A_2943,B_2944,C_2945] :
      ( r2_hidden('#skF_3'('#skF_1'(A_2943),B_2944,C_2945),k10_relat_1(C_2945,A_2943))
      | ~ r2_hidden('#skF_1'(A_2943),k2_relat_1(C_2945))
      | v1_xboole_0(A_2943)
      | ~ r2_hidden('#skF_1'(A_2943),k9_relat_1(C_2945,B_2944))
      | ~ v1_relat_1(C_2945) ) ),
    inference(resolution,[status(thm)],[c_26,c_6165])).

tff(c_178505,plain,(
    ! [B_2944] :
      ( r2_hidden('#skF_3'('#skF_1'('#skF_5'),B_2944,'#skF_6'),k1_xboole_0)
      | ~ r2_hidden('#skF_1'('#skF_5'),k2_relat_1('#skF_6'))
      | v1_xboole_0('#skF_5')
      | ~ r2_hidden('#skF_1'('#skF_5'),k9_relat_1('#skF_6',B_2944))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_178239])).

tff(c_178589,plain,(
    ! [B_2944] :
      ( r2_hidden('#skF_3'('#skF_1'('#skF_5'),B_2944,'#skF_6'),k1_xboole_0)
      | ~ r2_hidden('#skF_1'('#skF_5'),k2_relat_1('#skF_6'))
      | v1_xboole_0('#skF_5')
      | ~ r2_hidden('#skF_1'('#skF_5'),k9_relat_1('#skF_6',B_2944)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_178505])).

tff(c_178590,plain,(
    ! [B_2944] :
      ( ~ r2_hidden('#skF_1'('#skF_5'),k2_relat_1('#skF_6'))
      | v1_xboole_0('#skF_5')
      | ~ r2_hidden('#skF_1'('#skF_5'),k9_relat_1('#skF_6',B_2944)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_178589])).

tff(c_178591,plain,(
    ~ r2_hidden('#skF_1'('#skF_5'),k2_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_178590])).

tff(c_178597,plain,
    ( ~ r1_tarski('#skF_5','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_7370,c_178591])).

tff(c_178606,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_178597])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_178623,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_178606,c_12])).

tff(c_178632,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_178623])).

tff(c_178634,plain,(
    r2_hidden('#skF_1'('#skF_5'),k2_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_178590])).

tff(c_30,plain,(
    ! [A_21] :
      ( k9_relat_1(A_21,k1_relat_1(A_21)) = k2_relat_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_809,plain,(
    ! [A_126,B_127,C_128] :
      ( r2_hidden(k4_tarski('#skF_3'(A_126,B_127,C_128),A_126),C_128)
      | ~ r2_hidden(A_126,k9_relat_1(C_128,B_127))
      | ~ v1_relat_1(C_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4305,plain,(
    ! [A_303,B_304,C_305,B_306] :
      ( r2_hidden(k4_tarski('#skF_3'(A_303,B_304,C_305),A_303),B_306)
      | ~ r1_tarski(C_305,B_306)
      | ~ r2_hidden(A_303,k9_relat_1(C_305,B_304))
      | ~ v1_relat_1(C_305) ) ),
    inference(resolution,[status(thm)],[c_809,c_6])).

tff(c_42,plain,(
    ! [A_28,C_30,B_29] :
      ( r2_hidden(A_28,k1_relat_1(C_30))
      | ~ r2_hidden(k4_tarski(A_28,B_29),C_30)
      | ~ v1_relat_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4431,plain,(
    ! [A_303,B_304,C_305,B_306] :
      ( r2_hidden('#skF_3'(A_303,B_304,C_305),k1_relat_1(B_306))
      | ~ v1_relat_1(B_306)
      | ~ r1_tarski(C_305,B_306)
      | ~ r2_hidden(A_303,k9_relat_1(C_305,B_304))
      | ~ v1_relat_1(C_305) ) ),
    inference(resolution,[status(thm)],[c_4305,c_42])).

tff(c_28,plain,(
    ! [A_15,B_16,C_17] :
      ( r2_hidden('#skF_3'(A_15,B_16,C_17),k1_relat_1(C_17))
      | ~ r2_hidden(A_15,k9_relat_1(C_17,B_16))
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1091,plain,(
    ! [A_152,C_153,B_154,D_155] :
      ( r2_hidden(A_152,k9_relat_1(C_153,B_154))
      | ~ r2_hidden(D_155,B_154)
      | ~ r2_hidden(k4_tarski(D_155,A_152),C_153)
      | ~ r2_hidden(D_155,k1_relat_1(C_153))
      | ~ v1_relat_1(C_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10985,plain,(
    ! [B_551,A_553,C_552,A_550,C_549] :
      ( r2_hidden(A_550,k9_relat_1(C_552,k1_relat_1(C_549)))
      | ~ r2_hidden(k4_tarski('#skF_3'(A_553,B_551,C_549),A_550),C_552)
      | ~ r2_hidden('#skF_3'(A_553,B_551,C_549),k1_relat_1(C_552))
      | ~ v1_relat_1(C_552)
      | ~ r2_hidden(A_553,k9_relat_1(C_549,B_551))
      | ~ v1_relat_1(C_549) ) ),
    inference(resolution,[status(thm)],[c_28,c_1091])).

tff(c_123234,plain,(
    ! [A_2441,C_2442,B_2443] :
      ( r2_hidden(A_2441,k9_relat_1(C_2442,k1_relat_1(C_2442)))
      | ~ r2_hidden('#skF_3'(A_2441,B_2443,C_2442),k1_relat_1(C_2442))
      | ~ r2_hidden(A_2441,k9_relat_1(C_2442,B_2443))
      | ~ v1_relat_1(C_2442) ) ),
    inference(resolution,[status(thm)],[c_26,c_10985])).

tff(c_123246,plain,(
    ! [A_303,B_306,B_304] :
      ( r2_hidden(A_303,k9_relat_1(B_306,k1_relat_1(B_306)))
      | ~ r1_tarski(B_306,B_306)
      | ~ r2_hidden(A_303,k9_relat_1(B_306,B_304))
      | ~ v1_relat_1(B_306) ) ),
    inference(resolution,[status(thm)],[c_4431,c_123234])).

tff(c_123273,plain,(
    ! [A_2444,B_2445,B_2446] :
      ( r2_hidden(A_2444,k9_relat_1(B_2445,k1_relat_1(B_2445)))
      | ~ r2_hidden(A_2444,k9_relat_1(B_2445,B_2446))
      | ~ v1_relat_1(B_2445) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_123246])).

tff(c_123403,plain,(
    ! [A_2452,A_2453] :
      ( r2_hidden(A_2452,k9_relat_1(A_2453,k1_relat_1(A_2453)))
      | ~ r2_hidden(A_2452,k2_relat_1(A_2453))
      | ~ v1_relat_1(A_2453)
      | ~ v1_relat_1(A_2453) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_123273])).

tff(c_147000,plain,(
    ! [A_2660,B_2661,A_2662] :
      ( r2_hidden(A_2660,B_2661)
      | ~ r1_tarski(k9_relat_1(A_2662,k1_relat_1(A_2662)),B_2661)
      | ~ r2_hidden(A_2660,k2_relat_1(A_2662))
      | ~ v1_relat_1(A_2662) ) ),
    inference(resolution,[status(thm)],[c_123403,c_6])).

tff(c_147086,plain,(
    ! [A_2660,A_2662] :
      ( r2_hidden(A_2660,k9_relat_1(A_2662,k1_relat_1(A_2662)))
      | ~ r2_hidden(A_2660,k2_relat_1(A_2662))
      | ~ v1_relat_1(A_2662) ) ),
    inference(resolution,[status(thm)],[c_124,c_147000])).

tff(c_178633,plain,(
    ! [B_2944] :
      ( ~ r2_hidden('#skF_1'('#skF_5'),k9_relat_1('#skF_6',B_2944))
      | v1_xboole_0('#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_178590])).

tff(c_178678,plain,(
    ! [B_2946] : ~ r2_hidden('#skF_1'('#skF_5'),k9_relat_1('#skF_6',B_2946)) ),
    inference(splitLeft,[status(thm)],[c_178633])).

tff(c_178694,plain,
    ( ~ r2_hidden('#skF_1'('#skF_5'),k2_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_147086,c_178678])).

tff(c_178788,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_178634,c_178694])).

tff(c_178789,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_178633])).

tff(c_178803,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_178789,c_12])).

tff(c_178812,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_178803])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:40:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 49.72/40.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 49.72/40.45  
% 49.72/40.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 49.72/40.45  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2
% 49.72/40.45  
% 49.72/40.45  %Foreground sorts:
% 49.72/40.45  
% 49.72/40.45  
% 49.72/40.45  %Background operators:
% 49.72/40.45  
% 49.72/40.45  
% 49.72/40.45  %Foreground operators:
% 49.72/40.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 49.72/40.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 49.72/40.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 49.72/40.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 49.72/40.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 49.72/40.45  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 49.72/40.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 49.72/40.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 49.72/40.45  tff('#skF_5', type, '#skF_5': $i).
% 49.72/40.45  tff('#skF_6', type, '#skF_6': $i).
% 49.72/40.45  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 49.72/40.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 49.72/40.45  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 49.72/40.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 49.72/40.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 49.72/40.45  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 49.72/40.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 49.72/40.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 49.72/40.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 49.72/40.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 49.72/40.45  
% 49.72/40.47  tff(f_96, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_relat_1)).
% 49.72/40.47  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 49.72/40.47  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 49.72/40.47  tff(f_48, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 49.72/40.47  tff(f_51, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 49.72/40.47  tff(f_62, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 49.72/40.47  tff(f_77, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 49.72/40.47  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 49.72/40.47  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 49.72/40.47  tff(f_85, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 49.72/40.47  tff(c_48, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_96])).
% 49.72/40.47  tff(c_50, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_96])).
% 49.72/40.47  tff(c_112, plain, (![A_43, B_44]: (r2_hidden('#skF_2'(A_43, B_44), A_43) | r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_38])).
% 49.72/40.47  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 49.72/40.47  tff(c_124, plain, (![A_43]: (r1_tarski(A_43, A_43))), inference(resolution, [status(thm)], [c_112, c_8])).
% 49.72/40.47  tff(c_46, plain, (r1_tarski('#skF_5', k2_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 49.72/40.47  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 49.72/40.47  tff(c_141, plain, (![C_51, B_52, A_53]: (r2_hidden(C_51, B_52) | ~r2_hidden(C_51, A_53) | ~r1_tarski(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_38])).
% 49.72/40.47  tff(c_148, plain, (![A_54, B_55]: (r2_hidden('#skF_1'(A_54), B_55) | ~r1_tarski(A_54, B_55) | v1_xboole_0(A_54))), inference(resolution, [status(thm)], [c_4, c_141])).
% 49.72/40.47  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 49.72/40.47  tff(c_7292, plain, (![A_408, B_409, B_410]: (r2_hidden('#skF_1'(A_408), B_409) | ~r1_tarski(B_410, B_409) | ~r1_tarski(A_408, B_410) | v1_xboole_0(A_408))), inference(resolution, [status(thm)], [c_148, c_6])).
% 49.72/40.47  tff(c_7370, plain, (![A_408]: (r2_hidden('#skF_1'(A_408), k2_relat_1('#skF_6')) | ~r1_tarski(A_408, '#skF_5') | v1_xboole_0(A_408))), inference(resolution, [status(thm)], [c_46, c_7292])).
% 49.72/40.47  tff(c_16, plain, (![A_11]: (k2_zfmisc_1(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 49.72/40.47  tff(c_79, plain, (![A_36, B_37]: (~r2_hidden(A_36, k2_zfmisc_1(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 49.72/40.47  tff(c_82, plain, (![A_11]: (~r2_hidden(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_79])).
% 49.72/40.47  tff(c_44, plain, (k10_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 49.72/40.47  tff(c_26, plain, (![A_15, B_16, C_17]: (r2_hidden(k4_tarski('#skF_3'(A_15, B_16, C_17), A_15), C_17) | ~r2_hidden(A_15, k9_relat_1(C_17, B_16)) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 49.72/40.47  tff(c_994, plain, (![A_140, C_141, B_142, D_143]: (r2_hidden(A_140, k10_relat_1(C_141, B_142)) | ~r2_hidden(D_143, B_142) | ~r2_hidden(k4_tarski(A_140, D_143), C_141) | ~r2_hidden(D_143, k2_relat_1(C_141)) | ~v1_relat_1(C_141))), inference(cnfTransformation, [status(thm)], [f_77])).
% 49.72/40.47  tff(c_6165, plain, (![A_360, C_361, A_362]: (r2_hidden(A_360, k10_relat_1(C_361, A_362)) | ~r2_hidden(k4_tarski(A_360, '#skF_1'(A_362)), C_361) | ~r2_hidden('#skF_1'(A_362), k2_relat_1(C_361)) | ~v1_relat_1(C_361) | v1_xboole_0(A_362))), inference(resolution, [status(thm)], [c_4, c_994])).
% 49.72/40.47  tff(c_178239, plain, (![A_2943, B_2944, C_2945]: (r2_hidden('#skF_3'('#skF_1'(A_2943), B_2944, C_2945), k10_relat_1(C_2945, A_2943)) | ~r2_hidden('#skF_1'(A_2943), k2_relat_1(C_2945)) | v1_xboole_0(A_2943) | ~r2_hidden('#skF_1'(A_2943), k9_relat_1(C_2945, B_2944)) | ~v1_relat_1(C_2945))), inference(resolution, [status(thm)], [c_26, c_6165])).
% 49.72/40.47  tff(c_178505, plain, (![B_2944]: (r2_hidden('#skF_3'('#skF_1'('#skF_5'), B_2944, '#skF_6'), k1_xboole_0) | ~r2_hidden('#skF_1'('#skF_5'), k2_relat_1('#skF_6')) | v1_xboole_0('#skF_5') | ~r2_hidden('#skF_1'('#skF_5'), k9_relat_1('#skF_6', B_2944)) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_178239])).
% 49.72/40.47  tff(c_178589, plain, (![B_2944]: (r2_hidden('#skF_3'('#skF_1'('#skF_5'), B_2944, '#skF_6'), k1_xboole_0) | ~r2_hidden('#skF_1'('#skF_5'), k2_relat_1('#skF_6')) | v1_xboole_0('#skF_5') | ~r2_hidden('#skF_1'('#skF_5'), k9_relat_1('#skF_6', B_2944)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_178505])).
% 49.72/40.47  tff(c_178590, plain, (![B_2944]: (~r2_hidden('#skF_1'('#skF_5'), k2_relat_1('#skF_6')) | v1_xboole_0('#skF_5') | ~r2_hidden('#skF_1'('#skF_5'), k9_relat_1('#skF_6', B_2944)))), inference(negUnitSimplification, [status(thm)], [c_82, c_178589])).
% 49.72/40.47  tff(c_178591, plain, (~r2_hidden('#skF_1'('#skF_5'), k2_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_178590])).
% 49.72/40.47  tff(c_178597, plain, (~r1_tarski('#skF_5', '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_7370, c_178591])).
% 49.72/40.47  tff(c_178606, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_178597])).
% 49.72/40.47  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 49.72/40.47  tff(c_178623, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_178606, c_12])).
% 49.72/40.47  tff(c_178632, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_178623])).
% 49.72/40.47  tff(c_178634, plain, (r2_hidden('#skF_1'('#skF_5'), k2_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_178590])).
% 49.72/40.47  tff(c_30, plain, (![A_21]: (k9_relat_1(A_21, k1_relat_1(A_21))=k2_relat_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_66])).
% 49.72/40.47  tff(c_809, plain, (![A_126, B_127, C_128]: (r2_hidden(k4_tarski('#skF_3'(A_126, B_127, C_128), A_126), C_128) | ~r2_hidden(A_126, k9_relat_1(C_128, B_127)) | ~v1_relat_1(C_128))), inference(cnfTransformation, [status(thm)], [f_62])).
% 49.72/40.47  tff(c_4305, plain, (![A_303, B_304, C_305, B_306]: (r2_hidden(k4_tarski('#skF_3'(A_303, B_304, C_305), A_303), B_306) | ~r1_tarski(C_305, B_306) | ~r2_hidden(A_303, k9_relat_1(C_305, B_304)) | ~v1_relat_1(C_305))), inference(resolution, [status(thm)], [c_809, c_6])).
% 49.72/40.47  tff(c_42, plain, (![A_28, C_30, B_29]: (r2_hidden(A_28, k1_relat_1(C_30)) | ~r2_hidden(k4_tarski(A_28, B_29), C_30) | ~v1_relat_1(C_30))), inference(cnfTransformation, [status(thm)], [f_85])).
% 49.72/40.47  tff(c_4431, plain, (![A_303, B_304, C_305, B_306]: (r2_hidden('#skF_3'(A_303, B_304, C_305), k1_relat_1(B_306)) | ~v1_relat_1(B_306) | ~r1_tarski(C_305, B_306) | ~r2_hidden(A_303, k9_relat_1(C_305, B_304)) | ~v1_relat_1(C_305))), inference(resolution, [status(thm)], [c_4305, c_42])).
% 49.72/40.47  tff(c_28, plain, (![A_15, B_16, C_17]: (r2_hidden('#skF_3'(A_15, B_16, C_17), k1_relat_1(C_17)) | ~r2_hidden(A_15, k9_relat_1(C_17, B_16)) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 49.72/40.47  tff(c_1091, plain, (![A_152, C_153, B_154, D_155]: (r2_hidden(A_152, k9_relat_1(C_153, B_154)) | ~r2_hidden(D_155, B_154) | ~r2_hidden(k4_tarski(D_155, A_152), C_153) | ~r2_hidden(D_155, k1_relat_1(C_153)) | ~v1_relat_1(C_153))), inference(cnfTransformation, [status(thm)], [f_62])).
% 49.72/40.47  tff(c_10985, plain, (![B_551, A_553, C_552, A_550, C_549]: (r2_hidden(A_550, k9_relat_1(C_552, k1_relat_1(C_549))) | ~r2_hidden(k4_tarski('#skF_3'(A_553, B_551, C_549), A_550), C_552) | ~r2_hidden('#skF_3'(A_553, B_551, C_549), k1_relat_1(C_552)) | ~v1_relat_1(C_552) | ~r2_hidden(A_553, k9_relat_1(C_549, B_551)) | ~v1_relat_1(C_549))), inference(resolution, [status(thm)], [c_28, c_1091])).
% 49.72/40.47  tff(c_123234, plain, (![A_2441, C_2442, B_2443]: (r2_hidden(A_2441, k9_relat_1(C_2442, k1_relat_1(C_2442))) | ~r2_hidden('#skF_3'(A_2441, B_2443, C_2442), k1_relat_1(C_2442)) | ~r2_hidden(A_2441, k9_relat_1(C_2442, B_2443)) | ~v1_relat_1(C_2442))), inference(resolution, [status(thm)], [c_26, c_10985])).
% 49.72/40.47  tff(c_123246, plain, (![A_303, B_306, B_304]: (r2_hidden(A_303, k9_relat_1(B_306, k1_relat_1(B_306))) | ~r1_tarski(B_306, B_306) | ~r2_hidden(A_303, k9_relat_1(B_306, B_304)) | ~v1_relat_1(B_306))), inference(resolution, [status(thm)], [c_4431, c_123234])).
% 49.72/40.47  tff(c_123273, plain, (![A_2444, B_2445, B_2446]: (r2_hidden(A_2444, k9_relat_1(B_2445, k1_relat_1(B_2445))) | ~r2_hidden(A_2444, k9_relat_1(B_2445, B_2446)) | ~v1_relat_1(B_2445))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_123246])).
% 49.72/40.47  tff(c_123403, plain, (![A_2452, A_2453]: (r2_hidden(A_2452, k9_relat_1(A_2453, k1_relat_1(A_2453))) | ~r2_hidden(A_2452, k2_relat_1(A_2453)) | ~v1_relat_1(A_2453) | ~v1_relat_1(A_2453))), inference(superposition, [status(thm), theory('equality')], [c_30, c_123273])).
% 49.72/40.47  tff(c_147000, plain, (![A_2660, B_2661, A_2662]: (r2_hidden(A_2660, B_2661) | ~r1_tarski(k9_relat_1(A_2662, k1_relat_1(A_2662)), B_2661) | ~r2_hidden(A_2660, k2_relat_1(A_2662)) | ~v1_relat_1(A_2662))), inference(resolution, [status(thm)], [c_123403, c_6])).
% 49.72/40.47  tff(c_147086, plain, (![A_2660, A_2662]: (r2_hidden(A_2660, k9_relat_1(A_2662, k1_relat_1(A_2662))) | ~r2_hidden(A_2660, k2_relat_1(A_2662)) | ~v1_relat_1(A_2662))), inference(resolution, [status(thm)], [c_124, c_147000])).
% 49.72/40.47  tff(c_178633, plain, (![B_2944]: (~r2_hidden('#skF_1'('#skF_5'), k9_relat_1('#skF_6', B_2944)) | v1_xboole_0('#skF_5'))), inference(splitRight, [status(thm)], [c_178590])).
% 49.72/40.47  tff(c_178678, plain, (![B_2946]: (~r2_hidden('#skF_1'('#skF_5'), k9_relat_1('#skF_6', B_2946)))), inference(splitLeft, [status(thm)], [c_178633])).
% 49.72/40.47  tff(c_178694, plain, (~r2_hidden('#skF_1'('#skF_5'), k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_147086, c_178678])).
% 49.72/40.47  tff(c_178788, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_178634, c_178694])).
% 49.72/40.47  tff(c_178789, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_178633])).
% 49.72/40.47  tff(c_178803, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_178789, c_12])).
% 49.72/40.47  tff(c_178812, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_178803])).
% 49.72/40.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 49.72/40.47  
% 49.72/40.47  Inference rules
% 49.72/40.47  ----------------------
% 49.72/40.47  #Ref     : 0
% 49.72/40.47  #Sup     : 44095
% 49.72/40.47  #Fact    : 0
% 49.72/40.47  #Define  : 0
% 49.72/40.47  #Split   : 70
% 49.72/40.47  #Chain   : 0
% 49.72/40.47  #Close   : 0
% 49.72/40.47  
% 49.72/40.47  Ordering : KBO
% 49.72/40.47  
% 49.72/40.47  Simplification rules
% 49.72/40.47  ----------------------
% 49.72/40.47  #Subsume      : 26115
% 49.72/40.47  #Demod        : 4885
% 49.72/40.47  #Tautology    : 3292
% 49.72/40.47  #SimpNegUnit  : 64
% 49.72/40.47  #BackRed      : 0
% 49.72/40.47  
% 49.72/40.47  #Partial instantiations: 0
% 49.72/40.47  #Strategies tried      : 1
% 49.72/40.47  
% 49.72/40.47  Timing (in seconds)
% 49.72/40.47  ----------------------
% 49.72/40.47  Preprocessing        : 0.31
% 49.72/40.47  Parsing              : 0.16
% 49.72/40.47  CNF conversion       : 0.02
% 49.72/40.47  Main loop            : 39.40
% 49.72/40.47  Inferencing          : 3.64
% 49.72/40.47  Reduction            : 4.58
% 49.72/40.47  Demodulation         : 2.91
% 49.72/40.47  BG Simplification    : 0.26
% 49.72/40.47  Subsumption          : 29.65
% 49.72/40.47  Abstraction          : 0.52
% 49.72/40.47  MUC search           : 0.00
% 49.72/40.47  Cooper               : 0.00
% 49.72/40.47  Total                : 39.74
% 49.72/40.47  Index Insertion      : 0.00
% 49.72/40.47  Index Deletion       : 0.00
% 49.72/40.47  Index Matching       : 0.00
% 49.72/40.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
