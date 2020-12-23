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
% DateTime   : Thu Dec  3 10:05:56 EST 2020

% Result     : Theorem 12.93s
% Output     : CNFRefutation 12.93s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 152 expanded)
%              Number of leaves         :   28 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :  120 ( 309 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_ordinal1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_69,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_47,axiom,(
    ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

tff(c_24,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_254,plain,(
    ! [B_75,C_76,A_77] :
      ( r2_hidden(B_75,C_76)
      | ~ r1_tarski(k2_tarski(A_77,B_75),C_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_262,plain,(
    ! [B_75,A_77] : r2_hidden(B_75,k2_tarski(A_77,B_75)) ),
    inference(resolution,[status(thm)],[c_24,c_254])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_378,plain,(
    ! [A_101,B_102,C_103] :
      ( r2_hidden(A_101,B_102)
      | r2_hidden(A_101,C_103)
      | ~ r2_hidden(A_101,k5_xboole_0(B_102,C_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_393,plain,(
    ! [B_102,C_103,B_2] :
      ( r2_hidden('#skF_1'(k5_xboole_0(B_102,C_103),B_2),B_102)
      | r2_hidden('#skF_1'(k5_xboole_0(B_102,C_103),B_2),C_103)
      | r1_tarski(k5_xboole_0(B_102,C_103),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_378])).

tff(c_1934,plain,(
    ! [B_102,B_2] :
      ( r1_tarski(k5_xboole_0(B_102,B_102),B_2)
      | r2_hidden('#skF_1'(k5_xboole_0(B_102,B_102),B_2),B_102) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_393])).

tff(c_343,plain,(
    ! [A_95,C_96,B_97] :
      ( ~ r2_hidden(A_95,C_96)
      | ~ r2_hidden(A_95,B_97)
      | ~ r2_hidden(A_95,k5_xboole_0(B_97,C_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2702,plain,(
    ! [B_327,C_328,B_329] :
      ( ~ r2_hidden('#skF_1'(k5_xboole_0(B_327,C_328),B_329),C_328)
      | ~ r2_hidden('#skF_1'(k5_xboole_0(B_327,C_328),B_329),B_327)
      | r1_tarski(k5_xboole_0(B_327,C_328),B_329) ) ),
    inference(resolution,[status(thm)],[c_6,c_343])).

tff(c_2762,plain,(
    ! [B_330,B_331] :
      ( ~ r2_hidden('#skF_1'(k5_xboole_0(B_330,B_330),B_331),B_330)
      | r1_tarski(k5_xboole_0(B_330,B_330),B_331) ) ),
    inference(resolution,[status(thm)],[c_1934,c_2702])).

tff(c_2815,plain,(
    ! [B_102,B_2] : r1_tarski(k5_xboole_0(B_102,B_102),B_2) ),
    inference(resolution,[status(thm)],[c_1934,c_2762])).

tff(c_2839,plain,(
    ! [B_332,B_333] : r1_tarski(k5_xboole_0(B_332,B_332),B_333) ),
    inference(resolution,[status(thm)],[c_1934,c_2762])).

tff(c_20,plain,(
    ! [B_10,A_9] :
      ( B_10 = A_9
      | ~ r1_tarski(B_10,A_9)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2925,plain,(
    ! [B_334,B_335] :
      ( k5_xboole_0(B_334,B_334) = B_335
      | ~ r1_tarski(B_335,k5_xboole_0(B_334,B_334)) ) ),
    inference(resolution,[status(thm)],[c_2839,c_20])).

tff(c_2947,plain,(
    ! [B_337,B_336] : k5_xboole_0(B_337,B_337) = k5_xboole_0(B_336,B_336) ),
    inference(resolution,[status(thm)],[c_2815,c_2925])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( ~ r2_hidden(A_6,C_8)
      | ~ r2_hidden(A_6,B_7)
      | ~ r2_hidden(A_6,k5_xboole_0(B_7,C_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4486,plain,(
    ! [A_381,B_382,B_383] :
      ( ~ r2_hidden(A_381,B_382)
      | ~ r2_hidden(A_381,B_382)
      | ~ r2_hidden(A_381,k5_xboole_0(B_383,B_383)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2947,c_8])).

tff(c_4530,plain,(
    ! [B_75,A_77,B_383] :
      ( ~ r2_hidden(B_75,k2_tarski(A_77,B_75))
      | ~ r2_hidden(B_75,k5_xboole_0(B_383,B_383)) ) ),
    inference(resolution,[status(thm)],[c_262,c_4486])).

tff(c_4560,plain,(
    ! [B_75,B_383] : ~ r2_hidden(B_75,k5_xboole_0(B_383,B_383)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_4530])).

tff(c_1936,plain,(
    ! [B_297,C_298,B_299] :
      ( r2_hidden('#skF_1'(k5_xboole_0(B_297,C_298),B_299),B_297)
      | r2_hidden('#skF_1'(k5_xboole_0(B_297,C_298),B_299),C_298)
      | r1_tarski(k5_xboole_0(B_297,C_298),B_299) ) ),
    inference(resolution,[status(thm)],[c_6,c_378])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2451,plain,(
    ! [B_313,C_314] :
      ( r2_hidden('#skF_1'(k5_xboole_0(B_313,C_314),B_313),C_314)
      | r1_tarski(k5_xboole_0(B_313,C_314),B_313) ) ),
    inference(resolution,[status(thm)],[c_1936,c_4])).

tff(c_50,plain,(
    ! [B_35,A_34] :
      ( ~ r1_tarski(B_35,A_34)
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2523,plain,(
    ! [C_314,B_313] :
      ( ~ r1_tarski(C_314,'#skF_1'(k5_xboole_0(B_313,C_314),B_313))
      | r1_tarski(k5_xboole_0(B_313,C_314),B_313) ) ),
    inference(resolution,[status(thm)],[c_2451,c_50])).

tff(c_3257,plain,(
    ! [B_340,B_341] : r1_tarski(k5_xboole_0(B_340,k5_xboole_0(B_341,B_341)),B_340) ),
    inference(resolution,[status(thm)],[c_2839,c_2523])).

tff(c_403,plain,(
    ! [A_108,C_109,B_110] :
      ( r2_hidden(A_108,C_109)
      | ~ r2_hidden(A_108,B_110)
      | r2_hidden(A_108,k5_xboole_0(B_110,C_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_429,plain,(
    ! [B_110,C_109,A_108] :
      ( ~ r1_tarski(k5_xboole_0(B_110,C_109),A_108)
      | r2_hidden(A_108,C_109)
      | ~ r2_hidden(A_108,B_110) ) ),
    inference(resolution,[status(thm)],[c_403,c_50])).

tff(c_3320,plain,(
    ! [B_340,B_341] :
      ( r2_hidden(B_340,k5_xboole_0(B_341,B_341))
      | ~ r2_hidden(B_340,B_340) ) ),
    inference(resolution,[status(thm)],[c_3257,c_429])).

tff(c_4568,plain,(
    ! [B_340] : ~ r2_hidden(B_340,B_340) ),
    inference(negUnitSimplification,[status(thm)],[c_4560,c_3320])).

tff(c_30,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_227,plain,(
    ! [A_66,C_67,B_68] :
      ( r2_hidden(A_66,C_67)
      | ~ r1_tarski(k2_tarski(A_66,B_68),C_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_236,plain,(
    ! [A_69,B_70] : r2_hidden(A_69,k2_tarski(A_69,B_70)) ),
    inference(resolution,[status(thm)],[c_24,c_227])).

tff(c_242,plain,(
    ! [A_16] : r2_hidden(A_16,k1_tarski(A_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_236])).

tff(c_355,plain,(
    ! [A_98,B_99,C_100] :
      ( r2_hidden(A_98,B_99)
      | ~ r2_hidden(A_98,C_100)
      | r2_hidden(A_98,k5_xboole_0(B_99,C_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_741,plain,(
    ! [A_161,B_162,B_163,C_164] :
      ( r2_hidden(A_161,B_162)
      | ~ r1_tarski(k5_xboole_0(B_163,C_164),B_162)
      | r2_hidden(A_161,B_163)
      | ~ r2_hidden(A_161,C_164) ) ),
    inference(resolution,[status(thm)],[c_355,c_2])).

tff(c_751,plain,(
    ! [A_161,B_163,C_164] :
      ( r2_hidden(A_161,k5_xboole_0(B_163,C_164))
      | r2_hidden(A_161,B_163)
      | ~ r2_hidden(A_161,C_164) ) ),
    inference(resolution,[status(thm)],[c_24,c_741])).

tff(c_48,plain,(
    ! [A_33] : k2_xboole_0(A_33,k1_tarski(A_33)) = k1_ordinal1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_103,plain,(
    ! [A_44,B_45,C_46] : r1_tarski(k3_xboole_0(A_44,B_45),k2_xboole_0(A_44,C_46)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_109,plain,(
    ! [A_33,B_45] : r1_tarski(k3_xboole_0(A_33,B_45),k1_ordinal1(A_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_103])).

tff(c_306,plain,(
    ! [A_92,B_93] : k5_xboole_0(k5_xboole_0(A_92,B_93),k2_xboole_0(A_92,B_93)) = k3_xboole_0(A_92,B_93) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_324,plain,(
    ! [A_33] : k5_xboole_0(k5_xboole_0(A_33,k1_tarski(A_33)),k1_ordinal1(A_33)) = k3_xboole_0(A_33,k1_tarski(A_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_306])).

tff(c_847,plain,(
    ! [A_177,B_178,B_179,C_180] :
      ( r2_hidden(A_177,B_178)
      | ~ r1_tarski(k5_xboole_0(B_179,C_180),B_178)
      | r2_hidden(A_177,C_180)
      | ~ r2_hidden(A_177,B_179) ) ),
    inference(resolution,[status(thm)],[c_403,c_2])).

tff(c_20331,plain,(
    ! [A_5893,B_5894,A_5895] :
      ( r2_hidden(A_5893,B_5894)
      | ~ r1_tarski(k3_xboole_0(A_5895,k1_tarski(A_5895)),B_5894)
      | r2_hidden(A_5893,k1_ordinal1(A_5895))
      | ~ r2_hidden(A_5893,k5_xboole_0(A_5895,k1_tarski(A_5895))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_847])).

tff(c_20379,plain,(
    ! [A_5922,A_5923] :
      ( r2_hidden(A_5922,k1_ordinal1(A_5923))
      | ~ r2_hidden(A_5922,k5_xboole_0(A_5923,k1_tarski(A_5923))) ) ),
    inference(resolution,[status(thm)],[c_109,c_20331])).

tff(c_20892,plain,(
    ! [A_6142,B_6143] :
      ( r2_hidden(A_6142,k1_ordinal1(B_6143))
      | r2_hidden(A_6142,B_6143)
      | ~ r2_hidden(A_6142,k1_tarski(B_6143)) ) ),
    inference(resolution,[status(thm)],[c_751,c_20379])).

tff(c_20976,plain,(
    ! [A_16] :
      ( r2_hidden(A_16,k1_ordinal1(A_16))
      | r2_hidden(A_16,A_16) ) ),
    inference(resolution,[status(thm)],[c_242,c_20892])).

tff(c_21004,plain,(
    ! [A_16] : r2_hidden(A_16,k1_ordinal1(A_16)) ),
    inference(negUnitSimplification,[status(thm)],[c_4568,c_20976])).

tff(c_52,plain,(
    ~ r2_hidden('#skF_2',k1_ordinal1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_21101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21004,c_52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:26:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.93/4.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.93/4.55  
% 12.93/4.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.93/4.55  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_ordinal1 > #skF_2 > #skF_1
% 12.93/4.55  
% 12.93/4.55  %Foreground sorts:
% 12.93/4.55  
% 12.93/4.55  
% 12.93/4.55  %Background operators:
% 12.93/4.55  
% 12.93/4.55  
% 12.93/4.55  %Foreground operators:
% 12.93/4.55  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 12.93/4.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.93/4.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.93/4.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.93/4.55  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 12.93/4.55  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.93/4.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.93/4.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.93/4.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.93/4.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.93/4.55  tff('#skF_2', type, '#skF_2': $i).
% 12.93/4.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.93/4.55  tff(k3_tarski, type, k3_tarski: $i > $i).
% 12.93/4.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.93/4.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.93/4.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.93/4.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.93/4.55  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 12.93/4.55  
% 12.93/4.56  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.93/4.56  tff(f_65, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 12.93/4.56  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 12.93/4.56  tff(f_39, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 12.93/4.56  tff(f_74, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 12.93/4.56  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 12.93/4.56  tff(f_69, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 12.93/4.56  tff(f_47, axiom, (![A, B, C]: r1_tarski(k3_xboole_0(A, B), k2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_xboole_1)).
% 12.93/4.56  tff(f_49, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 12.93/4.56  tff(f_77, negated_conjecture, ~(![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 12.93/4.56  tff(c_24, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.93/4.56  tff(c_254, plain, (![B_75, C_76, A_77]: (r2_hidden(B_75, C_76) | ~r1_tarski(k2_tarski(A_77, B_75), C_76))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.93/4.56  tff(c_262, plain, (![B_75, A_77]: (r2_hidden(B_75, k2_tarski(A_77, B_75)))), inference(resolution, [status(thm)], [c_24, c_254])).
% 12.93/4.56  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.93/4.56  tff(c_378, plain, (![A_101, B_102, C_103]: (r2_hidden(A_101, B_102) | r2_hidden(A_101, C_103) | ~r2_hidden(A_101, k5_xboole_0(B_102, C_103)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.93/4.56  tff(c_393, plain, (![B_102, C_103, B_2]: (r2_hidden('#skF_1'(k5_xboole_0(B_102, C_103), B_2), B_102) | r2_hidden('#skF_1'(k5_xboole_0(B_102, C_103), B_2), C_103) | r1_tarski(k5_xboole_0(B_102, C_103), B_2))), inference(resolution, [status(thm)], [c_6, c_378])).
% 12.93/4.56  tff(c_1934, plain, (![B_102, B_2]: (r1_tarski(k5_xboole_0(B_102, B_102), B_2) | r2_hidden('#skF_1'(k5_xboole_0(B_102, B_102), B_2), B_102))), inference(factorization, [status(thm), theory('equality')], [c_393])).
% 12.93/4.56  tff(c_343, plain, (![A_95, C_96, B_97]: (~r2_hidden(A_95, C_96) | ~r2_hidden(A_95, B_97) | ~r2_hidden(A_95, k5_xboole_0(B_97, C_96)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.93/4.56  tff(c_2702, plain, (![B_327, C_328, B_329]: (~r2_hidden('#skF_1'(k5_xboole_0(B_327, C_328), B_329), C_328) | ~r2_hidden('#skF_1'(k5_xboole_0(B_327, C_328), B_329), B_327) | r1_tarski(k5_xboole_0(B_327, C_328), B_329))), inference(resolution, [status(thm)], [c_6, c_343])).
% 12.93/4.56  tff(c_2762, plain, (![B_330, B_331]: (~r2_hidden('#skF_1'(k5_xboole_0(B_330, B_330), B_331), B_330) | r1_tarski(k5_xboole_0(B_330, B_330), B_331))), inference(resolution, [status(thm)], [c_1934, c_2702])).
% 12.93/4.56  tff(c_2815, plain, (![B_102, B_2]: (r1_tarski(k5_xboole_0(B_102, B_102), B_2))), inference(resolution, [status(thm)], [c_1934, c_2762])).
% 12.93/4.56  tff(c_2839, plain, (![B_332, B_333]: (r1_tarski(k5_xboole_0(B_332, B_332), B_333))), inference(resolution, [status(thm)], [c_1934, c_2762])).
% 12.93/4.56  tff(c_20, plain, (![B_10, A_9]: (B_10=A_9 | ~r1_tarski(B_10, A_9) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.93/4.56  tff(c_2925, plain, (![B_334, B_335]: (k5_xboole_0(B_334, B_334)=B_335 | ~r1_tarski(B_335, k5_xboole_0(B_334, B_334)))), inference(resolution, [status(thm)], [c_2839, c_20])).
% 12.93/4.56  tff(c_2947, plain, (![B_337, B_336]: (k5_xboole_0(B_337, B_337)=k5_xboole_0(B_336, B_336))), inference(resolution, [status(thm)], [c_2815, c_2925])).
% 12.93/4.56  tff(c_8, plain, (![A_6, C_8, B_7]: (~r2_hidden(A_6, C_8) | ~r2_hidden(A_6, B_7) | ~r2_hidden(A_6, k5_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.93/4.56  tff(c_4486, plain, (![A_381, B_382, B_383]: (~r2_hidden(A_381, B_382) | ~r2_hidden(A_381, B_382) | ~r2_hidden(A_381, k5_xboole_0(B_383, B_383)))), inference(superposition, [status(thm), theory('equality')], [c_2947, c_8])).
% 12.93/4.56  tff(c_4530, plain, (![B_75, A_77, B_383]: (~r2_hidden(B_75, k2_tarski(A_77, B_75)) | ~r2_hidden(B_75, k5_xboole_0(B_383, B_383)))), inference(resolution, [status(thm)], [c_262, c_4486])).
% 12.93/4.56  tff(c_4560, plain, (![B_75, B_383]: (~r2_hidden(B_75, k5_xboole_0(B_383, B_383)))), inference(demodulation, [status(thm), theory('equality')], [c_262, c_4530])).
% 12.93/4.56  tff(c_1936, plain, (![B_297, C_298, B_299]: (r2_hidden('#skF_1'(k5_xboole_0(B_297, C_298), B_299), B_297) | r2_hidden('#skF_1'(k5_xboole_0(B_297, C_298), B_299), C_298) | r1_tarski(k5_xboole_0(B_297, C_298), B_299))), inference(resolution, [status(thm)], [c_6, c_378])).
% 12.93/4.56  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.93/4.56  tff(c_2451, plain, (![B_313, C_314]: (r2_hidden('#skF_1'(k5_xboole_0(B_313, C_314), B_313), C_314) | r1_tarski(k5_xboole_0(B_313, C_314), B_313))), inference(resolution, [status(thm)], [c_1936, c_4])).
% 12.93/4.56  tff(c_50, plain, (![B_35, A_34]: (~r1_tarski(B_35, A_34) | ~r2_hidden(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_74])).
% 12.93/4.56  tff(c_2523, plain, (![C_314, B_313]: (~r1_tarski(C_314, '#skF_1'(k5_xboole_0(B_313, C_314), B_313)) | r1_tarski(k5_xboole_0(B_313, C_314), B_313))), inference(resolution, [status(thm)], [c_2451, c_50])).
% 12.93/4.56  tff(c_3257, plain, (![B_340, B_341]: (r1_tarski(k5_xboole_0(B_340, k5_xboole_0(B_341, B_341)), B_340))), inference(resolution, [status(thm)], [c_2839, c_2523])).
% 12.93/4.56  tff(c_403, plain, (![A_108, C_109, B_110]: (r2_hidden(A_108, C_109) | ~r2_hidden(A_108, B_110) | r2_hidden(A_108, k5_xboole_0(B_110, C_109)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.93/4.56  tff(c_429, plain, (![B_110, C_109, A_108]: (~r1_tarski(k5_xboole_0(B_110, C_109), A_108) | r2_hidden(A_108, C_109) | ~r2_hidden(A_108, B_110))), inference(resolution, [status(thm)], [c_403, c_50])).
% 12.93/4.56  tff(c_3320, plain, (![B_340, B_341]: (r2_hidden(B_340, k5_xboole_0(B_341, B_341)) | ~r2_hidden(B_340, B_340))), inference(resolution, [status(thm)], [c_3257, c_429])).
% 12.93/4.56  tff(c_4568, plain, (![B_340]: (~r2_hidden(B_340, B_340))), inference(negUnitSimplification, [status(thm)], [c_4560, c_3320])).
% 12.93/4.56  tff(c_30, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.93/4.56  tff(c_227, plain, (![A_66, C_67, B_68]: (r2_hidden(A_66, C_67) | ~r1_tarski(k2_tarski(A_66, B_68), C_67))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.93/4.56  tff(c_236, plain, (![A_69, B_70]: (r2_hidden(A_69, k2_tarski(A_69, B_70)))), inference(resolution, [status(thm)], [c_24, c_227])).
% 12.93/4.56  tff(c_242, plain, (![A_16]: (r2_hidden(A_16, k1_tarski(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_236])).
% 12.93/4.56  tff(c_355, plain, (![A_98, B_99, C_100]: (r2_hidden(A_98, B_99) | ~r2_hidden(A_98, C_100) | r2_hidden(A_98, k5_xboole_0(B_99, C_100)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.93/4.56  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.93/4.56  tff(c_741, plain, (![A_161, B_162, B_163, C_164]: (r2_hidden(A_161, B_162) | ~r1_tarski(k5_xboole_0(B_163, C_164), B_162) | r2_hidden(A_161, B_163) | ~r2_hidden(A_161, C_164))), inference(resolution, [status(thm)], [c_355, c_2])).
% 12.93/4.56  tff(c_751, plain, (![A_161, B_163, C_164]: (r2_hidden(A_161, k5_xboole_0(B_163, C_164)) | r2_hidden(A_161, B_163) | ~r2_hidden(A_161, C_164))), inference(resolution, [status(thm)], [c_24, c_741])).
% 12.93/4.56  tff(c_48, plain, (![A_33]: (k2_xboole_0(A_33, k1_tarski(A_33))=k1_ordinal1(A_33))), inference(cnfTransformation, [status(thm)], [f_69])).
% 12.93/4.56  tff(c_103, plain, (![A_44, B_45, C_46]: (r1_tarski(k3_xboole_0(A_44, B_45), k2_xboole_0(A_44, C_46)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.93/4.56  tff(c_109, plain, (![A_33, B_45]: (r1_tarski(k3_xboole_0(A_33, B_45), k1_ordinal1(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_103])).
% 12.93/4.56  tff(c_306, plain, (![A_92, B_93]: (k5_xboole_0(k5_xboole_0(A_92, B_93), k2_xboole_0(A_92, B_93))=k3_xboole_0(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.93/4.56  tff(c_324, plain, (![A_33]: (k5_xboole_0(k5_xboole_0(A_33, k1_tarski(A_33)), k1_ordinal1(A_33))=k3_xboole_0(A_33, k1_tarski(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_306])).
% 12.93/4.56  tff(c_847, plain, (![A_177, B_178, B_179, C_180]: (r2_hidden(A_177, B_178) | ~r1_tarski(k5_xboole_0(B_179, C_180), B_178) | r2_hidden(A_177, C_180) | ~r2_hidden(A_177, B_179))), inference(resolution, [status(thm)], [c_403, c_2])).
% 12.93/4.56  tff(c_20331, plain, (![A_5893, B_5894, A_5895]: (r2_hidden(A_5893, B_5894) | ~r1_tarski(k3_xboole_0(A_5895, k1_tarski(A_5895)), B_5894) | r2_hidden(A_5893, k1_ordinal1(A_5895)) | ~r2_hidden(A_5893, k5_xboole_0(A_5895, k1_tarski(A_5895))))), inference(superposition, [status(thm), theory('equality')], [c_324, c_847])).
% 12.93/4.56  tff(c_20379, plain, (![A_5922, A_5923]: (r2_hidden(A_5922, k1_ordinal1(A_5923)) | ~r2_hidden(A_5922, k5_xboole_0(A_5923, k1_tarski(A_5923))))), inference(resolution, [status(thm)], [c_109, c_20331])).
% 12.93/4.56  tff(c_20892, plain, (![A_6142, B_6143]: (r2_hidden(A_6142, k1_ordinal1(B_6143)) | r2_hidden(A_6142, B_6143) | ~r2_hidden(A_6142, k1_tarski(B_6143)))), inference(resolution, [status(thm)], [c_751, c_20379])).
% 12.93/4.56  tff(c_20976, plain, (![A_16]: (r2_hidden(A_16, k1_ordinal1(A_16)) | r2_hidden(A_16, A_16))), inference(resolution, [status(thm)], [c_242, c_20892])).
% 12.93/4.56  tff(c_21004, plain, (![A_16]: (r2_hidden(A_16, k1_ordinal1(A_16)))), inference(negUnitSimplification, [status(thm)], [c_4568, c_20976])).
% 12.93/4.56  tff(c_52, plain, (~r2_hidden('#skF_2', k1_ordinal1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 12.93/4.56  tff(c_21101, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21004, c_52])).
% 12.93/4.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.93/4.56  
% 12.93/4.56  Inference rules
% 12.93/4.56  ----------------------
% 12.93/4.56  #Ref     : 0
% 12.93/4.56  #Sup     : 4967
% 12.93/4.56  #Fact    : 2
% 12.93/4.56  #Define  : 0
% 12.93/4.56  #Split   : 1
% 12.93/4.56  #Chain   : 0
% 12.93/4.56  #Close   : 0
% 12.93/4.56  
% 12.93/4.56  Ordering : KBO
% 12.93/4.56  
% 12.93/4.56  Simplification rules
% 12.93/4.56  ----------------------
% 12.93/4.56  #Subsume      : 1049
% 12.93/4.56  #Demod        : 2043
% 12.93/4.56  #Tautology    : 1157
% 12.93/4.56  #SimpNegUnit  : 202
% 12.93/4.56  #BackRed      : 54
% 12.93/4.56  
% 12.93/4.56  #Partial instantiations: 2756
% 12.93/4.56  #Strategies tried      : 1
% 12.93/4.56  
% 12.93/4.56  Timing (in seconds)
% 12.93/4.56  ----------------------
% 12.93/4.57  Preprocessing        : 0.31
% 12.93/4.57  Parsing              : 0.16
% 12.93/4.57  CNF conversion       : 0.02
% 12.93/4.57  Main loop            : 3.47
% 12.93/4.57  Inferencing          : 0.86
% 12.93/4.57  Reduction            : 1.34
% 12.93/4.57  Demodulation         : 1.02
% 12.93/4.57  BG Simplification    : 0.10
% 12.93/4.57  Subsumption          : 0.96
% 12.93/4.57  Abstraction          : 0.13
% 12.93/4.57  MUC search           : 0.00
% 12.93/4.57  Cooper               : 0.00
% 12.93/4.57  Total                : 3.81
% 12.93/4.57  Index Insertion      : 0.00
% 12.93/4.57  Index Deletion       : 0.00
% 12.93/4.57  Index Matching       : 0.00
% 12.93/4.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
