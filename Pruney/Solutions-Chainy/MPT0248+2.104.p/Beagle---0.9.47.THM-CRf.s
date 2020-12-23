%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:18 EST 2020

% Result     : Theorem 47.62s
% Output     : CNFRefutation 47.67s
% Verified   : 
% Statistics : Number of formulae       :  213 (1097 expanded)
%              Number of leaves         :   36 ( 367 expanded)
%              Depth                    :   27
%              Number of atoms          :  399 (2276 expanded)
%              Number of equality atoms :  231 (1225 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_70,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_84,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_86,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_80,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_176,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_157,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_zfmisc_1)).

tff(f_104,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_116,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_88,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_102,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
        & r1_xboole_0(C,A)
        & r1_xboole_0(D,B) )
     => C = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

tff(c_22,plain,(
    ! [B_17] : r1_tarski(B_17,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3942,plain,(
    ! [A_284,B_285] :
      ( k4_xboole_0(A_284,B_285) = k1_xboole_0
      | ~ r1_tarski(A_284,B_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3969,plain,(
    ! [B_17] : k4_xboole_0(B_17,B_17) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_3942])).

tff(c_34,plain,(
    ! [A_25] : k4_xboole_0(A_25,k1_xboole_0) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_30,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | k4_xboole_0(A_23,B_24) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_28,plain,(
    ! [A_22] : r1_tarski(k1_xboole_0,A_22) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_5061,plain,(
    ! [A_366,C_367,B_368] :
      ( r1_tarski(A_366,C_367)
      | ~ r1_tarski(B_368,C_367)
      | ~ r1_tarski(A_366,B_368) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_5089,plain,(
    ! [A_369,A_370] :
      ( r1_tarski(A_369,A_370)
      | ~ r1_tarski(A_369,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28,c_5061])).

tff(c_5095,plain,(
    ! [A_23,A_370] :
      ( r1_tarski(A_23,A_370)
      | k4_xboole_0(A_23,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_5089])).

tff(c_5104,plain,(
    ! [A_23,A_370] :
      ( r1_tarski(A_23,A_370)
      | k1_xboole_0 != A_23 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_5095])).

tff(c_84,plain,
    ( k1_xboole_0 != '#skF_6'
    | k1_tarski('#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_168,plain,(
    k1_tarski('#skF_4') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_86,plain,
    ( k1_tarski('#skF_4') != '#skF_6'
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_146,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_78,plain,(
    ! [C_58,B_57] : r1_tarski(k1_tarski(C_58),k2_tarski(B_57,C_58)) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_207,plain,(
    ! [A_81,B_82] :
      ( k4_xboole_0(A_81,B_82) = k1_xboole_0
      | ~ r1_tarski(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_230,plain,(
    ! [C_58,B_57] : k4_xboole_0(k1_tarski(C_58),k2_tarski(B_57,C_58)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_78,c_207])).

tff(c_90,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_151,plain,(
    ! [A_66,B_67] : r1_tarski(A_66,k2_xboole_0(A_66,B_67)) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_154,plain,(
    r1_tarski('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_151])).

tff(c_1142,plain,(
    ! [A_157,C_158,B_159] :
      ( r1_tarski(A_157,C_158)
      | ~ r1_tarski(B_159,C_158)
      | ~ r1_tarski(A_157,B_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3639,plain,(
    ! [A_270,B_271,A_272] :
      ( r1_tarski(A_270,B_271)
      | ~ r1_tarski(A_270,A_272)
      | k4_xboole_0(A_272,B_271) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_1142])).

tff(c_3694,plain,(
    ! [B_273] :
      ( r1_tarski('#skF_5',B_273)
      | k4_xboole_0(k1_tarski('#skF_4'),B_273) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_154,c_3639])).

tff(c_3748,plain,(
    ! [B_274] : r1_tarski('#skF_5',k2_tarski(B_274,'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_3694])).

tff(c_74,plain,(
    ! [B_57,C_58,A_56] :
      ( k2_tarski(B_57,C_58) = A_56
      | k1_tarski(C_58) = A_56
      | k1_tarski(B_57) = A_56
      | k1_xboole_0 = A_56
      | ~ r1_tarski(A_56,k2_tarski(B_57,C_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_3761,plain,(
    ! [B_274] :
      ( k2_tarski(B_274,'#skF_4') = '#skF_5'
      | k1_tarski('#skF_4') = '#skF_5'
      | k1_tarski(B_274) = '#skF_5'
      | k1_xboole_0 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_3748,c_74])).

tff(c_3828,plain,(
    ! [B_276] :
      ( k2_tarski(B_276,'#skF_4') = '#skF_5'
      | k1_tarski(B_276) = '#skF_5' ) ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_168,c_3761])).

tff(c_52,plain,(
    ! [A_44] : k2_tarski(A_44,A_44) = k1_tarski(A_44) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_3870,plain,
    ( k1_tarski('#skF_4') = '#skF_5'
    | k1_tarski('#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_3828,c_52])).

tff(c_3885,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_168,c_168,c_3870])).

tff(c_3886,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_46,plain,(
    ! [A_36,B_37] : r1_tarski(A_36,k2_xboole_0(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_48,plain,(
    ! [A_38,C_40,B_39] :
      ( r1_tarski(k2_xboole_0(A_38,C_40),B_39)
      | ~ r1_tarski(C_40,B_39)
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_4126,plain,(
    ! [B_300,A_301] :
      ( B_300 = A_301
      | ~ r1_tarski(B_300,A_301)
      | ~ r1_tarski(A_301,B_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_7077,plain,(
    ! [A_484,B_485] :
      ( k2_xboole_0(A_484,B_485) = A_484
      | ~ r1_tarski(k2_xboole_0(A_484,B_485),A_484) ) ),
    inference(resolution,[status(thm)],[c_46,c_4126])).

tff(c_7089,plain,(
    ! [B_39,C_40] :
      ( k2_xboole_0(B_39,C_40) = B_39
      | ~ r1_tarski(C_40,B_39)
      | ~ r1_tarski(B_39,B_39) ) ),
    inference(resolution,[status(thm)],[c_48,c_7077])).

tff(c_7171,plain,(
    ! [B_489,C_490] :
      ( k2_xboole_0(B_489,C_490) = B_489
      | ~ r1_tarski(C_490,B_489) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_7089])).

tff(c_7238,plain,(
    ! [A_36,B_37] : k2_xboole_0(k2_xboole_0(A_36,B_37),A_36) = k2_xboole_0(A_36,B_37) ),
    inference(resolution,[status(thm)],[c_46,c_7171])).

tff(c_5086,plain,(
    ! [A_366,A_36,B_37] :
      ( r1_tarski(A_366,k2_xboole_0(A_36,B_37))
      | ~ r1_tarski(A_366,A_36) ) ),
    inference(resolution,[status(thm)],[c_46,c_5061])).

tff(c_5111,plain,(
    ! [A_371,A_372] :
      ( r1_tarski(A_371,A_372)
      | k1_xboole_0 != A_371 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_5095])).

tff(c_32,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = k1_xboole_0
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_5141,plain,(
    ! [A_373,A_374] :
      ( k4_xboole_0(A_373,A_374) = k1_xboole_0
      | k1_xboole_0 != A_373 ) ),
    inference(resolution,[status(thm)],[c_5111,c_32])).

tff(c_36,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_5168,plain,(
    ! [A_373,A_374] :
      ( k4_xboole_0(A_373,k1_xboole_0) = k3_xboole_0(A_373,A_374)
      | k1_xboole_0 != A_373 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5141,c_36])).

tff(c_5342,plain,(
    ! [A_377,A_378] :
      ( k3_xboole_0(A_377,A_378) = A_377
      | k1_xboole_0 != A_377 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_5168])).

tff(c_4182,plain,(
    ! [A_305,B_306] : k4_xboole_0(A_305,k4_xboole_0(A_305,B_306)) = k3_xboole_0(A_305,B_306) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_44,plain,(
    ! [A_34,B_35] : r1_xboole_0(k4_xboole_0(A_34,B_35),B_35) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_4191,plain,(
    ! [A_305,B_306] : r1_xboole_0(k3_xboole_0(A_305,B_306),k4_xboole_0(A_305,B_306)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4182,c_44])).

tff(c_5486,plain,(
    ! [A_386,A_387] :
      ( r1_xboole_0(A_386,k4_xboole_0(A_386,A_387))
      | k1_xboole_0 != A_386 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5342,c_4191])).

tff(c_5538,plain,(
    ! [A_388] :
      ( r1_xboole_0(A_388,A_388)
      | k1_xboole_0 != A_388 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_5486])).

tff(c_4219,plain,(
    ! [B_17] : k4_xboole_0(B_17,k1_xboole_0) = k3_xboole_0(B_17,B_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_3969,c_4182])).

tff(c_4237,plain,(
    ! [B_17] : k3_xboole_0(B_17,B_17) = B_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4219])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4443,plain,(
    ! [A_324,B_325,C_326] :
      ( ~ r1_xboole_0(A_324,B_325)
      | ~ r2_hidden(C_326,k3_xboole_0(A_324,B_325)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4509,plain,(
    ! [A_330,B_331,A_332] :
      ( ~ r1_xboole_0(A_330,B_331)
      | r1_xboole_0(A_332,k3_xboole_0(A_330,B_331)) ) ),
    inference(resolution,[status(thm)],[c_10,c_4443])).

tff(c_4524,plain,(
    ! [B_17,A_332] :
      ( ~ r1_xboole_0(B_17,B_17)
      | r1_xboole_0(A_332,B_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4237,c_4509])).

tff(c_5621,plain,(
    ! [A_395,A_396] :
      ( r1_xboole_0(A_395,A_396)
      | k1_xboole_0 != A_396 ) ),
    inference(resolution,[status(thm)],[c_5538,c_4524])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4627,plain,(
    ! [A_344,B_345,B_346] :
      ( ~ r1_xboole_0(A_344,B_345)
      | r1_tarski(k3_xboole_0(A_344,B_345),B_346) ) ),
    inference(resolution,[status(thm)],[c_6,c_4443])).

tff(c_4153,plain,(
    ! [A_22] :
      ( k1_xboole_0 = A_22
      | ~ r1_tarski(A_22,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28,c_4126])).

tff(c_4655,plain,(
    ! [A_344,B_345] :
      ( k3_xboole_0(A_344,B_345) = k1_xboole_0
      | ~ r1_xboole_0(A_344,B_345) ) ),
    inference(resolution,[status(thm)],[c_4627,c_4153])).

tff(c_5694,plain,(
    ! [A_395] : k3_xboole_0(A_395,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5621,c_4655])).

tff(c_3887,plain,(
    k1_tarski('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_3889,plain,(
    k2_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3887,c_90])).

tff(c_5812,plain,(
    ! [A_405,C_406,B_407] :
      ( r1_tarski(k2_xboole_0(A_405,C_406),k2_xboole_0(B_407,C_406))
      | ~ r1_tarski(A_405,B_407) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_5941,plain,(
    ! [B_412] :
      ( r1_tarski('#skF_5',k2_xboole_0(B_412,'#skF_6'))
      | ~ r1_tarski('#skF_5',B_412) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3889,c_5812])).

tff(c_8058,plain,(
    ! [B_508] :
      ( k4_xboole_0('#skF_5',k2_xboole_0(B_508,'#skF_6')) = k1_xboole_0
      | ~ r1_tarski('#skF_5',B_508) ) ),
    inference(resolution,[status(thm)],[c_5941,c_32])).

tff(c_5639,plain,(
    ! [A_395,A_396] :
      ( k3_xboole_0(A_395,A_396) = k1_xboole_0
      | k1_xboole_0 != A_396 ) ),
    inference(resolution,[status(thm)],[c_5621,c_4655])).

tff(c_7776,plain,(
    ! [A_502,B_503] : k4_xboole_0(A_502,k3_xboole_0(A_502,B_503)) = k3_xboole_0(A_502,k4_xboole_0(A_502,B_503)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4182,c_36])).

tff(c_7824,plain,(
    ! [A_395,A_396] :
      ( k3_xboole_0(A_395,k4_xboole_0(A_395,A_396)) = k4_xboole_0(A_395,k1_xboole_0)
      | k1_xboole_0 != A_396 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5639,c_7776])).

tff(c_7862,plain,(
    ! [A_395,A_396] :
      ( k3_xboole_0(A_395,k4_xboole_0(A_395,A_396)) = A_395
      | k1_xboole_0 != A_396 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_7824])).

tff(c_8064,plain,(
    ! [B_508] :
      ( k3_xboole_0('#skF_5',k1_xboole_0) = '#skF_5'
      | k2_xboole_0(B_508,'#skF_6') != k1_xboole_0
      | ~ r1_tarski('#skF_5',B_508) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8058,c_7862])).

tff(c_8122,plain,(
    ! [B_508] :
      ( k1_xboole_0 = '#skF_5'
      | k2_xboole_0(B_508,'#skF_6') != k1_xboole_0
      | ~ r1_tarski('#skF_5',B_508) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5694,c_8064])).

tff(c_8140,plain,(
    ! [B_509] :
      ( k2_xboole_0(B_509,'#skF_6') != k1_xboole_0
      | ~ r1_tarski('#skF_5',B_509) ) ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_8122])).

tff(c_14288,plain,(
    ! [A_709,B_710] :
      ( k2_xboole_0(k2_xboole_0(A_709,B_710),'#skF_6') != k1_xboole_0
      | ~ r1_tarski('#skF_5',A_709) ) ),
    inference(resolution,[status(thm)],[c_5086,c_8140])).

tff(c_14310,plain,(
    ! [B_37] :
      ( k2_xboole_0('#skF_6',B_37) != k1_xboole_0
      | ~ r1_tarski('#skF_5','#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7238,c_14288])).

tff(c_14334,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_14310])).

tff(c_14342,plain,(
    k4_xboole_0('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_14334])).

tff(c_5828,plain,(
    ! [A_405] :
      ( r1_tarski(k2_xboole_0(A_405,'#skF_6'),'#skF_5')
      | ~ r1_tarski(A_405,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3889,c_5812])).

tff(c_6596,plain,(
    ! [B_463,C_464,A_465] :
      ( k2_tarski(B_463,C_464) = A_465
      | k1_tarski(C_464) = A_465
      | k1_tarski(B_463) = A_465
      | k1_xboole_0 = A_465
      | ~ r1_tarski(A_465,k2_tarski(B_463,C_464)) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_6633,plain,(
    ! [A_44,A_465] :
      ( k2_tarski(A_44,A_44) = A_465
      | k1_tarski(A_44) = A_465
      | k1_tarski(A_44) = A_465
      | k1_xboole_0 = A_465
      | ~ r1_tarski(A_465,k1_tarski(A_44)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_6596])).

tff(c_14390,plain,(
    ! [A_717,A_718] :
      ( k1_tarski(A_717) = A_718
      | k1_tarski(A_717) = A_718
      | k1_tarski(A_717) = A_718
      | k1_xboole_0 = A_718
      | ~ r1_tarski(A_718,k1_tarski(A_717)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_6633])).

tff(c_14413,plain,(
    ! [A_718] :
      ( k1_tarski('#skF_4') = A_718
      | k1_tarski('#skF_4') = A_718
      | k1_tarski('#skF_4') = A_718
      | k1_xboole_0 = A_718
      | ~ r1_tarski(A_718,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3887,c_14390])).

tff(c_19083,plain,(
    ! [A_846] :
      ( A_846 = '#skF_5'
      | A_846 = '#skF_5'
      | A_846 = '#skF_5'
      | k1_xboole_0 = A_846
      | ~ r1_tarski(A_846,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3887,c_3887,c_3887,c_14413])).

tff(c_20010,plain,(
    ! [A_892] :
      ( k2_xboole_0(A_892,'#skF_6') = '#skF_5'
      | k2_xboole_0(A_892,'#skF_6') = k1_xboole_0
      | ~ r1_tarski(A_892,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5828,c_19083])).

tff(c_20041,plain,(
    ! [A_23] :
      ( k2_xboole_0(A_23,'#skF_6') = '#skF_5'
      | k2_xboole_0(A_23,'#skF_6') = k1_xboole_0
      | k1_xboole_0 != A_23 ) ),
    inference(resolution,[status(thm)],[c_5104,c_20010])).

tff(c_7239,plain,(
    ! [B_17] : k2_xboole_0(B_17,B_17) = B_17 ),
    inference(resolution,[status(thm)],[c_22,c_7171])).

tff(c_6320,plain,(
    ! [C_444,B_445,D_446,A_447] :
      ( C_444 = B_445
      | ~ r1_xboole_0(D_446,B_445)
      | ~ r1_xboole_0(C_444,A_447)
      | k2_xboole_0(C_444,D_446) != k2_xboole_0(A_447,B_445) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_13804,plain,(
    ! [C_688,B_689,A_690,A_691] :
      ( C_688 = B_689
      | ~ r1_xboole_0(C_688,A_690)
      | k2_xboole_0(C_688,k4_xboole_0(A_691,B_689)) != k2_xboole_0(A_690,B_689) ) ),
    inference(resolution,[status(thm)],[c_44,c_6320])).

tff(c_59077,plain,(
    ! [A_1642,B_1643,B_1644,A_1645] :
      ( k4_xboole_0(A_1642,B_1643) = B_1644
      | k2_xboole_0(k4_xboole_0(A_1642,B_1643),k4_xboole_0(A_1645,B_1644)) != k2_xboole_0(B_1643,B_1644) ) ),
    inference(resolution,[status(thm)],[c_44,c_13804])).

tff(c_59283,plain,(
    ! [B_17,B_1644,A_1645] :
      ( k4_xboole_0(B_17,B_17) = B_1644
      | k2_xboole_0(k1_xboole_0,k4_xboole_0(A_1645,B_1644)) != k2_xboole_0(B_17,B_1644) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3969,c_59077])).

tff(c_75586,plain,(
    ! [B_1896,A_1897,B_1898] :
      ( k1_xboole_0 = B_1896
      | k2_xboole_0(k1_xboole_0,k4_xboole_0(A_1897,B_1896)) != k2_xboole_0(B_1898,B_1896) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3969,c_59283])).

tff(c_75737,plain,(
    ! [B_17,B_1898] :
      ( k1_xboole_0 = B_17
      | k2_xboole_0(k1_xboole_0,k1_xboole_0) != k2_xboole_0(B_1898,B_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3969,c_75586])).

tff(c_76187,plain,(
    ! [B_1909,B_1910] :
      ( k1_xboole_0 = B_1909
      | k2_xboole_0(B_1910,B_1909) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7239,c_75737])).

tff(c_76196,plain,(
    ! [A_23] :
      ( k1_xboole_0 = '#skF_6'
      | k2_xboole_0(A_23,'#skF_6') = '#skF_5'
      | k1_xboole_0 != A_23 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20041,c_76187])).

tff(c_76246,plain,(
    ! [A_1911] :
      ( k2_xboole_0(A_1911,'#skF_6') = '#skF_5'
      | k1_xboole_0 != A_1911 ) ),
    inference(negUnitSimplification,[status(thm)],[c_3886,c_76196])).

tff(c_10894,plain,(
    ! [A_621,C_622,B_623] :
      ( k4_xboole_0(k2_xboole_0(A_621,C_622),k2_xboole_0(B_623,C_622)) = k1_xboole_0
      | ~ r1_tarski(A_621,B_623) ) ),
    inference(resolution,[status(thm)],[c_5812,c_32])).

tff(c_10992,plain,(
    ! [A_621,B_17] :
      ( k4_xboole_0(k2_xboole_0(A_621,B_17),B_17) = k1_xboole_0
      | ~ r1_tarski(A_621,B_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7239,c_10894])).

tff(c_76900,plain,(
    ! [A_1911] :
      ( k4_xboole_0('#skF_5','#skF_6') = k1_xboole_0
      | ~ r1_tarski(A_1911,'#skF_6')
      | k1_xboole_0 != A_1911 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76246,c_10992])).

tff(c_77177,plain,(
    ! [A_1912] :
      ( ~ r1_tarski(A_1912,'#skF_6')
      | k1_xboole_0 != A_1912 ) ),
    inference(negUnitSimplification,[status(thm)],[c_14342,c_76900])).

tff(c_77254,plain,(
    ! [A_23] : k1_xboole_0 != A_23 ),
    inference(resolution,[status(thm)],[c_5104,c_77177])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),A_6)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4536,plain,(
    ! [A_333,B_334,C_335] :
      ( ~ r1_xboole_0(A_333,B_334)
      | ~ r2_hidden(C_335,B_334)
      | ~ r2_hidden(C_335,A_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4782,plain,(
    ! [C_353,B_354,A_355] :
      ( ~ r2_hidden(C_353,B_354)
      | ~ r2_hidden(C_353,k4_xboole_0(A_355,B_354)) ) ),
    inference(resolution,[status(thm)],[c_44,c_4536])).

tff(c_35381,plain,(
    ! [A_1296,A_1297,B_1298] :
      ( ~ r2_hidden('#skF_2'(A_1296,k4_xboole_0(A_1297,B_1298)),B_1298)
      | r1_xboole_0(A_1296,k4_xboole_0(A_1297,B_1298)) ) ),
    inference(resolution,[status(thm)],[c_10,c_4782])).

tff(c_35502,plain,(
    ! [A_1299,A_1300] : r1_xboole_0(A_1299,k4_xboole_0(A_1300,A_1299)) ),
    inference(resolution,[status(thm)],[c_12,c_35381])).

tff(c_35958,plain,(
    ! [A_1303,B_1304] : r1_xboole_0(k4_xboole_0(A_1303,B_1304),k3_xboole_0(A_1303,B_1304)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_35502])).

tff(c_36175,plain,(
    ! [A_1303,B_1304] : k3_xboole_0(k4_xboole_0(A_1303,B_1304),k3_xboole_0(A_1303,B_1304)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_35958,c_4655])).

tff(c_77370,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77254,c_36175])).

tff(c_77372,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_14310])).

tff(c_77420,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_77372,c_32])).

tff(c_7317,plain,(
    ! [A_370] : k2_xboole_0(A_370,k1_xboole_0) = A_370 ),
    inference(resolution,[status(thm)],[c_5104,c_7171])).

tff(c_130782,plain,(
    ! [A_2813,B_2814,B_2815,A_2816] :
      ( k4_xboole_0(A_2813,B_2814) = B_2815
      | k2_xboole_0(k4_xboole_0(A_2813,B_2814),k4_xboole_0(A_2816,B_2815)) != k2_xboole_0(B_2814,B_2815) ) ),
    inference(resolution,[status(thm)],[c_44,c_13804])).

tff(c_131009,plain,(
    ! [A_2813,B_2814,B_17] :
      ( k4_xboole_0(A_2813,B_2814) = B_17
      | k2_xboole_0(k4_xboole_0(A_2813,B_2814),k1_xboole_0) != k2_xboole_0(B_2814,B_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3969,c_130782])).

tff(c_165003,plain,(
    ! [A_3281,B_3282,B_3283] :
      ( k4_xboole_0(A_3281,B_3282) = B_3283
      | k4_xboole_0(A_3281,B_3282) != k2_xboole_0(B_3282,B_3283) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7317,c_131009])).

tff(c_165156,plain,(
    ! [A_25,B_3283] :
      ( k4_xboole_0(A_25,k1_xboole_0) = B_3283
      | k2_xboole_0(k1_xboole_0,B_3283) != A_25 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_165003])).

tff(c_165242,plain,(
    ! [B_3283] : k2_xboole_0(k1_xboole_0,B_3283) = B_3283 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_165156])).

tff(c_131006,plain,(
    ! [B_17,B_2815,A_2816] :
      ( k4_xboole_0(B_17,B_17) = B_2815
      | k2_xboole_0(k1_xboole_0,k4_xboole_0(A_2816,B_2815)) != k2_xboole_0(B_17,B_2815) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3969,c_130782])).

tff(c_131059,plain,(
    ! [B_2815,A_2816,B_17] :
      ( k1_xboole_0 = B_2815
      | k2_xboole_0(k1_xboole_0,k4_xboole_0(A_2816,B_2815)) != k2_xboole_0(B_17,B_2815) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3969,c_131006])).

tff(c_165438,plain,(
    ! [B_3291,A_3292,B_3293] :
      ( k1_xboole_0 = B_3291
      | k4_xboole_0(A_3292,B_3291) != k2_xboole_0(B_3293,B_3291) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165242,c_131059])).

tff(c_165492,plain,(
    ! [B_3293] :
      ( k1_xboole_0 = '#skF_6'
      | k2_xboole_0(B_3293,'#skF_6') != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77420,c_165438])).

tff(c_165596,plain,(
    ! [B_3293] : k2_xboole_0(B_3293,'#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_3886,c_165492])).

tff(c_77442,plain,(
    ! [A_1914,A_1915] :
      ( k1_tarski(A_1914) = A_1915
      | k1_tarski(A_1914) = A_1915
      | k1_tarski(A_1914) = A_1915
      | k1_xboole_0 = A_1915
      | ~ r1_tarski(A_1915,k1_tarski(A_1914)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_6633])).

tff(c_77465,plain,(
    ! [A_1915] :
      ( k1_tarski('#skF_4') = A_1915
      | k1_tarski('#skF_4') = A_1915
      | k1_tarski('#skF_4') = A_1915
      | k1_xboole_0 = A_1915
      | ~ r1_tarski(A_1915,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3887,c_77442])).

tff(c_83554,plain,(
    ! [A_2067] :
      ( A_2067 = '#skF_5'
      | A_2067 = '#skF_5'
      | A_2067 = '#skF_5'
      | k1_xboole_0 = A_2067
      | ~ r1_tarski(A_2067,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3887,c_3887,c_3887,c_77465])).

tff(c_83590,plain,(
    ! [A_405] :
      ( k2_xboole_0(A_405,'#skF_6') = '#skF_5'
      | k2_xboole_0(A_405,'#skF_6') = k1_xboole_0
      | ~ r1_tarski(A_405,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5828,c_83554])).

tff(c_166470,plain,(
    ! [A_3315] :
      ( k2_xboole_0(A_3315,'#skF_6') = '#skF_5'
      | ~ r1_tarski(A_3315,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_165596,c_83590])).

tff(c_166560,plain,(
    ! [A_3316] :
      ( k2_xboole_0(A_3316,'#skF_6') = '#skF_5'
      | k1_xboole_0 != A_3316 ) ),
    inference(resolution,[status(thm)],[c_5104,c_166470])).

tff(c_165172,plain,(
    ! [B_3283,A_25] :
      ( B_3283 = A_25
      | k2_xboole_0(k1_xboole_0,B_3283) != A_25 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_165156])).

tff(c_167814,plain,(
    '#skF_5' = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_166560,c_165172])).

tff(c_88,plain,
    ( k1_tarski('#skF_4') != '#skF_6'
    | k1_tarski('#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_3932,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3887,c_3887,c_88])).

tff(c_4143,plain,(
    ! [B_24,A_23] :
      ( B_24 = A_23
      | ~ r1_tarski(B_24,A_23)
      | k4_xboole_0(A_23,B_24) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_4126])).

tff(c_77390,plain,
    ( '#skF_5' = '#skF_6'
    | k4_xboole_0('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_77372,c_4143])).

tff(c_77412,plain,(
    k4_xboole_0('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_3932,c_77390])).

tff(c_168121,plain,(
    k4_xboole_0('#skF_6','#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_167814,c_77412])).

tff(c_168208,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3969,c_168121])).

tff(c_168210,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_168292,plain,(
    ! [A_3331,B_3332] :
      ( k4_xboole_0(A_3331,B_3332) = '#skF_5'
      | ~ r1_tarski(A_3331,B_3332) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168210,c_32])).

tff(c_168313,plain,(
    ! [B_17] : k4_xboole_0(B_17,B_17) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_22,c_168292])).

tff(c_168212,plain,(
    ! [A_25] : k4_xboole_0(A_25,'#skF_5') = A_25 ),
    inference(demodulation,[status(thm),theory(equality)],[c_168210,c_34])).

tff(c_168373,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | k4_xboole_0(A_23,B_24) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168210,c_30])).

tff(c_168214,plain,(
    ! [A_22] : r1_tarski('#skF_5',A_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168210,c_28])).

tff(c_169308,plain,(
    ! [A_3418,C_3419,B_3420] :
      ( r1_tarski(A_3418,C_3419)
      | ~ r1_tarski(B_3420,C_3419)
      | ~ r1_tarski(A_3418,B_3420) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_169330,plain,(
    ! [A_3421,A_3422] :
      ( r1_tarski(A_3421,A_3422)
      | ~ r1_tarski(A_3421,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_168214,c_169308])).

tff(c_169336,plain,(
    ! [A_23,A_3422] :
      ( r1_tarski(A_23,A_3422)
      | k4_xboole_0(A_23,'#skF_5') != '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_168373,c_169330])).

tff(c_169345,plain,(
    ! [A_23,A_3422] :
      ( r1_tarski(A_23,A_3422)
      | A_23 != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168212,c_169336])).

tff(c_169350,plain,(
    ! [A_3422] : r1_tarski('#skF_5',A_3422) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168212,c_169336])).

tff(c_169686,plain,(
    ! [A_3437,C_3438,B_3439] :
      ( r1_tarski(k2_xboole_0(A_3437,C_3438),k2_xboole_0(B_3439,C_3438))
      | ~ r1_tarski(A_3437,B_3439) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_169696,plain,(
    ! [B_3439] :
      ( r1_tarski(k1_tarski('#skF_4'),k2_xboole_0(B_3439,'#skF_6'))
      | ~ r1_tarski('#skF_5',B_3439) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_169686])).

tff(c_169710,plain,(
    ! [B_3439] : r1_tarski(k1_tarski('#skF_4'),k2_xboole_0(B_3439,'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169350,c_169696])).

tff(c_169821,plain,(
    ! [A_3443] :
      ( r1_tarski(k2_xboole_0(A_3443,'#skF_6'),k1_tarski('#skF_4'))
      | ~ r1_tarski(A_3443,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_169686])).

tff(c_18,plain,(
    ! [B_17,A_16] :
      ( B_17 = A_16
      | ~ r1_tarski(B_17,A_16)
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_169825,plain,(
    ! [A_3443] :
      ( k2_xboole_0(A_3443,'#skF_6') = k1_tarski('#skF_4')
      | ~ r1_tarski(k1_tarski('#skF_4'),k2_xboole_0(A_3443,'#skF_6'))
      | ~ r1_tarski(A_3443,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_169821,c_18])).

tff(c_170332,plain,(
    ! [A_3484] :
      ( k2_xboole_0(A_3484,'#skF_6') = k1_tarski('#skF_4')
      | ~ r1_tarski(A_3484,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169710,c_169825])).

tff(c_170359,plain,(
    ! [A_23] :
      ( k2_xboole_0(A_23,'#skF_6') = k1_tarski('#skF_4')
      | A_23 != '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_169345,c_170332])).

tff(c_168588,plain,(
    ! [B_3359,A_3360] :
      ( B_3359 = A_3360
      | ~ r1_tarski(B_3359,A_3360)
      | ~ r1_tarski(A_3360,B_3359) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_171031,plain,(
    ! [A_3518,B_3519] :
      ( k2_xboole_0(A_3518,B_3519) = A_3518
      | ~ r1_tarski(k2_xboole_0(A_3518,B_3519),A_3518) ) ),
    inference(resolution,[status(thm)],[c_46,c_168588])).

tff(c_171054,plain,(
    ! [B_39,C_40] :
      ( k2_xboole_0(B_39,C_40) = B_39
      | ~ r1_tarski(C_40,B_39)
      | ~ r1_tarski(B_39,B_39) ) ),
    inference(resolution,[status(thm)],[c_48,c_171031])).

tff(c_171176,plain,(
    ! [B_3522,C_3523] :
      ( k2_xboole_0(B_3522,C_3523) = B_3522
      | ~ r1_tarski(C_3523,B_3522) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_171054])).

tff(c_171501,plain,(
    ! [A_3422] : k2_xboole_0(A_3422,'#skF_5') = A_3422 ),
    inference(resolution,[status(thm)],[c_169345,c_171176])).

tff(c_170070,plain,(
    ! [C_3458,B_3459,D_3460,A_3461] :
      ( C_3458 = B_3459
      | ~ r1_xboole_0(D_3460,B_3459)
      | ~ r1_xboole_0(C_3458,A_3461)
      | k2_xboole_0(C_3458,D_3460) != k2_xboole_0(A_3461,B_3459) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_175790,plain,(
    ! [C_3643,B_3644,A_3645,A_3646] :
      ( C_3643 = B_3644
      | ~ r1_xboole_0(C_3643,A_3645)
      | k2_xboole_0(C_3643,k4_xboole_0(A_3646,B_3644)) != k2_xboole_0(A_3645,B_3644) ) ),
    inference(resolution,[status(thm)],[c_44,c_170070])).

tff(c_234213,plain,(
    ! [A_4652,B_4653,B_4654,A_4655] :
      ( k4_xboole_0(A_4652,B_4653) = B_4654
      | k2_xboole_0(k4_xboole_0(A_4652,B_4653),k4_xboole_0(A_4655,B_4654)) != k2_xboole_0(B_4653,B_4654) ) ),
    inference(resolution,[status(thm)],[c_44,c_175790])).

tff(c_234446,plain,(
    ! [A_4652,B_4653,B_17] :
      ( k4_xboole_0(A_4652,B_4653) = B_17
      | k2_xboole_0(k4_xboole_0(A_4652,B_4653),'#skF_5') != k2_xboole_0(B_4653,B_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168313,c_234213])).

tff(c_253241,plain,(
    ! [A_4912,B_4913,B_4914] :
      ( k4_xboole_0(A_4912,B_4913) = B_4914
      | k4_xboole_0(A_4912,B_4913) != k2_xboole_0(B_4913,B_4914) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171501,c_234446])).

tff(c_253421,plain,(
    ! [A_25,B_4914] :
      ( k4_xboole_0(A_25,'#skF_5') = B_4914
      | k2_xboole_0('#skF_5',B_4914) != A_25 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168212,c_253241])).

tff(c_253852,plain,(
    ! [B_4921,A_4922] :
      ( B_4921 = A_4922
      | k2_xboole_0('#skF_5',B_4921) != A_4922 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168212,c_253421])).

tff(c_253907,plain,(
    k1_tarski('#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_170359,c_253852])).

tff(c_168209,plain,(
    k1_tarski('#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_171241,plain,(
    ! [B_3524] : k2_xboole_0(B_3524,B_3524) = B_3524 ),
    inference(resolution,[status(thm)],[c_22,c_171176])).

tff(c_171305,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_171241,c_169710])).

tff(c_168601,plain,(
    ! [B_24,A_23] :
      ( B_24 = A_23
      | ~ r1_tarski(B_24,A_23)
      | k4_xboole_0(A_23,B_24) != '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_168373,c_168588])).

tff(c_171357,plain,
    ( k1_tarski('#skF_4') = '#skF_6'
    | k4_xboole_0('#skF_6',k1_tarski('#skF_4')) != '#skF_5' ),
    inference(resolution,[status(thm)],[c_171305,c_168601])).

tff(c_171373,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_4')) != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_168209,c_171357])).

tff(c_254033,plain,(
    k4_xboole_0('#skF_6','#skF_6') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_253907,c_171373])).

tff(c_254063,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_168313,c_254033])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:15:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 47.62/37.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 47.67/37.74  
% 47.67/37.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 47.67/37.75  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 47.67/37.75  
% 47.67/37.75  %Foreground sorts:
% 47.67/37.75  
% 47.67/37.75  
% 47.67/37.75  %Background operators:
% 47.67/37.75  
% 47.67/37.75  
% 47.67/37.75  %Foreground operators:
% 47.67/37.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 47.67/37.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 47.67/37.75  tff(k1_tarski, type, k1_tarski: $i > $i).
% 47.67/37.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 47.67/37.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 47.67/37.75  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 47.67/37.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 47.67/37.75  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 47.67/37.75  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 47.67/37.75  tff('#skF_5', type, '#skF_5': $i).
% 47.67/37.75  tff('#skF_6', type, '#skF_6': $i).
% 47.67/37.75  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 47.67/37.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 47.67/37.75  tff('#skF_4', type, '#skF_4': $i).
% 47.67/37.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 47.67/37.75  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 47.67/37.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 47.67/37.75  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 47.67/37.75  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 47.67/37.75  
% 47.67/37.78  tff(f_70, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 47.67/37.78  tff(f_84, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 47.67/37.78  tff(f_86, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 47.67/37.78  tff(f_80, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 47.67/37.78  tff(f_78, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 47.67/37.78  tff(f_176, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 47.67/37.78  tff(f_157, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_zfmisc_1)).
% 47.67/37.78  tff(f_104, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 47.67/37.78  tff(f_116, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 47.67/37.78  tff(f_110, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 47.67/37.78  tff(f_88, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 47.67/37.78  tff(f_102, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 47.67/37.78  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 47.67/37.78  tff(f_64, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 47.67/37.78  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 47.67/37.78  tff(f_114, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_xboole_1)).
% 47.67/37.78  tff(f_100, axiom, (![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 47.67/37.78  tff(c_22, plain, (![B_17]: (r1_tarski(B_17, B_17))), inference(cnfTransformation, [status(thm)], [f_70])).
% 47.67/37.78  tff(c_3942, plain, (![A_284, B_285]: (k4_xboole_0(A_284, B_285)=k1_xboole_0 | ~r1_tarski(A_284, B_285))), inference(cnfTransformation, [status(thm)], [f_84])).
% 47.67/37.78  tff(c_3969, plain, (![B_17]: (k4_xboole_0(B_17, B_17)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_3942])).
% 47.67/37.78  tff(c_34, plain, (![A_25]: (k4_xboole_0(A_25, k1_xboole_0)=A_25)), inference(cnfTransformation, [status(thm)], [f_86])).
% 47.67/37.78  tff(c_30, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | k4_xboole_0(A_23, B_24)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_84])).
% 47.67/37.78  tff(c_28, plain, (![A_22]: (r1_tarski(k1_xboole_0, A_22))), inference(cnfTransformation, [status(thm)], [f_80])).
% 47.67/37.78  tff(c_5061, plain, (![A_366, C_367, B_368]: (r1_tarski(A_366, C_367) | ~r1_tarski(B_368, C_367) | ~r1_tarski(A_366, B_368))), inference(cnfTransformation, [status(thm)], [f_78])).
% 47.67/37.78  tff(c_5089, plain, (![A_369, A_370]: (r1_tarski(A_369, A_370) | ~r1_tarski(A_369, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_5061])).
% 47.67/37.78  tff(c_5095, plain, (![A_23, A_370]: (r1_tarski(A_23, A_370) | k4_xboole_0(A_23, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_5089])).
% 47.67/37.78  tff(c_5104, plain, (![A_23, A_370]: (r1_tarski(A_23, A_370) | k1_xboole_0!=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_5095])).
% 47.67/37.78  tff(c_84, plain, (k1_xboole_0!='#skF_6' | k1_tarski('#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_176])).
% 47.67/37.78  tff(c_168, plain, (k1_tarski('#skF_4')!='#skF_5'), inference(splitLeft, [status(thm)], [c_84])).
% 47.67/37.78  tff(c_86, plain, (k1_tarski('#skF_4')!='#skF_6' | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_176])).
% 47.67/37.78  tff(c_146, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_86])).
% 47.67/37.78  tff(c_78, plain, (![C_58, B_57]: (r1_tarski(k1_tarski(C_58), k2_tarski(B_57, C_58)))), inference(cnfTransformation, [status(thm)], [f_157])).
% 47.67/37.78  tff(c_207, plain, (![A_81, B_82]: (k4_xboole_0(A_81, B_82)=k1_xboole_0 | ~r1_tarski(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_84])).
% 47.67/37.78  tff(c_230, plain, (![C_58, B_57]: (k4_xboole_0(k1_tarski(C_58), k2_tarski(B_57, C_58))=k1_xboole_0)), inference(resolution, [status(thm)], [c_78, c_207])).
% 47.67/37.78  tff(c_90, plain, (k2_xboole_0('#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_176])).
% 47.67/37.78  tff(c_151, plain, (![A_66, B_67]: (r1_tarski(A_66, k2_xboole_0(A_66, B_67)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 47.67/37.78  tff(c_154, plain, (r1_tarski('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_151])).
% 47.67/37.78  tff(c_1142, plain, (![A_157, C_158, B_159]: (r1_tarski(A_157, C_158) | ~r1_tarski(B_159, C_158) | ~r1_tarski(A_157, B_159))), inference(cnfTransformation, [status(thm)], [f_78])).
% 47.67/37.78  tff(c_3639, plain, (![A_270, B_271, A_272]: (r1_tarski(A_270, B_271) | ~r1_tarski(A_270, A_272) | k4_xboole_0(A_272, B_271)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_1142])).
% 47.67/37.78  tff(c_3694, plain, (![B_273]: (r1_tarski('#skF_5', B_273) | k4_xboole_0(k1_tarski('#skF_4'), B_273)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_154, c_3639])).
% 47.67/37.78  tff(c_3748, plain, (![B_274]: (r1_tarski('#skF_5', k2_tarski(B_274, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_230, c_3694])).
% 47.67/37.78  tff(c_74, plain, (![B_57, C_58, A_56]: (k2_tarski(B_57, C_58)=A_56 | k1_tarski(C_58)=A_56 | k1_tarski(B_57)=A_56 | k1_xboole_0=A_56 | ~r1_tarski(A_56, k2_tarski(B_57, C_58)))), inference(cnfTransformation, [status(thm)], [f_157])).
% 47.67/37.78  tff(c_3761, plain, (![B_274]: (k2_tarski(B_274, '#skF_4')='#skF_5' | k1_tarski('#skF_4')='#skF_5' | k1_tarski(B_274)='#skF_5' | k1_xboole_0='#skF_5')), inference(resolution, [status(thm)], [c_3748, c_74])).
% 47.67/37.78  tff(c_3828, plain, (![B_276]: (k2_tarski(B_276, '#skF_4')='#skF_5' | k1_tarski(B_276)='#skF_5')), inference(negUnitSimplification, [status(thm)], [c_146, c_168, c_3761])).
% 47.67/37.78  tff(c_52, plain, (![A_44]: (k2_tarski(A_44, A_44)=k1_tarski(A_44))), inference(cnfTransformation, [status(thm)], [f_116])).
% 47.67/37.78  tff(c_3870, plain, (k1_tarski('#skF_4')='#skF_5' | k1_tarski('#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_3828, c_52])).
% 47.67/37.78  tff(c_3885, plain, $false, inference(negUnitSimplification, [status(thm)], [c_168, c_168, c_3870])).
% 47.67/37.78  tff(c_3886, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_84])).
% 47.67/37.78  tff(c_46, plain, (![A_36, B_37]: (r1_tarski(A_36, k2_xboole_0(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 47.67/37.78  tff(c_48, plain, (![A_38, C_40, B_39]: (r1_tarski(k2_xboole_0(A_38, C_40), B_39) | ~r1_tarski(C_40, B_39) | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_110])).
% 47.67/37.78  tff(c_4126, plain, (![B_300, A_301]: (B_300=A_301 | ~r1_tarski(B_300, A_301) | ~r1_tarski(A_301, B_300))), inference(cnfTransformation, [status(thm)], [f_70])).
% 47.67/37.78  tff(c_7077, plain, (![A_484, B_485]: (k2_xboole_0(A_484, B_485)=A_484 | ~r1_tarski(k2_xboole_0(A_484, B_485), A_484))), inference(resolution, [status(thm)], [c_46, c_4126])).
% 47.67/37.78  tff(c_7089, plain, (![B_39, C_40]: (k2_xboole_0(B_39, C_40)=B_39 | ~r1_tarski(C_40, B_39) | ~r1_tarski(B_39, B_39))), inference(resolution, [status(thm)], [c_48, c_7077])).
% 47.67/37.78  tff(c_7171, plain, (![B_489, C_490]: (k2_xboole_0(B_489, C_490)=B_489 | ~r1_tarski(C_490, B_489))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_7089])).
% 47.67/37.78  tff(c_7238, plain, (![A_36, B_37]: (k2_xboole_0(k2_xboole_0(A_36, B_37), A_36)=k2_xboole_0(A_36, B_37))), inference(resolution, [status(thm)], [c_46, c_7171])).
% 47.67/37.78  tff(c_5086, plain, (![A_366, A_36, B_37]: (r1_tarski(A_366, k2_xboole_0(A_36, B_37)) | ~r1_tarski(A_366, A_36))), inference(resolution, [status(thm)], [c_46, c_5061])).
% 47.67/37.78  tff(c_5111, plain, (![A_371, A_372]: (r1_tarski(A_371, A_372) | k1_xboole_0!=A_371)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_5095])).
% 47.67/37.78  tff(c_32, plain, (![A_23, B_24]: (k4_xboole_0(A_23, B_24)=k1_xboole_0 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_84])).
% 47.67/37.78  tff(c_5141, plain, (![A_373, A_374]: (k4_xboole_0(A_373, A_374)=k1_xboole_0 | k1_xboole_0!=A_373)), inference(resolution, [status(thm)], [c_5111, c_32])).
% 47.67/37.78  tff(c_36, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_88])).
% 47.67/37.78  tff(c_5168, plain, (![A_373, A_374]: (k4_xboole_0(A_373, k1_xboole_0)=k3_xboole_0(A_373, A_374) | k1_xboole_0!=A_373)), inference(superposition, [status(thm), theory('equality')], [c_5141, c_36])).
% 47.67/37.78  tff(c_5342, plain, (![A_377, A_378]: (k3_xboole_0(A_377, A_378)=A_377 | k1_xboole_0!=A_377)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_5168])).
% 47.67/37.78  tff(c_4182, plain, (![A_305, B_306]: (k4_xboole_0(A_305, k4_xboole_0(A_305, B_306))=k3_xboole_0(A_305, B_306))), inference(cnfTransformation, [status(thm)], [f_88])).
% 47.67/37.78  tff(c_44, plain, (![A_34, B_35]: (r1_xboole_0(k4_xboole_0(A_34, B_35), B_35))), inference(cnfTransformation, [status(thm)], [f_102])).
% 47.67/37.78  tff(c_4191, plain, (![A_305, B_306]: (r1_xboole_0(k3_xboole_0(A_305, B_306), k4_xboole_0(A_305, B_306)))), inference(superposition, [status(thm), theory('equality')], [c_4182, c_44])).
% 47.67/37.78  tff(c_5486, plain, (![A_386, A_387]: (r1_xboole_0(A_386, k4_xboole_0(A_386, A_387)) | k1_xboole_0!=A_386)), inference(superposition, [status(thm), theory('equality')], [c_5342, c_4191])).
% 47.67/37.78  tff(c_5538, plain, (![A_388]: (r1_xboole_0(A_388, A_388) | k1_xboole_0!=A_388)), inference(superposition, [status(thm), theory('equality')], [c_34, c_5486])).
% 47.67/37.78  tff(c_4219, plain, (![B_17]: (k4_xboole_0(B_17, k1_xboole_0)=k3_xboole_0(B_17, B_17))), inference(superposition, [status(thm), theory('equality')], [c_3969, c_4182])).
% 47.67/37.78  tff(c_4237, plain, (![B_17]: (k3_xboole_0(B_17, B_17)=B_17)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_4219])).
% 47.67/37.78  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 47.67/37.78  tff(c_4443, plain, (![A_324, B_325, C_326]: (~r1_xboole_0(A_324, B_325) | ~r2_hidden(C_326, k3_xboole_0(A_324, B_325)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 47.67/37.78  tff(c_4509, plain, (![A_330, B_331, A_332]: (~r1_xboole_0(A_330, B_331) | r1_xboole_0(A_332, k3_xboole_0(A_330, B_331)))), inference(resolution, [status(thm)], [c_10, c_4443])).
% 47.67/37.78  tff(c_4524, plain, (![B_17, A_332]: (~r1_xboole_0(B_17, B_17) | r1_xboole_0(A_332, B_17))), inference(superposition, [status(thm), theory('equality')], [c_4237, c_4509])).
% 47.67/37.78  tff(c_5621, plain, (![A_395, A_396]: (r1_xboole_0(A_395, A_396) | k1_xboole_0!=A_396)), inference(resolution, [status(thm)], [c_5538, c_4524])).
% 47.67/37.78  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 47.67/37.78  tff(c_4627, plain, (![A_344, B_345, B_346]: (~r1_xboole_0(A_344, B_345) | r1_tarski(k3_xboole_0(A_344, B_345), B_346))), inference(resolution, [status(thm)], [c_6, c_4443])).
% 47.67/37.78  tff(c_4153, plain, (![A_22]: (k1_xboole_0=A_22 | ~r1_tarski(A_22, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_4126])).
% 47.67/37.78  tff(c_4655, plain, (![A_344, B_345]: (k3_xboole_0(A_344, B_345)=k1_xboole_0 | ~r1_xboole_0(A_344, B_345))), inference(resolution, [status(thm)], [c_4627, c_4153])).
% 47.67/37.78  tff(c_5694, plain, (![A_395]: (k3_xboole_0(A_395, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_5621, c_4655])).
% 47.67/37.78  tff(c_3887, plain, (k1_tarski('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_84])).
% 47.67/37.78  tff(c_3889, plain, (k2_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3887, c_90])).
% 47.67/37.78  tff(c_5812, plain, (![A_405, C_406, B_407]: (r1_tarski(k2_xboole_0(A_405, C_406), k2_xboole_0(B_407, C_406)) | ~r1_tarski(A_405, B_407))), inference(cnfTransformation, [status(thm)], [f_114])).
% 47.67/37.78  tff(c_5941, plain, (![B_412]: (r1_tarski('#skF_5', k2_xboole_0(B_412, '#skF_6')) | ~r1_tarski('#skF_5', B_412))), inference(superposition, [status(thm), theory('equality')], [c_3889, c_5812])).
% 47.67/37.78  tff(c_8058, plain, (![B_508]: (k4_xboole_0('#skF_5', k2_xboole_0(B_508, '#skF_6'))=k1_xboole_0 | ~r1_tarski('#skF_5', B_508))), inference(resolution, [status(thm)], [c_5941, c_32])).
% 47.67/37.78  tff(c_5639, plain, (![A_395, A_396]: (k3_xboole_0(A_395, A_396)=k1_xboole_0 | k1_xboole_0!=A_396)), inference(resolution, [status(thm)], [c_5621, c_4655])).
% 47.67/37.78  tff(c_7776, plain, (![A_502, B_503]: (k4_xboole_0(A_502, k3_xboole_0(A_502, B_503))=k3_xboole_0(A_502, k4_xboole_0(A_502, B_503)))), inference(superposition, [status(thm), theory('equality')], [c_4182, c_36])).
% 47.67/37.78  tff(c_7824, plain, (![A_395, A_396]: (k3_xboole_0(A_395, k4_xboole_0(A_395, A_396))=k4_xboole_0(A_395, k1_xboole_0) | k1_xboole_0!=A_396)), inference(superposition, [status(thm), theory('equality')], [c_5639, c_7776])).
% 47.67/37.78  tff(c_7862, plain, (![A_395, A_396]: (k3_xboole_0(A_395, k4_xboole_0(A_395, A_396))=A_395 | k1_xboole_0!=A_396)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_7824])).
% 47.67/37.78  tff(c_8064, plain, (![B_508]: (k3_xboole_0('#skF_5', k1_xboole_0)='#skF_5' | k2_xboole_0(B_508, '#skF_6')!=k1_xboole_0 | ~r1_tarski('#skF_5', B_508))), inference(superposition, [status(thm), theory('equality')], [c_8058, c_7862])).
% 47.67/37.78  tff(c_8122, plain, (![B_508]: (k1_xboole_0='#skF_5' | k2_xboole_0(B_508, '#skF_6')!=k1_xboole_0 | ~r1_tarski('#skF_5', B_508))), inference(demodulation, [status(thm), theory('equality')], [c_5694, c_8064])).
% 47.67/37.78  tff(c_8140, plain, (![B_509]: (k2_xboole_0(B_509, '#skF_6')!=k1_xboole_0 | ~r1_tarski('#skF_5', B_509))), inference(negUnitSimplification, [status(thm)], [c_146, c_8122])).
% 47.67/37.78  tff(c_14288, plain, (![A_709, B_710]: (k2_xboole_0(k2_xboole_0(A_709, B_710), '#skF_6')!=k1_xboole_0 | ~r1_tarski('#skF_5', A_709))), inference(resolution, [status(thm)], [c_5086, c_8140])).
% 47.67/37.78  tff(c_14310, plain, (![B_37]: (k2_xboole_0('#skF_6', B_37)!=k1_xboole_0 | ~r1_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_7238, c_14288])).
% 47.67/37.78  tff(c_14334, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_14310])).
% 47.67/37.78  tff(c_14342, plain, (k4_xboole_0('#skF_5', '#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_14334])).
% 47.67/37.78  tff(c_5828, plain, (![A_405]: (r1_tarski(k2_xboole_0(A_405, '#skF_6'), '#skF_5') | ~r1_tarski(A_405, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3889, c_5812])).
% 47.67/37.78  tff(c_6596, plain, (![B_463, C_464, A_465]: (k2_tarski(B_463, C_464)=A_465 | k1_tarski(C_464)=A_465 | k1_tarski(B_463)=A_465 | k1_xboole_0=A_465 | ~r1_tarski(A_465, k2_tarski(B_463, C_464)))), inference(cnfTransformation, [status(thm)], [f_157])).
% 47.67/37.78  tff(c_6633, plain, (![A_44, A_465]: (k2_tarski(A_44, A_44)=A_465 | k1_tarski(A_44)=A_465 | k1_tarski(A_44)=A_465 | k1_xboole_0=A_465 | ~r1_tarski(A_465, k1_tarski(A_44)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_6596])).
% 47.67/37.78  tff(c_14390, plain, (![A_717, A_718]: (k1_tarski(A_717)=A_718 | k1_tarski(A_717)=A_718 | k1_tarski(A_717)=A_718 | k1_xboole_0=A_718 | ~r1_tarski(A_718, k1_tarski(A_717)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_6633])).
% 47.67/37.78  tff(c_14413, plain, (![A_718]: (k1_tarski('#skF_4')=A_718 | k1_tarski('#skF_4')=A_718 | k1_tarski('#skF_4')=A_718 | k1_xboole_0=A_718 | ~r1_tarski(A_718, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3887, c_14390])).
% 47.67/37.78  tff(c_19083, plain, (![A_846]: (A_846='#skF_5' | A_846='#skF_5' | A_846='#skF_5' | k1_xboole_0=A_846 | ~r1_tarski(A_846, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_3887, c_3887, c_3887, c_14413])).
% 47.67/37.78  tff(c_20010, plain, (![A_892]: (k2_xboole_0(A_892, '#skF_6')='#skF_5' | k2_xboole_0(A_892, '#skF_6')=k1_xboole_0 | ~r1_tarski(A_892, '#skF_5'))), inference(resolution, [status(thm)], [c_5828, c_19083])).
% 47.67/37.78  tff(c_20041, plain, (![A_23]: (k2_xboole_0(A_23, '#skF_6')='#skF_5' | k2_xboole_0(A_23, '#skF_6')=k1_xboole_0 | k1_xboole_0!=A_23)), inference(resolution, [status(thm)], [c_5104, c_20010])).
% 47.67/37.78  tff(c_7239, plain, (![B_17]: (k2_xboole_0(B_17, B_17)=B_17)), inference(resolution, [status(thm)], [c_22, c_7171])).
% 47.67/37.78  tff(c_6320, plain, (![C_444, B_445, D_446, A_447]: (C_444=B_445 | ~r1_xboole_0(D_446, B_445) | ~r1_xboole_0(C_444, A_447) | k2_xboole_0(C_444, D_446)!=k2_xboole_0(A_447, B_445))), inference(cnfTransformation, [status(thm)], [f_100])).
% 47.67/37.78  tff(c_13804, plain, (![C_688, B_689, A_690, A_691]: (C_688=B_689 | ~r1_xboole_0(C_688, A_690) | k2_xboole_0(C_688, k4_xboole_0(A_691, B_689))!=k2_xboole_0(A_690, B_689))), inference(resolution, [status(thm)], [c_44, c_6320])).
% 47.67/37.78  tff(c_59077, plain, (![A_1642, B_1643, B_1644, A_1645]: (k4_xboole_0(A_1642, B_1643)=B_1644 | k2_xboole_0(k4_xboole_0(A_1642, B_1643), k4_xboole_0(A_1645, B_1644))!=k2_xboole_0(B_1643, B_1644))), inference(resolution, [status(thm)], [c_44, c_13804])).
% 47.67/37.78  tff(c_59283, plain, (![B_17, B_1644, A_1645]: (k4_xboole_0(B_17, B_17)=B_1644 | k2_xboole_0(k1_xboole_0, k4_xboole_0(A_1645, B_1644))!=k2_xboole_0(B_17, B_1644))), inference(superposition, [status(thm), theory('equality')], [c_3969, c_59077])).
% 47.67/37.78  tff(c_75586, plain, (![B_1896, A_1897, B_1898]: (k1_xboole_0=B_1896 | k2_xboole_0(k1_xboole_0, k4_xboole_0(A_1897, B_1896))!=k2_xboole_0(B_1898, B_1896))), inference(demodulation, [status(thm), theory('equality')], [c_3969, c_59283])).
% 47.67/37.78  tff(c_75737, plain, (![B_17, B_1898]: (k1_xboole_0=B_17 | k2_xboole_0(k1_xboole_0, k1_xboole_0)!=k2_xboole_0(B_1898, B_17))), inference(superposition, [status(thm), theory('equality')], [c_3969, c_75586])).
% 47.67/37.78  tff(c_76187, plain, (![B_1909, B_1910]: (k1_xboole_0=B_1909 | k2_xboole_0(B_1910, B_1909)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7239, c_75737])).
% 47.67/37.78  tff(c_76196, plain, (![A_23]: (k1_xboole_0='#skF_6' | k2_xboole_0(A_23, '#skF_6')='#skF_5' | k1_xboole_0!=A_23)), inference(superposition, [status(thm), theory('equality')], [c_20041, c_76187])).
% 47.67/37.78  tff(c_76246, plain, (![A_1911]: (k2_xboole_0(A_1911, '#skF_6')='#skF_5' | k1_xboole_0!=A_1911)), inference(negUnitSimplification, [status(thm)], [c_3886, c_76196])).
% 47.67/37.78  tff(c_10894, plain, (![A_621, C_622, B_623]: (k4_xboole_0(k2_xboole_0(A_621, C_622), k2_xboole_0(B_623, C_622))=k1_xboole_0 | ~r1_tarski(A_621, B_623))), inference(resolution, [status(thm)], [c_5812, c_32])).
% 47.67/37.78  tff(c_10992, plain, (![A_621, B_17]: (k4_xboole_0(k2_xboole_0(A_621, B_17), B_17)=k1_xboole_0 | ~r1_tarski(A_621, B_17))), inference(superposition, [status(thm), theory('equality')], [c_7239, c_10894])).
% 47.67/37.78  tff(c_76900, plain, (![A_1911]: (k4_xboole_0('#skF_5', '#skF_6')=k1_xboole_0 | ~r1_tarski(A_1911, '#skF_6') | k1_xboole_0!=A_1911)), inference(superposition, [status(thm), theory('equality')], [c_76246, c_10992])).
% 47.67/37.78  tff(c_77177, plain, (![A_1912]: (~r1_tarski(A_1912, '#skF_6') | k1_xboole_0!=A_1912)), inference(negUnitSimplification, [status(thm)], [c_14342, c_76900])).
% 47.67/37.78  tff(c_77254, plain, (![A_23]: (k1_xboole_0!=A_23)), inference(resolution, [status(thm)], [c_5104, c_77177])).
% 47.67/37.78  tff(c_12, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), A_6) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 47.67/37.78  tff(c_4536, plain, (![A_333, B_334, C_335]: (~r1_xboole_0(A_333, B_334) | ~r2_hidden(C_335, B_334) | ~r2_hidden(C_335, A_333))), inference(cnfTransformation, [status(thm)], [f_50])).
% 47.67/37.78  tff(c_4782, plain, (![C_353, B_354, A_355]: (~r2_hidden(C_353, B_354) | ~r2_hidden(C_353, k4_xboole_0(A_355, B_354)))), inference(resolution, [status(thm)], [c_44, c_4536])).
% 47.67/37.78  tff(c_35381, plain, (![A_1296, A_1297, B_1298]: (~r2_hidden('#skF_2'(A_1296, k4_xboole_0(A_1297, B_1298)), B_1298) | r1_xboole_0(A_1296, k4_xboole_0(A_1297, B_1298)))), inference(resolution, [status(thm)], [c_10, c_4782])).
% 47.67/37.78  tff(c_35502, plain, (![A_1299, A_1300]: (r1_xboole_0(A_1299, k4_xboole_0(A_1300, A_1299)))), inference(resolution, [status(thm)], [c_12, c_35381])).
% 47.67/37.78  tff(c_35958, plain, (![A_1303, B_1304]: (r1_xboole_0(k4_xboole_0(A_1303, B_1304), k3_xboole_0(A_1303, B_1304)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_35502])).
% 47.67/37.78  tff(c_36175, plain, (![A_1303, B_1304]: (k3_xboole_0(k4_xboole_0(A_1303, B_1304), k3_xboole_0(A_1303, B_1304))=k1_xboole_0)), inference(resolution, [status(thm)], [c_35958, c_4655])).
% 47.67/37.78  tff(c_77370, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77254, c_36175])).
% 47.67/37.78  tff(c_77372, plain, (r1_tarski('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_14310])).
% 47.67/37.78  tff(c_77420, plain, (k4_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_77372, c_32])).
% 47.67/37.78  tff(c_7317, plain, (![A_370]: (k2_xboole_0(A_370, k1_xboole_0)=A_370)), inference(resolution, [status(thm)], [c_5104, c_7171])).
% 47.67/37.78  tff(c_130782, plain, (![A_2813, B_2814, B_2815, A_2816]: (k4_xboole_0(A_2813, B_2814)=B_2815 | k2_xboole_0(k4_xboole_0(A_2813, B_2814), k4_xboole_0(A_2816, B_2815))!=k2_xboole_0(B_2814, B_2815))), inference(resolution, [status(thm)], [c_44, c_13804])).
% 47.67/37.78  tff(c_131009, plain, (![A_2813, B_2814, B_17]: (k4_xboole_0(A_2813, B_2814)=B_17 | k2_xboole_0(k4_xboole_0(A_2813, B_2814), k1_xboole_0)!=k2_xboole_0(B_2814, B_17))), inference(superposition, [status(thm), theory('equality')], [c_3969, c_130782])).
% 47.67/37.78  tff(c_165003, plain, (![A_3281, B_3282, B_3283]: (k4_xboole_0(A_3281, B_3282)=B_3283 | k4_xboole_0(A_3281, B_3282)!=k2_xboole_0(B_3282, B_3283))), inference(demodulation, [status(thm), theory('equality')], [c_7317, c_131009])).
% 47.67/37.78  tff(c_165156, plain, (![A_25, B_3283]: (k4_xboole_0(A_25, k1_xboole_0)=B_3283 | k2_xboole_0(k1_xboole_0, B_3283)!=A_25)), inference(superposition, [status(thm), theory('equality')], [c_34, c_165003])).
% 47.67/37.78  tff(c_165242, plain, (![B_3283]: (k2_xboole_0(k1_xboole_0, B_3283)=B_3283)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_165156])).
% 47.67/37.78  tff(c_131006, plain, (![B_17, B_2815, A_2816]: (k4_xboole_0(B_17, B_17)=B_2815 | k2_xboole_0(k1_xboole_0, k4_xboole_0(A_2816, B_2815))!=k2_xboole_0(B_17, B_2815))), inference(superposition, [status(thm), theory('equality')], [c_3969, c_130782])).
% 47.67/37.78  tff(c_131059, plain, (![B_2815, A_2816, B_17]: (k1_xboole_0=B_2815 | k2_xboole_0(k1_xboole_0, k4_xboole_0(A_2816, B_2815))!=k2_xboole_0(B_17, B_2815))), inference(demodulation, [status(thm), theory('equality')], [c_3969, c_131006])).
% 47.67/37.78  tff(c_165438, plain, (![B_3291, A_3292, B_3293]: (k1_xboole_0=B_3291 | k4_xboole_0(A_3292, B_3291)!=k2_xboole_0(B_3293, B_3291))), inference(demodulation, [status(thm), theory('equality')], [c_165242, c_131059])).
% 47.67/37.78  tff(c_165492, plain, (![B_3293]: (k1_xboole_0='#skF_6' | k2_xboole_0(B_3293, '#skF_6')!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_77420, c_165438])).
% 47.67/37.78  tff(c_165596, plain, (![B_3293]: (k2_xboole_0(B_3293, '#skF_6')!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_3886, c_165492])).
% 47.67/37.78  tff(c_77442, plain, (![A_1914, A_1915]: (k1_tarski(A_1914)=A_1915 | k1_tarski(A_1914)=A_1915 | k1_tarski(A_1914)=A_1915 | k1_xboole_0=A_1915 | ~r1_tarski(A_1915, k1_tarski(A_1914)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_6633])).
% 47.67/37.78  tff(c_77465, plain, (![A_1915]: (k1_tarski('#skF_4')=A_1915 | k1_tarski('#skF_4')=A_1915 | k1_tarski('#skF_4')=A_1915 | k1_xboole_0=A_1915 | ~r1_tarski(A_1915, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3887, c_77442])).
% 47.67/37.78  tff(c_83554, plain, (![A_2067]: (A_2067='#skF_5' | A_2067='#skF_5' | A_2067='#skF_5' | k1_xboole_0=A_2067 | ~r1_tarski(A_2067, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_3887, c_3887, c_3887, c_77465])).
% 47.67/37.78  tff(c_83590, plain, (![A_405]: (k2_xboole_0(A_405, '#skF_6')='#skF_5' | k2_xboole_0(A_405, '#skF_6')=k1_xboole_0 | ~r1_tarski(A_405, '#skF_5'))), inference(resolution, [status(thm)], [c_5828, c_83554])).
% 47.67/37.78  tff(c_166470, plain, (![A_3315]: (k2_xboole_0(A_3315, '#skF_6')='#skF_5' | ~r1_tarski(A_3315, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_165596, c_83590])).
% 47.67/37.78  tff(c_166560, plain, (![A_3316]: (k2_xboole_0(A_3316, '#skF_6')='#skF_5' | k1_xboole_0!=A_3316)), inference(resolution, [status(thm)], [c_5104, c_166470])).
% 47.67/37.78  tff(c_165172, plain, (![B_3283, A_25]: (B_3283=A_25 | k2_xboole_0(k1_xboole_0, B_3283)!=A_25)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_165156])).
% 47.67/37.78  tff(c_167814, plain, ('#skF_5'='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_166560, c_165172])).
% 47.67/37.78  tff(c_88, plain, (k1_tarski('#skF_4')!='#skF_6' | k1_tarski('#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_176])).
% 47.67/37.78  tff(c_3932, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3887, c_3887, c_88])).
% 47.67/37.78  tff(c_4143, plain, (![B_24, A_23]: (B_24=A_23 | ~r1_tarski(B_24, A_23) | k4_xboole_0(A_23, B_24)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_4126])).
% 47.67/37.78  tff(c_77390, plain, ('#skF_5'='#skF_6' | k4_xboole_0('#skF_6', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_77372, c_4143])).
% 47.67/37.78  tff(c_77412, plain, (k4_xboole_0('#skF_6', '#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_3932, c_77390])).
% 47.67/37.78  tff(c_168121, plain, (k4_xboole_0('#skF_6', '#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_167814, c_77412])).
% 47.67/37.78  tff(c_168208, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3969, c_168121])).
% 47.67/37.78  tff(c_168210, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_86])).
% 47.67/37.78  tff(c_168292, plain, (![A_3331, B_3332]: (k4_xboole_0(A_3331, B_3332)='#skF_5' | ~r1_tarski(A_3331, B_3332))), inference(demodulation, [status(thm), theory('equality')], [c_168210, c_32])).
% 47.67/37.78  tff(c_168313, plain, (![B_17]: (k4_xboole_0(B_17, B_17)='#skF_5')), inference(resolution, [status(thm)], [c_22, c_168292])).
% 47.67/37.78  tff(c_168212, plain, (![A_25]: (k4_xboole_0(A_25, '#skF_5')=A_25)), inference(demodulation, [status(thm), theory('equality')], [c_168210, c_34])).
% 47.67/37.78  tff(c_168373, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | k4_xboole_0(A_23, B_24)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_168210, c_30])).
% 47.67/37.78  tff(c_168214, plain, (![A_22]: (r1_tarski('#skF_5', A_22))), inference(demodulation, [status(thm), theory('equality')], [c_168210, c_28])).
% 47.67/37.78  tff(c_169308, plain, (![A_3418, C_3419, B_3420]: (r1_tarski(A_3418, C_3419) | ~r1_tarski(B_3420, C_3419) | ~r1_tarski(A_3418, B_3420))), inference(cnfTransformation, [status(thm)], [f_78])).
% 47.67/37.78  tff(c_169330, plain, (![A_3421, A_3422]: (r1_tarski(A_3421, A_3422) | ~r1_tarski(A_3421, '#skF_5'))), inference(resolution, [status(thm)], [c_168214, c_169308])).
% 47.67/37.78  tff(c_169336, plain, (![A_23, A_3422]: (r1_tarski(A_23, A_3422) | k4_xboole_0(A_23, '#skF_5')!='#skF_5')), inference(resolution, [status(thm)], [c_168373, c_169330])).
% 47.67/37.78  tff(c_169345, plain, (![A_23, A_3422]: (r1_tarski(A_23, A_3422) | A_23!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_168212, c_169336])).
% 47.67/37.78  tff(c_169350, plain, (![A_3422]: (r1_tarski('#skF_5', A_3422))), inference(demodulation, [status(thm), theory('equality')], [c_168212, c_169336])).
% 47.67/37.78  tff(c_169686, plain, (![A_3437, C_3438, B_3439]: (r1_tarski(k2_xboole_0(A_3437, C_3438), k2_xboole_0(B_3439, C_3438)) | ~r1_tarski(A_3437, B_3439))), inference(cnfTransformation, [status(thm)], [f_114])).
% 47.67/37.78  tff(c_169696, plain, (![B_3439]: (r1_tarski(k1_tarski('#skF_4'), k2_xboole_0(B_3439, '#skF_6')) | ~r1_tarski('#skF_5', B_3439))), inference(superposition, [status(thm), theory('equality')], [c_90, c_169686])).
% 47.67/37.78  tff(c_169710, plain, (![B_3439]: (r1_tarski(k1_tarski('#skF_4'), k2_xboole_0(B_3439, '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_169350, c_169696])).
% 47.67/37.78  tff(c_169821, plain, (![A_3443]: (r1_tarski(k2_xboole_0(A_3443, '#skF_6'), k1_tarski('#skF_4')) | ~r1_tarski(A_3443, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_169686])).
% 47.67/37.78  tff(c_18, plain, (![B_17, A_16]: (B_17=A_16 | ~r1_tarski(B_17, A_16) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_70])).
% 47.67/37.78  tff(c_169825, plain, (![A_3443]: (k2_xboole_0(A_3443, '#skF_6')=k1_tarski('#skF_4') | ~r1_tarski(k1_tarski('#skF_4'), k2_xboole_0(A_3443, '#skF_6')) | ~r1_tarski(A_3443, '#skF_5'))), inference(resolution, [status(thm)], [c_169821, c_18])).
% 47.67/37.78  tff(c_170332, plain, (![A_3484]: (k2_xboole_0(A_3484, '#skF_6')=k1_tarski('#skF_4') | ~r1_tarski(A_3484, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_169710, c_169825])).
% 47.67/37.78  tff(c_170359, plain, (![A_23]: (k2_xboole_0(A_23, '#skF_6')=k1_tarski('#skF_4') | A_23!='#skF_5')), inference(resolution, [status(thm)], [c_169345, c_170332])).
% 47.67/37.78  tff(c_168588, plain, (![B_3359, A_3360]: (B_3359=A_3360 | ~r1_tarski(B_3359, A_3360) | ~r1_tarski(A_3360, B_3359))), inference(cnfTransformation, [status(thm)], [f_70])).
% 47.67/37.78  tff(c_171031, plain, (![A_3518, B_3519]: (k2_xboole_0(A_3518, B_3519)=A_3518 | ~r1_tarski(k2_xboole_0(A_3518, B_3519), A_3518))), inference(resolution, [status(thm)], [c_46, c_168588])).
% 47.67/37.78  tff(c_171054, plain, (![B_39, C_40]: (k2_xboole_0(B_39, C_40)=B_39 | ~r1_tarski(C_40, B_39) | ~r1_tarski(B_39, B_39))), inference(resolution, [status(thm)], [c_48, c_171031])).
% 47.67/37.78  tff(c_171176, plain, (![B_3522, C_3523]: (k2_xboole_0(B_3522, C_3523)=B_3522 | ~r1_tarski(C_3523, B_3522))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_171054])).
% 47.67/37.78  tff(c_171501, plain, (![A_3422]: (k2_xboole_0(A_3422, '#skF_5')=A_3422)), inference(resolution, [status(thm)], [c_169345, c_171176])).
% 47.67/37.78  tff(c_170070, plain, (![C_3458, B_3459, D_3460, A_3461]: (C_3458=B_3459 | ~r1_xboole_0(D_3460, B_3459) | ~r1_xboole_0(C_3458, A_3461) | k2_xboole_0(C_3458, D_3460)!=k2_xboole_0(A_3461, B_3459))), inference(cnfTransformation, [status(thm)], [f_100])).
% 47.67/37.78  tff(c_175790, plain, (![C_3643, B_3644, A_3645, A_3646]: (C_3643=B_3644 | ~r1_xboole_0(C_3643, A_3645) | k2_xboole_0(C_3643, k4_xboole_0(A_3646, B_3644))!=k2_xboole_0(A_3645, B_3644))), inference(resolution, [status(thm)], [c_44, c_170070])).
% 47.67/37.78  tff(c_234213, plain, (![A_4652, B_4653, B_4654, A_4655]: (k4_xboole_0(A_4652, B_4653)=B_4654 | k2_xboole_0(k4_xboole_0(A_4652, B_4653), k4_xboole_0(A_4655, B_4654))!=k2_xboole_0(B_4653, B_4654))), inference(resolution, [status(thm)], [c_44, c_175790])).
% 47.67/37.78  tff(c_234446, plain, (![A_4652, B_4653, B_17]: (k4_xboole_0(A_4652, B_4653)=B_17 | k2_xboole_0(k4_xboole_0(A_4652, B_4653), '#skF_5')!=k2_xboole_0(B_4653, B_17))), inference(superposition, [status(thm), theory('equality')], [c_168313, c_234213])).
% 47.67/37.78  tff(c_253241, plain, (![A_4912, B_4913, B_4914]: (k4_xboole_0(A_4912, B_4913)=B_4914 | k4_xboole_0(A_4912, B_4913)!=k2_xboole_0(B_4913, B_4914))), inference(demodulation, [status(thm), theory('equality')], [c_171501, c_234446])).
% 47.67/37.78  tff(c_253421, plain, (![A_25, B_4914]: (k4_xboole_0(A_25, '#skF_5')=B_4914 | k2_xboole_0('#skF_5', B_4914)!=A_25)), inference(superposition, [status(thm), theory('equality')], [c_168212, c_253241])).
% 47.67/37.78  tff(c_253852, plain, (![B_4921, A_4922]: (B_4921=A_4922 | k2_xboole_0('#skF_5', B_4921)!=A_4922)), inference(demodulation, [status(thm), theory('equality')], [c_168212, c_253421])).
% 47.67/37.78  tff(c_253907, plain, (k1_tarski('#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_170359, c_253852])).
% 47.67/37.78  tff(c_168209, plain, (k1_tarski('#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_86])).
% 47.67/37.78  tff(c_171241, plain, (![B_3524]: (k2_xboole_0(B_3524, B_3524)=B_3524)), inference(resolution, [status(thm)], [c_22, c_171176])).
% 47.67/37.78  tff(c_171305, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_171241, c_169710])).
% 47.67/37.78  tff(c_168601, plain, (![B_24, A_23]: (B_24=A_23 | ~r1_tarski(B_24, A_23) | k4_xboole_0(A_23, B_24)!='#skF_5')), inference(resolution, [status(thm)], [c_168373, c_168588])).
% 47.67/37.78  tff(c_171357, plain, (k1_tarski('#skF_4')='#skF_6' | k4_xboole_0('#skF_6', k1_tarski('#skF_4'))!='#skF_5'), inference(resolution, [status(thm)], [c_171305, c_168601])).
% 47.67/37.78  tff(c_171373, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_4'))!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_168209, c_171357])).
% 47.67/37.78  tff(c_254033, plain, (k4_xboole_0('#skF_6', '#skF_6')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_253907, c_171373])).
% 47.67/37.78  tff(c_254063, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_168313, c_254033])).
% 47.67/37.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 47.67/37.78  
% 47.67/37.78  Inference rules
% 47.67/37.78  ----------------------
% 47.67/37.78  #Ref     : 25
% 47.67/37.78  #Sup     : 65314
% 47.67/37.78  #Fact    : 1
% 47.67/37.78  #Define  : 0
% 47.67/37.78  #Split   : 29
% 47.67/37.78  #Chain   : 0
% 47.67/37.78  #Close   : 0
% 47.67/37.78  
% 47.67/37.78  Ordering : KBO
% 47.67/37.78  
% 47.67/37.78  Simplification rules
% 47.67/37.78  ----------------------
% 47.67/37.78  #Subsume      : 37150
% 47.67/37.78  #Demod        : 26048
% 47.67/37.78  #Tautology    : 12289
% 47.67/37.78  #SimpNegUnit  : 2656
% 47.67/37.78  #BackRed      : 840
% 47.67/37.78  
% 47.67/37.78  #Partial instantiations: 0
% 47.67/37.78  #Strategies tried      : 1
% 47.67/37.78  
% 47.67/37.78  Timing (in seconds)
% 47.67/37.78  ----------------------
% 47.67/37.78  Preprocessing        : 0.36
% 47.67/37.78  Parsing              : 0.19
% 47.67/37.78  CNF conversion       : 0.03
% 47.67/37.78  Main loop            : 36.62
% 47.67/37.78  Inferencing          : 4.13
% 47.67/37.78  Reduction            : 15.03
% 47.67/37.78  Demodulation         : 11.17
% 47.67/37.78  BG Simplification    : 0.35
% 47.67/37.78  Subsumption          : 15.46
% 47.67/37.78  Abstraction          : 0.70
% 47.67/37.78  MUC search           : 0.00
% 47.67/37.78  Cooper               : 0.00
% 47.67/37.78  Total                : 37.05
% 47.67/37.78  Index Insertion      : 0.00
% 47.67/37.78  Index Deletion       : 0.00
% 47.67/37.78  Index Matching       : 0.00
% 47.67/37.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
