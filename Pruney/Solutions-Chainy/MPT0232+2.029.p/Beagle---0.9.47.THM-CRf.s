%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:23 EST 2020

% Result     : Theorem 6.23s
% Output     : CNFRefutation 6.23s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 620 expanded)
%              Number of leaves         :   37 ( 224 expanded)
%              Depth                    :   18
%              Number of atoms          :  139 (1405 expanded)
%              Number of equality atoms :   61 ( 350 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_110,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_98,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_78,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k3_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l36_xboole_1)).

tff(f_72,axiom,(
    ! [A,B,C] : k2_xboole_0(A,k3_xboole_0(B,C)) = k3_xboole_0(k2_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).

tff(f_120,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => k2_tarski(A,B) = k1_tarski(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_zfmisc_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_62,plain,(
    ! [A_45,B_46] : r1_tarski(k1_tarski(A_45),k2_tarski(A_45,B_46)) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_46,plain,(
    ! [A_34,B_35] :
      ( k2_xboole_0(A_34,k4_xboole_0(B_35,A_34)) = B_35
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1621,plain,(
    ! [A_172,B_173,C_174] :
      ( r2_hidden('#skF_2'(A_172,B_173,C_174),A_172)
      | r2_hidden('#skF_3'(A_172,B_173,C_174),C_174)
      | k4_xboole_0(A_172,B_173) = C_174 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),B_7)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1649,plain,(
    ! [A_172,C_174] :
      ( r2_hidden('#skF_3'(A_172,A_172,C_174),C_174)
      | k4_xboole_0(A_172,A_172) = C_174 ) ),
    inference(resolution,[status(thm)],[c_1621,c_22])).

tff(c_3522,plain,(
    ! [A_263,C_264] :
      ( r2_hidden('#skF_3'(A_263,A_263,C_264),C_264)
      | k4_xboole_0(A_263,A_263) = C_264 ) ),
    inference(resolution,[status(thm)],[c_1621,c_22])).

tff(c_28,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_4'(A_12,B_13),B_13)
      | r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_48,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_86,plain,(
    ! [A_55,B_56] :
      ( k4_xboole_0(A_55,B_56) = A_55
      | ~ r1_xboole_0(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_90,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_86])).

tff(c_168,plain,(
    ! [D_82,B_83,A_84] :
      ( ~ r2_hidden(D_82,B_83)
      | ~ r2_hidden(D_82,k4_xboole_0(A_84,B_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_182,plain,(
    ! [D_85] :
      ( ~ r2_hidden(D_85,k1_xboole_0)
      | ~ r2_hidden(D_85,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_168])).

tff(c_549,plain,(
    ! [A_117] :
      ( ~ r2_hidden('#skF_4'(A_117,k1_xboole_0),k1_xboole_0)
      | r1_xboole_0(A_117,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28,c_182])).

tff(c_596,plain,(
    ! [A_120] : r1_xboole_0(A_120,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_28,c_549])).

tff(c_26,plain,(
    ! [A_12,B_13,C_16] :
      ( ~ r1_xboole_0(A_12,B_13)
      | ~ r2_hidden(C_16,B_13)
      | ~ r2_hidden(C_16,A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_606,plain,(
    ! [C_16,A_120] :
      ( ~ r2_hidden(C_16,k1_xboole_0)
      | ~ r2_hidden(C_16,A_120) ) ),
    inference(resolution,[status(thm)],[c_596,c_26])).

tff(c_3723,plain,(
    ! [A_270,A_271] :
      ( ~ r2_hidden('#skF_3'(A_270,A_270,k1_xboole_0),A_271)
      | k4_xboole_0(A_270,A_270) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3522,c_606])).

tff(c_3748,plain,(
    ! [A_272] : k4_xboole_0(A_272,A_272) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1649,c_3723])).

tff(c_52,plain,(
    ! [A_37,B_38] :
      ( k4_xboole_0(A_37,B_38) = A_37
      | ~ r1_xboole_0(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_607,plain,(
    ! [A_120] : k4_xboole_0(A_120,k1_xboole_0) = A_120 ),
    inference(resolution,[status(thm)],[c_596,c_52])).

tff(c_191,plain,(
    ! [A_86,B_87] :
      ( r2_hidden('#skF_1'(A_86,B_87),A_86)
      | r1_tarski(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_220,plain,(
    ! [A_91] : r1_tarski(A_91,A_91) ),
    inference(resolution,[status(thm)],[c_191,c_4])).

tff(c_42,plain,(
    ! [A_31] : k3_xboole_0(A_31,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_134,plain,(
    ! [A_65,B_66,C_67] :
      ( r1_tarski(A_65,B_66)
      | ~ r1_tarski(A_65,k3_xboole_0(B_66,C_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_137,plain,(
    ! [A_65,A_31] :
      ( r1_tarski(A_65,A_31)
      | ~ r1_tarski(A_65,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_134])).

tff(c_234,plain,(
    ! [A_92] : r1_tarski(k1_xboole_0,A_92) ),
    inference(resolution,[status(thm)],[c_220,c_137])).

tff(c_40,plain,(
    ! [A_29,B_30] :
      ( k3_xboole_0(A_29,B_30) = A_29
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_253,plain,(
    ! [A_92] : k3_xboole_0(k1_xboole_0,A_92) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_234,c_40])).

tff(c_1162,plain,(
    ! [A_154,B_155,C_156] : k2_xboole_0(k4_xboole_0(A_154,B_155),k4_xboole_0(A_154,C_156)) = k4_xboole_0(A_154,k3_xboole_0(B_155,C_156)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1193,plain,(
    ! [A_120,C_156] : k4_xboole_0(A_120,k3_xboole_0(k1_xboole_0,C_156)) = k2_xboole_0(A_120,k4_xboole_0(A_120,C_156)) ),
    inference(superposition,[status(thm),theory(equality)],[c_607,c_1162])).

tff(c_1215,plain,(
    ! [A_120,C_156] : k2_xboole_0(A_120,k4_xboole_0(A_120,C_156)) = A_120 ),
    inference(demodulation,[status(thm),theory(equality)],[c_607,c_253,c_1193])).

tff(c_3837,plain,(
    ! [A_272] : k2_xboole_0(A_272,k1_xboole_0) = A_272 ),
    inference(superposition,[status(thm),theory(equality)],[c_3748,c_1215])).

tff(c_3944,plain,(
    ! [A_274] : k2_xboole_0(A_274,k1_xboole_0) = A_274 ),
    inference(superposition,[status(thm),theory(equality)],[c_3748,c_1215])).

tff(c_38,plain,(
    ! [A_26,B_27,C_28] : k3_xboole_0(k2_xboole_0(A_26,B_27),k2_xboole_0(A_26,C_28)) = k2_xboole_0(A_26,k3_xboole_0(B_27,C_28)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3968,plain,(
    ! [A_274,B_27] : k3_xboole_0(k2_xboole_0(A_274,B_27),A_274) = k2_xboole_0(A_274,k3_xboole_0(B_27,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3944,c_38])).

tff(c_4237,plain,(
    ! [A_283,B_284] : k3_xboole_0(k2_xboole_0(A_283,B_284),A_283) = A_283 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3837,c_42,c_3968])).

tff(c_4613,plain,(
    ! [B_297,A_298] :
      ( k3_xboole_0(B_297,A_298) = A_298
      | ~ r1_tarski(A_298,B_297) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_4237])).

tff(c_4717,plain,(
    ! [A_45,B_46] : k3_xboole_0(k2_tarski(A_45,B_46),k1_tarski(A_45)) = k1_tarski(A_45) ),
    inference(resolution,[status(thm)],[c_62,c_4613])).

tff(c_70,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_4718,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),k2_tarski('#skF_5','#skF_6')) = k2_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_4613])).

tff(c_36,plain,(
    ! [A_23,B_24,C_25] :
      ( r1_tarski(A_23,B_24)
      | ~ r1_tarski(A_23,k3_xboole_0(B_24,C_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_316,plain,(
    ! [B_98,C_99] : r1_tarski(k3_xboole_0(B_98,C_99),B_98) ),
    inference(resolution,[status(thm)],[c_220,c_36])).

tff(c_341,plain,(
    ! [B_24,C_25,C_99] : r1_tarski(k3_xboole_0(k3_xboole_0(B_24,C_25),C_99),B_24) ),
    inference(resolution,[status(thm)],[c_316,c_36])).

tff(c_9830,plain,(
    ! [C_401] : r1_tarski(k3_xboole_0(k2_tarski('#skF_5','#skF_6'),C_401),k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4718,c_341])).

tff(c_9843,plain,(
    r1_tarski(k1_tarski('#skF_5'),k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4717,c_9830])).

tff(c_3740,plain,(
    ! [A_172] : k4_xboole_0(A_172,A_172) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1649,c_3723])).

tff(c_64,plain,(
    ! [B_48] : k4_xboole_0(k1_tarski(B_48),k1_tarski(B_48)) != k1_tarski(B_48) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_3747,plain,(
    ! [B_48] : k1_tarski(B_48) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3740,c_64])).

tff(c_562,plain,(
    ! [A_118,B_119] :
      ( k4_xboole_0(k1_tarski(A_118),k1_tarski(B_119)) = k1_tarski(A_118)
      | B_119 = A_118 ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_44,plain,(
    ! [A_32,B_33] :
      ( k1_xboole_0 = A_32
      | ~ r1_tarski(A_32,k4_xboole_0(B_33,A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_585,plain,(
    ! [B_119,A_118] :
      ( k1_tarski(B_119) = k1_xboole_0
      | ~ r1_tarski(k1_tarski(B_119),k1_tarski(A_118))
      | B_119 = A_118 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_562,c_44])).

tff(c_3920,plain,(
    ! [B_119,A_118] :
      ( ~ r1_tarski(k1_tarski(B_119),k1_tarski(A_118))
      | B_119 = A_118 ) ),
    inference(negUnitSimplification,[status(thm)],[c_3747,c_585])).

tff(c_9993,plain,(
    '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_9843,c_3920])).

tff(c_68,plain,(
    k2_tarski('#skF_5','#skF_6') != k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_109,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(A_60,B_61) = A_60
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_117,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),k1_tarski('#skF_7')) = k2_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_109])).

tff(c_231,plain,(
    ! [A_31] : r1_tarski(k1_xboole_0,A_31) ),
    inference(resolution,[status(thm)],[c_220,c_137])).

tff(c_610,plain,(
    ! [A_121] : k4_xboole_0(A_121,k1_xboole_0) = A_121 ),
    inference(resolution,[status(thm)],[c_596,c_52])).

tff(c_620,plain,(
    ! [A_121] :
      ( k2_xboole_0(k1_xboole_0,A_121) = A_121
      | ~ r1_tarski(k1_xboole_0,A_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_610,c_46])).

tff(c_644,plain,(
    ! [A_121] : k2_xboole_0(k1_xboole_0,A_121) = A_121 ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_620])).

tff(c_32,plain,(
    ! [A_17,B_18,C_19] : k2_xboole_0(k4_xboole_0(A_17,B_18),k4_xboole_0(A_17,C_19)) = k4_xboole_0(A_17,k3_xboole_0(B_18,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3840,plain,(
    ! [A_272,C_19] : k4_xboole_0(A_272,k3_xboole_0(A_272,C_19)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(A_272,C_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3748,c_32])).

tff(c_4996,plain,(
    ! [A_309,C_310] : k4_xboole_0(A_309,k3_xboole_0(A_309,C_310)) = k4_xboole_0(A_309,C_310) ),
    inference(demodulation,[status(thm),theory(equality)],[c_644,c_3840])).

tff(c_5146,plain,(
    k4_xboole_0(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_5','#skF_6')) = k4_xboole_0(k2_tarski('#skF_5','#skF_6'),k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_4996])).

tff(c_5189,plain,(
    k4_xboole_0(k2_tarski('#skF_5','#skF_6'),k1_tarski('#skF_7')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3740,c_5146])).

tff(c_5925,plain,
    ( k2_xboole_0(k1_tarski('#skF_7'),k1_xboole_0) = k2_tarski('#skF_5','#skF_6')
    | ~ r1_tarski(k1_tarski('#skF_7'),k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5189,c_46])).

tff(c_5953,plain,
    ( k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_7')
    | ~ r1_tarski(k1_tarski('#skF_7'),k2_tarski('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3837,c_5925])).

tff(c_5954,plain,(
    ~ r1_tarski(k1_tarski('#skF_7'),k2_tarski('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_5953])).

tff(c_10001,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),k2_tarski('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9993,c_5954])).

tff(c_10011,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_10001])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:14:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.23/2.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.23/2.33  
% 6.23/2.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.23/2.33  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.23/2.33  
% 6.23/2.33  %Foreground sorts:
% 6.23/2.33  
% 6.23/2.33  
% 6.23/2.33  %Background operators:
% 6.23/2.33  
% 6.23/2.33  
% 6.23/2.33  %Foreground operators:
% 6.23/2.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.23/2.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.23/2.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.23/2.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.23/2.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.23/2.33  tff('#skF_7', type, '#skF_7': $i).
% 6.23/2.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.23/2.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.23/2.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.23/2.33  tff('#skF_5', type, '#skF_5': $i).
% 6.23/2.33  tff('#skF_6', type, '#skF_6': $i).
% 6.23/2.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.23/2.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.23/2.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.23/2.33  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.23/2.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.23/2.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.23/2.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.23/2.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.23/2.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.23/2.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.23/2.33  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.23/2.33  
% 6.23/2.35  tff(f_110, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 6.23/2.35  tff(f_86, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 6.23/2.35  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 6.23/2.35  tff(f_60, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.23/2.35  tff(f_98, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 6.23/2.35  tff(f_102, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 6.23/2.35  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.23/2.35  tff(f_78, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 6.23/2.35  tff(f_70, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 6.23/2.35  tff(f_76, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.23/2.35  tff(f_62, axiom, (![A, B, C]: (k4_xboole_0(A, k3_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l36_xboole_1)).
% 6.23/2.35  tff(f_72, axiom, (![A, B, C]: (k2_xboole_0(A, k3_xboole_0(B, C)) = k3_xboole_0(k2_xboole_0(A, B), k2_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_xboole_1)).
% 6.23/2.35  tff(f_120, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (k2_tarski(A, B) = k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_zfmisc_1)).
% 6.23/2.35  tff(f_115, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 6.23/2.35  tff(f_82, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 6.23/2.35  tff(c_62, plain, (![A_45, B_46]: (r1_tarski(k1_tarski(A_45), k2_tarski(A_45, B_46)))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.23/2.35  tff(c_46, plain, (![A_34, B_35]: (k2_xboole_0(A_34, k4_xboole_0(B_35, A_34))=B_35 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.23/2.35  tff(c_1621, plain, (![A_172, B_173, C_174]: (r2_hidden('#skF_2'(A_172, B_173, C_174), A_172) | r2_hidden('#skF_3'(A_172, B_173, C_174), C_174) | k4_xboole_0(A_172, B_173)=C_174)), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.23/2.35  tff(c_22, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), B_7) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.23/2.35  tff(c_1649, plain, (![A_172, C_174]: (r2_hidden('#skF_3'(A_172, A_172, C_174), C_174) | k4_xboole_0(A_172, A_172)=C_174)), inference(resolution, [status(thm)], [c_1621, c_22])).
% 6.23/2.35  tff(c_3522, plain, (![A_263, C_264]: (r2_hidden('#skF_3'(A_263, A_263, C_264), C_264) | k4_xboole_0(A_263, A_263)=C_264)), inference(resolution, [status(thm)], [c_1621, c_22])).
% 6.23/2.35  tff(c_28, plain, (![A_12, B_13]: (r2_hidden('#skF_4'(A_12, B_13), B_13) | r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.23/2.35  tff(c_48, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.23/2.35  tff(c_86, plain, (![A_55, B_56]: (k4_xboole_0(A_55, B_56)=A_55 | ~r1_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.23/2.35  tff(c_90, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_86])).
% 6.23/2.35  tff(c_168, plain, (![D_82, B_83, A_84]: (~r2_hidden(D_82, B_83) | ~r2_hidden(D_82, k4_xboole_0(A_84, B_83)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.23/2.35  tff(c_182, plain, (![D_85]: (~r2_hidden(D_85, k1_xboole_0) | ~r2_hidden(D_85, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_90, c_168])).
% 6.23/2.35  tff(c_549, plain, (![A_117]: (~r2_hidden('#skF_4'(A_117, k1_xboole_0), k1_xboole_0) | r1_xboole_0(A_117, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_182])).
% 6.23/2.35  tff(c_596, plain, (![A_120]: (r1_xboole_0(A_120, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_549])).
% 6.23/2.35  tff(c_26, plain, (![A_12, B_13, C_16]: (~r1_xboole_0(A_12, B_13) | ~r2_hidden(C_16, B_13) | ~r2_hidden(C_16, A_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.23/2.35  tff(c_606, plain, (![C_16, A_120]: (~r2_hidden(C_16, k1_xboole_0) | ~r2_hidden(C_16, A_120))), inference(resolution, [status(thm)], [c_596, c_26])).
% 6.23/2.35  tff(c_3723, plain, (![A_270, A_271]: (~r2_hidden('#skF_3'(A_270, A_270, k1_xboole_0), A_271) | k4_xboole_0(A_270, A_270)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3522, c_606])).
% 6.23/2.35  tff(c_3748, plain, (![A_272]: (k4_xboole_0(A_272, A_272)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1649, c_3723])).
% 6.23/2.35  tff(c_52, plain, (![A_37, B_38]: (k4_xboole_0(A_37, B_38)=A_37 | ~r1_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.23/2.35  tff(c_607, plain, (![A_120]: (k4_xboole_0(A_120, k1_xboole_0)=A_120)), inference(resolution, [status(thm)], [c_596, c_52])).
% 6.23/2.35  tff(c_191, plain, (![A_86, B_87]: (r2_hidden('#skF_1'(A_86, B_87), A_86) | r1_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.23/2.35  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.23/2.35  tff(c_220, plain, (![A_91]: (r1_tarski(A_91, A_91))), inference(resolution, [status(thm)], [c_191, c_4])).
% 6.23/2.35  tff(c_42, plain, (![A_31]: (k3_xboole_0(A_31, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.23/2.35  tff(c_134, plain, (![A_65, B_66, C_67]: (r1_tarski(A_65, B_66) | ~r1_tarski(A_65, k3_xboole_0(B_66, C_67)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.23/2.35  tff(c_137, plain, (![A_65, A_31]: (r1_tarski(A_65, A_31) | ~r1_tarski(A_65, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_42, c_134])).
% 6.23/2.35  tff(c_234, plain, (![A_92]: (r1_tarski(k1_xboole_0, A_92))), inference(resolution, [status(thm)], [c_220, c_137])).
% 6.23/2.35  tff(c_40, plain, (![A_29, B_30]: (k3_xboole_0(A_29, B_30)=A_29 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.23/2.35  tff(c_253, plain, (![A_92]: (k3_xboole_0(k1_xboole_0, A_92)=k1_xboole_0)), inference(resolution, [status(thm)], [c_234, c_40])).
% 6.23/2.35  tff(c_1162, plain, (![A_154, B_155, C_156]: (k2_xboole_0(k4_xboole_0(A_154, B_155), k4_xboole_0(A_154, C_156))=k4_xboole_0(A_154, k3_xboole_0(B_155, C_156)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.23/2.35  tff(c_1193, plain, (![A_120, C_156]: (k4_xboole_0(A_120, k3_xboole_0(k1_xboole_0, C_156))=k2_xboole_0(A_120, k4_xboole_0(A_120, C_156)))), inference(superposition, [status(thm), theory('equality')], [c_607, c_1162])).
% 6.23/2.35  tff(c_1215, plain, (![A_120, C_156]: (k2_xboole_0(A_120, k4_xboole_0(A_120, C_156))=A_120)), inference(demodulation, [status(thm), theory('equality')], [c_607, c_253, c_1193])).
% 6.23/2.35  tff(c_3837, plain, (![A_272]: (k2_xboole_0(A_272, k1_xboole_0)=A_272)), inference(superposition, [status(thm), theory('equality')], [c_3748, c_1215])).
% 6.23/2.35  tff(c_3944, plain, (![A_274]: (k2_xboole_0(A_274, k1_xboole_0)=A_274)), inference(superposition, [status(thm), theory('equality')], [c_3748, c_1215])).
% 6.23/2.35  tff(c_38, plain, (![A_26, B_27, C_28]: (k3_xboole_0(k2_xboole_0(A_26, B_27), k2_xboole_0(A_26, C_28))=k2_xboole_0(A_26, k3_xboole_0(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.23/2.35  tff(c_3968, plain, (![A_274, B_27]: (k3_xboole_0(k2_xboole_0(A_274, B_27), A_274)=k2_xboole_0(A_274, k3_xboole_0(B_27, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_3944, c_38])).
% 6.23/2.35  tff(c_4237, plain, (![A_283, B_284]: (k3_xboole_0(k2_xboole_0(A_283, B_284), A_283)=A_283)), inference(demodulation, [status(thm), theory('equality')], [c_3837, c_42, c_3968])).
% 6.23/2.35  tff(c_4613, plain, (![B_297, A_298]: (k3_xboole_0(B_297, A_298)=A_298 | ~r1_tarski(A_298, B_297))), inference(superposition, [status(thm), theory('equality')], [c_46, c_4237])).
% 6.23/2.35  tff(c_4717, plain, (![A_45, B_46]: (k3_xboole_0(k2_tarski(A_45, B_46), k1_tarski(A_45))=k1_tarski(A_45))), inference(resolution, [status(thm)], [c_62, c_4613])).
% 6.23/2.35  tff(c_70, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.23/2.35  tff(c_4718, plain, (k3_xboole_0(k1_tarski('#skF_7'), k2_tarski('#skF_5', '#skF_6'))=k2_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_70, c_4613])).
% 6.23/2.35  tff(c_36, plain, (![A_23, B_24, C_25]: (r1_tarski(A_23, B_24) | ~r1_tarski(A_23, k3_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.23/2.35  tff(c_316, plain, (![B_98, C_99]: (r1_tarski(k3_xboole_0(B_98, C_99), B_98))), inference(resolution, [status(thm)], [c_220, c_36])).
% 6.23/2.35  tff(c_341, plain, (![B_24, C_25, C_99]: (r1_tarski(k3_xboole_0(k3_xboole_0(B_24, C_25), C_99), B_24))), inference(resolution, [status(thm)], [c_316, c_36])).
% 6.23/2.35  tff(c_9830, plain, (![C_401]: (r1_tarski(k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), C_401), k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_4718, c_341])).
% 6.23/2.35  tff(c_9843, plain, (r1_tarski(k1_tarski('#skF_5'), k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_4717, c_9830])).
% 6.23/2.35  tff(c_3740, plain, (![A_172]: (k4_xboole_0(A_172, A_172)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1649, c_3723])).
% 6.23/2.35  tff(c_64, plain, (![B_48]: (k4_xboole_0(k1_tarski(B_48), k1_tarski(B_48))!=k1_tarski(B_48))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.23/2.35  tff(c_3747, plain, (![B_48]: (k1_tarski(B_48)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3740, c_64])).
% 6.23/2.35  tff(c_562, plain, (![A_118, B_119]: (k4_xboole_0(k1_tarski(A_118), k1_tarski(B_119))=k1_tarski(A_118) | B_119=A_118)), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.23/2.35  tff(c_44, plain, (![A_32, B_33]: (k1_xboole_0=A_32 | ~r1_tarski(A_32, k4_xboole_0(B_33, A_32)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.23/2.35  tff(c_585, plain, (![B_119, A_118]: (k1_tarski(B_119)=k1_xboole_0 | ~r1_tarski(k1_tarski(B_119), k1_tarski(A_118)) | B_119=A_118)), inference(superposition, [status(thm), theory('equality')], [c_562, c_44])).
% 6.23/2.35  tff(c_3920, plain, (![B_119, A_118]: (~r1_tarski(k1_tarski(B_119), k1_tarski(A_118)) | B_119=A_118)), inference(negUnitSimplification, [status(thm)], [c_3747, c_585])).
% 6.23/2.35  tff(c_9993, plain, ('#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_9843, c_3920])).
% 6.23/2.35  tff(c_68, plain, (k2_tarski('#skF_5', '#skF_6')!=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.23/2.35  tff(c_109, plain, (![A_60, B_61]: (k3_xboole_0(A_60, B_61)=A_60 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.23/2.35  tff(c_117, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), k1_tarski('#skF_7'))=k2_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_70, c_109])).
% 6.23/2.35  tff(c_231, plain, (![A_31]: (r1_tarski(k1_xboole_0, A_31))), inference(resolution, [status(thm)], [c_220, c_137])).
% 6.23/2.35  tff(c_610, plain, (![A_121]: (k4_xboole_0(A_121, k1_xboole_0)=A_121)), inference(resolution, [status(thm)], [c_596, c_52])).
% 6.23/2.35  tff(c_620, plain, (![A_121]: (k2_xboole_0(k1_xboole_0, A_121)=A_121 | ~r1_tarski(k1_xboole_0, A_121))), inference(superposition, [status(thm), theory('equality')], [c_610, c_46])).
% 6.23/2.35  tff(c_644, plain, (![A_121]: (k2_xboole_0(k1_xboole_0, A_121)=A_121)), inference(demodulation, [status(thm), theory('equality')], [c_231, c_620])).
% 6.23/2.35  tff(c_32, plain, (![A_17, B_18, C_19]: (k2_xboole_0(k4_xboole_0(A_17, B_18), k4_xboole_0(A_17, C_19))=k4_xboole_0(A_17, k3_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.23/2.35  tff(c_3840, plain, (![A_272, C_19]: (k4_xboole_0(A_272, k3_xboole_0(A_272, C_19))=k2_xboole_0(k1_xboole_0, k4_xboole_0(A_272, C_19)))), inference(superposition, [status(thm), theory('equality')], [c_3748, c_32])).
% 6.23/2.35  tff(c_4996, plain, (![A_309, C_310]: (k4_xboole_0(A_309, k3_xboole_0(A_309, C_310))=k4_xboole_0(A_309, C_310))), inference(demodulation, [status(thm), theory('equality')], [c_644, c_3840])).
% 6.23/2.35  tff(c_5146, plain, (k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_5', '#skF_6'))=k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_117, c_4996])).
% 6.23/2.35  tff(c_5189, plain, (k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), k1_tarski('#skF_7'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3740, c_5146])).
% 6.23/2.35  tff(c_5925, plain, (k2_xboole_0(k1_tarski('#skF_7'), k1_xboole_0)=k2_tarski('#skF_5', '#skF_6') | ~r1_tarski(k1_tarski('#skF_7'), k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_5189, c_46])).
% 6.23/2.35  tff(c_5953, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_7') | ~r1_tarski(k1_tarski('#skF_7'), k2_tarski('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_3837, c_5925])).
% 6.23/2.35  tff(c_5954, plain, (~r1_tarski(k1_tarski('#skF_7'), k2_tarski('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_68, c_5953])).
% 6.23/2.35  tff(c_10001, plain, (~r1_tarski(k1_tarski('#skF_5'), k2_tarski('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_9993, c_5954])).
% 6.23/2.35  tff(c_10011, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_10001])).
% 6.23/2.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.23/2.35  
% 6.23/2.35  Inference rules
% 6.23/2.35  ----------------------
% 6.23/2.35  #Ref     : 0
% 6.23/2.35  #Sup     : 2351
% 6.23/2.35  #Fact    : 0
% 6.23/2.35  #Define  : 0
% 6.23/2.35  #Split   : 0
% 6.23/2.35  #Chain   : 0
% 6.23/2.35  #Close   : 0
% 6.23/2.35  
% 6.23/2.35  Ordering : KBO
% 6.23/2.35  
% 6.23/2.35  Simplification rules
% 6.23/2.35  ----------------------
% 6.23/2.35  #Subsume      : 139
% 6.23/2.35  #Demod        : 2415
% 6.23/2.35  #Tautology    : 1584
% 6.23/2.35  #SimpNegUnit  : 4
% 6.23/2.35  #BackRed      : 31
% 6.23/2.35  
% 6.23/2.35  #Partial instantiations: 0
% 6.23/2.35  #Strategies tried      : 1
% 6.23/2.35  
% 6.23/2.35  Timing (in seconds)
% 6.23/2.35  ----------------------
% 6.23/2.36  Preprocessing        : 0.34
% 6.23/2.36  Parsing              : 0.19
% 6.23/2.36  CNF conversion       : 0.03
% 6.23/2.36  Main loop            : 1.19
% 6.23/2.36  Inferencing          : 0.38
% 6.23/2.36  Reduction            : 0.48
% 6.23/2.36  Demodulation         : 0.38
% 6.23/2.36  BG Simplification    : 0.04
% 6.23/2.36  Subsumption          : 0.21
% 6.23/2.36  Abstraction          : 0.06
% 6.23/2.36  MUC search           : 0.00
% 6.23/2.36  Cooper               : 0.00
% 6.23/2.36  Total                : 1.58
% 6.23/2.36  Index Insertion      : 0.00
% 6.23/2.36  Index Deletion       : 0.00
% 6.23/2.36  Index Matching       : 0.00
% 6.23/2.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
