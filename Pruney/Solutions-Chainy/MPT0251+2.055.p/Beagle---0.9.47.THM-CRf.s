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
% DateTime   : Thu Dec  3 09:50:53 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 384 expanded)
%              Number of leaves         :   33 ( 142 expanded)
%              Depth                    :   23
%              Number of atoms          :   97 ( 441 expanded)
%              Number of equality atoms :   52 ( 332 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_54,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

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

tff(f_70,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_84,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_52,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_22,plain,(
    ! [A_11] : k2_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,(
    ! [A_4,B_5] :
      ( r2_hidden('#skF_1'(A_4,B_5),A_4)
      | r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_34,plain,(
    ! [B_23,A_22] : k2_tarski(B_23,A_22) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_133,plain,(
    ! [A_52,B_53] : k3_tarski(k2_tarski(A_52,B_53)) = k2_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_168,plain,(
    ! [B_55,A_56] : k3_tarski(k2_tarski(B_55,A_56)) = k2_xboole_0(A_56,B_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_133])).

tff(c_48,plain,(
    ! [A_36,B_37] : k3_tarski(k2_tarski(A_36,B_37)) = k2_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_195,plain,(
    ! [B_57,A_58] : k2_xboole_0(B_57,A_58) = k2_xboole_0(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_48])).

tff(c_211,plain,(
    ! [A_58] : k2_xboole_0(k1_xboole_0,A_58) = A_58 ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_22])).

tff(c_351,plain,(
    ! [A_70,B_71] : k2_xboole_0(A_70,k4_xboole_0(B_71,A_70)) = k2_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_358,plain,(
    ! [B_71] : k4_xboole_0(B_71,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_211])).

tff(c_382,plain,(
    ! [B_72] : k4_xboole_0(B_72,k1_xboole_0) = B_72 ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_358])).

tff(c_242,plain,(
    ! [A_59] : k2_xboole_0(k1_xboole_0,A_59) = A_59 ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_22])).

tff(c_24,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_255,plain,(
    ! [B_13] : k3_xboole_0(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_24])).

tff(c_305,plain,(
    ! [A_65,B_66] : k5_xboole_0(A_65,k3_xboole_0(A_65,B_66)) = k4_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_317,plain,(
    ! [B_67] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_305])).

tff(c_314,plain,(
    ! [B_13] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_305])).

tff(c_320,plain,(
    ! [B_67,B_13] : k4_xboole_0(k1_xboole_0,B_67) = k4_xboole_0(k1_xboole_0,B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_314])).

tff(c_396,plain,(
    ! [B_67] : k4_xboole_0(k1_xboole_0,B_67) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_320])).

tff(c_413,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_314])).

tff(c_706,plain,(
    ! [A_93,C_94,B_95] :
      ( ~ r2_hidden(A_93,C_94)
      | ~ r2_hidden(A_93,B_95)
      | ~ r2_hidden(A_93,k5_xboole_0(B_95,C_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_723,plain,(
    ! [A_96] :
      ( ~ r2_hidden(A_96,k1_xboole_0)
      | ~ r2_hidden(A_96,k1_xboole_0)
      | ~ r2_hidden(A_96,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_706])).

tff(c_782,plain,(
    ! [B_104] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0,B_104),k1_xboole_0)
      | r1_xboole_0(k1_xboole_0,B_104) ) ),
    inference(resolution,[status(thm)],[c_18,c_723])).

tff(c_793,plain,(
    ! [B_5] : r1_xboole_0(k1_xboole_0,B_5) ),
    inference(resolution,[status(thm)],[c_18,c_782])).

tff(c_504,plain,(
    ! [A_77,B_78] :
      ( k4_xboole_0(k2_xboole_0(A_77,B_78),B_78) = A_77
      | ~ r1_xboole_0(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_536,plain,(
    ! [A_58] :
      ( k4_xboole_0(A_58,A_58) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_504])).

tff(c_796,plain,(
    ! [A_58] : k4_xboole_0(A_58,A_58) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_793,c_536])).

tff(c_16,plain,(
    ! [A_4,B_5] :
      ( r2_hidden('#skF_1'(A_4,B_5),B_5)
      | r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_749,plain,(
    ! [A_100] :
      ( ~ r2_hidden('#skF_1'(A_100,k1_xboole_0),k1_xboole_0)
      | r1_xboole_0(A_100,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_723])).

tff(c_758,plain,(
    ! [A_4] : r1_xboole_0(A_4,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_749])).

tff(c_376,plain,(
    ! [B_71] : k4_xboole_0(B_71,k1_xboole_0) = B_71 ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_358])).

tff(c_801,plain,(
    ! [A_106] : k4_xboole_0(A_106,A_106) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_793,c_536])).

tff(c_30,plain,(
    ! [A_18,B_19] : k2_xboole_0(k3_xboole_0(A_18,B_19),k4_xboole_0(A_18,B_19)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_921,plain,(
    ! [A_117] : k2_xboole_0(k3_xboole_0(A_117,A_117),k1_xboole_0) = A_117 ),
    inference(superposition,[status(thm),theory(equality)],[c_801,c_30])).

tff(c_32,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(k2_xboole_0(A_20,B_21),B_21) = A_20
      | ~ r1_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_930,plain,(
    ! [A_117] :
      ( k4_xboole_0(A_117,k1_xboole_0) = k3_xboole_0(A_117,A_117)
      | ~ r1_xboole_0(k3_xboole_0(A_117,A_117),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_921,c_32])).

tff(c_980,plain,(
    ! [A_118] : k3_xboole_0(A_118,A_118) = A_118 ),
    inference(demodulation,[status(thm),theory(equality)],[c_758,c_376,c_930])).

tff(c_20,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_997,plain,(
    ! [A_118] : k5_xboole_0(A_118,A_118) = k4_xboole_0(A_118,A_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_980,c_20])).

tff(c_1020,plain,(
    ! [A_118] : k5_xboole_0(A_118,A_118) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_796,c_997])).

tff(c_115,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(k1_tarski(A_48),B_49)
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_572,plain,(
    ! [A_86,B_87] :
      ( k3_xboole_0(k1_tarski(A_86),B_87) = k1_tarski(A_86)
      | ~ r2_hidden(A_86,B_87) ) ),
    inference(resolution,[status(thm)],[c_115,c_26])).

tff(c_585,plain,(
    ! [A_86,B_87] :
      ( k5_xboole_0(k1_tarski(A_86),k1_tarski(A_86)) = k4_xboole_0(k1_tarski(A_86),B_87)
      | ~ r2_hidden(A_86,B_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_572,c_20])).

tff(c_1404,plain,(
    ! [A_140,B_141] :
      ( k4_xboole_0(k1_tarski(A_140),B_141) = k1_xboole_0
      | ~ r2_hidden(A_140,B_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1020,c_585])).

tff(c_28,plain,(
    ! [A_16,B_17] : k2_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1424,plain,(
    ! [B_141,A_140] :
      ( k2_xboole_0(B_141,k1_tarski(A_140)) = k2_xboole_0(B_141,k1_xboole_0)
      | ~ r2_hidden(A_140,B_141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1404,c_28])).

tff(c_1509,plain,(
    ! [B_145,A_146] :
      ( k2_xboole_0(B_145,k1_tarski(A_146)) = B_145
      | ~ r2_hidden(A_146,B_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1424])).

tff(c_174,plain,(
    ! [B_55,A_56] : k2_xboole_0(B_55,A_56) = k2_xboole_0(A_56,B_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_48])).

tff(c_50,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),'#skF_3') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_194,plain,(
    k2_xboole_0('#skF_3',k1_tarski('#skF_2')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_50])).

tff(c_1541,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1509,c_194])).

tff(c_1583,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1541])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:52:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.47  
% 2.97/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.48  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.97/1.48  
% 2.97/1.48  %Foreground sorts:
% 2.97/1.48  
% 2.97/1.48  
% 2.97/1.48  %Background operators:
% 2.97/1.48  
% 2.97/1.48  
% 2.97/1.48  %Foreground operators:
% 2.97/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.97/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.97/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.97/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.97/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.97/1.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.97/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.97/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.97/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.97/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.97/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.97/1.48  tff('#skF_2', type, '#skF_2': $i).
% 2.97/1.48  tff('#skF_3', type, '#skF_3': $i).
% 2.97/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.48  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.97/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.97/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.97/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.97/1.48  
% 3.15/1.49  tff(f_89, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 3.15/1.49  tff(f_54, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.15/1.49  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.15/1.49  tff(f_70, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.15/1.49  tff(f_84, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.15/1.49  tff(f_62, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.15/1.49  tff(f_56, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 3.15/1.49  tff(f_52, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.15/1.49  tff(f_32, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.15/1.49  tff(f_68, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 3.15/1.49  tff(f_64, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.15/1.49  tff(f_82, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.15/1.49  tff(f_60, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.15/1.49  tff(c_52, plain, (r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.15/1.49  tff(c_22, plain, (![A_11]: (k2_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.15/1.49  tff(c_18, plain, (![A_4, B_5]: (r2_hidden('#skF_1'(A_4, B_5), A_4) | r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.15/1.49  tff(c_34, plain, (![B_23, A_22]: (k2_tarski(B_23, A_22)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.15/1.49  tff(c_133, plain, (![A_52, B_53]: (k3_tarski(k2_tarski(A_52, B_53))=k2_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.15/1.49  tff(c_168, plain, (![B_55, A_56]: (k3_tarski(k2_tarski(B_55, A_56))=k2_xboole_0(A_56, B_55))), inference(superposition, [status(thm), theory('equality')], [c_34, c_133])).
% 3.15/1.49  tff(c_48, plain, (![A_36, B_37]: (k3_tarski(k2_tarski(A_36, B_37))=k2_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.15/1.49  tff(c_195, plain, (![B_57, A_58]: (k2_xboole_0(B_57, A_58)=k2_xboole_0(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_168, c_48])).
% 3.15/1.49  tff(c_211, plain, (![A_58]: (k2_xboole_0(k1_xboole_0, A_58)=A_58)), inference(superposition, [status(thm), theory('equality')], [c_195, c_22])).
% 3.15/1.49  tff(c_351, plain, (![A_70, B_71]: (k2_xboole_0(A_70, k4_xboole_0(B_71, A_70))=k2_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.15/1.49  tff(c_358, plain, (![B_71]: (k4_xboole_0(B_71, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_71))), inference(superposition, [status(thm), theory('equality')], [c_351, c_211])).
% 3.15/1.49  tff(c_382, plain, (![B_72]: (k4_xboole_0(B_72, k1_xboole_0)=B_72)), inference(demodulation, [status(thm), theory('equality')], [c_211, c_358])).
% 3.15/1.49  tff(c_242, plain, (![A_59]: (k2_xboole_0(k1_xboole_0, A_59)=A_59)), inference(superposition, [status(thm), theory('equality')], [c_195, c_22])).
% 3.15/1.49  tff(c_24, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k3_xboole_0(A_12, B_13))=A_12)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.15/1.49  tff(c_255, plain, (![B_13]: (k3_xboole_0(k1_xboole_0, B_13)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_242, c_24])).
% 3.15/1.49  tff(c_305, plain, (![A_65, B_66]: (k5_xboole_0(A_65, k3_xboole_0(A_65, B_66))=k4_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.15/1.49  tff(c_317, plain, (![B_67]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_67))), inference(superposition, [status(thm), theory('equality')], [c_255, c_305])).
% 3.15/1.49  tff(c_314, plain, (![B_13]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_13))), inference(superposition, [status(thm), theory('equality')], [c_255, c_305])).
% 3.15/1.49  tff(c_320, plain, (![B_67, B_13]: (k4_xboole_0(k1_xboole_0, B_67)=k4_xboole_0(k1_xboole_0, B_13))), inference(superposition, [status(thm), theory('equality')], [c_317, c_314])).
% 3.15/1.49  tff(c_396, plain, (![B_67]: (k4_xboole_0(k1_xboole_0, B_67)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_382, c_320])).
% 3.15/1.49  tff(c_413, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_396, c_314])).
% 3.15/1.49  tff(c_706, plain, (![A_93, C_94, B_95]: (~r2_hidden(A_93, C_94) | ~r2_hidden(A_93, B_95) | ~r2_hidden(A_93, k5_xboole_0(B_95, C_94)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.15/1.49  tff(c_723, plain, (![A_96]: (~r2_hidden(A_96, k1_xboole_0) | ~r2_hidden(A_96, k1_xboole_0) | ~r2_hidden(A_96, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_413, c_706])).
% 3.15/1.49  tff(c_782, plain, (![B_104]: (~r2_hidden('#skF_1'(k1_xboole_0, B_104), k1_xboole_0) | r1_xboole_0(k1_xboole_0, B_104))), inference(resolution, [status(thm)], [c_18, c_723])).
% 3.15/1.49  tff(c_793, plain, (![B_5]: (r1_xboole_0(k1_xboole_0, B_5))), inference(resolution, [status(thm)], [c_18, c_782])).
% 3.15/1.49  tff(c_504, plain, (![A_77, B_78]: (k4_xboole_0(k2_xboole_0(A_77, B_78), B_78)=A_77 | ~r1_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.15/1.49  tff(c_536, plain, (![A_58]: (k4_xboole_0(A_58, A_58)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_58))), inference(superposition, [status(thm), theory('equality')], [c_211, c_504])).
% 3.15/1.49  tff(c_796, plain, (![A_58]: (k4_xboole_0(A_58, A_58)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_793, c_536])).
% 3.15/1.49  tff(c_16, plain, (![A_4, B_5]: (r2_hidden('#skF_1'(A_4, B_5), B_5) | r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.15/1.49  tff(c_749, plain, (![A_100]: (~r2_hidden('#skF_1'(A_100, k1_xboole_0), k1_xboole_0) | r1_xboole_0(A_100, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_723])).
% 3.15/1.49  tff(c_758, plain, (![A_4]: (r1_xboole_0(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_749])).
% 3.15/1.49  tff(c_376, plain, (![B_71]: (k4_xboole_0(B_71, k1_xboole_0)=B_71)), inference(demodulation, [status(thm), theory('equality')], [c_211, c_358])).
% 3.15/1.49  tff(c_801, plain, (![A_106]: (k4_xboole_0(A_106, A_106)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_793, c_536])).
% 3.15/1.49  tff(c_30, plain, (![A_18, B_19]: (k2_xboole_0(k3_xboole_0(A_18, B_19), k4_xboole_0(A_18, B_19))=A_18)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.15/1.49  tff(c_921, plain, (![A_117]: (k2_xboole_0(k3_xboole_0(A_117, A_117), k1_xboole_0)=A_117)), inference(superposition, [status(thm), theory('equality')], [c_801, c_30])).
% 3.15/1.49  tff(c_32, plain, (![A_20, B_21]: (k4_xboole_0(k2_xboole_0(A_20, B_21), B_21)=A_20 | ~r1_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.15/1.49  tff(c_930, plain, (![A_117]: (k4_xboole_0(A_117, k1_xboole_0)=k3_xboole_0(A_117, A_117) | ~r1_xboole_0(k3_xboole_0(A_117, A_117), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_921, c_32])).
% 3.15/1.49  tff(c_980, plain, (![A_118]: (k3_xboole_0(A_118, A_118)=A_118)), inference(demodulation, [status(thm), theory('equality')], [c_758, c_376, c_930])).
% 3.15/1.49  tff(c_20, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.15/1.49  tff(c_997, plain, (![A_118]: (k5_xboole_0(A_118, A_118)=k4_xboole_0(A_118, A_118))), inference(superposition, [status(thm), theory('equality')], [c_980, c_20])).
% 3.15/1.49  tff(c_1020, plain, (![A_118]: (k5_xboole_0(A_118, A_118)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_796, c_997])).
% 3.15/1.49  tff(c_115, plain, (![A_48, B_49]: (r1_tarski(k1_tarski(A_48), B_49) | ~r2_hidden(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.15/1.49  tff(c_26, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.15/1.49  tff(c_572, plain, (![A_86, B_87]: (k3_xboole_0(k1_tarski(A_86), B_87)=k1_tarski(A_86) | ~r2_hidden(A_86, B_87))), inference(resolution, [status(thm)], [c_115, c_26])).
% 3.15/1.49  tff(c_585, plain, (![A_86, B_87]: (k5_xboole_0(k1_tarski(A_86), k1_tarski(A_86))=k4_xboole_0(k1_tarski(A_86), B_87) | ~r2_hidden(A_86, B_87))), inference(superposition, [status(thm), theory('equality')], [c_572, c_20])).
% 3.15/1.49  tff(c_1404, plain, (![A_140, B_141]: (k4_xboole_0(k1_tarski(A_140), B_141)=k1_xboole_0 | ~r2_hidden(A_140, B_141))), inference(demodulation, [status(thm), theory('equality')], [c_1020, c_585])).
% 3.15/1.49  tff(c_28, plain, (![A_16, B_17]: (k2_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.15/1.49  tff(c_1424, plain, (![B_141, A_140]: (k2_xboole_0(B_141, k1_tarski(A_140))=k2_xboole_0(B_141, k1_xboole_0) | ~r2_hidden(A_140, B_141))), inference(superposition, [status(thm), theory('equality')], [c_1404, c_28])).
% 3.15/1.49  tff(c_1509, plain, (![B_145, A_146]: (k2_xboole_0(B_145, k1_tarski(A_146))=B_145 | ~r2_hidden(A_146, B_145))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1424])).
% 3.15/1.49  tff(c_174, plain, (![B_55, A_56]: (k2_xboole_0(B_55, A_56)=k2_xboole_0(A_56, B_55))), inference(superposition, [status(thm), theory('equality')], [c_168, c_48])).
% 3.15/1.49  tff(c_50, plain, (k2_xboole_0(k1_tarski('#skF_2'), '#skF_3')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.15/1.49  tff(c_194, plain, (k2_xboole_0('#skF_3', k1_tarski('#skF_2'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_174, c_50])).
% 3.15/1.49  tff(c_1541, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1509, c_194])).
% 3.15/1.49  tff(c_1583, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_1541])).
% 3.15/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.49  
% 3.15/1.49  Inference rules
% 3.15/1.49  ----------------------
% 3.15/1.49  #Ref     : 0
% 3.15/1.49  #Sup     : 367
% 3.15/1.49  #Fact    : 0
% 3.15/1.49  #Define  : 0
% 3.15/1.49  #Split   : 1
% 3.15/1.49  #Chain   : 0
% 3.15/1.49  #Close   : 0
% 3.15/1.49  
% 3.15/1.49  Ordering : KBO
% 3.15/1.49  
% 3.15/1.49  Simplification rules
% 3.15/1.49  ----------------------
% 3.15/1.49  #Subsume      : 58
% 3.15/1.49  #Demod        : 206
% 3.15/1.49  #Tautology    : 226
% 3.15/1.49  #SimpNegUnit  : 0
% 3.15/1.49  #BackRed      : 6
% 3.15/1.49  
% 3.15/1.49  #Partial instantiations: 0
% 3.15/1.49  #Strategies tried      : 1
% 3.15/1.49  
% 3.15/1.49  Timing (in seconds)
% 3.15/1.49  ----------------------
% 3.15/1.50  Preprocessing        : 0.30
% 3.15/1.50  Parsing              : 0.15
% 3.15/1.50  CNF conversion       : 0.02
% 3.15/1.50  Main loop            : 0.43
% 3.15/1.50  Inferencing          : 0.16
% 3.15/1.50  Reduction            : 0.15
% 3.15/1.50  Demodulation         : 0.12
% 3.15/1.50  BG Simplification    : 0.02
% 3.15/1.50  Subsumption          : 0.06
% 3.15/1.50  Abstraction          : 0.03
% 3.15/1.50  MUC search           : 0.00
% 3.15/1.50  Cooper               : 0.00
% 3.15/1.50  Total                : 0.76
% 3.15/1.50  Index Insertion      : 0.00
% 3.15/1.50  Index Deletion       : 0.00
% 3.15/1.50  Index Matching       : 0.00
% 3.15/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
