%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:22 EST 2020

% Result     : Theorem 5.53s
% Output     : CNFRefutation 5.53s
% Verified   : 
% Statistics : Number of formulae       :  128 (1344 expanded)
%              Number of leaves         :   34 ( 450 expanded)
%              Depth                    :   15
%              Number of atoms          :  140 (2144 expanded)
%              Number of equality atoms :  114 (2061 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_36,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_102,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_59,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_10,plain,(
    ! [A_8] : k3_xboole_0(A_8,A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_62,plain,
    ( k1_tarski('#skF_2') != '#skF_4'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_104,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_60,plain,
    ( k1_xboole_0 != '#skF_4'
    | k1_tarski('#skF_2') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_93,plain,(
    k1_tarski('#skF_2') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_66,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k1_tarski('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_110,plain,(
    ! [A_68,B_69] : r1_tarski(A_68,k2_xboole_0(A_68,B_69)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_113,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_110])).

tff(c_183,plain,(
    ! [B_84,A_85] :
      ( k1_tarski(B_84) = A_85
      | k1_xboole_0 = A_85
      | ~ r1_tarski(A_85,k1_tarski(B_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_190,plain,
    ( k1_tarski('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_113,c_183])).

tff(c_204,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_93,c_190])).

tff(c_206,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_34,plain,(
    ! [A_25] : k5_xboole_0(A_25,A_25) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_207,plain,(
    ! [A_25] : k5_xboole_0(A_25,A_25) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_34])).

tff(c_8,plain,(
    ! [A_6] : k2_xboole_0(A_6,A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_572,plain,(
    ! [A_144,B_145] : k5_xboole_0(k5_xboole_0(A_144,B_145),k2_xboole_0(A_144,B_145)) = k3_xboole_0(A_144,B_145) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_593,plain,(
    ! [A_25] : k5_xboole_0('#skF_3',k2_xboole_0(A_25,A_25)) = k3_xboole_0(A_25,A_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_572])).

tff(c_599,plain,(
    ! [A_25] : k5_xboole_0('#skF_3',A_25) = A_25 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8,c_593])).

tff(c_731,plain,(
    ! [A_153,B_154,C_155] : k5_xboole_0(k5_xboole_0(A_153,B_154),C_155) = k5_xboole_0(A_153,k5_xboole_0(B_154,C_155)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_780,plain,(
    ! [A_25,C_155] : k5_xboole_0(A_25,k5_xboole_0(A_25,C_155)) = k5_xboole_0('#skF_3',C_155) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_731])).

tff(c_791,plain,(
    ! [A_156,C_157] : k5_xboole_0(A_156,k5_xboole_0(A_156,C_157)) = C_157 ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_780])).

tff(c_843,plain,(
    ! [A_25] : k5_xboole_0(A_25,'#skF_3') = A_25 ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_791])).

tff(c_590,plain,(
    k5_xboole_0(k5_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_2')) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_572])).

tff(c_667,plain,(
    k5_xboole_0('#skF_4',k1_tarski('#skF_2')) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_590])).

tff(c_918,plain,(
    ! [C_159] : k5_xboole_0('#skF_4',k5_xboole_0(k1_tarski('#skF_2'),C_159)) = k5_xboole_0(k3_xboole_0('#skF_3','#skF_4'),C_159) ),
    inference(superposition,[status(thm),theory(equality)],[c_667,c_731])).

tff(c_949,plain,(
    k5_xboole_0(k3_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_2')) = k5_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_918])).

tff(c_954,plain,(
    k5_xboole_0(k3_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_949])).

tff(c_205,plain,(
    k1_tarski('#skF_2') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_32,plain,(
    ! [A_22,B_23,C_24] : k5_xboole_0(k5_xboole_0(A_22,B_23),C_24) = k5_xboole_0(A_22,k5_xboole_0(B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_601,plain,(
    ! [A_146] : k5_xboole_0('#skF_3',A_146) = A_146 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8,c_593])).

tff(c_622,plain,(
    ! [B_14] : k4_xboole_0('#skF_3',B_14) = k3_xboole_0('#skF_3',B_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_601])).

tff(c_28,plain,(
    ! [A_18,B_19] : r1_tarski(k4_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_268,plain,(
    ! [A_100,B_101] : k5_xboole_0(A_100,k3_xboole_0(A_100,B_101)) = k4_xboole_0(A_100,B_101) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_277,plain,(
    ! [A_8] : k5_xboole_0(A_8,A_8) = k4_xboole_0(A_8,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_268])).

tff(c_288,plain,(
    ! [A_104] : k4_xboole_0(A_104,A_104) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_277])).

tff(c_293,plain,(
    ! [A_104] : r1_tarski('#skF_3',A_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_28])).

tff(c_300,plain,(
    ! [A_106,C_107,B_108] :
      ( r1_tarski(A_106,C_107)
      | ~ r1_tarski(B_108,C_107)
      | ~ r1_tarski(A_106,B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_313,plain,(
    ! [A_109,A_110] :
      ( r1_tarski(A_109,A_110)
      | ~ r1_tarski(A_109,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_293,c_300])).

tff(c_325,plain,(
    ! [B_19,A_110] : r1_tarski(k4_xboole_0('#skF_3',B_19),A_110) ),
    inference(resolution,[status(thm)],[c_28,c_313])).

tff(c_52,plain,(
    ! [B_57,A_56] :
      ( k1_tarski(B_57) = A_56
      | k1_xboole_0 = A_56
      | ~ r1_tarski(A_56,k1_tarski(B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_468,plain,(
    ! [B_134,A_135] :
      ( k1_tarski(B_134) = A_135
      | A_135 = '#skF_3'
      | ~ r1_tarski(A_135,k1_tarski(B_134)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_52])).

tff(c_495,plain,(
    ! [B_19,B_134] :
      ( k4_xboole_0('#skF_3',B_19) = k1_tarski(B_134)
      | k4_xboole_0('#skF_3',B_19) = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_325,c_468])).

tff(c_5407,plain,(
    ! [B_281,B_282] :
      ( k3_xboole_0('#skF_3',B_281) = k1_tarski(B_282)
      | k3_xboole_0('#skF_3',B_281) = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_622,c_495])).

tff(c_1013,plain,(
    ! [A_163,B_164] : k5_xboole_0(A_163,k5_xboole_0(B_164,k5_xboole_0(A_163,B_164))) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_731])).

tff(c_790,plain,(
    ! [A_25,C_155] : k5_xboole_0(A_25,k5_xboole_0(A_25,C_155)) = C_155 ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_780])).

tff(c_1029,plain,(
    ! [B_164,A_163] : k5_xboole_0(B_164,k5_xboole_0(A_163,B_164)) = k5_xboole_0(A_163,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1013,c_790])).

tff(c_1158,plain,(
    ! [B_169,A_170] : k5_xboole_0(B_169,k5_xboole_0(A_170,B_169)) = A_170 ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_1029])).

tff(c_1235,plain,(
    k5_xboole_0(k1_tarski('#skF_2'),k3_xboole_0('#skF_3','#skF_4')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_667,c_1158])).

tff(c_5484,plain,(
    ! [B_282] :
      ( k5_xboole_0(k1_tarski('#skF_2'),k1_tarski(B_282)) = '#skF_4'
      | k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5407,c_1235])).

tff(c_5620,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5484])).

tff(c_761,plain,(
    ! [C_155] : k5_xboole_0('#skF_4',k5_xboole_0(k1_tarski('#skF_2'),C_155)) = k5_xboole_0(k3_xboole_0('#skF_3','#skF_4'),C_155) ),
    inference(superposition,[status(thm),theory(equality)],[c_667,c_731])).

tff(c_1208,plain,(
    ! [C_155] : k5_xboole_0(k5_xboole_0(k1_tarski('#skF_2'),C_155),k5_xboole_0(k3_xboole_0('#skF_3','#skF_4'),C_155)) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_761,c_1158])).

tff(c_5624,plain,(
    ! [C_155] : k5_xboole_0(k5_xboole_0(k1_tarski('#skF_2'),C_155),k5_xboole_0('#skF_3',C_155)) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5620,c_1208])).

tff(c_5639,plain,(
    k1_tarski('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_207,c_32,c_599,c_5624])).

tff(c_5641,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_205,c_5639])).

tff(c_5648,plain,(
    ! [B_286] : k5_xboole_0(k1_tarski('#skF_2'),k1_tarski(B_286)) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5484])).

tff(c_1360,plain,(
    ! [B_173,A_174] : k5_xboole_0(B_173,A_174) = k5_xboole_0(A_174,B_173) ),
    inference(superposition,[status(thm),theory(equality)],[c_1158,c_790])).

tff(c_1412,plain,(
    ! [A_174] : k5_xboole_0('#skF_4',k5_xboole_0(A_174,k1_tarski('#skF_2'))) = k5_xboole_0(k3_xboole_0('#skF_3','#skF_4'),A_174) ),
    inference(superposition,[status(thm),theory(equality)],[c_1360,c_761])).

tff(c_5654,plain,(
    k5_xboole_0(k3_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_2')) = k5_xboole_0('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5648,c_1412])).

tff(c_5721,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_954,c_5654])).

tff(c_5643,plain,(
    k3_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5484])).

tff(c_5726,plain,(
    k3_xboole_0('#skF_4','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5721,c_5721,c_5643])).

tff(c_5784,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_5726])).

tff(c_5785,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_6378,plain,(
    ! [A_350,B_351] : k5_xboole_0(k5_xboole_0(A_350,B_351),k2_xboole_0(A_350,B_351)) = k3_xboole_0(A_350,B_351) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6399,plain,(
    ! [A_6] : k5_xboole_0(k5_xboole_0(A_6,A_6),A_6) = k3_xboole_0(A_6,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_6378])).

tff(c_6405,plain,(
    ! [A_6] : k5_xboole_0(k1_xboole_0,A_6) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_10,c_6399])).

tff(c_6532,plain,(
    ! [A_358,B_359,C_360] : k5_xboole_0(k5_xboole_0(A_358,B_359),C_360) = k5_xboole_0(A_358,k5_xboole_0(B_359,C_360)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6587,plain,(
    ! [A_25,C_360] : k5_xboole_0(A_25,k5_xboole_0(A_25,C_360)) = k5_xboole_0(k1_xboole_0,C_360) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_6532])).

tff(c_6598,plain,(
    ! [A_361,C_362] : k5_xboole_0(A_361,k5_xboole_0(A_361,C_362)) = C_362 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6405,c_6587])).

tff(c_6650,plain,(
    ! [A_25] : k5_xboole_0(A_25,k1_xboole_0) = A_25 ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_6598])).

tff(c_5786,plain,(
    k1_tarski('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_64,plain,
    ( k1_tarski('#skF_2') != '#skF_4'
    | k1_tarski('#skF_2') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_5832,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5786,c_5786,c_64])).

tff(c_5905,plain,(
    ! [B_307,A_308] :
      ( k1_tarski(B_307) = A_308
      | k1_xboole_0 = A_308
      | ~ r1_tarski(A_308,k1_tarski(B_307)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_5920,plain,(
    ! [A_308] :
      ( k1_tarski('#skF_2') = A_308
      | k1_xboole_0 = A_308
      | ~ r1_tarski(A_308,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5786,c_5905])).

tff(c_5927,plain,(
    ! [A_309] :
      ( A_309 = '#skF_3'
      | k1_xboole_0 = A_309
      | ~ r1_tarski(A_309,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5786,c_5920])).

tff(c_5948,plain,(
    ! [B_19] :
      ( k4_xboole_0('#skF_3',B_19) = '#skF_3'
      | k4_xboole_0('#skF_3',B_19) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_5927])).

tff(c_5803,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5786,c_66])).

tff(c_6396,plain,(
    k5_xboole_0(k5_xboole_0('#skF_3','#skF_4'),'#skF_3') = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5803,c_6378])).

tff(c_6568,plain,(
    k5_xboole_0('#skF_3',k5_xboole_0('#skF_4','#skF_3')) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6396,c_6532])).

tff(c_6597,plain,(
    ! [A_25,C_360] : k5_xboole_0(A_25,k5_xboole_0(A_25,C_360)) = C_360 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6405,c_6587])).

tff(c_6730,plain,(
    k5_xboole_0('#skF_3',k3_xboole_0('#skF_3','#skF_4')) = k5_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6568,c_6597])).

tff(c_6739,plain,(
    k5_xboole_0('#skF_4','#skF_3') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_6730])).

tff(c_6746,plain,(
    k5_xboole_0('#skF_4',k4_xboole_0('#skF_3','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_6739,c_6597])).

tff(c_6769,plain,
    ( k5_xboole_0('#skF_4',k1_xboole_0) = '#skF_3'
    | k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_5948,c_6746])).

tff(c_6773,plain,
    ( '#skF_3' = '#skF_4'
    | k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6650,c_6769])).

tff(c_6774,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_5832,c_6773])).

tff(c_6775,plain,(
    k5_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6774,c_6746])).

tff(c_6890,plain,(
    ! [A_372,B_373] : k5_xboole_0(A_372,k5_xboole_0(B_373,k5_xboole_0(A_372,B_373))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_6532])).

tff(c_6927,plain,(
    k5_xboole_0('#skF_4',k5_xboole_0('#skF_3','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6775,c_6890])).

tff(c_6986,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6650,c_34,c_6927])).

tff(c_6988,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5785,c_6986])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:11:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.53/2.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.53/2.19  
% 5.53/2.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.53/2.19  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.53/2.19  
% 5.53/2.19  %Foreground sorts:
% 5.53/2.19  
% 5.53/2.19  
% 5.53/2.19  %Background operators:
% 5.53/2.19  
% 5.53/2.19  
% 5.53/2.19  %Foreground operators:
% 5.53/2.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.53/2.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.53/2.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.53/2.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.53/2.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.53/2.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.53/2.19  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.53/2.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.53/2.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.53/2.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.53/2.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.53/2.19  tff('#skF_2', type, '#skF_2': $i).
% 5.53/2.19  tff('#skF_3', type, '#skF_3': $i).
% 5.53/2.19  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.53/2.19  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.53/2.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.53/2.19  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.53/2.19  tff('#skF_4', type, '#skF_4': $i).
% 5.53/2.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.53/2.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.53/2.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.53/2.19  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.53/2.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.53/2.19  
% 5.53/2.21  tff(f_36, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.53/2.21  tff(f_102, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 5.53/2.21  tff(f_55, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.53/2.21  tff(f_81, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 5.53/2.21  tff(f_59, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.53/2.21  tff(f_34, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 5.53/2.21  tff(f_61, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 5.53/2.21  tff(f_57, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.53/2.21  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.53/2.21  tff(f_53, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.53/2.21  tff(f_51, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.53/2.21  tff(c_10, plain, (![A_8]: (k3_xboole_0(A_8, A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.53/2.21  tff(c_62, plain, (k1_tarski('#skF_2')!='#skF_4' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.53/2.21  tff(c_104, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_62])).
% 5.53/2.21  tff(c_60, plain, (k1_xboole_0!='#skF_4' | k1_tarski('#skF_2')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.53/2.21  tff(c_93, plain, (k1_tarski('#skF_2')!='#skF_3'), inference(splitLeft, [status(thm)], [c_60])).
% 5.53/2.21  tff(c_66, plain, (k2_xboole_0('#skF_3', '#skF_4')=k1_tarski('#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.53/2.21  tff(c_110, plain, (![A_68, B_69]: (r1_tarski(A_68, k2_xboole_0(A_68, B_69)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.53/2.21  tff(c_113, plain, (r1_tarski('#skF_3', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_110])).
% 5.53/2.21  tff(c_183, plain, (![B_84, A_85]: (k1_tarski(B_84)=A_85 | k1_xboole_0=A_85 | ~r1_tarski(A_85, k1_tarski(B_84)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.53/2.21  tff(c_190, plain, (k1_tarski('#skF_2')='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_113, c_183])).
% 5.53/2.21  tff(c_204, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_93, c_190])).
% 5.53/2.21  tff(c_206, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_62])).
% 5.53/2.21  tff(c_34, plain, (![A_25]: (k5_xboole_0(A_25, A_25)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.53/2.21  tff(c_207, plain, (![A_25]: (k5_xboole_0(A_25, A_25)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_206, c_34])).
% 5.53/2.21  tff(c_8, plain, (![A_6]: (k2_xboole_0(A_6, A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.53/2.21  tff(c_572, plain, (![A_144, B_145]: (k5_xboole_0(k5_xboole_0(A_144, B_145), k2_xboole_0(A_144, B_145))=k3_xboole_0(A_144, B_145))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.53/2.21  tff(c_593, plain, (![A_25]: (k5_xboole_0('#skF_3', k2_xboole_0(A_25, A_25))=k3_xboole_0(A_25, A_25))), inference(superposition, [status(thm), theory('equality')], [c_207, c_572])).
% 5.53/2.21  tff(c_599, plain, (![A_25]: (k5_xboole_0('#skF_3', A_25)=A_25)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_8, c_593])).
% 5.53/2.21  tff(c_731, plain, (![A_153, B_154, C_155]: (k5_xboole_0(k5_xboole_0(A_153, B_154), C_155)=k5_xboole_0(A_153, k5_xboole_0(B_154, C_155)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.53/2.21  tff(c_780, plain, (![A_25, C_155]: (k5_xboole_0(A_25, k5_xboole_0(A_25, C_155))=k5_xboole_0('#skF_3', C_155))), inference(superposition, [status(thm), theory('equality')], [c_207, c_731])).
% 5.53/2.21  tff(c_791, plain, (![A_156, C_157]: (k5_xboole_0(A_156, k5_xboole_0(A_156, C_157))=C_157)), inference(demodulation, [status(thm), theory('equality')], [c_599, c_780])).
% 5.53/2.21  tff(c_843, plain, (![A_25]: (k5_xboole_0(A_25, '#skF_3')=A_25)), inference(superposition, [status(thm), theory('equality')], [c_207, c_791])).
% 5.53/2.21  tff(c_590, plain, (k5_xboole_0(k5_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_2'))=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_66, c_572])).
% 5.53/2.21  tff(c_667, plain, (k5_xboole_0('#skF_4', k1_tarski('#skF_2'))=k3_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_599, c_590])).
% 5.53/2.21  tff(c_918, plain, (![C_159]: (k5_xboole_0('#skF_4', k5_xboole_0(k1_tarski('#skF_2'), C_159))=k5_xboole_0(k3_xboole_0('#skF_3', '#skF_4'), C_159))), inference(superposition, [status(thm), theory('equality')], [c_667, c_731])).
% 5.53/2.21  tff(c_949, plain, (k5_xboole_0(k3_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_2'))=k5_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_207, c_918])).
% 5.53/2.21  tff(c_954, plain, (k5_xboole_0(k3_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_843, c_949])).
% 5.53/2.21  tff(c_205, plain, (k1_tarski('#skF_2')!='#skF_4'), inference(splitRight, [status(thm)], [c_62])).
% 5.53/2.21  tff(c_32, plain, (![A_22, B_23, C_24]: (k5_xboole_0(k5_xboole_0(A_22, B_23), C_24)=k5_xboole_0(A_22, k5_xboole_0(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.53/2.21  tff(c_24, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.53/2.21  tff(c_601, plain, (![A_146]: (k5_xboole_0('#skF_3', A_146)=A_146)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_8, c_593])).
% 5.53/2.21  tff(c_622, plain, (![B_14]: (k4_xboole_0('#skF_3', B_14)=k3_xboole_0('#skF_3', B_14))), inference(superposition, [status(thm), theory('equality')], [c_24, c_601])).
% 5.53/2.21  tff(c_28, plain, (![A_18, B_19]: (r1_tarski(k4_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.53/2.21  tff(c_268, plain, (![A_100, B_101]: (k5_xboole_0(A_100, k3_xboole_0(A_100, B_101))=k4_xboole_0(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.53/2.21  tff(c_277, plain, (![A_8]: (k5_xboole_0(A_8, A_8)=k4_xboole_0(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_10, c_268])).
% 5.53/2.21  tff(c_288, plain, (![A_104]: (k4_xboole_0(A_104, A_104)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_207, c_277])).
% 5.53/2.21  tff(c_293, plain, (![A_104]: (r1_tarski('#skF_3', A_104))), inference(superposition, [status(thm), theory('equality')], [c_288, c_28])).
% 5.53/2.21  tff(c_300, plain, (![A_106, C_107, B_108]: (r1_tarski(A_106, C_107) | ~r1_tarski(B_108, C_107) | ~r1_tarski(A_106, B_108))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.53/2.21  tff(c_313, plain, (![A_109, A_110]: (r1_tarski(A_109, A_110) | ~r1_tarski(A_109, '#skF_3'))), inference(resolution, [status(thm)], [c_293, c_300])).
% 5.53/2.21  tff(c_325, plain, (![B_19, A_110]: (r1_tarski(k4_xboole_0('#skF_3', B_19), A_110))), inference(resolution, [status(thm)], [c_28, c_313])).
% 5.53/2.21  tff(c_52, plain, (![B_57, A_56]: (k1_tarski(B_57)=A_56 | k1_xboole_0=A_56 | ~r1_tarski(A_56, k1_tarski(B_57)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.53/2.21  tff(c_468, plain, (![B_134, A_135]: (k1_tarski(B_134)=A_135 | A_135='#skF_3' | ~r1_tarski(A_135, k1_tarski(B_134)))), inference(demodulation, [status(thm), theory('equality')], [c_206, c_52])).
% 5.53/2.21  tff(c_495, plain, (![B_19, B_134]: (k4_xboole_0('#skF_3', B_19)=k1_tarski(B_134) | k4_xboole_0('#skF_3', B_19)='#skF_3')), inference(resolution, [status(thm)], [c_325, c_468])).
% 5.53/2.21  tff(c_5407, plain, (![B_281, B_282]: (k3_xboole_0('#skF_3', B_281)=k1_tarski(B_282) | k3_xboole_0('#skF_3', B_281)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_622, c_622, c_495])).
% 5.53/2.21  tff(c_1013, plain, (![A_163, B_164]: (k5_xboole_0(A_163, k5_xboole_0(B_164, k5_xboole_0(A_163, B_164)))='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_207, c_731])).
% 5.53/2.21  tff(c_790, plain, (![A_25, C_155]: (k5_xboole_0(A_25, k5_xboole_0(A_25, C_155))=C_155)), inference(demodulation, [status(thm), theory('equality')], [c_599, c_780])).
% 5.53/2.21  tff(c_1029, plain, (![B_164, A_163]: (k5_xboole_0(B_164, k5_xboole_0(A_163, B_164))=k5_xboole_0(A_163, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1013, c_790])).
% 5.53/2.21  tff(c_1158, plain, (![B_169, A_170]: (k5_xboole_0(B_169, k5_xboole_0(A_170, B_169))=A_170)), inference(demodulation, [status(thm), theory('equality')], [c_843, c_1029])).
% 5.53/2.21  tff(c_1235, plain, (k5_xboole_0(k1_tarski('#skF_2'), k3_xboole_0('#skF_3', '#skF_4'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_667, c_1158])).
% 5.53/2.21  tff(c_5484, plain, (![B_282]: (k5_xboole_0(k1_tarski('#skF_2'), k1_tarski(B_282))='#skF_4' | k3_xboole_0('#skF_3', '#skF_4')='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5407, c_1235])).
% 5.53/2.21  tff(c_5620, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(splitLeft, [status(thm)], [c_5484])).
% 5.53/2.21  tff(c_761, plain, (![C_155]: (k5_xboole_0('#skF_4', k5_xboole_0(k1_tarski('#skF_2'), C_155))=k5_xboole_0(k3_xboole_0('#skF_3', '#skF_4'), C_155))), inference(superposition, [status(thm), theory('equality')], [c_667, c_731])).
% 5.53/2.21  tff(c_1208, plain, (![C_155]: (k5_xboole_0(k5_xboole_0(k1_tarski('#skF_2'), C_155), k5_xboole_0(k3_xboole_0('#skF_3', '#skF_4'), C_155))='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_761, c_1158])).
% 5.53/2.21  tff(c_5624, plain, (![C_155]: (k5_xboole_0(k5_xboole_0(k1_tarski('#skF_2'), C_155), k5_xboole_0('#skF_3', C_155))='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5620, c_1208])).
% 5.53/2.21  tff(c_5639, plain, (k1_tarski('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_843, c_207, c_32, c_599, c_5624])).
% 5.53/2.21  tff(c_5641, plain, $false, inference(negUnitSimplification, [status(thm)], [c_205, c_5639])).
% 5.53/2.21  tff(c_5648, plain, (![B_286]: (k5_xboole_0(k1_tarski('#skF_2'), k1_tarski(B_286))='#skF_4')), inference(splitRight, [status(thm)], [c_5484])).
% 5.53/2.21  tff(c_1360, plain, (![B_173, A_174]: (k5_xboole_0(B_173, A_174)=k5_xboole_0(A_174, B_173))), inference(superposition, [status(thm), theory('equality')], [c_1158, c_790])).
% 5.53/2.21  tff(c_1412, plain, (![A_174]: (k5_xboole_0('#skF_4', k5_xboole_0(A_174, k1_tarski('#skF_2')))=k5_xboole_0(k3_xboole_0('#skF_3', '#skF_4'), A_174))), inference(superposition, [status(thm), theory('equality')], [c_1360, c_761])).
% 5.53/2.21  tff(c_5654, plain, (k5_xboole_0(k3_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_2'))=k5_xboole_0('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5648, c_1412])).
% 5.53/2.21  tff(c_5721, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_207, c_954, c_5654])).
% 5.53/2.21  tff(c_5643, plain, (k3_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(splitRight, [status(thm)], [c_5484])).
% 5.53/2.21  tff(c_5726, plain, (k3_xboole_0('#skF_4', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5721, c_5721, c_5643])).
% 5.53/2.21  tff(c_5784, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_5726])).
% 5.53/2.21  tff(c_5785, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_60])).
% 5.53/2.21  tff(c_6378, plain, (![A_350, B_351]: (k5_xboole_0(k5_xboole_0(A_350, B_351), k2_xboole_0(A_350, B_351))=k3_xboole_0(A_350, B_351))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.53/2.21  tff(c_6399, plain, (![A_6]: (k5_xboole_0(k5_xboole_0(A_6, A_6), A_6)=k3_xboole_0(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_8, c_6378])).
% 5.53/2.21  tff(c_6405, plain, (![A_6]: (k5_xboole_0(k1_xboole_0, A_6)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_10, c_6399])).
% 5.53/2.21  tff(c_6532, plain, (![A_358, B_359, C_360]: (k5_xboole_0(k5_xboole_0(A_358, B_359), C_360)=k5_xboole_0(A_358, k5_xboole_0(B_359, C_360)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.53/2.21  tff(c_6587, plain, (![A_25, C_360]: (k5_xboole_0(A_25, k5_xboole_0(A_25, C_360))=k5_xboole_0(k1_xboole_0, C_360))), inference(superposition, [status(thm), theory('equality')], [c_34, c_6532])).
% 5.53/2.21  tff(c_6598, plain, (![A_361, C_362]: (k5_xboole_0(A_361, k5_xboole_0(A_361, C_362))=C_362)), inference(demodulation, [status(thm), theory('equality')], [c_6405, c_6587])).
% 5.53/2.21  tff(c_6650, plain, (![A_25]: (k5_xboole_0(A_25, k1_xboole_0)=A_25)), inference(superposition, [status(thm), theory('equality')], [c_34, c_6598])).
% 5.53/2.21  tff(c_5786, plain, (k1_tarski('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_60])).
% 5.53/2.21  tff(c_64, plain, (k1_tarski('#skF_2')!='#skF_4' | k1_tarski('#skF_2')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.53/2.21  tff(c_5832, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5786, c_5786, c_64])).
% 5.53/2.21  tff(c_5905, plain, (![B_307, A_308]: (k1_tarski(B_307)=A_308 | k1_xboole_0=A_308 | ~r1_tarski(A_308, k1_tarski(B_307)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.53/2.21  tff(c_5920, plain, (![A_308]: (k1_tarski('#skF_2')=A_308 | k1_xboole_0=A_308 | ~r1_tarski(A_308, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5786, c_5905])).
% 5.53/2.21  tff(c_5927, plain, (![A_309]: (A_309='#skF_3' | k1_xboole_0=A_309 | ~r1_tarski(A_309, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5786, c_5920])).
% 5.53/2.21  tff(c_5948, plain, (![B_19]: (k4_xboole_0('#skF_3', B_19)='#skF_3' | k4_xboole_0('#skF_3', B_19)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_5927])).
% 5.53/2.21  tff(c_5803, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5786, c_66])).
% 5.53/2.21  tff(c_6396, plain, (k5_xboole_0(k5_xboole_0('#skF_3', '#skF_4'), '#skF_3')=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5803, c_6378])).
% 5.53/2.21  tff(c_6568, plain, (k5_xboole_0('#skF_3', k5_xboole_0('#skF_4', '#skF_3'))=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6396, c_6532])).
% 5.53/2.21  tff(c_6597, plain, (![A_25, C_360]: (k5_xboole_0(A_25, k5_xboole_0(A_25, C_360))=C_360)), inference(demodulation, [status(thm), theory('equality')], [c_6405, c_6587])).
% 5.53/2.21  tff(c_6730, plain, (k5_xboole_0('#skF_3', k3_xboole_0('#skF_3', '#skF_4'))=k5_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6568, c_6597])).
% 5.53/2.21  tff(c_6739, plain, (k5_xboole_0('#skF_4', '#skF_3')=k4_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_6730])).
% 5.53/2.21  tff(c_6746, plain, (k5_xboole_0('#skF_4', k4_xboole_0('#skF_3', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_6739, c_6597])).
% 5.53/2.21  tff(c_6769, plain, (k5_xboole_0('#skF_4', k1_xboole_0)='#skF_3' | k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_5948, c_6746])).
% 5.53/2.21  tff(c_6773, plain, ('#skF_3'='#skF_4' | k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6650, c_6769])).
% 5.53/2.21  tff(c_6774, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_5832, c_6773])).
% 5.53/2.21  tff(c_6775, plain, (k5_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6774, c_6746])).
% 5.53/2.21  tff(c_6890, plain, (![A_372, B_373]: (k5_xboole_0(A_372, k5_xboole_0(B_373, k5_xboole_0(A_372, B_373)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_34, c_6532])).
% 5.53/2.21  tff(c_6927, plain, (k5_xboole_0('#skF_4', k5_xboole_0('#skF_3', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6775, c_6890])).
% 5.53/2.21  tff(c_6986, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6650, c_34, c_6927])).
% 5.53/2.21  tff(c_6988, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5785, c_6986])).
% 5.53/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.53/2.21  
% 5.53/2.21  Inference rules
% 5.53/2.21  ----------------------
% 5.53/2.21  #Ref     : 0
% 5.53/2.21  #Sup     : 1703
% 5.53/2.21  #Fact    : 5
% 5.53/2.21  #Define  : 0
% 5.53/2.21  #Split   : 6
% 5.53/2.21  #Chain   : 0
% 5.53/2.21  #Close   : 0
% 5.53/2.21  
% 5.53/2.21  Ordering : KBO
% 5.53/2.21  
% 5.53/2.21  Simplification rules
% 5.53/2.21  ----------------------
% 5.53/2.21  #Subsume      : 44
% 5.53/2.21  #Demod        : 1065
% 5.53/2.21  #Tautology    : 919
% 5.53/2.21  #SimpNegUnit  : 13
% 5.53/2.21  #BackRed      : 90
% 5.53/2.21  
% 5.53/2.21  #Partial instantiations: 0
% 5.53/2.21  #Strategies tried      : 1
% 5.53/2.21  
% 5.53/2.21  Timing (in seconds)
% 5.53/2.21  ----------------------
% 5.53/2.22  Preprocessing        : 0.35
% 5.53/2.22  Parsing              : 0.19
% 5.53/2.22  CNF conversion       : 0.03
% 5.53/2.22  Main loop            : 1.04
% 5.53/2.22  Inferencing          : 0.33
% 5.53/2.22  Reduction            : 0.41
% 5.53/2.22  Demodulation         : 0.32
% 5.53/2.22  BG Simplification    : 0.04
% 5.53/2.22  Subsumption          : 0.18
% 5.53/2.22  Abstraction          : 0.05
% 5.53/2.22  MUC search           : 0.00
% 5.53/2.22  Cooper               : 0.00
% 5.53/2.22  Total                : 1.43
% 5.53/2.22  Index Insertion      : 0.00
% 5.53/2.22  Index Deletion       : 0.00
% 5.53/2.22  Index Matching       : 0.00
% 5.53/2.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
