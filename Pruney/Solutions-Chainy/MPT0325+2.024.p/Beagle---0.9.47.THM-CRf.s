%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:23 EST 2020

% Result     : Theorem 14.47s
% Output     : CNFRefutation 14.47s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 243 expanded)
%              Number of leaves         :   32 (  95 expanded)
%              Depth                    :   10
%              Number of atoms          :   72 ( 351 expanded)
%              Number of equality atoms :   56 ( 235 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_71,axiom,(
    ! [A,B,C,D] : k4_xboole_0(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(A,C),B),k2_zfmisc_1(A,k4_xboole_0(B,D))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(c_22893,plain,(
    ! [A_285,B_286] :
      ( r1_tarski(A_285,B_286)
      | k4_xboole_0(A_285,B_286) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_222,plain,(
    ! [A_66,B_67] :
      ( r1_tarski(A_66,B_67)
      | k4_xboole_0(A_66,B_67) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,
    ( ~ r1_tarski('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_201,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_226,plain,(
    k4_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_222,c_201])).

tff(c_14,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_50,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_236,plain,(
    ! [A_70,B_71] :
      ( k4_xboole_0(A_70,B_71) = k1_xboole_0
      | ~ r1_tarski(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_244,plain,(
    k4_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_236])).

tff(c_1809,plain,(
    ! [A_149,C_150,B_151,D_152] : k2_xboole_0(k2_zfmisc_1(k4_xboole_0(A_149,C_150),B_151),k2_zfmisc_1(A_149,k4_xboole_0(B_151,D_152))) = k4_xboole_0(k2_zfmisc_1(A_149,B_151),k2_zfmisc_1(C_150,D_152)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_10,plain,(
    ! [A_7,B_8] : k3_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_21373,plain,(
    ! [A_267,C_268,B_269,D_270] : k3_xboole_0(k2_zfmisc_1(k4_xboole_0(A_267,C_268),B_269),k4_xboole_0(k2_zfmisc_1(A_267,B_269),k2_zfmisc_1(C_268,D_270))) = k2_zfmisc_1(k4_xboole_0(A_267,C_268),B_269) ),
    inference(superposition,[status(thm),theory(equality)],[c_1809,c_10])).

tff(c_21437,plain,(
    k3_xboole_0(k2_zfmisc_1(k4_xboole_0('#skF_1','#skF_3'),'#skF_2'),k1_xboole_0) = k2_zfmisc_1(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_21373])).

tff(c_21473,plain,(
    k2_zfmisc_1(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_21437])).

tff(c_38,plain,(
    ! [B_49,A_48] :
      ( k1_xboole_0 = B_49
      | k1_xboole_0 = A_48
      | k2_zfmisc_1(A_48,B_49) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_21495,plain,
    ( k1_xboole_0 = '#skF_2'
    | k4_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_21473,c_38])).

tff(c_21504,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_226,c_21495])).

tff(c_40,plain,(
    ! [A_48] : k2_zfmisc_1(A_48,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_21528,plain,(
    ! [A_48] : k2_zfmisc_1(A_48,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21504,c_21504,c_40])).

tff(c_48,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_21533,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21504,c_48])).

tff(c_22861,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21528,c_21533])).

tff(c_22862,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_22897,plain,(
    k4_xboole_0('#skF_2','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22893,c_22862])).

tff(c_16,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22936,plain,(
    ! [A_291,B_292] : k5_xboole_0(A_291,k3_xboole_0(A_291,B_292)) = k4_xboole_0(A_291,B_292) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22959,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = k4_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_22936])).

tff(c_22964,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_22959])).

tff(c_22981,plain,(
    ! [A_296,B_297] : k5_xboole_0(A_296,k4_xboole_0(B_297,A_296)) = k2_xboole_0(A_296,B_297) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_106,plain,(
    ! [B_59,A_60] : k5_xboole_0(B_59,A_60) = k5_xboole_0(A_60,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_122,plain,(
    ! [A_60] : k5_xboole_0(k1_xboole_0,A_60) = A_60 ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_16])).

tff(c_22988,plain,(
    ! [B_297] : k4_xboole_0(B_297,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_297) ),
    inference(superposition,[status(thm),theory(equality)],[c_22981,c_122])).

tff(c_23009,plain,(
    ! [B_297] : k2_xboole_0(k1_xboole_0,B_297) = B_297 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22964,c_22988])).

tff(c_42,plain,(
    ! [B_49] : k2_zfmisc_1(k1_xboole_0,B_49) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22863,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_22898,plain,(
    ! [A_287,B_288] :
      ( k4_xboole_0(A_287,B_288) = k1_xboole_0
      | ~ r1_tarski(A_287,B_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22910,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22863,c_22898])).

tff(c_24685,plain,(
    ! [A_367,C_368,B_369,D_370] : k2_xboole_0(k2_zfmisc_1(k4_xboole_0(A_367,C_368),B_369),k2_zfmisc_1(A_367,k4_xboole_0(B_369,D_370))) = k4_xboole_0(k2_zfmisc_1(A_367,B_369),k2_zfmisc_1(C_368,D_370)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_24745,plain,(
    ! [B_369,D_370] : k2_xboole_0(k2_zfmisc_1(k1_xboole_0,B_369),k2_zfmisc_1('#skF_1',k4_xboole_0(B_369,D_370))) = k4_xboole_0(k2_zfmisc_1('#skF_1',B_369),k2_zfmisc_1('#skF_3',D_370)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22910,c_24685])).

tff(c_27444,plain,(
    ! [B_396,D_397] : k4_xboole_0(k2_zfmisc_1('#skF_1',B_396),k2_zfmisc_1('#skF_3',D_397)) = k2_zfmisc_1('#skF_1',k4_xboole_0(B_396,D_397)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23009,c_42,c_24745])).

tff(c_22909,plain,(
    k4_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_22898])).

tff(c_27487,plain,(
    k2_zfmisc_1('#skF_1',k4_xboole_0('#skF_2','#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_27444,c_22909])).

tff(c_27521,plain,
    ( k4_xboole_0('#skF_2','#skF_4') = k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_27487,c_38])).

tff(c_27528,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_22897,c_27521])).

tff(c_27553,plain,(
    ! [B_49] : k2_zfmisc_1('#skF_1',B_49) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27528,c_27528,c_42])).

tff(c_27554,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27528,c_48])).

tff(c_27903,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27553,c_27554])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:29:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.47/6.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.47/6.51  
% 14.47/6.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.47/6.51  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 14.47/6.51  
% 14.47/6.51  %Foreground sorts:
% 14.47/6.51  
% 14.47/6.51  
% 14.47/6.51  %Background operators:
% 14.47/6.51  
% 14.47/6.51  
% 14.47/6.51  %Foreground operators:
% 14.47/6.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.47/6.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.47/6.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.47/6.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 14.47/6.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 14.47/6.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.47/6.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 14.47/6.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.47/6.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 14.47/6.51  tff('#skF_2', type, '#skF_2': $i).
% 14.47/6.51  tff('#skF_3', type, '#skF_3': $i).
% 14.47/6.51  tff('#skF_1', type, '#skF_1': $i).
% 14.47/6.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 14.47/6.51  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 14.47/6.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.47/6.51  tff(k3_tarski, type, k3_tarski: $i > $i).
% 14.47/6.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.47/6.51  tff('#skF_4', type, '#skF_4': $i).
% 14.47/6.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.47/6.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.47/6.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.47/6.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 14.47/6.51  
% 14.47/6.53  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 14.47/6.53  tff(f_80, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 14.47/6.53  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 14.47/6.53  tff(f_71, axiom, (![A, B, C, D]: (k4_xboole_0(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(A, C), B), k2_zfmisc_1(A, k4_xboole_0(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_zfmisc_1)).
% 14.47/6.53  tff(f_35, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 14.47/6.53  tff(f_69, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 14.47/6.53  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 14.47/6.53  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 14.47/6.53  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 14.47/6.53  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 14.47/6.53  tff(c_22893, plain, (![A_285, B_286]: (r1_tarski(A_285, B_286) | k4_xboole_0(A_285, B_286)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.47/6.53  tff(c_222, plain, (![A_66, B_67]: (r1_tarski(A_66, B_67) | k4_xboole_0(A_66, B_67)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.47/6.53  tff(c_46, plain, (~r1_tarski('#skF_2', '#skF_4') | ~r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 14.47/6.53  tff(c_201, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_46])).
% 14.47/6.53  tff(c_226, plain, (k4_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_222, c_201])).
% 14.47/6.53  tff(c_14, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.47/6.53  tff(c_50, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 14.47/6.53  tff(c_236, plain, (![A_70, B_71]: (k4_xboole_0(A_70, B_71)=k1_xboole_0 | ~r1_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.47/6.53  tff(c_244, plain, (k4_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_236])).
% 14.47/6.53  tff(c_1809, plain, (![A_149, C_150, B_151, D_152]: (k2_xboole_0(k2_zfmisc_1(k4_xboole_0(A_149, C_150), B_151), k2_zfmisc_1(A_149, k4_xboole_0(B_151, D_152)))=k4_xboole_0(k2_zfmisc_1(A_149, B_151), k2_zfmisc_1(C_150, D_152)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.47/6.53  tff(c_10, plain, (![A_7, B_8]: (k3_xboole_0(A_7, k2_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.47/6.53  tff(c_21373, plain, (![A_267, C_268, B_269, D_270]: (k3_xboole_0(k2_zfmisc_1(k4_xboole_0(A_267, C_268), B_269), k4_xboole_0(k2_zfmisc_1(A_267, B_269), k2_zfmisc_1(C_268, D_270)))=k2_zfmisc_1(k4_xboole_0(A_267, C_268), B_269))), inference(superposition, [status(thm), theory('equality')], [c_1809, c_10])).
% 14.47/6.53  tff(c_21437, plain, (k3_xboole_0(k2_zfmisc_1(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2'), k1_xboole_0)=k2_zfmisc_1(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_244, c_21373])).
% 14.47/6.53  tff(c_21473, plain, (k2_zfmisc_1(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_21437])).
% 14.47/6.53  tff(c_38, plain, (![B_49, A_48]: (k1_xboole_0=B_49 | k1_xboole_0=A_48 | k2_zfmisc_1(A_48, B_49)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.47/6.53  tff(c_21495, plain, (k1_xboole_0='#skF_2' | k4_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_21473, c_38])).
% 14.47/6.53  tff(c_21504, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_226, c_21495])).
% 14.47/6.53  tff(c_40, plain, (![A_48]: (k2_zfmisc_1(A_48, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.47/6.53  tff(c_21528, plain, (![A_48]: (k2_zfmisc_1(A_48, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_21504, c_21504, c_40])).
% 14.47/6.53  tff(c_48, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 14.47/6.53  tff(c_21533, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_21504, c_48])).
% 14.47/6.53  tff(c_22861, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21528, c_21533])).
% 14.47/6.53  tff(c_22862, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_46])).
% 14.47/6.53  tff(c_22897, plain, (k4_xboole_0('#skF_2', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_22893, c_22862])).
% 14.47/6.53  tff(c_16, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.47/6.53  tff(c_22936, plain, (![A_291, B_292]: (k5_xboole_0(A_291, k3_xboole_0(A_291, B_292))=k4_xboole_0(A_291, B_292))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.47/6.53  tff(c_22959, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=k4_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_22936])).
% 14.47/6.53  tff(c_22964, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_22959])).
% 14.47/6.53  tff(c_22981, plain, (![A_296, B_297]: (k5_xboole_0(A_296, k4_xboole_0(B_297, A_296))=k2_xboole_0(A_296, B_297))), inference(cnfTransformation, [status(thm)], [f_49])).
% 14.47/6.53  tff(c_106, plain, (![B_59, A_60]: (k5_xboole_0(B_59, A_60)=k5_xboole_0(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.47/6.53  tff(c_122, plain, (![A_60]: (k5_xboole_0(k1_xboole_0, A_60)=A_60)), inference(superposition, [status(thm), theory('equality')], [c_106, c_16])).
% 14.47/6.53  tff(c_22988, plain, (![B_297]: (k4_xboole_0(B_297, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_297))), inference(superposition, [status(thm), theory('equality')], [c_22981, c_122])).
% 14.47/6.53  tff(c_23009, plain, (![B_297]: (k2_xboole_0(k1_xboole_0, B_297)=B_297)), inference(demodulation, [status(thm), theory('equality')], [c_22964, c_22988])).
% 14.47/6.53  tff(c_42, plain, (![B_49]: (k2_zfmisc_1(k1_xboole_0, B_49)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.47/6.53  tff(c_22863, plain, (r1_tarski('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_46])).
% 14.47/6.53  tff(c_22898, plain, (![A_287, B_288]: (k4_xboole_0(A_287, B_288)=k1_xboole_0 | ~r1_tarski(A_287, B_288))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.47/6.53  tff(c_22910, plain, (k4_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_22863, c_22898])).
% 14.47/6.53  tff(c_24685, plain, (![A_367, C_368, B_369, D_370]: (k2_xboole_0(k2_zfmisc_1(k4_xboole_0(A_367, C_368), B_369), k2_zfmisc_1(A_367, k4_xboole_0(B_369, D_370)))=k4_xboole_0(k2_zfmisc_1(A_367, B_369), k2_zfmisc_1(C_368, D_370)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.47/6.53  tff(c_24745, plain, (![B_369, D_370]: (k2_xboole_0(k2_zfmisc_1(k1_xboole_0, B_369), k2_zfmisc_1('#skF_1', k4_xboole_0(B_369, D_370)))=k4_xboole_0(k2_zfmisc_1('#skF_1', B_369), k2_zfmisc_1('#skF_3', D_370)))), inference(superposition, [status(thm), theory('equality')], [c_22910, c_24685])).
% 14.47/6.53  tff(c_27444, plain, (![B_396, D_397]: (k4_xboole_0(k2_zfmisc_1('#skF_1', B_396), k2_zfmisc_1('#skF_3', D_397))=k2_zfmisc_1('#skF_1', k4_xboole_0(B_396, D_397)))), inference(demodulation, [status(thm), theory('equality')], [c_23009, c_42, c_24745])).
% 14.47/6.53  tff(c_22909, plain, (k4_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_22898])).
% 14.47/6.53  tff(c_27487, plain, (k2_zfmisc_1('#skF_1', k4_xboole_0('#skF_2', '#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_27444, c_22909])).
% 14.47/6.53  tff(c_27521, plain, (k4_xboole_0('#skF_2', '#skF_4')=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_27487, c_38])).
% 14.47/6.53  tff(c_27528, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_22897, c_27521])).
% 14.47/6.53  tff(c_27553, plain, (![B_49]: (k2_zfmisc_1('#skF_1', B_49)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_27528, c_27528, c_42])).
% 14.47/6.53  tff(c_27554, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_27528, c_48])).
% 14.47/6.53  tff(c_27903, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27553, c_27554])).
% 14.47/6.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.47/6.53  
% 14.47/6.53  Inference rules
% 14.47/6.53  ----------------------
% 14.47/6.53  #Ref     : 0
% 14.47/6.53  #Sup     : 7191
% 14.47/6.53  #Fact    : 0
% 14.47/6.53  #Define  : 0
% 14.47/6.53  #Split   : 1
% 14.47/6.53  #Chain   : 0
% 14.47/6.53  #Close   : 0
% 14.47/6.53  
% 14.47/6.53  Ordering : KBO
% 14.47/6.53  
% 14.47/6.53  Simplification rules
% 14.47/6.53  ----------------------
% 14.47/6.53  #Subsume      : 626
% 14.47/6.53  #Demod        : 8760
% 14.47/6.53  #Tautology    : 3033
% 14.47/6.53  #SimpNegUnit  : 2
% 14.47/6.53  #BackRed      : 75
% 14.47/6.53  
% 14.47/6.53  #Partial instantiations: 0
% 14.47/6.53  #Strategies tried      : 1
% 14.47/6.53  
% 14.47/6.53  Timing (in seconds)
% 14.47/6.53  ----------------------
% 14.47/6.53  Preprocessing        : 0.34
% 14.47/6.53  Parsing              : 0.19
% 14.47/6.53  CNF conversion       : 0.02
% 14.47/6.53  Main loop            : 5.38
% 14.47/6.53  Inferencing          : 0.86
% 14.47/6.53  Reduction            : 3.73
% 14.47/6.53  Demodulation         : 3.50
% 14.47/6.53  BG Simplification    : 0.13
% 14.47/6.53  Subsumption          : 0.50
% 14.47/6.53  Abstraction          : 0.22
% 14.47/6.53  MUC search           : 0.00
% 14.47/6.53  Cooper               : 0.00
% 14.47/6.53  Total                : 5.75
% 14.47/6.53  Index Insertion      : 0.00
% 14.47/6.53  Index Deletion       : 0.00
% 14.47/6.53  Index Matching       : 0.00
% 14.47/6.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
