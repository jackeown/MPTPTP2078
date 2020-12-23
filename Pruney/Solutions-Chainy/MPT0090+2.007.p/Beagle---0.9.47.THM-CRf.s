%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:25 EST 2020

% Result     : Theorem 9.35s
% Output     : CNFRefutation 9.49s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 149 expanded)
%              Number of leaves         :   20 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :   82 ( 165 expanded)
%              Number of equality atoms :   57 ( 112 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(A,B)
      <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_22,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_2')
    | r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_39,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_20,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_173,plain,(
    k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_363,plain,(
    ! [A_39,B_40,C_41] : k4_xboole_0(k4_xboole_0(A_39,B_40),C_41) = k4_xboole_0(A_39,k2_xboole_0(B_40,C_41)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_34,plain,(
    ! [A_16,B_17] : r1_xboole_0(k4_xboole_0(A_16,B_17),B_17) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_37,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_34])).

tff(c_78,plain,(
    ! [A_23,B_24] :
      ( k3_xboole_0(A_23,B_24) = k1_xboole_0
      | ~ r1_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_89,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_37,c_78])).

tff(c_210,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k4_xboole_0(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_231,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_210])).

tff(c_234,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_231])).

tff(c_379,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k2_xboole_0(B_40,k4_xboole_0(A_39,B_40))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_234])).

tff(c_426,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k2_xboole_0(B_40,A_39)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_379])).

tff(c_14,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6928,plain,(
    ! [A_142,B_143,C_144] : k4_xboole_0(k4_xboole_0(A_142,B_143),k4_xboole_0(A_142,k2_xboole_0(B_143,C_144))) = k3_xboole_0(k4_xboole_0(A_142,B_143),C_144) ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_14])).

tff(c_7069,plain,(
    ! [A_39,B_40] : k4_xboole_0(k4_xboole_0(A_39,B_40),k1_xboole_0) = k3_xboole_0(k4_xboole_0(A_39,B_40),A_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_426,c_6928])).

tff(c_7141,plain,(
    ! [A_145,B_146] : k3_xboole_0(k4_xboole_0(A_145,B_146),A_145) = k4_xboole_0(A_145,B_146) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_7069])).

tff(c_11419,plain,(
    ! [B_217,B_218] : k3_xboole_0(B_217,k4_xboole_0(B_217,B_218)) = k4_xboole_0(B_217,B_218) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_7141])).

tff(c_24,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_91,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_95,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_4])).

tff(c_1729,plain,(
    ! [A_74,B_75] : k4_xboole_0(A_74,k3_xboole_0(A_74,B_75)) = k3_xboole_0(A_74,k4_xboole_0(A_74,B_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_14])).

tff(c_1817,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_4')) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_1729])).

tff(c_1841,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1817])).

tff(c_11494,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_11419,c_1841])).

tff(c_11613,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_11494])).

tff(c_11614,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_xboole_0(k4_xboole_0(A_13,B_14),B_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_11619,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_11614,c_16])).

tff(c_11623,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_11619])).

tff(c_11624,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_11634,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_11624,c_16])).

tff(c_11638,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_11634])).

tff(c_11640,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_18,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_2')
    | k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_11641,plain,(
    k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_11968,plain,(
    ! [A_239,B_240,C_241] : k4_xboole_0(k4_xboole_0(A_239,B_240),C_241) = k4_xboole_0(A_239,k2_xboole_0(B_240,C_241)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12001,plain,(
    ! [A_239,B_240] : k4_xboole_0(A_239,k2_xboole_0(B_240,k1_xboole_0)) = k4_xboole_0(A_239,B_240) ),
    inference(superposition,[status(thm),theory(equality)],[c_11968,c_10])).

tff(c_11675,plain,(
    ! [A_221,B_222] :
      ( k3_xboole_0(A_221,B_222) = k1_xboole_0
      | ~ r1_xboole_0(A_221,B_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_11690,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_37,c_11675])).

tff(c_11780,plain,(
    ! [A_227,B_228] : k4_xboole_0(A_227,k4_xboole_0(A_227,B_228)) = k3_xboole_0(A_227,B_228) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_11798,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_11780])).

tff(c_11801,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11690,c_11798])).

tff(c_11987,plain,(
    ! [A_239,B_240] : k4_xboole_0(A_239,k2_xboole_0(B_240,k4_xboole_0(A_239,B_240))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11968,c_11801])).

tff(c_12031,plain,(
    ! [A_239,B_240] : k4_xboole_0(A_239,k2_xboole_0(B_240,A_239)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_11987])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] : k4_xboole_0(k4_xboole_0(A_8,B_9),C_10) = k4_xboole_0(A_8,k2_xboole_0(B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12021,plain,(
    ! [A_239,B_240,B_12] : k4_xboole_0(A_239,k2_xboole_0(B_240,k4_xboole_0(k4_xboole_0(A_239,B_240),B_12))) = k3_xboole_0(k4_xboole_0(A_239,B_240),B_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_11968])).

tff(c_16856,plain,(
    ! [A_325,B_326,B_327] : k4_xboole_0(A_325,k2_xboole_0(B_326,k4_xboole_0(A_325,k2_xboole_0(B_326,B_327)))) = k3_xboole_0(k4_xboole_0(A_325,B_326),B_327) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12021])).

tff(c_17034,plain,(
    ! [A_239,B_240] : k4_xboole_0(A_239,k2_xboole_0(B_240,k1_xboole_0)) = k3_xboole_0(k4_xboole_0(A_239,B_240),A_239) ),
    inference(superposition,[status(thm),theory(equality)],[c_12031,c_16856])).

tff(c_18926,plain,(
    ! [A_346,B_347] : k3_xboole_0(k4_xboole_0(A_346,B_347),A_346) = k4_xboole_0(A_346,B_347) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12001,c_17034])).

tff(c_27952,plain,(
    ! [A_450,B_451] : k3_xboole_0(A_450,k4_xboole_0(A_450,B_451)) = k4_xboole_0(A_450,B_451) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_18926])).

tff(c_11639,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_11689,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_11639,c_11675])).

tff(c_13808,plain,(
    ! [A_286,B_287] : k4_xboole_0(A_286,k3_xboole_0(A_286,B_287)) = k3_xboole_0(A_286,k4_xboole_0(A_286,B_287)) ),
    inference(superposition,[status(thm),theory(equality)],[c_11780,c_14])).

tff(c_13911,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_4')) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_11689,c_13808])).

tff(c_13942,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_13911])).

tff(c_28046,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_27952,c_13942])).

tff(c_28190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11641,c_28046])).

tff(c_28191,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_28194,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11640,c_28191])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:33:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.35/3.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.49/3.69  
% 9.49/3.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.49/3.69  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.49/3.69  
% 9.49/3.69  %Foreground sorts:
% 9.49/3.69  
% 9.49/3.69  
% 9.49/3.69  %Background operators:
% 9.49/3.69  
% 9.49/3.69  
% 9.49/3.69  %Foreground operators:
% 9.49/3.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.49/3.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.49/3.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.49/3.69  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.49/3.69  tff('#skF_2', type, '#skF_2': $i).
% 9.49/3.69  tff('#skF_3', type, '#skF_3': $i).
% 9.49/3.69  tff('#skF_1', type, '#skF_1': $i).
% 9.49/3.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.49/3.69  tff('#skF_4', type, '#skF_4': $i).
% 9.49/3.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.49/3.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.49/3.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.49/3.69  
% 9.49/3.71  tff(f_46, negated_conjecture, ~(![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 9.49/3.71  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.49/3.71  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 9.49/3.71  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 9.49/3.71  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 9.49/3.71  tff(f_41, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 9.49/3.71  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 9.49/3.71  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.49/3.71  tff(c_22, plain, (~r1_xboole_0('#skF_1', '#skF_2') | r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.49/3.71  tff(c_39, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_22])).
% 9.49/3.71  tff(c_20, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1' | k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.49/3.71  tff(c_173, plain, (k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_20])).
% 9.49/3.71  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.49/3.71  tff(c_10, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.49/3.71  tff(c_8, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.49/3.71  tff(c_363, plain, (![A_39, B_40, C_41]: (k4_xboole_0(k4_xboole_0(A_39, B_40), C_41)=k4_xboole_0(A_39, k2_xboole_0(B_40, C_41)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.49/3.71  tff(c_34, plain, (![A_16, B_17]: (r1_xboole_0(k4_xboole_0(A_16, B_17), B_17))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.49/3.71  tff(c_37, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_34])).
% 9.49/3.71  tff(c_78, plain, (![A_23, B_24]: (k3_xboole_0(A_23, B_24)=k1_xboole_0 | ~r1_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.49/3.71  tff(c_89, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_37, c_78])).
% 9.49/3.71  tff(c_210, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k4_xboole_0(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.49/3.71  tff(c_231, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_210])).
% 9.49/3.71  tff(c_234, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_89, c_231])).
% 9.49/3.71  tff(c_379, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k2_xboole_0(B_40, k4_xboole_0(A_39, B_40)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_363, c_234])).
% 9.49/3.71  tff(c_426, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k2_xboole_0(B_40, A_39))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_379])).
% 9.49/3.71  tff(c_14, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.49/3.71  tff(c_6928, plain, (![A_142, B_143, C_144]: (k4_xboole_0(k4_xboole_0(A_142, B_143), k4_xboole_0(A_142, k2_xboole_0(B_143, C_144)))=k3_xboole_0(k4_xboole_0(A_142, B_143), C_144))), inference(superposition, [status(thm), theory('equality')], [c_363, c_14])).
% 9.49/3.71  tff(c_7069, plain, (![A_39, B_40]: (k4_xboole_0(k4_xboole_0(A_39, B_40), k1_xboole_0)=k3_xboole_0(k4_xboole_0(A_39, B_40), A_39))), inference(superposition, [status(thm), theory('equality')], [c_426, c_6928])).
% 9.49/3.71  tff(c_7141, plain, (![A_145, B_146]: (k3_xboole_0(k4_xboole_0(A_145, B_146), A_145)=k4_xboole_0(A_145, B_146))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_7069])).
% 9.49/3.71  tff(c_11419, plain, (![B_217, B_218]: (k3_xboole_0(B_217, k4_xboole_0(B_217, B_218))=k4_xboole_0(B_217, B_218))), inference(superposition, [status(thm), theory('equality')], [c_2, c_7141])).
% 9.49/3.71  tff(c_24, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1' | r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.49/3.71  tff(c_91, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_24])).
% 9.49/3.71  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.49/3.71  tff(c_95, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_91, c_4])).
% 9.49/3.71  tff(c_1729, plain, (![A_74, B_75]: (k4_xboole_0(A_74, k3_xboole_0(A_74, B_75))=k3_xboole_0(A_74, k4_xboole_0(A_74, B_75)))), inference(superposition, [status(thm), theory('equality')], [c_210, c_14])).
% 9.49/3.71  tff(c_1817, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_4'))=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_95, c_1729])).
% 9.49/3.71  tff(c_1841, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1817])).
% 9.49/3.71  tff(c_11494, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_11419, c_1841])).
% 9.49/3.71  tff(c_11613, plain, $false, inference(negUnitSimplification, [status(thm)], [c_173, c_11494])).
% 9.49/3.71  tff(c_11614, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_20])).
% 9.49/3.71  tff(c_16, plain, (![A_13, B_14]: (r1_xboole_0(k4_xboole_0(A_13, B_14), B_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.49/3.71  tff(c_11619, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_11614, c_16])).
% 9.49/3.71  tff(c_11623, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39, c_11619])).
% 9.49/3.71  tff(c_11624, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_24])).
% 9.49/3.71  tff(c_11634, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_11624, c_16])).
% 9.49/3.71  tff(c_11638, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39, c_11634])).
% 9.49/3.71  tff(c_11640, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_22])).
% 9.49/3.71  tff(c_18, plain, (~r1_xboole_0('#skF_1', '#skF_2') | k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.49/3.71  tff(c_11641, plain, (k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_18])).
% 9.49/3.71  tff(c_11968, plain, (![A_239, B_240, C_241]: (k4_xboole_0(k4_xboole_0(A_239, B_240), C_241)=k4_xboole_0(A_239, k2_xboole_0(B_240, C_241)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.49/3.71  tff(c_12001, plain, (![A_239, B_240]: (k4_xboole_0(A_239, k2_xboole_0(B_240, k1_xboole_0))=k4_xboole_0(A_239, B_240))), inference(superposition, [status(thm), theory('equality')], [c_11968, c_10])).
% 9.49/3.71  tff(c_11675, plain, (![A_221, B_222]: (k3_xboole_0(A_221, B_222)=k1_xboole_0 | ~r1_xboole_0(A_221, B_222))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.49/3.71  tff(c_11690, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_37, c_11675])).
% 9.49/3.71  tff(c_11780, plain, (![A_227, B_228]: (k4_xboole_0(A_227, k4_xboole_0(A_227, B_228))=k3_xboole_0(A_227, B_228))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.49/3.71  tff(c_11798, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_11780])).
% 9.49/3.71  tff(c_11801, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_11690, c_11798])).
% 9.49/3.71  tff(c_11987, plain, (![A_239, B_240]: (k4_xboole_0(A_239, k2_xboole_0(B_240, k4_xboole_0(A_239, B_240)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_11968, c_11801])).
% 9.49/3.71  tff(c_12031, plain, (![A_239, B_240]: (k4_xboole_0(A_239, k2_xboole_0(B_240, A_239))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_11987])).
% 9.49/3.71  tff(c_12, plain, (![A_8, B_9, C_10]: (k4_xboole_0(k4_xboole_0(A_8, B_9), C_10)=k4_xboole_0(A_8, k2_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.49/3.71  tff(c_12021, plain, (![A_239, B_240, B_12]: (k4_xboole_0(A_239, k2_xboole_0(B_240, k4_xboole_0(k4_xboole_0(A_239, B_240), B_12)))=k3_xboole_0(k4_xboole_0(A_239, B_240), B_12))), inference(superposition, [status(thm), theory('equality')], [c_14, c_11968])).
% 9.49/3.71  tff(c_16856, plain, (![A_325, B_326, B_327]: (k4_xboole_0(A_325, k2_xboole_0(B_326, k4_xboole_0(A_325, k2_xboole_0(B_326, B_327))))=k3_xboole_0(k4_xboole_0(A_325, B_326), B_327))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12021])).
% 9.49/3.71  tff(c_17034, plain, (![A_239, B_240]: (k4_xboole_0(A_239, k2_xboole_0(B_240, k1_xboole_0))=k3_xboole_0(k4_xboole_0(A_239, B_240), A_239))), inference(superposition, [status(thm), theory('equality')], [c_12031, c_16856])).
% 9.49/3.71  tff(c_18926, plain, (![A_346, B_347]: (k3_xboole_0(k4_xboole_0(A_346, B_347), A_346)=k4_xboole_0(A_346, B_347))), inference(demodulation, [status(thm), theory('equality')], [c_12001, c_17034])).
% 9.49/3.71  tff(c_27952, plain, (![A_450, B_451]: (k3_xboole_0(A_450, k4_xboole_0(A_450, B_451))=k4_xboole_0(A_450, B_451))), inference(superposition, [status(thm), theory('equality')], [c_2, c_18926])).
% 9.49/3.71  tff(c_11639, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_22])).
% 9.49/3.71  tff(c_11689, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_11639, c_11675])).
% 9.49/3.71  tff(c_13808, plain, (![A_286, B_287]: (k4_xboole_0(A_286, k3_xboole_0(A_286, B_287))=k3_xboole_0(A_286, k4_xboole_0(A_286, B_287)))), inference(superposition, [status(thm), theory('equality')], [c_11780, c_14])).
% 9.49/3.71  tff(c_13911, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_4'))=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_11689, c_13808])).
% 9.49/3.71  tff(c_13942, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_13911])).
% 9.49/3.71  tff(c_28046, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_27952, c_13942])).
% 9.49/3.71  tff(c_28190, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11641, c_28046])).
% 9.49/3.71  tff(c_28191, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_18])).
% 9.49/3.71  tff(c_28194, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11640, c_28191])).
% 9.49/3.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.49/3.71  
% 9.49/3.71  Inference rules
% 9.49/3.71  ----------------------
% 9.49/3.71  #Ref     : 0
% 9.49/3.71  #Sup     : 7073
% 9.49/3.71  #Fact    : 0
% 9.49/3.71  #Define  : 0
% 9.49/3.71  #Split   : 4
% 9.49/3.71  #Chain   : 0
% 9.49/3.71  #Close   : 0
% 9.49/3.71  
% 9.49/3.71  Ordering : KBO
% 9.49/3.71  
% 9.49/3.71  Simplification rules
% 9.49/3.71  ----------------------
% 9.49/3.71  #Subsume      : 36
% 9.49/3.71  #Demod        : 7764
% 9.49/3.71  #Tautology    : 5158
% 9.49/3.71  #SimpNegUnit  : 4
% 9.49/3.71  #BackRed      : 53
% 9.49/3.71  
% 9.49/3.71  #Partial instantiations: 0
% 9.49/3.71  #Strategies tried      : 1
% 9.49/3.71  
% 9.49/3.71  Timing (in seconds)
% 9.49/3.71  ----------------------
% 9.49/3.71  Preprocessing        : 0.26
% 9.49/3.71  Parsing              : 0.14
% 9.49/3.71  CNF conversion       : 0.02
% 9.49/3.71  Main loop            : 2.67
% 9.49/3.71  Inferencing          : 0.63
% 9.49/3.71  Reduction            : 1.42
% 9.49/3.71  Demodulation         : 1.23
% 9.49/3.71  BG Simplification    : 0.07
% 9.49/3.71  Subsumption          : 0.39
% 9.49/3.71  Abstraction          : 0.11
% 9.49/3.71  MUC search           : 0.00
% 9.49/3.71  Cooper               : 0.00
% 9.49/3.71  Total                : 2.97
% 9.49/3.71  Index Insertion      : 0.00
% 9.49/3.71  Index Deletion       : 0.00
% 9.49/3.71  Index Matching       : 0.00
% 9.49/3.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
