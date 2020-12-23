%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:09 EST 2020

% Result     : Theorem 8.95s
% Output     : CNFRefutation 8.95s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 183 expanded)
%              Number of leaves         :   20 (  70 expanded)
%              Depth                    :   11
%              Number of atoms          :   69 ( 199 expanded)
%              Number of equality atoms :   53 ( 148 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_51,plain,(
    ! [A_26,B_27] :
      ( r1_xboole_0(A_26,B_27)
      | k3_xboole_0(A_26,B_27) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_55,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_51,c_28])).

tff(c_14,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_56,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_72,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_56])).

tff(c_253,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k4_xboole_0(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_297,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_253])).

tff(c_310,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_297])).

tff(c_12,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_71,plain,(
    ! [A_6,B_7] : k4_xboole_0(k4_xboole_0(A_6,B_7),A_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_56])).

tff(c_510,plain,(
    ! [A_49,B_50] : k4_xboole_0(k3_xboole_0(A_49,B_50),A_49) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_71])).

tff(c_20,plain,(
    ! [A_13,B_14,C_15] : k4_xboole_0(k3_xboole_0(A_13,B_14),C_15) = k3_xboole_0(A_13,k4_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_571,plain,(
    ! [A_51,B_52] : k3_xboole_0(A_51,k4_xboole_0(B_52,A_51)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_20])).

tff(c_16,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_591,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k4_xboole_0(B_52,A_51)) = k4_xboole_0(A_51,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_571,c_16])).

tff(c_633,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k4_xboole_0(B_52,A_51)) = A_51 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_591])).

tff(c_343,plain,(
    ! [A_42,B_43,C_44] : k4_xboole_0(k3_xboole_0(A_42,B_43),C_44) = k3_xboole_0(A_42,k4_xboole_0(B_43,C_44)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1805,plain,(
    ! [C_79] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_3',C_79)) = k4_xboole_0('#skF_1',C_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_343])).

tff(c_1855,plain,(
    ! [B_52] : k4_xboole_0('#skF_1',k4_xboole_0(B_52,'#skF_3')) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_633,c_1805])).

tff(c_2036,plain,(
    ! [B_83] : k4_xboole_0('#skF_1',k4_xboole_0(B_83,'#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_1855])).

tff(c_878,plain,(
    ! [A_62,B_63] : k4_xboole_0(A_62,k4_xboole_0(B_63,A_62)) = A_62 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_591])).

tff(c_515,plain,(
    ! [A_49,B_50] : k3_xboole_0(A_49,k4_xboole_0(B_50,A_49)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_20])).

tff(c_893,plain,(
    ! [B_63,A_62] : k3_xboole_0(k4_xboole_0(B_63,A_62),A_62) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_878,c_515])).

tff(c_2049,plain,(
    ! [B_83] : k3_xboole_0('#skF_1',k4_xboole_0(B_83,'#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2036,c_893])).

tff(c_18,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_384,plain,(
    ! [A_42,B_43,B_12] : k3_xboole_0(A_42,k4_xboole_0(B_43,k4_xboole_0(k3_xboole_0(A_42,B_43),B_12))) = k3_xboole_0(k3_xboole_0(A_42,B_43),B_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_343])).

tff(c_408,plain,(
    ! [A_42,B_43,B_12] : k3_xboole_0(A_42,k4_xboole_0(B_43,k3_xboole_0(A_42,k4_xboole_0(B_43,B_12)))) = k3_xboole_0(k3_xboole_0(A_42,B_43),B_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_384])).

tff(c_3980,plain,(
    ! [A_108,B_109,B_110] : k3_xboole_0(A_108,k4_xboole_0(B_109,k3_xboole_0(A_108,k4_xboole_0(B_109,B_110)))) = k3_xboole_0(k3_xboole_0(A_108,B_109),B_110) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_384])).

tff(c_4170,plain,(
    ! [A_108,A_9,B_10] : k3_xboole_0(A_108,k4_xboole_0(A_9,k3_xboole_0(A_108,k4_xboole_0(A_9,B_10)))) = k3_xboole_0(k3_xboole_0(A_108,A_9),k3_xboole_0(A_9,B_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_3980])).

tff(c_21073,plain,(
    ! [A_239,A_240,B_241] : k3_xboole_0(k3_xboole_0(A_239,A_240),k3_xboole_0(A_240,B_241)) = k3_xboole_0(k3_xboole_0(A_239,A_240),B_241) ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_4170])).

tff(c_518,plain,(
    ! [A_49,B_50] : k4_xboole_0(k3_xboole_0(A_49,B_50),k1_xboole_0) = k3_xboole_0(k3_xboole_0(A_49,B_50),A_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_18])).

tff(c_558,plain,(
    ! [A_49,B_50] : k3_xboole_0(k3_xboole_0(A_49,B_50),A_49) = k3_xboole_0(A_49,B_50) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_518])).

tff(c_45,plain,(
    ! [A_21,B_22] : r1_tarski(k4_xboole_0(A_21,B_22),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_48,plain,(
    ! [A_8] : r1_tarski(A_8,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_45])).

tff(c_70,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_56])).

tff(c_364,plain,(
    ! [A_42,B_43] : k3_xboole_0(A_42,k4_xboole_0(B_43,k3_xboole_0(A_42,B_43))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_70])).

tff(c_24,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_110,plain,(
    ! [A_32,B_33] :
      ( k3_xboole_0(A_32,B_33) = k1_xboole_0
      | ~ r1_xboole_0(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_118,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_110])).

tff(c_161,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k3_xboole_0(A_35,B_36)) = k4_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_177,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_161])).

tff(c_189,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_177])).

tff(c_4164,plain,(
    ! [A_108] : k3_xboole_0(k3_xboole_0(A_108,'#skF_1'),k3_xboole_0('#skF_2','#skF_3')) = k3_xboole_0(A_108,k4_xboole_0('#skF_1',k3_xboole_0(A_108,'#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_3980])).

tff(c_4946,plain,(
    ! [A_123] : k3_xboole_0(k3_xboole_0(A_123,'#skF_1'),k3_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_4164])).

tff(c_5013,plain,(
    ! [B_50] : k3_xboole_0(k3_xboole_0('#skF_1',B_50),k3_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_4946])).

tff(c_21157,plain,(
    k3_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_21073,c_5013])).

tff(c_1671,plain,(
    ! [A_77,B_78] : k3_xboole_0(A_77,k4_xboole_0(B_78,k3_xboole_0(A_77,B_78))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_70])).

tff(c_1713,plain,(
    ! [A_77,B_78] : k4_xboole_0(A_77,k4_xboole_0(B_78,k3_xboole_0(A_77,B_78))) = k4_xboole_0(A_77,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1671,c_16])).

tff(c_1786,plain,(
    ! [A_77,B_78] : k4_xboole_0(A_77,k4_xboole_0(B_78,k3_xboole_0(A_77,B_78))) = A_77 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1713])).

tff(c_21763,plain,(
    k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_3',k1_xboole_0)) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_21157,c_1786])).

tff(c_21855,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2049,c_20,c_14,c_21763])).

tff(c_21857,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_21855])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:30:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.95/3.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.95/3.42  
% 8.95/3.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.95/3.42  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 8.95/3.42  
% 8.95/3.42  %Foreground sorts:
% 8.95/3.42  
% 8.95/3.42  
% 8.95/3.42  %Background operators:
% 8.95/3.42  
% 8.95/3.42  
% 8.95/3.42  %Foreground operators:
% 8.95/3.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.95/3.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.95/3.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.95/3.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.95/3.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.95/3.42  tff('#skF_2', type, '#skF_2': $i).
% 8.95/3.42  tff('#skF_3', type, '#skF_3': $i).
% 8.95/3.42  tff('#skF_1', type, '#skF_1': $i).
% 8.95/3.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.95/3.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.95/3.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.95/3.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.95/3.42  
% 8.95/3.43  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.95/3.43  tff(f_56, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_xboole_1)).
% 8.95/3.43  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 8.95/3.43  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 8.95/3.43  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.95/3.43  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.95/3.43  tff(f_45, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 8.95/3.43  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 8.95/3.43  tff(c_51, plain, (![A_26, B_27]: (r1_xboole_0(A_26, B_27) | k3_xboole_0(A_26, B_27)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.95/3.43  tff(c_28, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.95/3.43  tff(c_55, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_51, c_28])).
% 8.95/3.43  tff(c_14, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.95/3.43  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.95/3.43  tff(c_56, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.95/3.43  tff(c_72, plain, (k4_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_56])).
% 8.95/3.43  tff(c_253, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k4_xboole_0(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.95/3.43  tff(c_297, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_72, c_253])).
% 8.95/3.43  tff(c_310, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_297])).
% 8.95/3.43  tff(c_12, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.95/3.43  tff(c_71, plain, (![A_6, B_7]: (k4_xboole_0(k4_xboole_0(A_6, B_7), A_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_56])).
% 8.95/3.43  tff(c_510, plain, (![A_49, B_50]: (k4_xboole_0(k3_xboole_0(A_49, B_50), A_49)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_253, c_71])).
% 8.95/3.43  tff(c_20, plain, (![A_13, B_14, C_15]: (k4_xboole_0(k3_xboole_0(A_13, B_14), C_15)=k3_xboole_0(A_13, k4_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.95/3.43  tff(c_571, plain, (![A_51, B_52]: (k3_xboole_0(A_51, k4_xboole_0(B_52, A_51))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_510, c_20])).
% 8.95/3.43  tff(c_16, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.95/3.43  tff(c_591, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k4_xboole_0(B_52, A_51))=k4_xboole_0(A_51, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_571, c_16])).
% 8.95/3.43  tff(c_633, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k4_xboole_0(B_52, A_51))=A_51)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_591])).
% 8.95/3.43  tff(c_343, plain, (![A_42, B_43, C_44]: (k4_xboole_0(k3_xboole_0(A_42, B_43), C_44)=k3_xboole_0(A_42, k4_xboole_0(B_43, C_44)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.95/3.43  tff(c_1805, plain, (![C_79]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_3', C_79))=k4_xboole_0('#skF_1', C_79))), inference(superposition, [status(thm), theory('equality')], [c_310, c_343])).
% 8.95/3.43  tff(c_1855, plain, (![B_52]: (k4_xboole_0('#skF_1', k4_xboole_0(B_52, '#skF_3'))=k3_xboole_0('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_633, c_1805])).
% 8.95/3.43  tff(c_2036, plain, (![B_83]: (k4_xboole_0('#skF_1', k4_xboole_0(B_83, '#skF_3'))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_310, c_1855])).
% 8.95/3.43  tff(c_878, plain, (![A_62, B_63]: (k4_xboole_0(A_62, k4_xboole_0(B_63, A_62))=A_62)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_591])).
% 8.95/3.43  tff(c_515, plain, (![A_49, B_50]: (k3_xboole_0(A_49, k4_xboole_0(B_50, A_49))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_510, c_20])).
% 8.95/3.43  tff(c_893, plain, (![B_63, A_62]: (k3_xboole_0(k4_xboole_0(B_63, A_62), A_62)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_878, c_515])).
% 8.95/3.43  tff(c_2049, plain, (![B_83]: (k3_xboole_0('#skF_1', k4_xboole_0(B_83, '#skF_3'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2036, c_893])).
% 8.95/3.43  tff(c_18, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.95/3.43  tff(c_384, plain, (![A_42, B_43, B_12]: (k3_xboole_0(A_42, k4_xboole_0(B_43, k4_xboole_0(k3_xboole_0(A_42, B_43), B_12)))=k3_xboole_0(k3_xboole_0(A_42, B_43), B_12))), inference(superposition, [status(thm), theory('equality')], [c_18, c_343])).
% 8.95/3.43  tff(c_408, plain, (![A_42, B_43, B_12]: (k3_xboole_0(A_42, k4_xboole_0(B_43, k3_xboole_0(A_42, k4_xboole_0(B_43, B_12))))=k3_xboole_0(k3_xboole_0(A_42, B_43), B_12))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_384])).
% 8.95/3.43  tff(c_3980, plain, (![A_108, B_109, B_110]: (k3_xboole_0(A_108, k4_xboole_0(B_109, k3_xboole_0(A_108, k4_xboole_0(B_109, B_110))))=k3_xboole_0(k3_xboole_0(A_108, B_109), B_110))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_384])).
% 8.95/3.43  tff(c_4170, plain, (![A_108, A_9, B_10]: (k3_xboole_0(A_108, k4_xboole_0(A_9, k3_xboole_0(A_108, k4_xboole_0(A_9, B_10))))=k3_xboole_0(k3_xboole_0(A_108, A_9), k3_xboole_0(A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_3980])).
% 8.95/3.43  tff(c_21073, plain, (![A_239, A_240, B_241]: (k3_xboole_0(k3_xboole_0(A_239, A_240), k3_xboole_0(A_240, B_241))=k3_xboole_0(k3_xboole_0(A_239, A_240), B_241))), inference(demodulation, [status(thm), theory('equality')], [c_408, c_4170])).
% 8.95/3.43  tff(c_518, plain, (![A_49, B_50]: (k4_xboole_0(k3_xboole_0(A_49, B_50), k1_xboole_0)=k3_xboole_0(k3_xboole_0(A_49, B_50), A_49))), inference(superposition, [status(thm), theory('equality')], [c_510, c_18])).
% 8.95/3.43  tff(c_558, plain, (![A_49, B_50]: (k3_xboole_0(k3_xboole_0(A_49, B_50), A_49)=k3_xboole_0(A_49, B_50))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_518])).
% 8.95/3.43  tff(c_45, plain, (![A_21, B_22]: (r1_tarski(k4_xboole_0(A_21, B_22), A_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.95/3.43  tff(c_48, plain, (![A_8]: (r1_tarski(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_14, c_45])).
% 8.95/3.43  tff(c_70, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_56])).
% 8.95/3.43  tff(c_364, plain, (![A_42, B_43]: (k3_xboole_0(A_42, k4_xboole_0(B_43, k3_xboole_0(A_42, B_43)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_343, c_70])).
% 8.95/3.43  tff(c_24, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.95/3.43  tff(c_110, plain, (![A_32, B_33]: (k3_xboole_0(A_32, B_33)=k1_xboole_0 | ~r1_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.95/3.43  tff(c_118, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_110])).
% 8.95/3.43  tff(c_161, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k3_xboole_0(A_35, B_36))=k4_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.95/3.43  tff(c_177, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_118, c_161])).
% 8.95/3.43  tff(c_189, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_177])).
% 8.95/3.43  tff(c_4164, plain, (![A_108]: (k3_xboole_0(k3_xboole_0(A_108, '#skF_1'), k3_xboole_0('#skF_2', '#skF_3'))=k3_xboole_0(A_108, k4_xboole_0('#skF_1', k3_xboole_0(A_108, '#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_189, c_3980])).
% 8.95/3.43  tff(c_4946, plain, (![A_123]: (k3_xboole_0(k3_xboole_0(A_123, '#skF_1'), k3_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_364, c_4164])).
% 8.95/3.43  tff(c_5013, plain, (![B_50]: (k3_xboole_0(k3_xboole_0('#skF_1', B_50), k3_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_558, c_4946])).
% 8.95/3.43  tff(c_21157, plain, (k3_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_21073, c_5013])).
% 8.95/3.43  tff(c_1671, plain, (![A_77, B_78]: (k3_xboole_0(A_77, k4_xboole_0(B_78, k3_xboole_0(A_77, B_78)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_343, c_70])).
% 8.95/3.43  tff(c_1713, plain, (![A_77, B_78]: (k4_xboole_0(A_77, k4_xboole_0(B_78, k3_xboole_0(A_77, B_78)))=k4_xboole_0(A_77, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1671, c_16])).
% 8.95/3.43  tff(c_1786, plain, (![A_77, B_78]: (k4_xboole_0(A_77, k4_xboole_0(B_78, k3_xboole_0(A_77, B_78)))=A_77)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1713])).
% 8.95/3.43  tff(c_21763, plain, (k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_3', k1_xboole_0))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_21157, c_1786])).
% 8.95/3.43  tff(c_21855, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2049, c_20, c_14, c_21763])).
% 8.95/3.43  tff(c_21857, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_21855])).
% 8.95/3.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.95/3.43  
% 8.95/3.43  Inference rules
% 8.95/3.43  ----------------------
% 8.95/3.43  #Ref     : 0
% 8.95/3.43  #Sup     : 5418
% 8.95/3.43  #Fact    : 0
% 8.95/3.43  #Define  : 0
% 8.95/3.43  #Split   : 0
% 8.95/3.43  #Chain   : 0
% 8.95/3.43  #Close   : 0
% 8.95/3.43  
% 8.95/3.43  Ordering : KBO
% 8.95/3.43  
% 8.95/3.43  Simplification rules
% 8.95/3.43  ----------------------
% 8.95/3.43  #Subsume      : 0
% 8.95/3.43  #Demod        : 7213
% 8.95/3.43  #Tautology    : 4015
% 8.95/3.43  #SimpNegUnit  : 1
% 8.95/3.43  #BackRed      : 8
% 8.95/3.43  
% 8.95/3.43  #Partial instantiations: 0
% 8.95/3.43  #Strategies tried      : 1
% 8.95/3.43  
% 8.95/3.43  Timing (in seconds)
% 8.95/3.43  ----------------------
% 8.95/3.44  Preprocessing        : 0.29
% 8.95/3.44  Parsing              : 0.16
% 8.95/3.44  CNF conversion       : 0.02
% 8.95/3.44  Main loop            : 2.33
% 8.95/3.44  Inferencing          : 0.55
% 8.95/3.44  Reduction            : 1.31
% 8.95/3.44  Demodulation         : 1.16
% 8.95/3.44  BG Simplification    : 0.06
% 8.95/3.44  Subsumption          : 0.30
% 8.95/3.44  Abstraction          : 0.12
% 8.95/3.44  MUC search           : 0.00
% 8.95/3.44  Cooper               : 0.00
% 8.95/3.44  Total                : 2.66
% 8.95/3.44  Index Insertion      : 0.00
% 8.95/3.44  Index Deletion       : 0.00
% 8.95/3.44  Index Matching       : 0.00
% 8.95/3.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
