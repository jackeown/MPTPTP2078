%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:15 EST 2020

% Result     : Theorem 15.37s
% Output     : CNFRefutation 15.64s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 109 expanded)
%              Number of leaves         :   23 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :   72 ( 131 expanded)
%              Number of equality atoms :   46 (  72 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_66572,plain,(
    ! [A_524,B_525] :
      ( r1_xboole_0(A_524,B_525)
      | k3_xboole_0(A_524,B_525) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_526,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(A_56,B_57)
      | k4_xboole_0(A_56,B_57) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_66,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_538,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_526,c_66])).

tff(c_32,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_160,plain,(
    ! [A_36,B_37] :
      ( k3_xboole_0(A_36,B_37) = A_36
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_170,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_160])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1198,plain,(
    ! [A_80,B_81,C_82] : k4_xboole_0(k3_xboole_0(A_80,B_81),k3_xboole_0(A_80,C_82)) = k3_xboole_0(A_80,k4_xboole_0(B_81,C_82)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_7451,plain,(
    ! [A_146,B_147,C_148] : k4_xboole_0(k3_xboole_0(A_146,B_147),k3_xboole_0(B_147,C_148)) = k3_xboole_0(B_147,k4_xboole_0(A_146,C_148)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1198])).

tff(c_7665,plain,(
    ! [C_148] : k4_xboole_0('#skF_1',k3_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_148)) = k3_xboole_0(k4_xboole_0('#skF_2','#skF_3'),k4_xboole_0('#skF_1',C_148)) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_7451])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_771,plain,(
    ! [A_69,B_70,C_71] : k3_xboole_0(k3_xboole_0(A_69,B_70),C_71) = k3_xboole_0(A_69,k3_xboole_0(B_70,C_71)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_9671,plain,(
    ! [A_174,B_175,C_176] : k5_xboole_0(k3_xboole_0(A_174,B_175),k3_xboole_0(A_174,k3_xboole_0(B_175,C_176))) = k4_xboole_0(k3_xboole_0(A_174,B_175),C_176) ),
    inference(superposition,[status(thm),theory(equality)],[c_771,c_12])).

tff(c_9908,plain,(
    ! [C_176] : k5_xboole_0('#skF_1',k3_xboole_0('#skF_1',k3_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_176))) = k4_xboole_0(k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')),C_176) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_9671])).

tff(c_65857,plain,(
    ! [C_508] : k3_xboole_0(k4_xboole_0('#skF_2','#skF_3'),k4_xboole_0('#skF_1',C_508)) = k4_xboole_0('#skF_1',C_508) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7665,c_12,c_170,c_9908])).

tff(c_67,plain,(
    ! [B_33,A_34] : k3_xboole_0(B_33,A_34) = k3_xboole_0(A_34,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_16] : k3_xboole_0(A_16,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_89,plain,(
    ! [A_34] : k3_xboole_0(k1_xboole_0,A_34) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_20])).

tff(c_61,plain,(
    ! [A_30,B_31] : r1_tarski(k3_xboole_0(A_30,B_31),A_30) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_64,plain,(
    ! [A_16] : r1_tarski(k1_xboole_0,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_61])).

tff(c_302,plain,(
    ! [A_46,B_47] :
      ( k4_xboole_0(A_46,B_47) = k1_xboole_0
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_321,plain,(
    ! [A_16] : k4_xboole_0(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_302])).

tff(c_26,plain,(
    ! [A_21,B_22] : r1_xboole_0(k4_xboole_0(A_21,B_22),B_22) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_223,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_232,plain,(
    ! [A_21,B_22] : k3_xboole_0(k4_xboole_0(A_21,B_22),B_22) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_223])).

tff(c_8624,plain,(
    ! [B_161,B_162,A_163] : k4_xboole_0(k3_xboole_0(B_161,B_162),k3_xboole_0(A_163,B_161)) = k3_xboole_0(B_161,k4_xboole_0(B_162,A_163)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1198])).

tff(c_8834,plain,(
    ! [A_163,A_21,B_22] : k4_xboole_0(k1_xboole_0,k3_xboole_0(A_163,k4_xboole_0(A_21,B_22))) = k3_xboole_0(k4_xboole_0(A_21,B_22),k4_xboole_0(B_22,A_163)) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_8624])).

tff(c_19655,plain,(
    ! [A_235,B_236,A_237] : k3_xboole_0(k4_xboole_0(A_235,B_236),k4_xboole_0(B_236,A_237)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_8834])).

tff(c_16,plain,(
    ! [A_12,B_13] : r1_tarski(k3_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1610,plain,(
    ! [A_87,B_88] : k3_xboole_0(k3_xboole_0(A_87,B_88),A_87) = k3_xboole_0(A_87,B_88) ),
    inference(resolution,[status(thm)],[c_16,c_160])).

tff(c_1727,plain,(
    ! [A_1,B_2] : k3_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k3_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1610])).

tff(c_19663,plain,(
    ! [B_236,A_237,A_235] : k3_xboole_0(k4_xboole_0(B_236,A_237),k4_xboole_0(A_235,B_236)) = k3_xboole_0(k1_xboole_0,k4_xboole_0(B_236,A_237)) ),
    inference(superposition,[status(thm),theory(equality)],[c_19655,c_1727])).

tff(c_20023,plain,(
    ! [B_236,A_237,A_235] : k3_xboole_0(k4_xboole_0(B_236,A_237),k4_xboole_0(A_235,B_236)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_19663])).

tff(c_66025,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_65857,c_20023])).

tff(c_66313,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_538,c_66025])).

tff(c_66314,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_66580,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_66572,c_66314])).

tff(c_66369,plain,(
    ! [A_511,B_512] :
      ( k3_xboole_0(A_511,B_512) = k1_xboole_0
      | ~ r1_xboole_0(A_511,B_512) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66378,plain,(
    ! [A_21,B_22] : k3_xboole_0(k4_xboole_0(A_21,B_22),B_22) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_66369])).

tff(c_66506,plain,(
    ! [A_522,B_523] :
      ( k3_xboole_0(A_522,B_523) = A_522
      | ~ r1_tarski(A_522,B_523) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_66528,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_66506])).

tff(c_66955,plain,(
    ! [A_539,B_540,C_541] : k3_xboole_0(k3_xboole_0(A_539,B_540),C_541) = k3_xboole_0(A_539,k3_xboole_0(B_540,C_541)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_68284,plain,(
    ! [C_571] : k3_xboole_0('#skF_1',k3_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_571)) = k3_xboole_0('#skF_1',C_571) ),
    inference(superposition,[status(thm),theory(equality)],[c_66528,c_66955])).

tff(c_68356,plain,(
    k3_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_66378,c_68284])).

tff(c_68387,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_68356])).

tff(c_68389,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66580,c_68387])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:56:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.37/9.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.37/9.09  
% 15.37/9.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.37/9.09  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 15.37/9.09  
% 15.37/9.09  %Foreground sorts:
% 15.37/9.09  
% 15.37/9.09  
% 15.37/9.09  %Background operators:
% 15.37/9.09  
% 15.37/9.09  
% 15.37/9.09  %Foreground operators:
% 15.37/9.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.37/9.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.37/9.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.37/9.09  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 15.37/9.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.37/9.09  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 15.37/9.09  tff('#skF_2', type, '#skF_2': $i).
% 15.37/9.09  tff('#skF_3', type, '#skF_3': $i).
% 15.37/9.09  tff('#skF_1', type, '#skF_1': $i).
% 15.37/9.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.37/9.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.37/9.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.37/9.09  
% 15.64/9.10  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 15.64/9.10  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 15.64/9.10  tff(f_62, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 15.64/9.10  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 15.64/9.10  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 15.64/9.10  tff(f_51, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_xboole_1)).
% 15.64/9.10  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 15.64/9.10  tff(f_39, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 15.64/9.10  tff(f_47, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 15.64/9.10  tff(f_41, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 15.64/9.10  tff(f_53, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 15.64/9.10  tff(c_66572, plain, (![A_524, B_525]: (r1_xboole_0(A_524, B_525) | k3_xboole_0(A_524, B_525)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.64/9.10  tff(c_526, plain, (![A_56, B_57]: (r1_tarski(A_56, B_57) | k4_xboole_0(A_56, B_57)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.64/9.10  tff(c_30, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 15.64/9.10  tff(c_66, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_30])).
% 15.64/9.10  tff(c_538, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_526, c_66])).
% 15.64/9.10  tff(c_32, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 15.64/9.10  tff(c_160, plain, (![A_36, B_37]: (k3_xboole_0(A_36, B_37)=A_36 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.64/9.10  tff(c_170, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_32, c_160])).
% 15.64/9.10  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 15.64/9.10  tff(c_1198, plain, (![A_80, B_81, C_82]: (k4_xboole_0(k3_xboole_0(A_80, B_81), k3_xboole_0(A_80, C_82))=k3_xboole_0(A_80, k4_xboole_0(B_81, C_82)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.64/9.10  tff(c_7451, plain, (![A_146, B_147, C_148]: (k4_xboole_0(k3_xboole_0(A_146, B_147), k3_xboole_0(B_147, C_148))=k3_xboole_0(B_147, k4_xboole_0(A_146, C_148)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1198])).
% 15.64/9.10  tff(c_7665, plain, (![C_148]: (k4_xboole_0('#skF_1', k3_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_148))=k3_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), k4_xboole_0('#skF_1', C_148)))), inference(superposition, [status(thm), theory('equality')], [c_170, c_7451])).
% 15.64/9.10  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.64/9.10  tff(c_771, plain, (![A_69, B_70, C_71]: (k3_xboole_0(k3_xboole_0(A_69, B_70), C_71)=k3_xboole_0(A_69, k3_xboole_0(B_70, C_71)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 15.64/9.10  tff(c_9671, plain, (![A_174, B_175, C_176]: (k5_xboole_0(k3_xboole_0(A_174, B_175), k3_xboole_0(A_174, k3_xboole_0(B_175, C_176)))=k4_xboole_0(k3_xboole_0(A_174, B_175), C_176))), inference(superposition, [status(thm), theory('equality')], [c_771, c_12])).
% 15.64/9.10  tff(c_9908, plain, (![C_176]: (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', k3_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_176)))=k4_xboole_0(k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), C_176))), inference(superposition, [status(thm), theory('equality')], [c_170, c_9671])).
% 15.64/9.10  tff(c_65857, plain, (![C_508]: (k3_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), k4_xboole_0('#skF_1', C_508))=k4_xboole_0('#skF_1', C_508))), inference(demodulation, [status(thm), theory('equality')], [c_7665, c_12, c_170, c_9908])).
% 15.64/9.10  tff(c_67, plain, (![B_33, A_34]: (k3_xboole_0(B_33, A_34)=k3_xboole_0(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_27])).
% 15.64/9.10  tff(c_20, plain, (![A_16]: (k3_xboole_0(A_16, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 15.64/9.10  tff(c_89, plain, (![A_34]: (k3_xboole_0(k1_xboole_0, A_34)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_67, c_20])).
% 15.64/9.10  tff(c_61, plain, (![A_30, B_31]: (r1_tarski(k3_xboole_0(A_30, B_31), A_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.64/9.10  tff(c_64, plain, (![A_16]: (r1_tarski(k1_xboole_0, A_16))), inference(superposition, [status(thm), theory('equality')], [c_20, c_61])).
% 15.64/9.10  tff(c_302, plain, (![A_46, B_47]: (k4_xboole_0(A_46, B_47)=k1_xboole_0 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.64/9.10  tff(c_321, plain, (![A_16]: (k4_xboole_0(k1_xboole_0, A_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_64, c_302])).
% 15.64/9.10  tff(c_26, plain, (![A_21, B_22]: (r1_xboole_0(k4_xboole_0(A_21, B_22), B_22))), inference(cnfTransformation, [status(thm)], [f_53])).
% 15.64/9.10  tff(c_223, plain, (![A_40, B_41]: (k3_xboole_0(A_40, B_41)=k1_xboole_0 | ~r1_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.64/9.10  tff(c_232, plain, (![A_21, B_22]: (k3_xboole_0(k4_xboole_0(A_21, B_22), B_22)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_223])).
% 15.64/9.10  tff(c_8624, plain, (![B_161, B_162, A_163]: (k4_xboole_0(k3_xboole_0(B_161, B_162), k3_xboole_0(A_163, B_161))=k3_xboole_0(B_161, k4_xboole_0(B_162, A_163)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1198])).
% 15.64/9.10  tff(c_8834, plain, (![A_163, A_21, B_22]: (k4_xboole_0(k1_xboole_0, k3_xboole_0(A_163, k4_xboole_0(A_21, B_22)))=k3_xboole_0(k4_xboole_0(A_21, B_22), k4_xboole_0(B_22, A_163)))), inference(superposition, [status(thm), theory('equality')], [c_232, c_8624])).
% 15.64/9.10  tff(c_19655, plain, (![A_235, B_236, A_237]: (k3_xboole_0(k4_xboole_0(A_235, B_236), k4_xboole_0(B_236, A_237))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_321, c_8834])).
% 15.64/9.10  tff(c_16, plain, (![A_12, B_13]: (r1_tarski(k3_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.64/9.10  tff(c_1610, plain, (![A_87, B_88]: (k3_xboole_0(k3_xboole_0(A_87, B_88), A_87)=k3_xboole_0(A_87, B_88))), inference(resolution, [status(thm)], [c_16, c_160])).
% 15.64/9.10  tff(c_1727, plain, (![A_1, B_2]: (k3_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k3_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1610])).
% 15.64/9.10  tff(c_19663, plain, (![B_236, A_237, A_235]: (k3_xboole_0(k4_xboole_0(B_236, A_237), k4_xboole_0(A_235, B_236))=k3_xboole_0(k1_xboole_0, k4_xboole_0(B_236, A_237)))), inference(superposition, [status(thm), theory('equality')], [c_19655, c_1727])).
% 15.64/9.10  tff(c_20023, plain, (![B_236, A_237, A_235]: (k3_xboole_0(k4_xboole_0(B_236, A_237), k4_xboole_0(A_235, B_236))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_89, c_19663])).
% 15.64/9.10  tff(c_66025, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_65857, c_20023])).
% 15.64/9.10  tff(c_66313, plain, $false, inference(negUnitSimplification, [status(thm)], [c_538, c_66025])).
% 15.64/9.10  tff(c_66314, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 15.64/9.10  tff(c_66580, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_66572, c_66314])).
% 15.64/9.10  tff(c_66369, plain, (![A_511, B_512]: (k3_xboole_0(A_511, B_512)=k1_xboole_0 | ~r1_xboole_0(A_511, B_512))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.64/9.10  tff(c_66378, plain, (![A_21, B_22]: (k3_xboole_0(k4_xboole_0(A_21, B_22), B_22)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_66369])).
% 15.64/9.10  tff(c_66506, plain, (![A_522, B_523]: (k3_xboole_0(A_522, B_523)=A_522 | ~r1_tarski(A_522, B_523))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.64/9.10  tff(c_66528, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_32, c_66506])).
% 15.64/9.10  tff(c_66955, plain, (![A_539, B_540, C_541]: (k3_xboole_0(k3_xboole_0(A_539, B_540), C_541)=k3_xboole_0(A_539, k3_xboole_0(B_540, C_541)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 15.64/9.10  tff(c_68284, plain, (![C_571]: (k3_xboole_0('#skF_1', k3_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_571))=k3_xboole_0('#skF_1', C_571))), inference(superposition, [status(thm), theory('equality')], [c_66528, c_66955])).
% 15.64/9.10  tff(c_68356, plain, (k3_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_66378, c_68284])).
% 15.64/9.10  tff(c_68387, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_68356])).
% 15.64/9.10  tff(c_68389, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66580, c_68387])).
% 15.64/9.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.64/9.10  
% 15.64/9.10  Inference rules
% 15.64/9.10  ----------------------
% 15.64/9.10  #Ref     : 0
% 15.64/9.10  #Sup     : 16905
% 15.64/9.10  #Fact    : 0
% 15.64/9.10  #Define  : 0
% 15.64/9.10  #Split   : 1
% 15.64/9.10  #Chain   : 0
% 15.64/9.10  #Close   : 0
% 15.64/9.10  
% 15.64/9.10  Ordering : KBO
% 15.64/9.10  
% 15.64/9.10  Simplification rules
% 15.64/9.10  ----------------------
% 15.64/9.10  #Subsume      : 200
% 15.64/9.10  #Demod        : 19966
% 15.64/9.10  #Tautology    : 11855
% 15.64/9.11  #SimpNegUnit  : 2
% 15.64/9.11  #BackRed      : 5
% 15.64/9.11  
% 15.64/9.11  #Partial instantiations: 0
% 15.64/9.11  #Strategies tried      : 1
% 15.64/9.11  
% 15.64/9.11  Timing (in seconds)
% 15.64/9.11  ----------------------
% 15.64/9.11  Preprocessing        : 0.30
% 15.64/9.11  Parsing              : 0.17
% 15.64/9.11  CNF conversion       : 0.02
% 15.64/9.11  Main loop            : 7.99
% 15.64/9.11  Inferencing          : 0.99
% 15.64/9.11  Reduction            : 5.28
% 15.64/9.11  Demodulation         : 4.87
% 15.64/9.11  BG Simplification    : 0.12
% 15.64/9.11  Subsumption          : 1.28
% 15.64/9.11  Abstraction          : 0.20
% 15.64/9.11  MUC search           : 0.00
% 15.64/9.11  Cooper               : 0.00
% 15.64/9.11  Total                : 8.33
% 15.64/9.11  Index Insertion      : 0.00
% 15.64/9.11  Index Deletion       : 0.00
% 15.64/9.11  Index Matching       : 0.00
% 15.64/9.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
