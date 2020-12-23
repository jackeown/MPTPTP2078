%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:18 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 263 expanded)
%              Number of leaves         :   18 (  97 expanded)
%              Depth                    :   12
%              Number of atoms          :   57 ( 258 expanded)
%              Number of equality atoms :   49 ( 247 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_68,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_53])).

tff(c_71,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_68])).

tff(c_183,plain,(
    ! [A_27,B_28,C_29] : k2_xboole_0(k4_xboole_0(A_27,B_28),k3_xboole_0(A_27,C_29)) = k4_xboole_0(A_27,k4_xboole_0(B_28,C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_210,plain,(
    ! [A_3,B_28] : k4_xboole_0(A_3,k4_xboole_0(B_28,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(A_3,B_28),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_183])).

tff(c_218,plain,(
    ! [A_30,B_31] : k2_xboole_0(k4_xboole_0(A_30,B_31),k1_xboole_0) = k4_xboole_0(A_30,B_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_210])).

tff(c_236,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = k2_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_218])).

tff(c_242,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_236])).

tff(c_18,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_40,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = k1_xboole_0
      | ~ r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_40])).

tff(c_207,plain,(
    ! [B_28] : k4_xboole_0('#skF_1',k4_xboole_0(B_28,'#skF_2')) = k2_xboole_0(k4_xboole_0('#skF_1',B_28),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_183])).

tff(c_260,plain,(
    ! [B_33] : k4_xboole_0('#skF_1',k4_xboole_0(B_33,'#skF_2')) = k4_xboole_0('#skF_1',B_33) ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_207])).

tff(c_283,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_260])).

tff(c_293,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_283])).

tff(c_12,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_72,plain,(
    ! [A_20,B_21] : k2_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_866,plain,(
    ! [A_47,B_48] : k2_xboole_0(k4_xboole_0(A_47,B_48),k3_xboole_0(A_47,B_48)) = k2_xboole_0(k4_xboole_0(A_47,B_48),A_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_72])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] : k2_xboole_0(k4_xboole_0(A_9,B_10),k3_xboole_0(A_9,C_11)) = k4_xboole_0(A_9,k4_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_872,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k4_xboole_0(B_48,B_48)) = k2_xboole_0(k4_xboole_0(A_47,B_48),A_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_866,c_14])).

tff(c_932,plain,(
    ! [A_47,B_48] : k2_xboole_0(k4_xboole_0(A_47,B_48),A_47) = A_47 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_71,c_872])).

tff(c_88,plain,(
    ! [A_22] : k4_xboole_0(A_22,A_22) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_68])).

tff(c_96,plain,(
    ! [A_22] : k4_xboole_0(A_22,k1_xboole_0) = k3_xboole_0(A_22,A_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_12])).

tff(c_108,plain,(
    ! [A_22] : k3_xboole_0(A_22,A_22) = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_96])).

tff(c_198,plain,(
    ! [A_22,B_28] : k4_xboole_0(A_22,k4_xboole_0(B_28,A_22)) = k2_xboole_0(k4_xboole_0(A_22,B_28),A_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_183])).

tff(c_1732,plain,(
    ! [A_69,B_70] : k4_xboole_0(A_69,k4_xboole_0(B_70,A_69)) = A_69 ),
    inference(demodulation,[status(thm),theory(equality)],[c_932,c_198])).

tff(c_1810,plain,(
    k4_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_1732])).

tff(c_953,plain,(
    ! [A_49,B_50] : k2_xboole_0(k4_xboole_0(A_49,B_50),A_49) = A_49 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_71,c_872])).

tff(c_960,plain,(
    ! [B_50] : k4_xboole_0(k1_xboole_0,B_50) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_953,c_242])).

tff(c_213,plain,(
    ! [A_6,C_29] : k4_xboole_0(A_6,k4_xboole_0(k1_xboole_0,C_29)) = k2_xboole_0(A_6,k3_xboole_0(A_6,C_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_183])).

tff(c_1006,plain,(
    ! [A_6,C_29] : k2_xboole_0(A_6,k3_xboole_0(A_6,C_29)) = k4_xboole_0(A_6,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_960,c_213])).

tff(c_1009,plain,(
    ! [A_6,C_29] : k2_xboole_0(A_6,k3_xboole_0(A_6,C_29)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1006])).

tff(c_1777,plain,(
    ! [A_69,B_70,C_11] : k4_xboole_0(A_69,k4_xboole_0(k4_xboole_0(B_70,A_69),C_11)) = k2_xboole_0(A_69,k3_xboole_0(A_69,C_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1732,c_14])).

tff(c_2766,plain,(
    ! [A_85,B_86,C_87] : k4_xboole_0(A_85,k4_xboole_0(k4_xboole_0(B_86,A_85),C_87)) = A_85 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1009,c_1777])).

tff(c_2979,plain,(
    ! [C_88] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_88)) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1810,c_2766])).

tff(c_1730,plain,(
    ! [A_22,B_28] : k4_xboole_0(A_22,k4_xboole_0(B_28,A_22)) = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_932,c_198])).

tff(c_1783,plain,(
    ! [A_69,B_70] : k3_xboole_0(A_69,k4_xboole_0(B_70,A_69)) = k4_xboole_0(A_69,A_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_1732,c_12])).

tff(c_1921,plain,(
    ! [A_71,B_72] : k3_xboole_0(A_71,k4_xboole_0(B_72,A_71)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_1783])).

tff(c_1956,plain,(
    ! [B_28,A_22] : k3_xboole_0(k4_xboole_0(B_28,A_22),A_22) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1730,c_1921])).

tff(c_3000,plain,(
    ! [C_88] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_88)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2979,c_1956])).

tff(c_35,plain,(
    ! [A_14,B_15] :
      ( r1_xboole_0(A_14,B_15)
      | k3_xboole_0(A_14,B_15) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ~ r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_39,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_35,c_16])).

tff(c_3112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3000,c_39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:38:29 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.48/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.56  
% 3.48/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.57  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.48/1.57  
% 3.48/1.57  %Foreground sorts:
% 3.48/1.57  
% 3.48/1.57  
% 3.48/1.57  %Background operators:
% 3.48/1.57  
% 3.48/1.57  
% 3.48/1.57  %Foreground operators:
% 3.48/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.48/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.48/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.48/1.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.48/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.48/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.48/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.48/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.48/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.48/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.48/1.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.48/1.57  
% 3.48/1.58  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.48/1.58  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.48/1.58  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.48/1.58  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 3.48/1.58  tff(f_44, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_xboole_1)).
% 3.48/1.58  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.48/1.58  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.48/1.58  tff(c_10, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.48/1.58  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.48/1.58  tff(c_53, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.48/1.58  tff(c_68, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_53])).
% 3.48/1.58  tff(c_71, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_68])).
% 3.48/1.58  tff(c_183, plain, (![A_27, B_28, C_29]: (k2_xboole_0(k4_xboole_0(A_27, B_28), k3_xboole_0(A_27, C_29))=k4_xboole_0(A_27, k4_xboole_0(B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.48/1.58  tff(c_210, plain, (![A_3, B_28]: (k4_xboole_0(A_3, k4_xboole_0(B_28, k1_xboole_0))=k2_xboole_0(k4_xboole_0(A_3, B_28), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_183])).
% 3.48/1.58  tff(c_218, plain, (![A_30, B_31]: (k2_xboole_0(k4_xboole_0(A_30, B_31), k1_xboole_0)=k4_xboole_0(A_30, B_31))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_210])).
% 3.48/1.58  tff(c_236, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=k2_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_218])).
% 3.48/1.58  tff(c_242, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_236])).
% 3.48/1.58  tff(c_18, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.48/1.58  tff(c_40, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=k1_xboole_0 | ~r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.48/1.58  tff(c_48, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_40])).
% 3.48/1.58  tff(c_207, plain, (![B_28]: (k4_xboole_0('#skF_1', k4_xboole_0(B_28, '#skF_2'))=k2_xboole_0(k4_xboole_0('#skF_1', B_28), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_48, c_183])).
% 3.48/1.58  tff(c_260, plain, (![B_33]: (k4_xboole_0('#skF_1', k4_xboole_0(B_33, '#skF_2'))=k4_xboole_0('#skF_1', B_33))), inference(demodulation, [status(thm), theory('equality')], [c_242, c_207])).
% 3.48/1.58  tff(c_283, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_71, c_260])).
% 3.48/1.58  tff(c_293, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_283])).
% 3.48/1.58  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.48/1.58  tff(c_72, plain, (![A_20, B_21]: (k2_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.48/1.58  tff(c_866, plain, (![A_47, B_48]: (k2_xboole_0(k4_xboole_0(A_47, B_48), k3_xboole_0(A_47, B_48))=k2_xboole_0(k4_xboole_0(A_47, B_48), A_47))), inference(superposition, [status(thm), theory('equality')], [c_12, c_72])).
% 3.48/1.58  tff(c_14, plain, (![A_9, B_10, C_11]: (k2_xboole_0(k4_xboole_0(A_9, B_10), k3_xboole_0(A_9, C_11))=k4_xboole_0(A_9, k4_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.48/1.58  tff(c_872, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k4_xboole_0(B_48, B_48))=k2_xboole_0(k4_xboole_0(A_47, B_48), A_47))), inference(superposition, [status(thm), theory('equality')], [c_866, c_14])).
% 3.48/1.58  tff(c_932, plain, (![A_47, B_48]: (k2_xboole_0(k4_xboole_0(A_47, B_48), A_47)=A_47)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_71, c_872])).
% 3.48/1.58  tff(c_88, plain, (![A_22]: (k4_xboole_0(A_22, A_22)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_68])).
% 3.48/1.58  tff(c_96, plain, (![A_22]: (k4_xboole_0(A_22, k1_xboole_0)=k3_xboole_0(A_22, A_22))), inference(superposition, [status(thm), theory('equality')], [c_88, c_12])).
% 3.48/1.58  tff(c_108, plain, (![A_22]: (k3_xboole_0(A_22, A_22)=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_96])).
% 3.48/1.58  tff(c_198, plain, (![A_22, B_28]: (k4_xboole_0(A_22, k4_xboole_0(B_28, A_22))=k2_xboole_0(k4_xboole_0(A_22, B_28), A_22))), inference(superposition, [status(thm), theory('equality')], [c_108, c_183])).
% 3.48/1.58  tff(c_1732, plain, (![A_69, B_70]: (k4_xboole_0(A_69, k4_xboole_0(B_70, A_69))=A_69)), inference(demodulation, [status(thm), theory('equality')], [c_932, c_198])).
% 3.48/1.58  tff(c_1810, plain, (k4_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_293, c_1732])).
% 3.48/1.58  tff(c_953, plain, (![A_49, B_50]: (k2_xboole_0(k4_xboole_0(A_49, B_50), A_49)=A_49)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_71, c_872])).
% 3.48/1.58  tff(c_960, plain, (![B_50]: (k4_xboole_0(k1_xboole_0, B_50)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_953, c_242])).
% 3.48/1.58  tff(c_213, plain, (![A_6, C_29]: (k4_xboole_0(A_6, k4_xboole_0(k1_xboole_0, C_29))=k2_xboole_0(A_6, k3_xboole_0(A_6, C_29)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_183])).
% 3.48/1.58  tff(c_1006, plain, (![A_6, C_29]: (k2_xboole_0(A_6, k3_xboole_0(A_6, C_29))=k4_xboole_0(A_6, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_960, c_213])).
% 3.48/1.58  tff(c_1009, plain, (![A_6, C_29]: (k2_xboole_0(A_6, k3_xboole_0(A_6, C_29))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1006])).
% 3.48/1.58  tff(c_1777, plain, (![A_69, B_70, C_11]: (k4_xboole_0(A_69, k4_xboole_0(k4_xboole_0(B_70, A_69), C_11))=k2_xboole_0(A_69, k3_xboole_0(A_69, C_11)))), inference(superposition, [status(thm), theory('equality')], [c_1732, c_14])).
% 3.48/1.58  tff(c_2766, plain, (![A_85, B_86, C_87]: (k4_xboole_0(A_85, k4_xboole_0(k4_xboole_0(B_86, A_85), C_87))=A_85)), inference(demodulation, [status(thm), theory('equality')], [c_1009, c_1777])).
% 3.48/1.58  tff(c_2979, plain, (![C_88]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_88))='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1810, c_2766])).
% 3.48/1.58  tff(c_1730, plain, (![A_22, B_28]: (k4_xboole_0(A_22, k4_xboole_0(B_28, A_22))=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_932, c_198])).
% 3.48/1.58  tff(c_1783, plain, (![A_69, B_70]: (k3_xboole_0(A_69, k4_xboole_0(B_70, A_69))=k4_xboole_0(A_69, A_69))), inference(superposition, [status(thm), theory('equality')], [c_1732, c_12])).
% 3.48/1.58  tff(c_1921, plain, (![A_71, B_72]: (k3_xboole_0(A_71, k4_xboole_0(B_72, A_71))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_71, c_1783])).
% 3.48/1.58  tff(c_1956, plain, (![B_28, A_22]: (k3_xboole_0(k4_xboole_0(B_28, A_22), A_22)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1730, c_1921])).
% 3.48/1.58  tff(c_3000, plain, (![C_88]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_88))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2979, c_1956])).
% 3.48/1.58  tff(c_35, plain, (![A_14, B_15]: (r1_xboole_0(A_14, B_15) | k3_xboole_0(A_14, B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.48/1.58  tff(c_16, plain, (~r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.48/1.58  tff(c_39, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_35, c_16])).
% 3.48/1.58  tff(c_3112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3000, c_39])).
% 3.48/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.58  
% 3.48/1.58  Inference rules
% 3.48/1.58  ----------------------
% 3.48/1.58  #Ref     : 0
% 3.48/1.58  #Sup     : 749
% 3.48/1.58  #Fact    : 0
% 3.48/1.58  #Define  : 0
% 3.48/1.58  #Split   : 0
% 3.48/1.58  #Chain   : 0
% 3.48/1.58  #Close   : 0
% 3.48/1.58  
% 3.48/1.58  Ordering : KBO
% 3.48/1.58  
% 3.48/1.58  Simplification rules
% 3.48/1.58  ----------------------
% 3.48/1.58  #Subsume      : 0
% 3.48/1.58  #Demod        : 788
% 3.48/1.58  #Tautology    : 554
% 3.48/1.58  #SimpNegUnit  : 0
% 3.48/1.58  #BackRed      : 13
% 3.48/1.58  
% 3.48/1.58  #Partial instantiations: 0
% 3.48/1.58  #Strategies tried      : 1
% 3.48/1.58  
% 3.48/1.58  Timing (in seconds)
% 3.48/1.58  ----------------------
% 3.48/1.58  Preprocessing        : 0.26
% 3.48/1.58  Parsing              : 0.15
% 3.48/1.58  CNF conversion       : 0.01
% 3.48/1.58  Main loop            : 0.57
% 3.48/1.58  Inferencing          : 0.21
% 3.48/1.58  Reduction            : 0.23
% 3.48/1.58  Demodulation         : 0.19
% 3.48/1.58  BG Simplification    : 0.02
% 3.48/1.58  Subsumption          : 0.07
% 3.48/1.58  Abstraction          : 0.03
% 3.48/1.58  MUC search           : 0.00
% 3.48/1.58  Cooper               : 0.00
% 3.48/1.58  Total                : 0.86
% 3.48/1.58  Index Insertion      : 0.00
% 3.48/1.58  Index Deletion       : 0.00
% 3.48/1.58  Index Matching       : 0.00
% 3.48/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
