%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:15 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   48 (  57 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   45 (  56 expanded)
%              Number of equality atoms :   29 (  37 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_43,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_47,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_468,plain,(
    ! [A_48,B_49,C_50] : k4_xboole_0(k3_xboole_0(A_48,B_49),C_50) = k3_xboole_0(A_48,k4_xboole_0(B_49,C_50)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [A_15,B_16] : k2_xboole_0(k3_xboole_0(A_15,B_16),k4_xboole_0(A_15,B_16)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [A_17] : r1_xboole_0(A_17,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_40,plain,(
    ! [B_21,A_22] :
      ( r1_xboole_0(B_21,A_22)
      | ~ r1_xboole_0(A_22,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_43,plain,(
    ! [A_17] : r1_xboole_0(k1_xboole_0,A_17) ),
    inference(resolution,[status(thm)],[c_20,c_40])).

tff(c_57,plain,(
    ! [A_26,B_27] :
      ( k3_xboole_0(A_26,B_27) = k1_xboole_0
      | ~ r1_xboole_0(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_98,plain,(
    ! [A_31] : k3_xboole_0(k1_xboole_0,A_31) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_43,c_57])).

tff(c_116,plain,(
    ! [A_32] : k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,A_32)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_18])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_71,plain,(
    ! [A_28,B_29] : k2_xboole_0(k3_xboole_0(A_28,B_29),k4_xboole_0(A_28,B_29)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_80,plain,(
    ! [A_6] : k2_xboole_0(k3_xboole_0(A_6,k1_xboole_0),A_6) = A_6 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_71])).

tff(c_86,plain,(
    ! [A_6] : k2_xboole_0(k1_xboole_0,A_6) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_80])).

tff(c_121,plain,(
    ! [A_32] : k4_xboole_0(k1_xboole_0,A_32) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_86])).

tff(c_157,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k4_xboole_0(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_186,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_157])).

tff(c_192,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_186])).

tff(c_277,plain,(
    ! [A_39,B_40,C_41] : k4_xboole_0(k4_xboole_0(A_39,B_40),C_41) = k4_xboole_0(A_39,k2_xboole_0(B_40,C_41)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_310,plain,(
    ! [A_6,C_41] : k4_xboole_0(A_6,k2_xboole_0(A_6,C_41)) = k4_xboole_0(k1_xboole_0,C_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_277])).

tff(c_345,plain,(
    ! [A_42,C_43] : k4_xboole_0(A_42,k2_xboole_0(A_42,C_43)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_310])).

tff(c_381,plain,(
    ! [A_15,B_16] : k4_xboole_0(k3_xboole_0(A_15,B_16),A_15) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_345])).

tff(c_475,plain,(
    ! [C_50,B_49] : k3_xboole_0(C_50,k4_xboole_0(B_49,C_50)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_468,c_381])).

tff(c_44,plain,(
    ! [A_23,B_24] :
      ( r1_xboole_0(A_23,B_24)
      | k3_xboole_0(A_23,B_24) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_600,plain,(
    ! [B_53,A_54] :
      ( r1_xboole_0(B_53,A_54)
      | k3_xboole_0(A_54,B_53) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_44,c_6])).

tff(c_22,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_608,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_600,c_22])).

tff(c_614,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_475,c_608])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:41:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.27  
% 2.10/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.27  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.10/1.27  
% 2.10/1.27  %Foreground sorts:
% 2.10/1.27  
% 2.10/1.27  
% 2.10/1.27  %Background operators:
% 2.10/1.27  
% 2.10/1.27  
% 2.10/1.27  %Foreground operators:
% 2.10/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.10/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.10/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.10/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.10/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.10/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.10/1.27  
% 2.10/1.28  tff(f_43, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.10/1.28  tff(f_45, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.10/1.28  tff(f_47, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.10/1.28  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.10/1.28  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.10/1.28  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.10/1.28  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.10/1.28  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.10/1.28  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.10/1.28  tff(f_50, negated_conjecture, ~(![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.10/1.28  tff(c_468, plain, (![A_48, B_49, C_50]: (k4_xboole_0(k3_xboole_0(A_48, B_49), C_50)=k3_xboole_0(A_48, k4_xboole_0(B_49, C_50)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.10/1.28  tff(c_18, plain, (![A_15, B_16]: (k2_xboole_0(k3_xboole_0(A_15, B_16), k4_xboole_0(A_15, B_16))=A_15)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.10/1.28  tff(c_20, plain, (![A_17]: (r1_xboole_0(A_17, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.10/1.28  tff(c_40, plain, (![B_21, A_22]: (r1_xboole_0(B_21, A_22) | ~r1_xboole_0(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.10/1.28  tff(c_43, plain, (![A_17]: (r1_xboole_0(k1_xboole_0, A_17))), inference(resolution, [status(thm)], [c_20, c_40])).
% 2.10/1.28  tff(c_57, plain, (![A_26, B_27]: (k3_xboole_0(A_26, B_27)=k1_xboole_0 | ~r1_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.10/1.28  tff(c_98, plain, (![A_31]: (k3_xboole_0(k1_xboole_0, A_31)=k1_xboole_0)), inference(resolution, [status(thm)], [c_43, c_57])).
% 2.10/1.28  tff(c_116, plain, (![A_32]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(k1_xboole_0, A_32))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_98, c_18])).
% 2.10/1.28  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.10/1.28  tff(c_10, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.10/1.28  tff(c_71, plain, (![A_28, B_29]: (k2_xboole_0(k3_xboole_0(A_28, B_29), k4_xboole_0(A_28, B_29))=A_28)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.10/1.28  tff(c_80, plain, (![A_6]: (k2_xboole_0(k3_xboole_0(A_6, k1_xboole_0), A_6)=A_6)), inference(superposition, [status(thm), theory('equality')], [c_10, c_71])).
% 2.10/1.28  tff(c_86, plain, (![A_6]: (k2_xboole_0(k1_xboole_0, A_6)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_80])).
% 2.10/1.28  tff(c_121, plain, (![A_32]: (k4_xboole_0(k1_xboole_0, A_32)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_116, c_86])).
% 2.10/1.28  tff(c_157, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k4_xboole_0(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.10/1.28  tff(c_186, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_157])).
% 2.10/1.28  tff(c_192, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_186])).
% 2.10/1.28  tff(c_277, plain, (![A_39, B_40, C_41]: (k4_xboole_0(k4_xboole_0(A_39, B_40), C_41)=k4_xboole_0(A_39, k2_xboole_0(B_40, C_41)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.10/1.28  tff(c_310, plain, (![A_6, C_41]: (k4_xboole_0(A_6, k2_xboole_0(A_6, C_41))=k4_xboole_0(k1_xboole_0, C_41))), inference(superposition, [status(thm), theory('equality')], [c_192, c_277])).
% 2.10/1.28  tff(c_345, plain, (![A_42, C_43]: (k4_xboole_0(A_42, k2_xboole_0(A_42, C_43))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_121, c_310])).
% 2.10/1.28  tff(c_381, plain, (![A_15, B_16]: (k4_xboole_0(k3_xboole_0(A_15, B_16), A_15)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_345])).
% 2.10/1.28  tff(c_475, plain, (![C_50, B_49]: (k3_xboole_0(C_50, k4_xboole_0(B_49, C_50))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_468, c_381])).
% 2.10/1.28  tff(c_44, plain, (![A_23, B_24]: (r1_xboole_0(A_23, B_24) | k3_xboole_0(A_23, B_24)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.10/1.28  tff(c_6, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.10/1.28  tff(c_600, plain, (![B_53, A_54]: (r1_xboole_0(B_53, A_54) | k3_xboole_0(A_54, B_53)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_6])).
% 2.10/1.28  tff(c_22, plain, (~r1_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.10/1.28  tff(c_608, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_600, c_22])).
% 2.10/1.28  tff(c_614, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_475, c_608])).
% 2.10/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.28  
% 2.10/1.28  Inference rules
% 2.10/1.28  ----------------------
% 2.10/1.28  #Ref     : 0
% 2.10/1.28  #Sup     : 144
% 2.10/1.28  #Fact    : 0
% 2.10/1.28  #Define  : 0
% 2.10/1.28  #Split   : 0
% 2.10/1.28  #Chain   : 0
% 2.10/1.28  #Close   : 0
% 2.10/1.28  
% 2.10/1.28  Ordering : KBO
% 2.10/1.28  
% 2.10/1.28  Simplification rules
% 2.10/1.28  ----------------------
% 2.10/1.28  #Subsume      : 1
% 2.10/1.28  #Demod        : 70
% 2.10/1.28  #Tautology    : 93
% 2.10/1.28  #SimpNegUnit  : 0
% 2.10/1.28  #BackRed      : 1
% 2.10/1.28  
% 2.10/1.28  #Partial instantiations: 0
% 2.10/1.28  #Strategies tried      : 1
% 2.10/1.28  
% 2.10/1.28  Timing (in seconds)
% 2.10/1.28  ----------------------
% 2.10/1.28  Preprocessing        : 0.28
% 2.10/1.28  Parsing              : 0.15
% 2.10/1.28  CNF conversion       : 0.02
% 2.10/1.28  Main loop            : 0.24
% 2.10/1.28  Inferencing          : 0.09
% 2.10/1.28  Reduction            : 0.08
% 2.10/1.28  Demodulation         : 0.07
% 2.10/1.28  BG Simplification    : 0.01
% 2.10/1.28  Subsumption          : 0.03
% 2.10/1.29  Abstraction          : 0.02
% 2.10/1.29  MUC search           : 0.00
% 2.10/1.29  Cooper               : 0.00
% 2.10/1.29  Total                : 0.55
% 2.10/1.29  Index Insertion      : 0.00
% 2.10/1.29  Index Deletion       : 0.00
% 2.10/1.29  Index Matching       : 0.00
% 2.10/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
