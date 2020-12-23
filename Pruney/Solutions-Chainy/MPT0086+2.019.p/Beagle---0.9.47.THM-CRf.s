%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:15 EST 2020

% Result     : Theorem 3.96s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :   51 (  86 expanded)
%              Number of leaves         :   19 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :   48 (  94 expanded)
%              Number of equality atoms :   37 (  71 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_63,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k4_xboole_0(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_78,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_63])).

tff(c_81,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_78])).

tff(c_158,plain,(
    ! [A_35,B_36,C_37] : k4_xboole_0(k4_xboole_0(A_35,B_36),C_37) = k4_xboole_0(A_35,k2_xboole_0(B_36,C_37)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_192,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k2_xboole_0(B_36,k4_xboole_0(A_35,B_36))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_158])).

tff(c_82,plain,(
    ! [A_30] : k4_xboole_0(A_30,A_30) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_78])).

tff(c_14,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_87,plain,(
    ! [A_30] : k4_xboole_0(A_30,k1_xboole_0) = k3_xboole_0(A_30,A_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_14])).

tff(c_99,plain,(
    ! [A_30] : k3_xboole_0(A_30,A_30) = A_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_87])).

tff(c_38,plain,(
    ! [A_22,B_23] :
      ( r1_xboole_0(A_22,B_23)
      | k3_xboole_0(A_22,B_23) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_51,plain,(
    ! [B_26,A_27] :
      ( r1_xboole_0(B_26,A_27)
      | k3_xboole_0(A_27,B_26) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_6])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_122,plain,(
    ! [B_32,A_33] :
      ( k3_xboole_0(B_32,A_33) = k1_xboole_0
      | k3_xboole_0(A_33,B_32) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_51,c_2])).

tff(c_128,plain,(
    ! [A_5] : k3_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_122])).

tff(c_213,plain,(
    ! [A_38,B_39,C_40] : k4_xboole_0(k3_xboole_0(A_38,B_39),C_40) = k3_xboole_0(A_38,k4_xboole_0(B_39,C_40)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_240,plain,(
    ! [A_5,C_40] : k3_xboole_0(k1_xboole_0,k4_xboole_0(A_5,C_40)) = k4_xboole_0(k1_xboole_0,C_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_213])).

tff(c_264,plain,(
    ! [C_40] : k4_xboole_0(k1_xboole_0,C_40) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_240])).

tff(c_396,plain,(
    ! [A_45,B_46,C_47] : k2_xboole_0(k4_xboole_0(A_45,B_46),k3_xboole_0(A_45,C_47)) = k4_xboole_0(A_45,k4_xboole_0(B_46,C_47)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_435,plain,(
    ! [A_6,C_47] : k4_xboole_0(A_6,k4_xboole_0(k1_xboole_0,C_47)) = k2_xboole_0(A_6,k3_xboole_0(A_6,C_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_396])).

tff(c_526,plain,(
    ! [A_51,C_52] : k2_xboole_0(A_51,k3_xboole_0(A_51,C_52)) = A_51 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_264,c_435])).

tff(c_538,plain,(
    ! [A_30] : k2_xboole_0(A_30,A_30) = A_30 ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_526])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9] : k4_xboole_0(k4_xboole_0(A_7,B_8),C_9) = k4_xboole_0(A_7,k2_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_199,plain,(
    ! [A_35,B_36,B_11] : k4_xboole_0(A_35,k2_xboole_0(B_36,k4_xboole_0(k4_xboole_0(A_35,B_36),B_11))) = k3_xboole_0(k4_xboole_0(A_35,B_36),B_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_158])).

tff(c_4120,plain,(
    ! [A_128,B_129,B_130] : k4_xboole_0(A_128,k2_xboole_0(B_129,k4_xboole_0(A_128,k2_xboole_0(B_129,B_130)))) = k3_xboole_0(k4_xboole_0(A_128,B_129),B_130) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_199])).

tff(c_4251,plain,(
    ! [A_128,A_30] : k4_xboole_0(A_128,k2_xboole_0(A_30,k4_xboole_0(A_128,A_30))) = k3_xboole_0(k4_xboole_0(A_128,A_30),A_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_538,c_4120])).

tff(c_4315,plain,(
    ! [A_128,A_30] : k3_xboole_0(k4_xboole_0(A_128,A_30),A_30) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_4251])).

tff(c_20,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_45,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_20])).

tff(c_4328,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4315,c_45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:50:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.96/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.72  
% 3.96/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.72  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.96/1.72  
% 3.96/1.72  %Foreground sorts:
% 3.96/1.72  
% 3.96/1.72  
% 3.96/1.72  %Background operators:
% 3.96/1.72  
% 3.96/1.72  
% 3.96/1.72  %Foreground operators:
% 3.96/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.96/1.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.96/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.96/1.72  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.96/1.72  tff('#skF_2', type, '#skF_2': $i).
% 3.96/1.72  tff('#skF_1', type, '#skF_1': $i).
% 3.96/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.96/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.96/1.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.96/1.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.96/1.72  
% 3.96/1.73  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.96/1.73  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.96/1.73  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.96/1.73  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.96/1.73  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.96/1.73  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.96/1.73  tff(f_43, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.96/1.73  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 3.96/1.73  tff(f_48, negated_conjecture, ~(![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.96/1.73  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.96/1.73  tff(c_10, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.96/1.73  tff(c_63, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k4_xboole_0(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.96/1.73  tff(c_78, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_63])).
% 3.96/1.73  tff(c_81, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_78])).
% 3.96/1.73  tff(c_158, plain, (![A_35, B_36, C_37]: (k4_xboole_0(k4_xboole_0(A_35, B_36), C_37)=k4_xboole_0(A_35, k2_xboole_0(B_36, C_37)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.96/1.73  tff(c_192, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k2_xboole_0(B_36, k4_xboole_0(A_35, B_36)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_81, c_158])).
% 3.96/1.73  tff(c_82, plain, (![A_30]: (k4_xboole_0(A_30, A_30)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_78])).
% 3.96/1.73  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.96/1.73  tff(c_87, plain, (![A_30]: (k4_xboole_0(A_30, k1_xboole_0)=k3_xboole_0(A_30, A_30))), inference(superposition, [status(thm), theory('equality')], [c_82, c_14])).
% 3.96/1.73  tff(c_99, plain, (![A_30]: (k3_xboole_0(A_30, A_30)=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_87])).
% 3.96/1.73  tff(c_38, plain, (![A_22, B_23]: (r1_xboole_0(A_22, B_23) | k3_xboole_0(A_22, B_23)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.96/1.73  tff(c_6, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.96/1.73  tff(c_51, plain, (![B_26, A_27]: (r1_xboole_0(B_26, A_27) | k3_xboole_0(A_27, B_26)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_6])).
% 3.96/1.73  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.96/1.73  tff(c_122, plain, (![B_32, A_33]: (k3_xboole_0(B_32, A_33)=k1_xboole_0 | k3_xboole_0(A_33, B_32)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_51, c_2])).
% 3.96/1.73  tff(c_128, plain, (![A_5]: (k3_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_122])).
% 3.96/1.73  tff(c_213, plain, (![A_38, B_39, C_40]: (k4_xboole_0(k3_xboole_0(A_38, B_39), C_40)=k3_xboole_0(A_38, k4_xboole_0(B_39, C_40)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.96/1.73  tff(c_240, plain, (![A_5, C_40]: (k3_xboole_0(k1_xboole_0, k4_xboole_0(A_5, C_40))=k4_xboole_0(k1_xboole_0, C_40))), inference(superposition, [status(thm), theory('equality')], [c_128, c_213])).
% 3.96/1.73  tff(c_264, plain, (![C_40]: (k4_xboole_0(k1_xboole_0, C_40)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_128, c_240])).
% 3.96/1.73  tff(c_396, plain, (![A_45, B_46, C_47]: (k2_xboole_0(k4_xboole_0(A_45, B_46), k3_xboole_0(A_45, C_47))=k4_xboole_0(A_45, k4_xboole_0(B_46, C_47)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.96/1.73  tff(c_435, plain, (![A_6, C_47]: (k4_xboole_0(A_6, k4_xboole_0(k1_xboole_0, C_47))=k2_xboole_0(A_6, k3_xboole_0(A_6, C_47)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_396])).
% 3.96/1.73  tff(c_526, plain, (![A_51, C_52]: (k2_xboole_0(A_51, k3_xboole_0(A_51, C_52))=A_51)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_264, c_435])).
% 3.96/1.73  tff(c_538, plain, (![A_30]: (k2_xboole_0(A_30, A_30)=A_30)), inference(superposition, [status(thm), theory('equality')], [c_99, c_526])).
% 3.96/1.73  tff(c_12, plain, (![A_7, B_8, C_9]: (k4_xboole_0(k4_xboole_0(A_7, B_8), C_9)=k4_xboole_0(A_7, k2_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.96/1.73  tff(c_199, plain, (![A_35, B_36, B_11]: (k4_xboole_0(A_35, k2_xboole_0(B_36, k4_xboole_0(k4_xboole_0(A_35, B_36), B_11)))=k3_xboole_0(k4_xboole_0(A_35, B_36), B_11))), inference(superposition, [status(thm), theory('equality')], [c_14, c_158])).
% 3.96/1.73  tff(c_4120, plain, (![A_128, B_129, B_130]: (k4_xboole_0(A_128, k2_xboole_0(B_129, k4_xboole_0(A_128, k2_xboole_0(B_129, B_130))))=k3_xboole_0(k4_xboole_0(A_128, B_129), B_130))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_199])).
% 3.96/1.73  tff(c_4251, plain, (![A_128, A_30]: (k4_xboole_0(A_128, k2_xboole_0(A_30, k4_xboole_0(A_128, A_30)))=k3_xboole_0(k4_xboole_0(A_128, A_30), A_30))), inference(superposition, [status(thm), theory('equality')], [c_538, c_4120])).
% 3.96/1.73  tff(c_4315, plain, (![A_128, A_30]: (k3_xboole_0(k4_xboole_0(A_128, A_30), A_30)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_192, c_4251])).
% 3.96/1.73  tff(c_20, plain, (~r1_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.96/1.73  tff(c_45, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_20])).
% 3.96/1.73  tff(c_4328, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4315, c_45])).
% 3.96/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.73  
% 3.96/1.73  Inference rules
% 3.96/1.73  ----------------------
% 3.96/1.73  #Ref     : 0
% 3.96/1.73  #Sup     : 1039
% 3.96/1.73  #Fact    : 0
% 3.96/1.73  #Define  : 0
% 3.96/1.73  #Split   : 0
% 3.96/1.73  #Chain   : 0
% 3.96/1.73  #Close   : 0
% 3.96/1.73  
% 3.96/1.73  Ordering : KBO
% 3.96/1.73  
% 3.96/1.73  Simplification rules
% 3.96/1.73  ----------------------
% 3.96/1.73  #Subsume      : 4
% 3.96/1.73  #Demod        : 1177
% 3.96/1.73  #Tautology    : 676
% 3.96/1.73  #SimpNegUnit  : 0
% 3.96/1.73  #BackRed      : 6
% 3.96/1.73  
% 3.96/1.73  #Partial instantiations: 0
% 3.96/1.73  #Strategies tried      : 1
% 3.96/1.73  
% 3.96/1.73  Timing (in seconds)
% 3.96/1.73  ----------------------
% 3.96/1.73  Preprocessing        : 0.28
% 3.96/1.73  Parsing              : 0.15
% 3.96/1.73  CNF conversion       : 0.01
% 3.96/1.73  Main loop            : 0.70
% 3.96/1.73  Inferencing          : 0.25
% 3.96/1.73  Reduction            : 0.30
% 3.96/1.73  Demodulation         : 0.24
% 3.96/1.73  BG Simplification    : 0.03
% 3.96/1.73  Subsumption          : 0.08
% 3.96/1.73  Abstraction          : 0.05
% 3.96/1.73  MUC search           : 0.00
% 3.96/1.73  Cooper               : 0.00
% 3.96/1.73  Total                : 1.00
% 3.96/1.73  Index Insertion      : 0.00
% 3.96/1.73  Index Deletion       : 0.00
% 3.96/1.73  Index Matching       : 0.00
% 3.96/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
