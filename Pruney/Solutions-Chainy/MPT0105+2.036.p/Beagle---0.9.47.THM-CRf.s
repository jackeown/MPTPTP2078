%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:52 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   46 (  51 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   39 (  46 expanded)
%              Number of equality atoms :   29 (  32 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_6,plain,(
    ! [A_4,B_5] : k2_xboole_0(A_4,k4_xboole_0(B_5,A_4)) = k2_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_xboole_0(k4_xboole_0(A_10,B_11),B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_55,plain,(
    ! [B_25,A_26] :
      ( r1_xboole_0(B_25,A_26)
      | ~ r1_xboole_0(A_26,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_61,plain,(
    ! [B_11,A_10] : r1_xboole_0(B_11,k4_xboole_0(A_10,B_11)) ),
    inference(resolution,[status(thm)],[c_14,c_55])).

tff(c_80,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = A_32
      | ~ r1_xboole_0(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_97,plain,(
    ! [B_11,A_10] : k4_xboole_0(B_11,k4_xboole_0(A_10,B_11)) = B_11 ),
    inference(resolution,[status(thm)],[c_61,c_80])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_176,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k4_xboole_0(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_222,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_176])).

tff(c_226,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_222])).

tff(c_587,plain,(
    ! [A_61,B_62] : k4_xboole_0(k4_xboole_0(A_61,B_62),B_62) = k4_xboole_0(A_61,B_62) ),
    inference(resolution,[status(thm)],[c_14,c_80])).

tff(c_10,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_611,plain,(
    ! [A_61,B_62] : k4_xboole_0(k4_xboole_0(A_61,B_62),k4_xboole_0(A_61,B_62)) = k3_xboole_0(k4_xboole_0(A_61,B_62),B_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_587,c_10])).

tff(c_709,plain,(
    ! [A_65,B_66] : k3_xboole_0(k4_xboole_0(A_65,B_66),B_66) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_611])).

tff(c_737,plain,(
    ! [B_11,A_10] : k3_xboole_0(B_11,k4_xboole_0(A_10,B_11)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_709])).

tff(c_381,plain,(
    ! [A_49,B_50,C_51] : k5_xboole_0(k5_xboole_0(A_49,B_50),C_51) = k5_xboole_0(A_49,k5_xboole_0(B_50,C_51)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    ! [A_17,B_18] : k5_xboole_0(k5_xboole_0(A_17,B_18),k3_xboole_0(A_17,B_18)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1292,plain,(
    ! [A_81,B_82] : k5_xboole_0(A_81,k5_xboole_0(B_82,k3_xboole_0(A_81,B_82))) = k2_xboole_0(A_81,B_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_381,c_22])).

tff(c_1329,plain,(
    ! [B_11,A_10] : k5_xboole_0(B_11,k5_xboole_0(k4_xboole_0(A_10,B_11),k1_xboole_0)) = k2_xboole_0(B_11,k4_xboole_0(A_10,B_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_737,c_1292])).

tff(c_1358,plain,(
    ! [B_11,A_10] : k5_xboole_0(B_11,k4_xboole_0(A_10,B_11)) = k2_xboole_0(B_11,A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12,c_1329])).

tff(c_24,plain,(
    k5_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_1')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1365,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1358,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:51:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.38  
% 2.72/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.38  %$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.72/1.38  
% 2.72/1.38  %Foreground sorts:
% 2.72/1.38  
% 2.72/1.38  
% 2.72/1.38  %Background operators:
% 2.72/1.38  
% 2.72/1.38  
% 2.72/1.38  %Foreground operators:
% 2.72/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.72/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.72/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.72/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.72/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.72/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.72/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.72/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.72/1.38  
% 2.72/1.39  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.72/1.39  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.72/1.39  tff(f_41, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.72/1.39  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.72/1.39  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.72/1.39  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.72/1.39  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.72/1.39  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.72/1.39  tff(f_47, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 2.72/1.39  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 2.72/1.39  tff(f_52, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.72/1.39  tff(c_6, plain, (![A_4, B_5]: (k2_xboole_0(A_4, k4_xboole_0(B_5, A_4))=k2_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.72/1.39  tff(c_12, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.72/1.39  tff(c_14, plain, (![A_10, B_11]: (r1_xboole_0(k4_xboole_0(A_10, B_11), B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.72/1.39  tff(c_55, plain, (![B_25, A_26]: (r1_xboole_0(B_25, A_26) | ~r1_xboole_0(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.72/1.39  tff(c_61, plain, (![B_11, A_10]: (r1_xboole_0(B_11, k4_xboole_0(A_10, B_11)))), inference(resolution, [status(thm)], [c_14, c_55])).
% 2.72/1.39  tff(c_80, plain, (![A_32, B_33]: (k4_xboole_0(A_32, B_33)=A_32 | ~r1_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.72/1.39  tff(c_97, plain, (![B_11, A_10]: (k4_xboole_0(B_11, k4_xboole_0(A_10, B_11))=B_11)), inference(resolution, [status(thm)], [c_61, c_80])).
% 2.72/1.39  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.72/1.39  tff(c_8, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.72/1.39  tff(c_176, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k4_xboole_0(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.72/1.39  tff(c_222, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_176])).
% 2.72/1.39  tff(c_226, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_222])).
% 2.72/1.39  tff(c_587, plain, (![A_61, B_62]: (k4_xboole_0(k4_xboole_0(A_61, B_62), B_62)=k4_xboole_0(A_61, B_62))), inference(resolution, [status(thm)], [c_14, c_80])).
% 2.72/1.39  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.72/1.39  tff(c_611, plain, (![A_61, B_62]: (k4_xboole_0(k4_xboole_0(A_61, B_62), k4_xboole_0(A_61, B_62))=k3_xboole_0(k4_xboole_0(A_61, B_62), B_62))), inference(superposition, [status(thm), theory('equality')], [c_587, c_10])).
% 2.72/1.39  tff(c_709, plain, (![A_65, B_66]: (k3_xboole_0(k4_xboole_0(A_65, B_66), B_66)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_226, c_611])).
% 2.72/1.39  tff(c_737, plain, (![B_11, A_10]: (k3_xboole_0(B_11, k4_xboole_0(A_10, B_11))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_97, c_709])).
% 2.72/1.39  tff(c_381, plain, (![A_49, B_50, C_51]: (k5_xboole_0(k5_xboole_0(A_49, B_50), C_51)=k5_xboole_0(A_49, k5_xboole_0(B_50, C_51)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.72/1.39  tff(c_22, plain, (![A_17, B_18]: (k5_xboole_0(k5_xboole_0(A_17, B_18), k3_xboole_0(A_17, B_18))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.72/1.39  tff(c_1292, plain, (![A_81, B_82]: (k5_xboole_0(A_81, k5_xboole_0(B_82, k3_xboole_0(A_81, B_82)))=k2_xboole_0(A_81, B_82))), inference(superposition, [status(thm), theory('equality')], [c_381, c_22])).
% 2.72/1.39  tff(c_1329, plain, (![B_11, A_10]: (k5_xboole_0(B_11, k5_xboole_0(k4_xboole_0(A_10, B_11), k1_xboole_0))=k2_xboole_0(B_11, k4_xboole_0(A_10, B_11)))), inference(superposition, [status(thm), theory('equality')], [c_737, c_1292])).
% 2.72/1.39  tff(c_1358, plain, (![B_11, A_10]: (k5_xboole_0(B_11, k4_xboole_0(A_10, B_11))=k2_xboole_0(B_11, A_10))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_12, c_1329])).
% 2.72/1.39  tff(c_24, plain, (k5_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_1'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.72/1.39  tff(c_1365, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1358, c_24])).
% 2.72/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.39  
% 2.72/1.39  Inference rules
% 2.72/1.39  ----------------------
% 2.72/1.39  #Ref     : 0
% 2.72/1.39  #Sup     : 326
% 2.72/1.39  #Fact    : 0
% 2.72/1.39  #Define  : 0
% 2.72/1.39  #Split   : 0
% 2.72/1.39  #Chain   : 0
% 2.72/1.39  #Close   : 0
% 2.72/1.39  
% 2.72/1.39  Ordering : KBO
% 2.72/1.39  
% 2.72/1.39  Simplification rules
% 2.72/1.39  ----------------------
% 2.72/1.39  #Subsume      : 1
% 2.72/1.39  #Demod        : 284
% 2.72/1.39  #Tautology    : 234
% 2.72/1.39  #SimpNegUnit  : 0
% 2.72/1.39  #BackRed      : 5
% 2.72/1.39  
% 2.72/1.39  #Partial instantiations: 0
% 2.72/1.39  #Strategies tried      : 1
% 2.72/1.39  
% 2.72/1.39  Timing (in seconds)
% 2.72/1.39  ----------------------
% 2.72/1.40  Preprocessing        : 0.26
% 2.72/1.40  Parsing              : 0.15
% 2.72/1.40  CNF conversion       : 0.02
% 2.72/1.40  Main loop            : 0.37
% 2.72/1.40  Inferencing          : 0.14
% 2.72/1.40  Reduction            : 0.14
% 2.72/1.40  Demodulation         : 0.11
% 2.72/1.40  BG Simplification    : 0.02
% 2.72/1.40  Subsumption          : 0.05
% 2.72/1.40  Abstraction          : 0.02
% 2.72/1.40  MUC search           : 0.00
% 2.72/1.40  Cooper               : 0.00
% 2.72/1.40  Total                : 0.66
% 2.72/1.40  Index Insertion      : 0.00
% 2.72/1.40  Index Deletion       : 0.00
% 2.72/1.40  Index Matching       : 0.00
% 2.72/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
