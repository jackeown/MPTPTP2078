%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:55 EST 2020

% Result     : Theorem 6.41s
% Output     : CNFRefutation 6.41s
% Verified   : 
% Statistics : Number of formulae       :   47 (  62 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   37 (  52 expanded)
%              Number of equality atoms :   36 (  51 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k3_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_57,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_20,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_232,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k4_xboole_0(A_44,B_45)) = k3_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [A_25] : k4_xboole_0(k1_xboole_0,A_25) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_266,plain,(
    ! [B_46] : k3_xboole_0(k1_xboole_0,B_46) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_24])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_274,plain,(
    ! [B_46] : k3_xboole_0(B_46,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_2])).

tff(c_1622,plain,(
    ! [A_90,B_91,C_92] : k2_xboole_0(k4_xboole_0(A_90,B_91),k4_xboole_0(A_90,C_92)) = k4_xboole_0(A_90,k3_xboole_0(B_91,C_92)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1711,plain,(
    ! [A_10,B_91] : k4_xboole_0(A_10,k3_xboole_0(B_91,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(A_10,B_91),A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1622])).

tff(c_1740,plain,(
    ! [A_10,B_91] : k2_xboole_0(k4_xboole_0(A_10,B_91),A_10) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_274,c_1711])).

tff(c_32,plain,(
    ! [A_31,B_32] : k5_xboole_0(A_31,k4_xboole_0(B_32,A_31)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_87,plain,(
    ! [B_37,A_38] : k5_xboole_0(B_37,A_38) = k5_xboole_0(A_38,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_26,plain,(
    ! [A_26] : k5_xboole_0(A_26,k1_xboole_0) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_103,plain,(
    ! [A_38] : k5_xboole_0(k1_xboole_0,A_38) = A_38 ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_26])).

tff(c_30,plain,(
    ! [A_30] : k5_xboole_0(A_30,A_30) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_991,plain,(
    ! [A_74,B_75,C_76] : k5_xboole_0(k5_xboole_0(A_74,B_75),C_76) = k5_xboole_0(A_74,k5_xboole_0(B_75,C_76)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1055,plain,(
    ! [A_30,C_76] : k5_xboole_0(A_30,k5_xboole_0(A_30,C_76)) = k5_xboole_0(k1_xboole_0,C_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_991])).

tff(c_1069,plain,(
    ! [A_77,C_78] : k5_xboole_0(A_77,k5_xboole_0(A_77,C_78)) = C_78 ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_1055])).

tff(c_3394,plain,(
    ! [A_127,B_128] : k5_xboole_0(A_127,k2_xboole_0(A_127,B_128)) = k4_xboole_0(B_128,A_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1069])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1112,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1069])).

tff(c_4276,plain,(
    ! [A_141,B_142] : k5_xboole_0(k2_xboole_0(A_141,B_142),k4_xboole_0(B_142,A_141)) = A_141 ),
    inference(superposition,[status(thm),theory(equality)],[c_3394,c_1112])).

tff(c_4336,plain,(
    ! [A_10,B_91] : k5_xboole_0(A_10,k4_xboole_0(A_10,k4_xboole_0(A_10,B_91))) = k4_xboole_0(A_10,B_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_1740,c_4276])).

tff(c_4401,plain,(
    ! [A_10,B_91] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_91)) = k4_xboole_0(A_10,B_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_4336])).

tff(c_34,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_9815,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4401,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:15:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.41/2.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.41/2.38  
% 6.41/2.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.41/2.38  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 6.41/2.38  
% 6.41/2.38  %Foreground sorts:
% 6.41/2.38  
% 6.41/2.38  
% 6.41/2.38  %Background operators:
% 6.41/2.38  
% 6.41/2.38  
% 6.41/2.38  %Foreground operators:
% 6.41/2.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.41/2.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.41/2.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.41/2.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.41/2.38  tff('#skF_2', type, '#skF_2': $i).
% 6.41/2.38  tff('#skF_1', type, '#skF_1': $i).
% 6.41/2.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.41/2.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.41/2.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.41/2.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.41/2.38  
% 6.41/2.39  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.41/2.39  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 6.41/2.39  tff(f_51, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 6.41/2.39  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.41/2.39  tff(f_31, axiom, (![A, B, C]: (k4_xboole_0(A, k3_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l36_xboole_1)).
% 6.41/2.39  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 6.41/2.39  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 6.41/2.39  tff(f_53, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 6.41/2.39  tff(f_57, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.41/2.39  tff(f_55, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.41/2.39  tff(f_62, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.41/2.39  tff(c_20, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.41/2.39  tff(c_10, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.41/2.39  tff(c_232, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k4_xboole_0(A_44, B_45))=k3_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.41/2.39  tff(c_24, plain, (![A_25]: (k4_xboole_0(k1_xboole_0, A_25)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.41/2.39  tff(c_266, plain, (![B_46]: (k3_xboole_0(k1_xboole_0, B_46)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_232, c_24])).
% 6.41/2.39  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.41/2.39  tff(c_274, plain, (![B_46]: (k3_xboole_0(B_46, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_266, c_2])).
% 6.41/2.39  tff(c_1622, plain, (![A_90, B_91, C_92]: (k2_xboole_0(k4_xboole_0(A_90, B_91), k4_xboole_0(A_90, C_92))=k4_xboole_0(A_90, k3_xboole_0(B_91, C_92)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.41/2.39  tff(c_1711, plain, (![A_10, B_91]: (k4_xboole_0(A_10, k3_xboole_0(B_91, k1_xboole_0))=k2_xboole_0(k4_xboole_0(A_10, B_91), A_10))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1622])).
% 6.41/2.39  tff(c_1740, plain, (![A_10, B_91]: (k2_xboole_0(k4_xboole_0(A_10, B_91), A_10)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_274, c_1711])).
% 6.41/2.39  tff(c_32, plain, (![A_31, B_32]: (k5_xboole_0(A_31, k4_xboole_0(B_32, A_31))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.41/2.39  tff(c_87, plain, (![B_37, A_38]: (k5_xboole_0(B_37, A_38)=k5_xboole_0(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.41/2.39  tff(c_26, plain, (![A_26]: (k5_xboole_0(A_26, k1_xboole_0)=A_26)), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.41/2.39  tff(c_103, plain, (![A_38]: (k5_xboole_0(k1_xboole_0, A_38)=A_38)), inference(superposition, [status(thm), theory('equality')], [c_87, c_26])).
% 6.41/2.39  tff(c_30, plain, (![A_30]: (k5_xboole_0(A_30, A_30)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.41/2.39  tff(c_991, plain, (![A_74, B_75, C_76]: (k5_xboole_0(k5_xboole_0(A_74, B_75), C_76)=k5_xboole_0(A_74, k5_xboole_0(B_75, C_76)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.41/2.39  tff(c_1055, plain, (![A_30, C_76]: (k5_xboole_0(A_30, k5_xboole_0(A_30, C_76))=k5_xboole_0(k1_xboole_0, C_76))), inference(superposition, [status(thm), theory('equality')], [c_30, c_991])).
% 6.41/2.39  tff(c_1069, plain, (![A_77, C_78]: (k5_xboole_0(A_77, k5_xboole_0(A_77, C_78))=C_78)), inference(demodulation, [status(thm), theory('equality')], [c_103, c_1055])).
% 6.41/2.39  tff(c_3394, plain, (![A_127, B_128]: (k5_xboole_0(A_127, k2_xboole_0(A_127, B_128))=k4_xboole_0(B_128, A_127))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1069])).
% 6.41/2.39  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.41/2.39  tff(c_1112, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1069])).
% 6.41/2.39  tff(c_4276, plain, (![A_141, B_142]: (k5_xboole_0(k2_xboole_0(A_141, B_142), k4_xboole_0(B_142, A_141))=A_141)), inference(superposition, [status(thm), theory('equality')], [c_3394, c_1112])).
% 6.41/2.39  tff(c_4336, plain, (![A_10, B_91]: (k5_xboole_0(A_10, k4_xboole_0(A_10, k4_xboole_0(A_10, B_91)))=k4_xboole_0(A_10, B_91))), inference(superposition, [status(thm), theory('equality')], [c_1740, c_4276])).
% 6.41/2.39  tff(c_4401, plain, (![A_10, B_91]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_91))=k4_xboole_0(A_10, B_91))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_4336])).
% 6.41/2.39  tff(c_34, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.41/2.39  tff(c_9815, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4401, c_34])).
% 6.41/2.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.41/2.39  
% 6.41/2.39  Inference rules
% 6.41/2.39  ----------------------
% 6.41/2.39  #Ref     : 1
% 6.41/2.39  #Sup     : 2438
% 6.41/2.39  #Fact    : 0
% 6.41/2.39  #Define  : 0
% 6.41/2.39  #Split   : 0
% 6.41/2.39  #Chain   : 0
% 6.41/2.39  #Close   : 0
% 6.41/2.39  
% 6.41/2.39  Ordering : KBO
% 6.41/2.39  
% 6.41/2.39  Simplification rules
% 6.41/2.39  ----------------------
% 6.41/2.39  #Subsume      : 13
% 6.41/2.39  #Demod        : 2398
% 6.41/2.39  #Tautology    : 1685
% 6.41/2.39  #SimpNegUnit  : 0
% 6.41/2.39  #BackRed      : 1
% 6.41/2.39  
% 6.41/2.39  #Partial instantiations: 0
% 6.41/2.39  #Strategies tried      : 1
% 6.41/2.39  
% 6.41/2.39  Timing (in seconds)
% 6.41/2.39  ----------------------
% 6.41/2.40  Preprocessing        : 0.31
% 6.41/2.40  Parsing              : 0.16
% 6.41/2.40  CNF conversion       : 0.02
% 6.41/2.40  Main loop            : 1.33
% 6.41/2.40  Inferencing          : 0.37
% 6.41/2.40  Reduction            : 0.66
% 6.41/2.40  Demodulation         : 0.56
% 6.41/2.40  BG Simplification    : 0.04
% 6.41/2.40  Subsumption          : 0.17
% 6.41/2.40  Abstraction          : 0.07
% 6.41/2.40  MUC search           : 0.00
% 6.41/2.40  Cooper               : 0.00
% 6.41/2.40  Total                : 1.66
% 6.41/2.40  Index Insertion      : 0.00
% 6.41/2.40  Index Deletion       : 0.00
% 6.41/2.40  Index Matching       : 0.00
% 6.41/2.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
