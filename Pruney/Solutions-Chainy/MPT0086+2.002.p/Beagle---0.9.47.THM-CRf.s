%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:13 EST 2020

% Result     : Theorem 4.53s
% Output     : CNFRefutation 4.53s
% Verified   : 
% Statistics : Number of formulae       :   53 (  67 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   46 (  66 expanded)
%              Number of equality atoms :   30 (  38 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_69,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_71,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_61,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_63,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_40,plain,(
    ! [A_25,B_26,C_27] : k4_xboole_0(k3_xboole_0(A_25,B_26),C_27) = k3_xboole_0(A_25,k4_xboole_0(B_26,C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_38,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_289,plain,(
    ! [A_65,B_66,C_67] : k4_xboole_0(k4_xboole_0(A_65,B_66),C_67) = k4_xboole_0(A_65,k2_xboole_0(B_66,C_67)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_332,plain,(
    ! [A_23,B_24,C_67] : k4_xboole_0(A_23,k2_xboole_0(k4_xboole_0(A_23,B_24),C_67)) = k4_xboole_0(k3_xboole_0(A_23,B_24),C_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_289])).

tff(c_5305,plain,(
    ! [A_200,B_201,C_202] : k4_xboole_0(A_200,k2_xboole_0(k4_xboole_0(A_200,B_201),C_202)) = k3_xboole_0(A_200,k4_xboole_0(B_201,C_202)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_332])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_42,plain,(
    ! [A_28] : r1_xboole_0(A_28,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_62,plain,(
    ! [B_32,A_33] :
      ( r1_xboole_0(B_32,A_33)
      | ~ r1_xboole_0(A_33,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_65,plain,(
    ! [A_28] : r1_xboole_0(k1_xboole_0,A_28) ),
    inference(resolution,[status(thm)],[c_42,c_62])).

tff(c_112,plain,(
    ! [A_39,B_40] :
      ( k3_xboole_0(A_39,B_40) = k1_xboole_0
      | ~ r1_xboole_0(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_123,plain,(
    ! [A_28] : k3_xboole_0(k1_xboole_0,A_28) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_65,c_112])).

tff(c_457,plain,(
    ! [A_71,B_72,C_73] : k4_xboole_0(k3_xboole_0(A_71,B_72),C_73) = k3_xboole_0(A_71,k4_xboole_0(B_72,C_73)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_509,plain,(
    ! [A_28,C_73] : k3_xboole_0(k1_xboole_0,k4_xboole_0(A_28,C_73)) = k4_xboole_0(k1_xboole_0,C_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_457])).

tff(c_525,plain,(
    ! [C_73] : k4_xboole_0(k1_xboole_0,C_73) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_509])).

tff(c_32,plain,(
    ! [A_18] : k3_xboole_0(A_18,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_34,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_168,plain,(
    ! [A_50,B_51] : k4_xboole_0(A_50,k4_xboole_0(A_50,B_51)) = k3_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_186,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k3_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_168])).

tff(c_189,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_186])).

tff(c_325,plain,(
    ! [A_19,C_67] : k4_xboole_0(A_19,k2_xboole_0(A_19,C_67)) = k4_xboole_0(k1_xboole_0,C_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_289])).

tff(c_1326,plain,(
    ! [A_97,C_98] : k4_xboole_0(A_97,k2_xboole_0(A_97,C_98)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_325])).

tff(c_1404,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1326])).

tff(c_5339,plain,(
    ! [C_202,B_201] : k3_xboole_0(C_202,k4_xboole_0(B_201,C_202)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5305,c_1404])).

tff(c_104,plain,(
    ! [A_37,B_38] :
      ( r1_xboole_0(A_37,B_38)
      | k3_xboole_0(A_37,B_38) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    ! [B_12,A_11] :
      ( r1_xboole_0(B_12,A_11)
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_141,plain,(
    ! [B_42,A_43] :
      ( r1_xboole_0(B_42,A_43)
      | k3_xboole_0(A_43,B_42) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_104,c_26])).

tff(c_44,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_4','#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_152,plain,(
    k3_xboole_0('#skF_5',k4_xboole_0('#skF_4','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_141,c_44])).

tff(c_5514,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5339,c_152])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:30:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.53/1.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.53/1.90  
% 4.53/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.53/1.91  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 4.53/1.91  
% 4.53/1.91  %Foreground sorts:
% 4.53/1.91  
% 4.53/1.91  
% 4.53/1.91  %Background operators:
% 4.53/1.91  
% 4.53/1.91  
% 4.53/1.91  %Foreground operators:
% 4.53/1.91  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.53/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.53/1.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.53/1.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.53/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.53/1.91  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.53/1.91  tff('#skF_5', type, '#skF_5': $i).
% 4.53/1.91  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.53/1.91  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.53/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.53/1.91  tff('#skF_4', type, '#skF_4': $i).
% 4.53/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.53/1.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.53/1.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.53/1.91  
% 4.53/1.92  tff(f_69, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 4.53/1.92  tff(f_67, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.53/1.92  tff(f_65, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.53/1.92  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.53/1.92  tff(f_71, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.53/1.92  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.53/1.92  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.53/1.92  tff(f_61, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 4.53/1.92  tff(f_63, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.53/1.92  tff(f_74, negated_conjecture, ~(![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.53/1.92  tff(c_40, plain, (![A_25, B_26, C_27]: (k4_xboole_0(k3_xboole_0(A_25, B_26), C_27)=k3_xboole_0(A_25, k4_xboole_0(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.53/1.92  tff(c_38, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.53/1.92  tff(c_289, plain, (![A_65, B_66, C_67]: (k4_xboole_0(k4_xboole_0(A_65, B_66), C_67)=k4_xboole_0(A_65, k2_xboole_0(B_66, C_67)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.53/1.92  tff(c_332, plain, (![A_23, B_24, C_67]: (k4_xboole_0(A_23, k2_xboole_0(k4_xboole_0(A_23, B_24), C_67))=k4_xboole_0(k3_xboole_0(A_23, B_24), C_67))), inference(superposition, [status(thm), theory('equality')], [c_38, c_289])).
% 4.53/1.92  tff(c_5305, plain, (![A_200, B_201, C_202]: (k4_xboole_0(A_200, k2_xboole_0(k4_xboole_0(A_200, B_201), C_202))=k3_xboole_0(A_200, k4_xboole_0(B_201, C_202)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_332])).
% 4.53/1.92  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.53/1.92  tff(c_42, plain, (![A_28]: (r1_xboole_0(A_28, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.53/1.92  tff(c_62, plain, (![B_32, A_33]: (r1_xboole_0(B_32, A_33) | ~r1_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.53/1.92  tff(c_65, plain, (![A_28]: (r1_xboole_0(k1_xboole_0, A_28))), inference(resolution, [status(thm)], [c_42, c_62])).
% 4.53/1.92  tff(c_112, plain, (![A_39, B_40]: (k3_xboole_0(A_39, B_40)=k1_xboole_0 | ~r1_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.53/1.92  tff(c_123, plain, (![A_28]: (k3_xboole_0(k1_xboole_0, A_28)=k1_xboole_0)), inference(resolution, [status(thm)], [c_65, c_112])).
% 4.53/1.92  tff(c_457, plain, (![A_71, B_72, C_73]: (k4_xboole_0(k3_xboole_0(A_71, B_72), C_73)=k3_xboole_0(A_71, k4_xboole_0(B_72, C_73)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.53/1.92  tff(c_509, plain, (![A_28, C_73]: (k3_xboole_0(k1_xboole_0, k4_xboole_0(A_28, C_73))=k4_xboole_0(k1_xboole_0, C_73))), inference(superposition, [status(thm), theory('equality')], [c_123, c_457])).
% 4.53/1.92  tff(c_525, plain, (![C_73]: (k4_xboole_0(k1_xboole_0, C_73)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_123, c_509])).
% 4.53/1.92  tff(c_32, plain, (![A_18]: (k3_xboole_0(A_18, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.53/1.92  tff(c_34, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.53/1.92  tff(c_168, plain, (![A_50, B_51]: (k4_xboole_0(A_50, k4_xboole_0(A_50, B_51))=k3_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.53/1.92  tff(c_186, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k3_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_168])).
% 4.53/1.92  tff(c_189, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_186])).
% 4.53/1.92  tff(c_325, plain, (![A_19, C_67]: (k4_xboole_0(A_19, k2_xboole_0(A_19, C_67))=k4_xboole_0(k1_xboole_0, C_67))), inference(superposition, [status(thm), theory('equality')], [c_189, c_289])).
% 4.53/1.92  tff(c_1326, plain, (![A_97, C_98]: (k4_xboole_0(A_97, k2_xboole_0(A_97, C_98))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_525, c_325])).
% 4.53/1.92  tff(c_1404, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1326])).
% 4.53/1.92  tff(c_5339, plain, (![C_202, B_201]: (k3_xboole_0(C_202, k4_xboole_0(B_201, C_202))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5305, c_1404])).
% 4.53/1.92  tff(c_104, plain, (![A_37, B_38]: (r1_xboole_0(A_37, B_38) | k3_xboole_0(A_37, B_38)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.53/1.92  tff(c_26, plain, (![B_12, A_11]: (r1_xboole_0(B_12, A_11) | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.53/1.92  tff(c_141, plain, (![B_42, A_43]: (r1_xboole_0(B_42, A_43) | k3_xboole_0(A_43, B_42)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_104, c_26])).
% 4.53/1.92  tff(c_44, plain, (~r1_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.53/1.92  tff(c_152, plain, (k3_xboole_0('#skF_5', k4_xboole_0('#skF_4', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_141, c_44])).
% 4.53/1.92  tff(c_5514, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5339, c_152])).
% 4.53/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.53/1.92  
% 4.53/1.92  Inference rules
% 4.53/1.92  ----------------------
% 4.53/1.92  #Ref     : 0
% 4.53/1.92  #Sup     : 1349
% 4.53/1.92  #Fact    : 0
% 4.53/1.92  #Define  : 0
% 4.53/1.92  #Split   : 0
% 4.53/1.92  #Chain   : 0
% 4.53/1.92  #Close   : 0
% 4.53/1.92  
% 4.53/1.92  Ordering : KBO
% 4.53/1.92  
% 4.53/1.92  Simplification rules
% 4.53/1.92  ----------------------
% 4.53/1.92  #Subsume      : 289
% 4.53/1.92  #Demod        : 708
% 4.53/1.92  #Tautology    : 601
% 4.53/1.92  #SimpNegUnit  : 24
% 4.53/1.92  #BackRed      : 1
% 4.53/1.92  
% 4.53/1.92  #Partial instantiations: 0
% 4.53/1.92  #Strategies tried      : 1
% 4.53/1.92  
% 4.53/1.92  Timing (in seconds)
% 4.53/1.92  ----------------------
% 4.53/1.92  Preprocessing        : 0.30
% 4.53/1.92  Parsing              : 0.16
% 4.53/1.92  CNF conversion       : 0.02
% 4.53/1.92  Main loop            : 0.83
% 4.53/1.92  Inferencing          : 0.27
% 4.53/1.92  Reduction            : 0.32
% 4.90/1.92  Demodulation         : 0.25
% 4.90/1.92  BG Simplification    : 0.03
% 4.90/1.92  Subsumption          : 0.15
% 4.90/1.92  Abstraction          : 0.04
% 4.90/1.92  MUC search           : 0.00
% 4.90/1.92  Cooper               : 0.00
% 4.90/1.92  Total                : 1.16
% 4.90/1.92  Index Insertion      : 0.00
% 4.90/1.92  Index Deletion       : 0.00
% 4.90/1.92  Index Matching       : 0.00
% 4.90/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
