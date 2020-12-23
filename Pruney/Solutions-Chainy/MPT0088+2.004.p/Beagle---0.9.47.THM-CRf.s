%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:20 EST 2020

% Result     : Theorem 15.06s
% Output     : CNFRefutation 15.06s
% Verified   : 
% Statistics : Number of formulae       :   52 (  82 expanded)
%              Number of leaves         :   20 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   51 (  98 expanded)
%              Number of equality atoms :   30 (  48 expanded)
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

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,k4_xboole_0(B,C))
       => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_47,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_170,plain,(
    ! [A_37,B_38] :
      ( r1_xboole_0(A_37,B_38)
      | k3_xboole_0(A_37,B_38) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_218,plain,(
    ! [B_43,A_44] :
      ( r1_xboole_0(B_43,A_44)
      | k3_xboole_0(A_44,B_43) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_170,c_8])).

tff(c_22,plain,(
    ~ r1_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_229,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_218,c_22])).

tff(c_334,plain,(
    ! [A_49,B_50,C_51] : k4_xboole_0(k4_xboole_0(A_49,B_50),C_51) = k4_xboole_0(A_49,k2_xboole_0(B_50,C_51)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_347,plain,(
    ! [A_49,B_50,C_51] : k4_xboole_0(k4_xboole_0(A_49,B_50),k4_xboole_0(A_49,k2_xboole_0(B_50,C_51))) = k3_xboole_0(k4_xboole_0(A_49,B_50),C_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_16])).

tff(c_10,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_7745,plain,(
    ! [A_183,B_184,C_185] : k4_xboole_0(k4_xboole_0(A_183,B_184),k4_xboole_0(A_183,k2_xboole_0(B_184,C_185))) = k3_xboole_0(k4_xboole_0(A_183,B_184),C_185) ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_16])).

tff(c_7993,plain,(
    ! [A_183,A_7,B_8] : k4_xboole_0(k4_xboole_0(A_183,A_7),k4_xboole_0(A_183,k2_xboole_0(A_7,B_8))) = k3_xboole_0(k4_xboole_0(A_183,A_7),k4_xboole_0(B_8,A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_7745])).

tff(c_54090,plain,(
    ! [A_466,A_467,B_468] : k3_xboole_0(k4_xboole_0(A_466,A_467),k4_xboole_0(B_468,A_467)) = k3_xboole_0(k4_xboole_0(A_466,A_467),B_468) ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_7993])).

tff(c_12,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_34,plain,(
    ! [A_21,B_22] : r1_xboole_0(k4_xboole_0(A_21,B_22),B_22) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_37,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_34])).

tff(c_39,plain,(
    ! [B_24,A_25] :
      ( r1_xboole_0(B_24,A_25)
      | ~ r1_xboole_0(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_46,plain,(
    ! [A_9] : r1_xboole_0(k1_xboole_0,A_9) ),
    inference(resolution,[status(thm)],[c_37,c_39])).

tff(c_100,plain,(
    ! [A_31,B_32] :
      ( k3_xboole_0(A_31,B_32) = k1_xboole_0
      | ~ r1_xboole_0(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_121,plain,(
    ! [A_9] : k3_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_100])).

tff(c_493,plain,(
    ! [A_55,B_56,C_57] : k4_xboole_0(k3_xboole_0(A_55,B_56),C_57) = k3_xboole_0(A_55,k4_xboole_0(B_56,C_57)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_566,plain,(
    ! [A_9,C_57] : k3_xboole_0(k1_xboole_0,k4_xboole_0(A_9,C_57)) = k4_xboole_0(k1_xboole_0,C_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_493])).

tff(c_582,plain,(
    ! [C_57] : k4_xboole_0(k1_xboole_0,C_57) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_566])).

tff(c_24,plain,(
    r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_48,plain,(
    r1_xboole_0(k4_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_39])).

tff(c_119,plain,(
    k3_xboole_0(k4_xboole_0('#skF_2','#skF_3'),'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_100])).

tff(c_557,plain,(
    ! [C_57] : k3_xboole_0(k4_xboole_0('#skF_2','#skF_3'),k4_xboole_0('#skF_1',C_57)) = k4_xboole_0(k1_xboole_0,C_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_493])).

tff(c_1197,plain,(
    ! [C_57] : k3_xboole_0(k4_xboole_0('#skF_2','#skF_3'),k4_xboole_0('#skF_1',C_57)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_582,c_557])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2961,plain,(
    ! [B_113,A_114] :
      ( k3_xboole_0(B_113,A_114) = k1_xboole_0
      | k3_xboole_0(A_114,B_113) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_218,c_4])).

tff(c_2992,plain,(
    ! [C_57] : k3_xboole_0(k4_xboole_0('#skF_1',C_57),k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1197,c_2961])).

tff(c_54135,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_54090,c_2992])).

tff(c_54690,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_229,c_54135])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:30:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.06/7.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.06/7.48  
% 15.06/7.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.06/7.48  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 15.06/7.48  
% 15.06/7.48  %Foreground sorts:
% 15.06/7.48  
% 15.06/7.48  
% 15.06/7.48  %Background operators:
% 15.06/7.48  
% 15.06/7.48  
% 15.06/7.48  %Foreground operators:
% 15.06/7.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.06/7.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.06/7.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.06/7.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 15.06/7.48  tff('#skF_2', type, '#skF_2': $i).
% 15.06/7.48  tff('#skF_3', type, '#skF_3': $i).
% 15.06/7.48  tff('#skF_1', type, '#skF_1': $i).
% 15.06/7.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.06/7.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.06/7.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.06/7.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 15.06/7.48  
% 15.06/7.50  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 15.06/7.50  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 15.06/7.50  tff(f_52, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 15.06/7.50  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 15.06/7.50  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 15.06/7.50  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 15.06/7.50  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 15.06/7.50  tff(f_47, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 15.06/7.50  tff(f_45, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 15.06/7.50  tff(c_170, plain, (![A_37, B_38]: (r1_xboole_0(A_37, B_38) | k3_xboole_0(A_37, B_38)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.06/7.50  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.06/7.50  tff(c_218, plain, (![B_43, A_44]: (r1_xboole_0(B_43, A_44) | k3_xboole_0(A_44, B_43)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_170, c_8])).
% 15.06/7.50  tff(c_22, plain, (~r1_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 15.06/7.50  tff(c_229, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_218, c_22])).
% 15.06/7.50  tff(c_334, plain, (![A_49, B_50, C_51]: (k4_xboole_0(k4_xboole_0(A_49, B_50), C_51)=k4_xboole_0(A_49, k2_xboole_0(B_50, C_51)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.06/7.50  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 15.06/7.50  tff(c_347, plain, (![A_49, B_50, C_51]: (k4_xboole_0(k4_xboole_0(A_49, B_50), k4_xboole_0(A_49, k2_xboole_0(B_50, C_51)))=k3_xboole_0(k4_xboole_0(A_49, B_50), C_51))), inference(superposition, [status(thm), theory('equality')], [c_334, c_16])).
% 15.06/7.50  tff(c_10, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.06/7.50  tff(c_7745, plain, (![A_183, B_184, C_185]: (k4_xboole_0(k4_xboole_0(A_183, B_184), k4_xboole_0(A_183, k2_xboole_0(B_184, C_185)))=k3_xboole_0(k4_xboole_0(A_183, B_184), C_185))), inference(superposition, [status(thm), theory('equality')], [c_334, c_16])).
% 15.06/7.50  tff(c_7993, plain, (![A_183, A_7, B_8]: (k4_xboole_0(k4_xboole_0(A_183, A_7), k4_xboole_0(A_183, k2_xboole_0(A_7, B_8)))=k3_xboole_0(k4_xboole_0(A_183, A_7), k4_xboole_0(B_8, A_7)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_7745])).
% 15.06/7.50  tff(c_54090, plain, (![A_466, A_467, B_468]: (k3_xboole_0(k4_xboole_0(A_466, A_467), k4_xboole_0(B_468, A_467))=k3_xboole_0(k4_xboole_0(A_466, A_467), B_468))), inference(demodulation, [status(thm), theory('equality')], [c_347, c_7993])).
% 15.06/7.50  tff(c_12, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 15.06/7.50  tff(c_34, plain, (![A_21, B_22]: (r1_xboole_0(k4_xboole_0(A_21, B_22), B_22))), inference(cnfTransformation, [status(thm)], [f_47])).
% 15.06/7.50  tff(c_37, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_34])).
% 15.06/7.50  tff(c_39, plain, (![B_24, A_25]: (r1_xboole_0(B_24, A_25) | ~r1_xboole_0(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.06/7.50  tff(c_46, plain, (![A_9]: (r1_xboole_0(k1_xboole_0, A_9))), inference(resolution, [status(thm)], [c_37, c_39])).
% 15.06/7.50  tff(c_100, plain, (![A_31, B_32]: (k3_xboole_0(A_31, B_32)=k1_xboole_0 | ~r1_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.06/7.50  tff(c_121, plain, (![A_9]: (k3_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_100])).
% 15.06/7.50  tff(c_493, plain, (![A_55, B_56, C_57]: (k4_xboole_0(k3_xboole_0(A_55, B_56), C_57)=k3_xboole_0(A_55, k4_xboole_0(B_56, C_57)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.06/7.50  tff(c_566, plain, (![A_9, C_57]: (k3_xboole_0(k1_xboole_0, k4_xboole_0(A_9, C_57))=k4_xboole_0(k1_xboole_0, C_57))), inference(superposition, [status(thm), theory('equality')], [c_121, c_493])).
% 15.06/7.50  tff(c_582, plain, (![C_57]: (k4_xboole_0(k1_xboole_0, C_57)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_121, c_566])).
% 15.06/7.50  tff(c_24, plain, (r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 15.06/7.50  tff(c_48, plain, (r1_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_24, c_39])).
% 15.06/7.50  tff(c_119, plain, (k3_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_100])).
% 15.06/7.50  tff(c_557, plain, (![C_57]: (k3_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), k4_xboole_0('#skF_1', C_57))=k4_xboole_0(k1_xboole_0, C_57))), inference(superposition, [status(thm), theory('equality')], [c_119, c_493])).
% 15.06/7.50  tff(c_1197, plain, (![C_57]: (k3_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), k4_xboole_0('#skF_1', C_57))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_582, c_557])).
% 15.06/7.50  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.06/7.50  tff(c_2961, plain, (![B_113, A_114]: (k3_xboole_0(B_113, A_114)=k1_xboole_0 | k3_xboole_0(A_114, B_113)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_218, c_4])).
% 15.06/7.50  tff(c_2992, plain, (![C_57]: (k3_xboole_0(k4_xboole_0('#skF_1', C_57), k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1197, c_2961])).
% 15.06/7.50  tff(c_54135, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_54090, c_2992])).
% 15.06/7.50  tff(c_54690, plain, $false, inference(negUnitSimplification, [status(thm)], [c_229, c_54135])).
% 15.06/7.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.06/7.50  
% 15.06/7.50  Inference rules
% 15.06/7.50  ----------------------
% 15.06/7.50  #Ref     : 0
% 15.06/7.50  #Sup     : 13781
% 15.06/7.50  #Fact    : 0
% 15.06/7.50  #Define  : 0
% 15.06/7.50  #Split   : 2
% 15.06/7.50  #Chain   : 0
% 15.06/7.50  #Close   : 0
% 15.06/7.50  
% 15.06/7.50  Ordering : KBO
% 15.06/7.50  
% 15.06/7.50  Simplification rules
% 15.06/7.50  ----------------------
% 15.06/7.50  #Subsume      : 1005
% 15.06/7.50  #Demod        : 15200
% 15.06/7.50  #Tautology    : 9252
% 15.06/7.50  #SimpNegUnit  : 63
% 15.06/7.50  #BackRed      : 12
% 15.06/7.50  
% 15.06/7.50  #Partial instantiations: 0
% 15.06/7.50  #Strategies tried      : 1
% 15.06/7.50  
% 15.06/7.50  Timing (in seconds)
% 15.06/7.50  ----------------------
% 15.06/7.50  Preprocessing        : 0.28
% 15.06/7.50  Parsing              : 0.15
% 15.06/7.50  CNF conversion       : 0.02
% 15.06/7.50  Main loop            : 6.46
% 15.06/7.50  Inferencing          : 0.89
% 15.06/7.50  Reduction            : 4.09
% 15.06/7.50  Demodulation         : 3.69
% 15.06/7.50  BG Simplification    : 0.10
% 15.06/7.50  Subsumption          : 1.10
% 15.06/7.50  Abstraction          : 0.17
% 15.06/7.50  MUC search           : 0.00
% 15.06/7.50  Cooper               : 0.00
% 15.06/7.50  Total                : 6.77
% 15.06/7.50  Index Insertion      : 0.00
% 15.06/7.50  Index Deletion       : 0.00
% 15.06/7.50  Index Matching       : 0.00
% 15.06/7.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
