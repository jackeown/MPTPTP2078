%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:22 EST 2020

% Result     : Theorem 4.51s
% Output     : CNFRefutation 4.51s
% Verified   : 
% Statistics : Number of formulae       :   47 (  55 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :   42 (  52 expanded)
%              Number of equality atoms :   30 (  37 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,k4_xboole_0(B,C))
       => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_47,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

tff(c_48,plain,(
    ! [A_24,B_25] :
      ( r1_xboole_0(A_24,B_25)
      | k3_xboole_0(A_24,B_25) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ~ r1_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_52,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_24])).

tff(c_380,plain,(
    ! [A_47,B_48,C_49] : k4_xboole_0(k3_xboole_0(A_47,B_48),C_49) = k3_xboole_0(A_47,k4_xboole_0(B_48,C_49)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_171,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k4_xboole_0(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_53,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(A_26,B_27) = k1_xboole_0
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_61,plain,(
    ! [A_6,B_7] : k4_xboole_0(k4_xboole_0(A_6,B_7),A_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_53])).

tff(c_180,plain,(
    ! [A_37,B_38] : k4_xboole_0(k3_xboole_0(A_37,B_38),A_37) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_61])).

tff(c_391,plain,(
    ! [C_49,B_48] : k3_xboole_0(C_49,k4_xboole_0(B_48,C_49)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_380,c_180])).

tff(c_16,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_162,plain,(
    ! [A_35,B_36] :
      ( k3_xboole_0(A_35,B_36) = k1_xboole_0
      | ~ r1_xboole_0(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_170,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_162])).

tff(c_937,plain,(
    ! [A_61,B_62,C_63] : k4_xboole_0(k3_xboole_0(A_61,B_62),k3_xboole_0(A_61,C_63)) = k3_xboole_0(A_61,k4_xboole_0(B_62,C_63)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1017,plain,(
    ! [B_62] : k3_xboole_0('#skF_1',k4_xboole_0(B_62,k4_xboole_0('#skF_2','#skF_3'))) = k4_xboole_0(k3_xboole_0('#skF_1',B_62),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_937])).

tff(c_1286,plain,(
    ! [B_68] : k3_xboole_0('#skF_1',k4_xboole_0(B_68,k4_xboole_0('#skF_2','#skF_3'))) = k3_xboole_0('#skF_1',B_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1017])).

tff(c_1346,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1286])).

tff(c_1622,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1346,c_16])).

tff(c_1637,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1622])).

tff(c_20,plain,(
    ! [A_13,B_14,C_15] : k4_xboole_0(k3_xboole_0(A_13,B_14),C_15) = k3_xboole_0(A_13,k4_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6376,plain,(
    ! [A_125,B_126,C_127] : k3_xboole_0(A_125,k4_xboole_0(B_126,k3_xboole_0(A_125,C_127))) = k3_xboole_0(A_125,k4_xboole_0(B_126,C_127)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_937])).

tff(c_6561,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1637,c_6376])).

tff(c_6706,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_6561])).

tff(c_6708,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_6706])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:25:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.51/1.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.51/1.89  
% 4.51/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.51/1.89  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.51/1.89  
% 4.51/1.89  %Foreground sorts:
% 4.51/1.89  
% 4.51/1.89  
% 4.51/1.89  %Background operators:
% 4.51/1.89  
% 4.51/1.89  
% 4.51/1.89  %Foreground operators:
% 4.51/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.51/1.89  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.51/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.51/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.51/1.89  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.51/1.89  tff('#skF_2', type, '#skF_2': $i).
% 4.51/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.51/1.89  tff('#skF_1', type, '#skF_1': $i).
% 4.51/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.51/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.51/1.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.51/1.89  
% 4.51/1.90  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.51/1.90  tff(f_52, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 4.51/1.90  tff(f_45, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 4.51/1.90  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.51/1.90  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.51/1.90  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.51/1.90  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.51/1.90  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.51/1.90  tff(f_47, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_xboole_1)).
% 4.51/1.90  tff(c_48, plain, (![A_24, B_25]: (r1_xboole_0(A_24, B_25) | k3_xboole_0(A_24, B_25)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.51/1.90  tff(c_24, plain, (~r1_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.51/1.90  tff(c_52, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_24])).
% 4.51/1.90  tff(c_380, plain, (![A_47, B_48, C_49]: (k4_xboole_0(k3_xboole_0(A_47, B_48), C_49)=k3_xboole_0(A_47, k4_xboole_0(B_48, C_49)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.51/1.90  tff(c_171, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k4_xboole_0(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.51/1.90  tff(c_12, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.51/1.90  tff(c_53, plain, (![A_26, B_27]: (k4_xboole_0(A_26, B_27)=k1_xboole_0 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.51/1.90  tff(c_61, plain, (![A_6, B_7]: (k4_xboole_0(k4_xboole_0(A_6, B_7), A_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_53])).
% 4.51/1.90  tff(c_180, plain, (![A_37, B_38]: (k4_xboole_0(k3_xboole_0(A_37, B_38), A_37)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_171, c_61])).
% 4.51/1.90  tff(c_391, plain, (![C_49, B_48]: (k3_xboole_0(C_49, k4_xboole_0(B_48, C_49))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_380, c_180])).
% 4.51/1.90  tff(c_16, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.51/1.90  tff(c_18, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.51/1.90  tff(c_14, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.51/1.90  tff(c_26, plain, (r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.51/1.90  tff(c_162, plain, (![A_35, B_36]: (k3_xboole_0(A_35, B_36)=k1_xboole_0 | ~r1_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.51/1.90  tff(c_170, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_162])).
% 4.51/1.90  tff(c_937, plain, (![A_61, B_62, C_63]: (k4_xboole_0(k3_xboole_0(A_61, B_62), k3_xboole_0(A_61, C_63))=k3_xboole_0(A_61, k4_xboole_0(B_62, C_63)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.51/1.90  tff(c_1017, plain, (![B_62]: (k3_xboole_0('#skF_1', k4_xboole_0(B_62, k4_xboole_0('#skF_2', '#skF_3')))=k4_xboole_0(k3_xboole_0('#skF_1', B_62), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_170, c_937])).
% 4.51/1.90  tff(c_1286, plain, (![B_68]: (k3_xboole_0('#skF_1', k4_xboole_0(B_68, k4_xboole_0('#skF_2', '#skF_3')))=k3_xboole_0('#skF_1', B_68))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1017])).
% 4.51/1.90  tff(c_1346, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_18, c_1286])).
% 4.51/1.90  tff(c_1622, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1346, c_16])).
% 4.51/1.90  tff(c_1637, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1622])).
% 4.51/1.90  tff(c_20, plain, (![A_13, B_14, C_15]: (k4_xboole_0(k3_xboole_0(A_13, B_14), C_15)=k3_xboole_0(A_13, k4_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.51/1.90  tff(c_6376, plain, (![A_125, B_126, C_127]: (k3_xboole_0(A_125, k4_xboole_0(B_126, k3_xboole_0(A_125, C_127)))=k3_xboole_0(A_125, k4_xboole_0(B_126, C_127)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_937])).
% 4.51/1.90  tff(c_6561, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1637, c_6376])).
% 4.51/1.90  tff(c_6706, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_391, c_6561])).
% 4.51/1.90  tff(c_6708, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_6706])).
% 4.51/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.51/1.90  
% 4.51/1.90  Inference rules
% 4.51/1.90  ----------------------
% 4.51/1.90  #Ref     : 0
% 4.51/1.90  #Sup     : 1690
% 4.51/1.90  #Fact    : 0
% 4.51/1.90  #Define  : 0
% 4.51/1.90  #Split   : 0
% 4.51/1.90  #Chain   : 0
% 4.51/1.90  #Close   : 0
% 4.51/1.90  
% 4.51/1.90  Ordering : KBO
% 4.51/1.90  
% 4.51/1.90  Simplification rules
% 4.51/1.90  ----------------------
% 4.51/1.90  #Subsume      : 0
% 4.51/1.90  #Demod        : 1576
% 4.51/1.90  #Tautology    : 1225
% 4.51/1.90  #SimpNegUnit  : 1
% 4.51/1.90  #BackRed      : 0
% 4.51/1.90  
% 4.51/1.90  #Partial instantiations: 0
% 4.51/1.90  #Strategies tried      : 1
% 4.51/1.90  
% 4.51/1.90  Timing (in seconds)
% 4.51/1.90  ----------------------
% 4.51/1.91  Preprocessing        : 0.28
% 4.51/1.91  Parsing              : 0.15
% 4.51/1.91  CNF conversion       : 0.02
% 4.51/1.91  Main loop            : 0.86
% 4.51/1.91  Inferencing          : 0.28
% 4.51/1.91  Reduction            : 0.39
% 4.51/1.91  Demodulation         : 0.32
% 4.51/1.91  BG Simplification    : 0.03
% 4.51/1.91  Subsumption          : 0.11
% 4.51/1.91  Abstraction          : 0.05
% 4.51/1.91  MUC search           : 0.00
% 4.51/1.91  Cooper               : 0.00
% 4.51/1.91  Total                : 1.17
% 4.51/1.91  Index Insertion      : 0.00
% 4.51/1.91  Index Deletion       : 0.00
% 4.51/1.91  Index Matching       : 0.00
% 4.51/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
