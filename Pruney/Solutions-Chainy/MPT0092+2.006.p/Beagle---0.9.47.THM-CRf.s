%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:29 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :   53 (  77 expanded)
%              Number of leaves         :   23 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   60 (  85 expanded)
%              Number of equality atoms :   27 (  50 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff(f_34,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_30,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_28,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D)
        & r1_xboole_0(B,D) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,k4_xboole_0(B,C))
     => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_52,plain,(
    ! [A_27,B_28] : k2_xboole_0(A_27,k3_xboole_0(A_27,B_28)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_61,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_52])).

tff(c_293,plain,(
    ! [A_61,B_62,C_63] : k3_xboole_0(k4_xboole_0(A_61,B_62),k4_xboole_0(A_61,C_63)) = k4_xboole_0(A_61,k2_xboole_0(B_62,C_63)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_329,plain,(
    ! [A_6,B_62] : k4_xboole_0(A_6,k2_xboole_0(B_62,k1_xboole_0)) = k3_xboole_0(k4_xboole_0(A_6,B_62),A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_293])).

tff(c_366,plain,(
    ! [A_66,B_67] : k3_xboole_0(k4_xboole_0(A_66,B_67),A_66) = k4_xboole_0(A_66,B_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_329])).

tff(c_402,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = k3_xboole_0(A_6,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_366])).

tff(c_412,plain,(
    ! [A_68] : k3_xboole_0(A_68,A_68) = A_68 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_402])).

tff(c_4,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_432,plain,(
    ! [A_68] : k2_xboole_0(A_68,A_68) = A_68 ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_4])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] : k3_xboole_0(k4_xboole_0(A_10,B_11),k4_xboole_0(A_10,C_12)) = k4_xboole_0(A_10,k2_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9] : k4_xboole_0(k3_xboole_0(A_7,B_8),C_9) = k3_xboole_0(A_7,k4_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_379,plain,(
    ! [A_66,B_67,C_9] : k3_xboole_0(k4_xboole_0(A_66,B_67),k4_xboole_0(A_66,C_9)) = k4_xboole_0(k4_xboole_0(A_66,B_67),C_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_366,c_12])).

tff(c_405,plain,(
    ! [A_66,B_67,C_9] : k4_xboole_0(k4_xboole_0(A_66,B_67),C_9) = k4_xboole_0(A_66,k2_xboole_0(B_67,C_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_379])).

tff(c_47,plain,(
    ! [A_24,B_25] : r1_tarski(k4_xboole_0(A_24,B_25),A_24) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,(
    ! [A_6] : r1_tarski(A_6,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_47])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22,plain,(
    ! [A_20,B_21] :
      ( r1_xboole_0(A_20,B_21)
      | k4_xboole_0(A_20,B_21) != A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_485,plain,(
    ! [A_72,C_73,B_74,D_75] :
      ( r1_xboole_0(A_72,C_73)
      | ~ r1_xboole_0(B_74,D_75)
      | ~ r1_tarski(C_73,D_75)
      | ~ r1_tarski(A_72,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1769,plain,(
    ! [A_123,C_124,B_125,A_126] :
      ( r1_xboole_0(A_123,C_124)
      | ~ r1_tarski(C_124,B_125)
      | ~ r1_tarski(A_123,A_126)
      | k4_xboole_0(A_126,B_125) != A_126 ) ),
    inference(resolution,[status(thm)],[c_22,c_485])).

tff(c_2261,plain,(
    ! [A_148,A_149] :
      ( r1_xboole_0(A_148,'#skF_1')
      | ~ r1_tarski(A_148,A_149)
      | k4_xboole_0(A_149,'#skF_2') != A_149 ) ),
    inference(resolution,[status(thm)],[c_26,c_1769])).

tff(c_2279,plain,(
    ! [A_150] :
      ( r1_xboole_0(A_150,'#skF_1')
      | k4_xboole_0(A_150,'#skF_2') != A_150 ) ),
    inference(resolution,[status(thm)],[c_50,c_2261])).

tff(c_83,plain,(
    ! [B_34,A_35,C_36] :
      ( r1_xboole_0(B_34,k4_xboole_0(A_35,C_36))
      | ~ r1_xboole_0(A_35,k4_xboole_0(B_34,C_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_88,plain,(
    ! [A_6,A_35] :
      ( r1_xboole_0(A_6,k4_xboole_0(A_35,k1_xboole_0))
      | ~ r1_xboole_0(A_35,A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_83])).

tff(c_90,plain,(
    ! [A_6,A_35] :
      ( r1_xboole_0(A_6,A_35)
      | ~ r1_xboole_0(A_35,A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_88])).

tff(c_2291,plain,(
    ! [A_151] :
      ( r1_xboole_0('#skF_1',A_151)
      | k4_xboole_0(A_151,'#skF_2') != A_151 ) ),
    inference(resolution,[status(thm)],[c_2279,c_90])).

tff(c_24,plain,(
    ~ r1_xboole_0('#skF_1',k4_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2307,plain,(
    k4_xboole_0(k4_xboole_0('#skF_3','#skF_2'),'#skF_2') != k4_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_2291,c_24])).

tff(c_2318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_405,c_2307])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:34:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.63  
% 3.52/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.63  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.52/1.63  
% 3.52/1.63  %Foreground sorts:
% 3.52/1.63  
% 3.52/1.63  
% 3.52/1.63  %Background operators:
% 3.52/1.63  
% 3.52/1.63  
% 3.52/1.63  %Foreground operators:
% 3.52/1.63  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 3.52/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.52/1.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.52/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.52/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.52/1.63  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.52/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.52/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.52/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.52/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.52/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.52/1.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.52/1.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.52/1.63  
% 3.52/1.64  tff(f_34, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.52/1.64  tff(f_30, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.52/1.64  tff(f_28, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 3.52/1.64  tff(f_38, axiom, (![A, B, C]: (k4_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_xboole_1)).
% 3.52/1.64  tff(f_36, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.52/1.64  tff(f_32, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.52/1.64  tff(f_59, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.52/1.64  tff(f_54, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.52/1.64  tff(f_46, axiom, (![A, B, C, D]: (((r1_tarski(A, B) & r1_tarski(C, D)) & r1_xboole_0(B, D)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_xboole_1)).
% 3.52/1.64  tff(f_50, axiom, (![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 3.52/1.64  tff(c_10, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.52/1.64  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.52/1.64  tff(c_52, plain, (![A_27, B_28]: (k2_xboole_0(A_27, k3_xboole_0(A_27, B_28))=A_27)), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.52/1.64  tff(c_61, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(superposition, [status(thm), theory('equality')], [c_6, c_52])).
% 3.52/1.64  tff(c_293, plain, (![A_61, B_62, C_63]: (k3_xboole_0(k4_xboole_0(A_61, B_62), k4_xboole_0(A_61, C_63))=k4_xboole_0(A_61, k2_xboole_0(B_62, C_63)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.52/1.64  tff(c_329, plain, (![A_6, B_62]: (k4_xboole_0(A_6, k2_xboole_0(B_62, k1_xboole_0))=k3_xboole_0(k4_xboole_0(A_6, B_62), A_6))), inference(superposition, [status(thm), theory('equality')], [c_10, c_293])).
% 3.52/1.64  tff(c_366, plain, (![A_66, B_67]: (k3_xboole_0(k4_xboole_0(A_66, B_67), A_66)=k4_xboole_0(A_66, B_67))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_329])).
% 3.52/1.64  tff(c_402, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=k3_xboole_0(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_10, c_366])).
% 3.52/1.64  tff(c_412, plain, (![A_68]: (k3_xboole_0(A_68, A_68)=A_68)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_402])).
% 3.52/1.64  tff(c_4, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k3_xboole_0(A_1, B_2))=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.52/1.64  tff(c_432, plain, (![A_68]: (k2_xboole_0(A_68, A_68)=A_68)), inference(superposition, [status(thm), theory('equality')], [c_412, c_4])).
% 3.52/1.64  tff(c_14, plain, (![A_10, B_11, C_12]: (k3_xboole_0(k4_xboole_0(A_10, B_11), k4_xboole_0(A_10, C_12))=k4_xboole_0(A_10, k2_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.52/1.64  tff(c_12, plain, (![A_7, B_8, C_9]: (k4_xboole_0(k3_xboole_0(A_7, B_8), C_9)=k3_xboole_0(A_7, k4_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.52/1.64  tff(c_379, plain, (![A_66, B_67, C_9]: (k3_xboole_0(k4_xboole_0(A_66, B_67), k4_xboole_0(A_66, C_9))=k4_xboole_0(k4_xboole_0(A_66, B_67), C_9))), inference(superposition, [status(thm), theory('equality')], [c_366, c_12])).
% 3.52/1.64  tff(c_405, plain, (![A_66, B_67, C_9]: (k4_xboole_0(k4_xboole_0(A_66, B_67), C_9)=k4_xboole_0(A_66, k2_xboole_0(B_67, C_9)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_379])).
% 3.52/1.64  tff(c_47, plain, (![A_24, B_25]: (r1_tarski(k4_xboole_0(A_24, B_25), A_24))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.52/1.64  tff(c_50, plain, (![A_6]: (r1_tarski(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_10, c_47])).
% 3.52/1.64  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.52/1.64  tff(c_22, plain, (![A_20, B_21]: (r1_xboole_0(A_20, B_21) | k4_xboole_0(A_20, B_21)!=A_20)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.52/1.64  tff(c_485, plain, (![A_72, C_73, B_74, D_75]: (r1_xboole_0(A_72, C_73) | ~r1_xboole_0(B_74, D_75) | ~r1_tarski(C_73, D_75) | ~r1_tarski(A_72, B_74))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.52/1.64  tff(c_1769, plain, (![A_123, C_124, B_125, A_126]: (r1_xboole_0(A_123, C_124) | ~r1_tarski(C_124, B_125) | ~r1_tarski(A_123, A_126) | k4_xboole_0(A_126, B_125)!=A_126)), inference(resolution, [status(thm)], [c_22, c_485])).
% 3.52/1.64  tff(c_2261, plain, (![A_148, A_149]: (r1_xboole_0(A_148, '#skF_1') | ~r1_tarski(A_148, A_149) | k4_xboole_0(A_149, '#skF_2')!=A_149)), inference(resolution, [status(thm)], [c_26, c_1769])).
% 3.52/1.64  tff(c_2279, plain, (![A_150]: (r1_xboole_0(A_150, '#skF_1') | k4_xboole_0(A_150, '#skF_2')!=A_150)), inference(resolution, [status(thm)], [c_50, c_2261])).
% 3.52/1.64  tff(c_83, plain, (![B_34, A_35, C_36]: (r1_xboole_0(B_34, k4_xboole_0(A_35, C_36)) | ~r1_xboole_0(A_35, k4_xboole_0(B_34, C_36)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.52/1.64  tff(c_88, plain, (![A_6, A_35]: (r1_xboole_0(A_6, k4_xboole_0(A_35, k1_xboole_0)) | ~r1_xboole_0(A_35, A_6))), inference(superposition, [status(thm), theory('equality')], [c_10, c_83])).
% 3.52/1.64  tff(c_90, plain, (![A_6, A_35]: (r1_xboole_0(A_6, A_35) | ~r1_xboole_0(A_35, A_6))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_88])).
% 3.52/1.64  tff(c_2291, plain, (![A_151]: (r1_xboole_0('#skF_1', A_151) | k4_xboole_0(A_151, '#skF_2')!=A_151)), inference(resolution, [status(thm)], [c_2279, c_90])).
% 3.52/1.64  tff(c_24, plain, (~r1_xboole_0('#skF_1', k4_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.52/1.64  tff(c_2307, plain, (k4_xboole_0(k4_xboole_0('#skF_3', '#skF_2'), '#skF_2')!=k4_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_2291, c_24])).
% 3.52/1.64  tff(c_2318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_432, c_405, c_2307])).
% 3.52/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.64  
% 3.52/1.64  Inference rules
% 3.52/1.64  ----------------------
% 3.52/1.64  #Ref     : 0
% 3.52/1.64  #Sup     : 564
% 3.52/1.64  #Fact    : 0
% 3.52/1.64  #Define  : 0
% 3.52/1.64  #Split   : 1
% 3.52/1.64  #Chain   : 0
% 3.52/1.64  #Close   : 0
% 3.52/1.64  
% 3.52/1.64  Ordering : KBO
% 3.52/1.64  
% 3.52/1.64  Simplification rules
% 3.52/1.64  ----------------------
% 3.52/1.64  #Subsume      : 77
% 3.52/1.64  #Demod        : 446
% 3.52/1.64  #Tautology    : 287
% 3.52/1.64  #SimpNegUnit  : 0
% 3.52/1.64  #BackRed      : 5
% 3.52/1.64  
% 3.52/1.64  #Partial instantiations: 0
% 3.52/1.64  #Strategies tried      : 1
% 3.52/1.64  
% 3.52/1.64  Timing (in seconds)
% 3.52/1.64  ----------------------
% 3.52/1.64  Preprocessing        : 0.30
% 3.52/1.64  Parsing              : 0.18
% 3.52/1.64  CNF conversion       : 0.02
% 3.52/1.64  Main loop            : 0.54
% 3.52/1.64  Inferencing          : 0.20
% 3.52/1.64  Reduction            : 0.20
% 3.52/1.64  Demodulation         : 0.15
% 3.52/1.64  BG Simplification    : 0.02
% 3.52/1.64  Subsumption          : 0.09
% 3.52/1.64  Abstraction          : 0.04
% 3.52/1.64  MUC search           : 0.00
% 3.52/1.64  Cooper               : 0.00
% 3.52/1.65  Total                : 0.88
% 3.52/1.65  Index Insertion      : 0.00
% 3.52/1.65  Index Deletion       : 0.00
% 3.52/1.65  Index Matching       : 0.00
% 3.52/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
