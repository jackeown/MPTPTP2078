%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:08 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :   53 (  72 expanded)
%              Number of leaves         :   21 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   49 (  73 expanded)
%              Number of equality atoms :   36 (  53 expanded)
%              Maximal formula depth    :    8 (   3 average)
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

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

tff(c_138,plain,(
    ! [A_26,B_27] :
      ( r1_xboole_0(A_26,B_27)
      | k3_xboole_0(A_26,B_27) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_146,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_138,c_28])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_238,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k3_xboole_0(A_36,B_37)) = k4_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_262,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_238])).

tff(c_395,plain,(
    ! [A_41,B_42,C_43] : k4_xboole_0(k3_xboole_0(A_41,B_42),C_43) = k3_xboole_0(A_41,k4_xboole_0(B_42,C_43)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_161,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k4_xboole_0(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_179,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_161])).

tff(c_183,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_179])).

tff(c_410,plain,(
    ! [A_41,B_42] : k3_xboole_0(A_41,k4_xboole_0(B_42,k3_xboole_0(A_41,B_42))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_395,c_183])).

tff(c_469,plain,(
    ! [A_41,B_42] : k3_xboole_0(A_41,k4_xboole_0(B_42,A_41)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_410])).

tff(c_20,plain,(
    ! [A_13,B_14,C_15] : k4_xboole_0(k3_xboole_0(A_13,B_14),C_15) = k3_xboole_0(A_13,k4_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_147,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_151,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_147])).

tff(c_176,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_161])).

tff(c_182,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_176])).

tff(c_893,plain,(
    ! [A_53,B_54,C_55] : k4_xboole_0(k3_xboole_0(A_53,B_54),k3_xboole_0(A_53,C_55)) = k3_xboole_0(A_53,k4_xboole_0(B_54,C_55)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_972,plain,(
    ! [B_54] : k4_xboole_0(k3_xboole_0('#skF_1',B_54),'#skF_1') = k3_xboole_0('#skF_1',k4_xboole_0(B_54,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_893])).

tff(c_1025,plain,(
    ! [B_54] : k3_xboole_0('#skF_1',k4_xboole_0(B_54,'#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_20,c_972])).

tff(c_24,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_29,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_24])).

tff(c_128,plain,(
    ! [A_24,B_25] :
      ( k3_xboole_0(A_24,B_25) = k1_xboole_0
      | ~ r1_xboole_0(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_132,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_29,c_128])).

tff(c_982,plain,(
    ! [B_54] : k3_xboole_0('#skF_1',k4_xboole_0(B_54,k3_xboole_0('#skF_3','#skF_2'))) = k4_xboole_0(k3_xboole_0('#skF_1',B_54),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_893])).

tff(c_2238,plain,(
    ! [B_75] : k3_xboole_0('#skF_1',k4_xboole_0(B_75,k3_xboole_0('#skF_3','#skF_2'))) = k3_xboole_0('#skF_1',B_75) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_982])).

tff(c_2322,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_2238])).

tff(c_2356,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1025,c_2322])).

tff(c_2358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_2356])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:55:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.66  
% 3.52/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.66  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.52/1.66  
% 3.52/1.66  %Foreground sorts:
% 3.52/1.66  
% 3.52/1.66  
% 3.52/1.66  %Background operators:
% 3.52/1.66  
% 3.52/1.66  
% 3.52/1.66  %Foreground operators:
% 3.52/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.52/1.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.52/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.52/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.52/1.66  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.52/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.52/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.52/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.52/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.52/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.52/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.52/1.66  
% 3.52/1.68  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.52/1.68  tff(f_56, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_xboole_1)).
% 3.52/1.68  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.52/1.68  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 3.52/1.68  tff(f_45, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.52/1.68  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.52/1.68  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.52/1.68  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.52/1.68  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 3.52/1.68  tff(f_47, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_xboole_1)).
% 3.52/1.68  tff(c_138, plain, (![A_26, B_27]: (r1_xboole_0(A_26, B_27) | k3_xboole_0(A_26, B_27)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.52/1.68  tff(c_28, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.52/1.68  tff(c_146, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_138, c_28])).
% 3.52/1.68  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.52/1.68  tff(c_238, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k3_xboole_0(A_36, B_37))=k4_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.52/1.68  tff(c_262, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_238])).
% 3.52/1.68  tff(c_395, plain, (![A_41, B_42, C_43]: (k4_xboole_0(k3_xboole_0(A_41, B_42), C_43)=k3_xboole_0(A_41, k4_xboole_0(B_42, C_43)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.52/1.68  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.52/1.68  tff(c_14, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.52/1.68  tff(c_161, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k4_xboole_0(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.52/1.68  tff(c_179, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_161])).
% 3.52/1.68  tff(c_183, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_179])).
% 3.52/1.68  tff(c_410, plain, (![A_41, B_42]: (k3_xboole_0(A_41, k4_xboole_0(B_42, k3_xboole_0(A_41, B_42)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_395, c_183])).
% 3.52/1.68  tff(c_469, plain, (![A_41, B_42]: (k3_xboole_0(A_41, k4_xboole_0(B_42, A_41))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_262, c_410])).
% 3.52/1.68  tff(c_20, plain, (![A_13, B_14, C_15]: (k4_xboole_0(k3_xboole_0(A_13, B_14), C_15)=k3_xboole_0(A_13, k4_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.52/1.68  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.52/1.68  tff(c_147, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.52/1.68  tff(c_151, plain, (k4_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_147])).
% 3.52/1.68  tff(c_176, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_151, c_161])).
% 3.52/1.68  tff(c_182, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_176])).
% 3.52/1.68  tff(c_893, plain, (![A_53, B_54, C_55]: (k4_xboole_0(k3_xboole_0(A_53, B_54), k3_xboole_0(A_53, C_55))=k3_xboole_0(A_53, k4_xboole_0(B_54, C_55)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.52/1.68  tff(c_972, plain, (![B_54]: (k4_xboole_0(k3_xboole_0('#skF_1', B_54), '#skF_1')=k3_xboole_0('#skF_1', k4_xboole_0(B_54, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_182, c_893])).
% 3.52/1.68  tff(c_1025, plain, (![B_54]: (k3_xboole_0('#skF_1', k4_xboole_0(B_54, '#skF_3'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_469, c_20, c_972])).
% 3.52/1.68  tff(c_24, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.52/1.68  tff(c_29, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_24])).
% 3.52/1.68  tff(c_128, plain, (![A_24, B_25]: (k3_xboole_0(A_24, B_25)=k1_xboole_0 | ~r1_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.52/1.68  tff(c_132, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_29, c_128])).
% 3.52/1.68  tff(c_982, plain, (![B_54]: (k3_xboole_0('#skF_1', k4_xboole_0(B_54, k3_xboole_0('#skF_3', '#skF_2')))=k4_xboole_0(k3_xboole_0('#skF_1', B_54), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_132, c_893])).
% 3.52/1.68  tff(c_2238, plain, (![B_75]: (k3_xboole_0('#skF_1', k4_xboole_0(B_75, k3_xboole_0('#skF_3', '#skF_2')))=k3_xboole_0('#skF_1', B_75))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_982])).
% 3.52/1.68  tff(c_2322, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_262, c_2238])).
% 3.52/1.68  tff(c_2356, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1025, c_2322])).
% 3.52/1.68  tff(c_2358, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_2356])).
% 3.52/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.68  
% 3.52/1.68  Inference rules
% 3.52/1.68  ----------------------
% 3.52/1.68  #Ref     : 0
% 3.52/1.68  #Sup     : 582
% 3.52/1.68  #Fact    : 0
% 3.52/1.68  #Define  : 0
% 3.52/1.68  #Split   : 0
% 3.52/1.68  #Chain   : 0
% 3.52/1.68  #Close   : 0
% 3.52/1.68  
% 3.52/1.68  Ordering : KBO
% 3.52/1.68  
% 3.52/1.68  Simplification rules
% 3.52/1.68  ----------------------
% 3.52/1.68  #Subsume      : 0
% 3.52/1.68  #Demod        : 547
% 3.52/1.68  #Tautology    : 400
% 3.52/1.68  #SimpNegUnit  : 1
% 3.52/1.68  #BackRed      : 0
% 3.52/1.68  
% 3.52/1.68  #Partial instantiations: 0
% 3.52/1.68  #Strategies tried      : 1
% 3.52/1.68  
% 3.52/1.68  Timing (in seconds)
% 3.52/1.68  ----------------------
% 3.52/1.68  Preprocessing        : 0.31
% 3.52/1.68  Parsing              : 0.17
% 3.52/1.68  CNF conversion       : 0.02
% 3.52/1.68  Main loop            : 0.53
% 3.52/1.68  Inferencing          : 0.17
% 3.52/1.68  Reduction            : 0.25
% 3.52/1.68  Demodulation         : 0.21
% 3.52/1.68  BG Simplification    : 0.02
% 3.52/1.68  Subsumption          : 0.07
% 3.52/1.68  Abstraction          : 0.03
% 3.52/1.68  MUC search           : 0.00
% 3.52/1.68  Cooper               : 0.00
% 3.52/1.68  Total                : 0.87
% 3.52/1.68  Index Insertion      : 0.00
% 3.52/1.68  Index Deletion       : 0.00
% 3.52/1.68  Index Matching       : 0.00
% 3.52/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
