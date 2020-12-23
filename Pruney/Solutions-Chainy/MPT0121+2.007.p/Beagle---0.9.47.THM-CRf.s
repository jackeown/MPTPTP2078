%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:34 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   50 (  74 expanded)
%              Number of leaves         :   19 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   48 (  91 expanded)
%              Number of equality atoms :   25 (  41 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_xboole_0(A,D)
          & r1_xboole_0(B,D)
          & r1_xboole_0(C,D) )
       => r1_xboole_0(k2_xboole_0(k2_xboole_0(A,B),C),D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(c_22,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_28,plain,(
    ! [B_20,A_21] :
      ( r1_xboole_0(B_20,A_21)
      | ~ r1_xboole_0(A_21,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_35,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_28])).

tff(c_58,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(A_24,B_25) = A_24
      | ~ r1_xboole_0(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_83,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_35,c_58])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_186,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k4_xboole_0(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_198,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,k4_xboole_0(A_5,B_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_186])).

tff(c_225,plain,(
    ! [A_5,B_6] : k3_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_198])).

tff(c_24,plain,(
    r1_xboole_0('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_36,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_28])).

tff(c_81,plain,(
    k4_xboole_0('#skF_4','#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_58])).

tff(c_690,plain,(
    ! [A_46,B_47,C_48] : k3_xboole_0(k4_xboole_0(A_46,B_47),k4_xboole_0(A_46,C_48)) = k4_xboole_0(A_46,k2_xboole_0(B_47,C_48)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_771,plain,(
    ! [C_48] : k4_xboole_0('#skF_4',k2_xboole_0('#skF_2',C_48)) = k3_xboole_0('#skF_4',k4_xboole_0('#skF_4',C_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_690])).

tff(c_815,plain,(
    ! [C_48] : k4_xboole_0('#skF_4',k2_xboole_0('#skF_2',C_48)) = k4_xboole_0('#skF_4',C_48) ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_771])).

tff(c_26,plain,(
    r1_xboole_0('#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_37,plain,(
    r1_xboole_0('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_28])).

tff(c_80,plain,(
    k4_xboole_0('#skF_4','#skF_1') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_37,c_58])).

tff(c_777,plain,(
    ! [C_48] : k4_xboole_0('#skF_4',k2_xboole_0('#skF_1',C_48)) = k3_xboole_0('#skF_4',k4_xboole_0('#skF_4',C_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_690])).

tff(c_816,plain,(
    ! [C_48] : k4_xboole_0('#skF_4',k2_xboole_0('#skF_1',C_48)) = k4_xboole_0('#skF_4',C_48) ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_777])).

tff(c_42,plain,(
    ! [A_22,B_23] :
      ( r1_xboole_0(A_22,B_23)
      | k4_xboole_0(A_22,B_23) != A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_162,plain,(
    ! [B_28,A_29] :
      ( r1_xboole_0(B_28,A_29)
      | k4_xboole_0(A_29,B_28) != A_29 ) ),
    inference(resolution,[status(thm)],[c_42,c_2])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] : k2_xboole_0(k2_xboole_0(A_7,B_8),C_9) = k2_xboole_0(A_7,k2_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ~ r1_xboole_0(k2_xboole_0(k2_xboole_0('#skF_1','#skF_2'),'#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_27,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_20])).

tff(c_172,plain,(
    k4_xboole_0('#skF_4',k2_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3'))) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_162,c_27])).

tff(c_988,plain,(
    k4_xboole_0('#skF_4',k2_xboole_0('#skF_2','#skF_3')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_816,c_172])).

tff(c_1020,plain,(
    k4_xboole_0('#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_815,c_988])).

tff(c_1023,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_1020])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:35:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.41  
% 2.73/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.41  %$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.73/1.41  
% 2.73/1.41  %Foreground sorts:
% 2.73/1.41  
% 2.73/1.41  
% 2.73/1.41  %Background operators:
% 2.73/1.41  
% 2.73/1.41  
% 2.73/1.41  %Foreground operators:
% 2.73/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.73/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.73/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.73/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.73/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.73/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.73/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.73/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.73/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.73/1.41  
% 2.73/1.42  tff(f_54, negated_conjecture, ~(![A, B, C, D]: (((r1_xboole_0(A, D) & r1_xboole_0(B, D)) & r1_xboole_0(C, D)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(A, B), C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_xboole_1)).
% 2.73/1.42  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.73/1.42  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.73/1.42  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.73/1.42  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.73/1.42  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_xboole_1)).
% 2.73/1.42  tff(f_35, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.73/1.42  tff(c_22, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.73/1.42  tff(c_28, plain, (![B_20, A_21]: (r1_xboole_0(B_20, A_21) | ~r1_xboole_0(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.73/1.42  tff(c_35, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_28])).
% 2.73/1.42  tff(c_58, plain, (![A_24, B_25]: (k4_xboole_0(A_24, B_25)=A_24 | ~r1_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.73/1.42  tff(c_83, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_35, c_58])).
% 2.73/1.42  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.73/1.42  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.73/1.42  tff(c_186, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k4_xboole_0(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.73/1.42  tff(c_198, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k3_xboole_0(A_5, k4_xboole_0(A_5, B_6)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_186])).
% 2.73/1.42  tff(c_225, plain, (![A_5, B_6]: (k3_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_198])).
% 2.73/1.42  tff(c_24, plain, (r1_xboole_0('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.73/1.42  tff(c_36, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_28])).
% 2.73/1.42  tff(c_81, plain, (k4_xboole_0('#skF_4', '#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_36, c_58])).
% 2.73/1.42  tff(c_690, plain, (![A_46, B_47, C_48]: (k3_xboole_0(k4_xboole_0(A_46, B_47), k4_xboole_0(A_46, C_48))=k4_xboole_0(A_46, k2_xboole_0(B_47, C_48)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.73/1.42  tff(c_771, plain, (![C_48]: (k4_xboole_0('#skF_4', k2_xboole_0('#skF_2', C_48))=k3_xboole_0('#skF_4', k4_xboole_0('#skF_4', C_48)))), inference(superposition, [status(thm), theory('equality')], [c_81, c_690])).
% 2.73/1.42  tff(c_815, plain, (![C_48]: (k4_xboole_0('#skF_4', k2_xboole_0('#skF_2', C_48))=k4_xboole_0('#skF_4', C_48))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_771])).
% 2.73/1.42  tff(c_26, plain, (r1_xboole_0('#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.73/1.42  tff(c_37, plain, (r1_xboole_0('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_26, c_28])).
% 2.73/1.42  tff(c_80, plain, (k4_xboole_0('#skF_4', '#skF_1')='#skF_4'), inference(resolution, [status(thm)], [c_37, c_58])).
% 2.73/1.42  tff(c_777, plain, (![C_48]: (k4_xboole_0('#skF_4', k2_xboole_0('#skF_1', C_48))=k3_xboole_0('#skF_4', k4_xboole_0('#skF_4', C_48)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_690])).
% 2.73/1.42  tff(c_816, plain, (![C_48]: (k4_xboole_0('#skF_4', k2_xboole_0('#skF_1', C_48))=k4_xboole_0('#skF_4', C_48))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_777])).
% 2.73/1.42  tff(c_42, plain, (![A_22, B_23]: (r1_xboole_0(A_22, B_23) | k4_xboole_0(A_22, B_23)!=A_22)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.73/1.42  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.73/1.42  tff(c_162, plain, (![B_28, A_29]: (r1_xboole_0(B_28, A_29) | k4_xboole_0(A_29, B_28)!=A_29)), inference(resolution, [status(thm)], [c_42, c_2])).
% 2.73/1.42  tff(c_8, plain, (![A_7, B_8, C_9]: (k2_xboole_0(k2_xboole_0(A_7, B_8), C_9)=k2_xboole_0(A_7, k2_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.73/1.42  tff(c_20, plain, (~r1_xboole_0(k2_xboole_0(k2_xboole_0('#skF_1', '#skF_2'), '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.73/1.42  tff(c_27, plain, (~r1_xboole_0(k2_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_20])).
% 2.73/1.42  tff(c_172, plain, (k4_xboole_0('#skF_4', k2_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')))!='#skF_4'), inference(resolution, [status(thm)], [c_162, c_27])).
% 2.73/1.42  tff(c_988, plain, (k4_xboole_0('#skF_4', k2_xboole_0('#skF_2', '#skF_3'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_816, c_172])).
% 2.73/1.42  tff(c_1020, plain, (k4_xboole_0('#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_815, c_988])).
% 2.73/1.42  tff(c_1023, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_1020])).
% 2.73/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.42  
% 2.73/1.42  Inference rules
% 2.73/1.42  ----------------------
% 2.73/1.42  #Ref     : 0
% 2.73/1.42  #Sup     : 294
% 2.73/1.42  #Fact    : 0
% 2.73/1.42  #Define  : 0
% 2.73/1.42  #Split   : 0
% 2.73/1.42  #Chain   : 0
% 2.73/1.42  #Close   : 0
% 2.73/1.42  
% 2.73/1.42  Ordering : KBO
% 2.73/1.42  
% 2.73/1.42  Simplification rules
% 2.73/1.42  ----------------------
% 2.73/1.42  #Subsume      : 1
% 2.73/1.42  #Demod        : 185
% 2.73/1.42  #Tautology    : 163
% 2.73/1.42  #SimpNegUnit  : 0
% 2.73/1.42  #BackRed      : 2
% 2.73/1.42  
% 2.73/1.42  #Partial instantiations: 0
% 2.73/1.42  #Strategies tried      : 1
% 2.73/1.42  
% 2.73/1.42  Timing (in seconds)
% 2.73/1.42  ----------------------
% 2.73/1.42  Preprocessing        : 0.26
% 2.73/1.42  Parsing              : 0.15
% 2.73/1.42  CNF conversion       : 0.02
% 2.73/1.42  Main loop            : 0.39
% 2.73/1.42  Inferencing          : 0.15
% 2.73/1.42  Reduction            : 0.14
% 2.73/1.42  Demodulation         : 0.11
% 2.73/1.42  BG Simplification    : 0.02
% 2.73/1.42  Subsumption          : 0.06
% 2.73/1.42  Abstraction          : 0.02
% 2.73/1.42  MUC search           : 0.00
% 2.73/1.42  Cooper               : 0.00
% 2.73/1.42  Total                : 0.68
% 2.73/1.42  Index Insertion      : 0.00
% 2.73/1.42  Index Deletion       : 0.00
% 2.73/1.42  Index Matching       : 0.00
% 2.73/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
