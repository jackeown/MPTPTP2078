%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:14 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :   48 (  63 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   46 (  75 expanded)
%              Number of equality atoms :   22 (  28 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_59,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | k4_xboole_0(A_24,B_25) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_25,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_63,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_59,c_25])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_81,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_81])).

tff(c_12,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_201,plain,(
    r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_12])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_218,plain,(
    k3_xboole_0(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_201,c_10])).

tff(c_312,plain,(
    k3_xboole_0('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_218])).

tff(c_92,plain,(
    ! [A_9,B_10] : k4_xboole_0(k4_xboole_0(A_9,B_10),A_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_81])).

tff(c_64,plain,(
    ! [A_26,B_27] :
      ( k3_xboole_0(A_26,B_27) = A_26
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_76,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22,c_64])).

tff(c_362,plain,(
    ! [A_39,B_40,C_41] : k4_xboole_0(k3_xboole_0(A_39,B_40),C_41) = k3_xboole_0(A_39,k4_xboole_0(B_40,C_41)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_419,plain,(
    ! [C_42] : k3_xboole_0('#skF_1',k4_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_42)) = k4_xboole_0('#skF_1',C_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_362])).

tff(c_439,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_419])).

tff(c_442,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_439])).

tff(c_444,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_442])).

tff(c_445,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_480,plain,(
    ! [A_45,B_46] :
      ( k3_xboole_0(A_45,B_46) = A_45
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_492,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22,c_480])).

tff(c_869,plain,(
    ! [A_62,B_63,C_64] : k4_xboole_0(k3_xboole_0(A_62,B_63),C_64) = k3_xboole_0(A_62,k4_xboole_0(B_63,C_64)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [A_16,B_17] : r1_xboole_0(k4_xboole_0(A_16,B_17),B_17) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1229,plain,(
    ! [A_76,B_77,C_78] : r1_xboole_0(k3_xboole_0(A_76,k4_xboole_0(B_77,C_78)),C_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_869,c_18])).

tff(c_1262,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_492,c_1229])).

tff(c_1283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_445,c_1262])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n005.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 20:41:02 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.48  
% 2.93/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.49  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.93/1.49  
% 2.93/1.49  %Foreground sorts:
% 2.93/1.49  
% 2.93/1.49  
% 2.93/1.49  %Background operators:
% 2.93/1.49  
% 2.93/1.49  
% 2.93/1.49  %Foreground operators:
% 2.93/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.93/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.93/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.93/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.93/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.93/1.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.93/1.49  tff('#skF_2', type, '#skF_2': $i).
% 2.93/1.49  tff('#skF_3', type, '#skF_3': $i).
% 2.93/1.49  tff('#skF_1', type, '#skF_1': $i).
% 2.93/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.93/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.93/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.93/1.49  
% 2.93/1.50  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.93/1.50  tff(f_52, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.93/1.50  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.93/1.50  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.93/1.50  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.93/1.50  tff(f_43, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.93/1.50  tff(f_45, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.93/1.50  tff(c_59, plain, (![A_24, B_25]: (r1_tarski(A_24, B_25) | k4_xboole_0(A_24, B_25)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.93/1.50  tff(c_20, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.93/1.50  tff(c_25, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_20])).
% 2.93/1.50  tff(c_63, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_59, c_25])).
% 2.93/1.50  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.93/1.50  tff(c_22, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.93/1.50  tff(c_81, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.93/1.50  tff(c_93, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_81])).
% 2.93/1.50  tff(c_12, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.93/1.50  tff(c_201, plain, (r1_tarski(k1_xboole_0, '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_93, c_12])).
% 2.93/1.50  tff(c_10, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.93/1.50  tff(c_218, plain, (k3_xboole_0(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_201, c_10])).
% 2.93/1.50  tff(c_312, plain, (k3_xboole_0('#skF_1', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2, c_218])).
% 2.93/1.50  tff(c_92, plain, (![A_9, B_10]: (k4_xboole_0(k4_xboole_0(A_9, B_10), A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_81])).
% 2.93/1.50  tff(c_64, plain, (![A_26, B_27]: (k3_xboole_0(A_26, B_27)=A_26 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.93/1.50  tff(c_76, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_22, c_64])).
% 2.93/1.50  tff(c_362, plain, (![A_39, B_40, C_41]: (k4_xboole_0(k3_xboole_0(A_39, B_40), C_41)=k3_xboole_0(A_39, k4_xboole_0(B_40, C_41)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.93/1.50  tff(c_419, plain, (![C_42]: (k3_xboole_0('#skF_1', k4_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_42))=k4_xboole_0('#skF_1', C_42))), inference(superposition, [status(thm), theory('equality')], [c_76, c_362])).
% 2.93/1.50  tff(c_439, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_92, c_419])).
% 2.93/1.50  tff(c_442, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_312, c_439])).
% 2.93/1.50  tff(c_444, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_442])).
% 2.93/1.50  tff(c_445, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_20])).
% 2.93/1.50  tff(c_480, plain, (![A_45, B_46]: (k3_xboole_0(A_45, B_46)=A_45 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.93/1.50  tff(c_492, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_22, c_480])).
% 2.93/1.50  tff(c_869, plain, (![A_62, B_63, C_64]: (k4_xboole_0(k3_xboole_0(A_62, B_63), C_64)=k3_xboole_0(A_62, k4_xboole_0(B_63, C_64)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.93/1.50  tff(c_18, plain, (![A_16, B_17]: (r1_xboole_0(k4_xboole_0(A_16, B_17), B_17))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.93/1.50  tff(c_1229, plain, (![A_76, B_77, C_78]: (r1_xboole_0(k3_xboole_0(A_76, k4_xboole_0(B_77, C_78)), C_78))), inference(superposition, [status(thm), theory('equality')], [c_869, c_18])).
% 2.93/1.50  tff(c_1262, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_492, c_1229])).
% 2.93/1.50  tff(c_1283, plain, $false, inference(negUnitSimplification, [status(thm)], [c_445, c_1262])).
% 2.93/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.50  
% 2.93/1.50  Inference rules
% 2.93/1.50  ----------------------
% 2.93/1.50  #Ref     : 0
% 2.93/1.50  #Sup     : 362
% 2.93/1.50  #Fact    : 0
% 2.93/1.50  #Define  : 0
% 2.93/1.50  #Split   : 1
% 2.93/1.50  #Chain   : 0
% 2.93/1.50  #Close   : 0
% 2.93/1.50  
% 2.93/1.50  Ordering : KBO
% 2.93/1.50  
% 2.93/1.50  Simplification rules
% 2.93/1.50  ----------------------
% 2.93/1.50  #Subsume      : 0
% 2.93/1.50  #Demod        : 151
% 2.93/1.50  #Tautology    : 216
% 2.93/1.50  #SimpNegUnit  : 2
% 2.93/1.50  #BackRed      : 0
% 2.93/1.50  
% 2.93/1.50  #Partial instantiations: 0
% 2.93/1.50  #Strategies tried      : 1
% 2.93/1.50  
% 2.93/1.50  Timing (in seconds)
% 2.93/1.50  ----------------------
% 2.93/1.50  Preprocessing        : 0.31
% 2.93/1.50  Parsing              : 0.17
% 2.93/1.50  CNF conversion       : 0.02
% 2.93/1.50  Main loop            : 0.38
% 2.93/1.50  Inferencing          : 0.13
% 2.93/1.50  Reduction            : 0.14
% 2.93/1.50  Demodulation         : 0.11
% 2.93/1.50  BG Simplification    : 0.02
% 3.04/1.50  Subsumption          : 0.05
% 3.04/1.50  Abstraction          : 0.02
% 3.04/1.50  MUC search           : 0.00
% 3.04/1.50  Cooper               : 0.00
% 3.04/1.50  Total                : 0.72
% 3.04/1.50  Index Insertion      : 0.00
% 3.04/1.50  Index Deletion       : 0.00
% 3.04/1.50  Index Matching       : 0.00
% 3.04/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
