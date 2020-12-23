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
% DateTime   : Thu Dec  3 09:45:18 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   46 (  59 expanded)
%              Number of leaves         :   18 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   42 (  66 expanded)
%              Number of equality atoms :   16 (  22 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_18,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_24,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_20,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_74,plain,(
    ! [A_29,B_30] :
      ( k3_xboole_0(A_29,B_30) = A_29
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_90,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_20,c_74])).

tff(c_343,plain,(
    ! [A_44,B_45,C_46] : k4_xboole_0(k3_xboole_0(A_44,B_45),C_46) = k3_xboole_0(A_44,k4_xboole_0(B_45,C_46)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1037,plain,(
    ! [A_73,B_74,C_75] : r1_tarski(k3_xboole_0(A_73,k4_xboole_0(B_74,C_75)),k3_xboole_0(A_73,B_74)) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_10])).

tff(c_1095,plain,(
    r1_tarski('#skF_1',k3_xboole_0('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_1037])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1129,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1095,c_8])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_181,plain,(
    ! [A_38,B_39] : k3_xboole_0(k3_xboole_0(A_38,B_39),A_38) = k3_xboole_0(A_38,B_39) ),
    inference(resolution,[status(thm)],[c_6,c_74])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_202,plain,(
    ! [A_38,B_39] : k3_xboole_0(A_38,k3_xboole_0(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_2])).

tff(c_1142,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1129,c_202])).

tff(c_25,plain,(
    ! [B_25,A_26] : k3_xboole_0(B_25,A_26) = k3_xboole_0(A_26,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    ! [B_25,A_26] : r1_tarski(k3_xboole_0(B_25,A_26),A_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_25,c_6])).

tff(c_1239,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1142,c_40])).

tff(c_1256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_1239])).

tff(c_1257,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_1308,plain,(
    ! [A_80,B_81] :
      ( k3_xboole_0(A_80,B_81) = A_80
      | ~ r1_tarski(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1328,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_20,c_1308])).

tff(c_1642,plain,(
    ! [A_95,B_96,C_97] : k4_xboole_0(k3_xboole_0(A_95,B_96),C_97) = k3_xboole_0(A_95,k4_xboole_0(B_96,C_97)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_17,B_18] : r1_xboole_0(k4_xboole_0(A_17,B_18),B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1676,plain,(
    ! [A_98,B_99,C_100] : r1_xboole_0(k3_xboole_0(A_98,k4_xboole_0(B_99,C_100)),C_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_1642,c_16])).

tff(c_1694,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1328,c_1676])).

tff(c_1705,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1257,c_1694])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:12:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.09/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.49  
% 3.09/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.49  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 3.09/1.49  
% 3.09/1.49  %Foreground sorts:
% 3.09/1.49  
% 3.09/1.49  
% 3.09/1.49  %Background operators:
% 3.09/1.49  
% 3.09/1.49  
% 3.09/1.49  %Foreground operators:
% 3.09/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.09/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.09/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.09/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.09/1.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.09/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.09/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.09/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.09/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.09/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.09/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.09/1.49  
% 3.09/1.50  tff(f_54, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.09/1.50  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.09/1.50  tff(f_39, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.09/1.50  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.09/1.50  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.09/1.50  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.09/1.50  tff(f_47, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.09/1.50  tff(c_18, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.09/1.50  tff(c_24, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_18])).
% 3.09/1.50  tff(c_20, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.09/1.50  tff(c_74, plain, (![A_29, B_30]: (k3_xboole_0(A_29, B_30)=A_29 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.09/1.50  tff(c_90, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_20, c_74])).
% 3.09/1.50  tff(c_343, plain, (![A_44, B_45, C_46]: (k4_xboole_0(k3_xboole_0(A_44, B_45), C_46)=k3_xboole_0(A_44, k4_xboole_0(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.09/1.50  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.09/1.50  tff(c_1037, plain, (![A_73, B_74, C_75]: (r1_tarski(k3_xboole_0(A_73, k4_xboole_0(B_74, C_75)), k3_xboole_0(A_73, B_74)))), inference(superposition, [status(thm), theory('equality')], [c_343, c_10])).
% 3.09/1.50  tff(c_1095, plain, (r1_tarski('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_1037])).
% 3.09/1.50  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.09/1.50  tff(c_1129, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))='#skF_1'), inference(resolution, [status(thm)], [c_1095, c_8])).
% 3.09/1.50  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.09/1.50  tff(c_181, plain, (![A_38, B_39]: (k3_xboole_0(k3_xboole_0(A_38, B_39), A_38)=k3_xboole_0(A_38, B_39))), inference(resolution, [status(thm)], [c_6, c_74])).
% 3.09/1.50  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.09/1.50  tff(c_202, plain, (![A_38, B_39]: (k3_xboole_0(A_38, k3_xboole_0(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(superposition, [status(thm), theory('equality')], [c_181, c_2])).
% 3.09/1.50  tff(c_1142, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1129, c_202])).
% 3.09/1.50  tff(c_25, plain, (![B_25, A_26]: (k3_xboole_0(B_25, A_26)=k3_xboole_0(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.09/1.50  tff(c_40, plain, (![B_25, A_26]: (r1_tarski(k3_xboole_0(B_25, A_26), A_26))), inference(superposition, [status(thm), theory('equality')], [c_25, c_6])).
% 3.09/1.50  tff(c_1239, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1142, c_40])).
% 3.09/1.50  tff(c_1256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_1239])).
% 3.09/1.50  tff(c_1257, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_18])).
% 3.09/1.50  tff(c_1308, plain, (![A_80, B_81]: (k3_xboole_0(A_80, B_81)=A_80 | ~r1_tarski(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.09/1.50  tff(c_1328, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_20, c_1308])).
% 3.09/1.50  tff(c_1642, plain, (![A_95, B_96, C_97]: (k4_xboole_0(k3_xboole_0(A_95, B_96), C_97)=k3_xboole_0(A_95, k4_xboole_0(B_96, C_97)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.09/1.50  tff(c_16, plain, (![A_17, B_18]: (r1_xboole_0(k4_xboole_0(A_17, B_18), B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.09/1.50  tff(c_1676, plain, (![A_98, B_99, C_100]: (r1_xboole_0(k3_xboole_0(A_98, k4_xboole_0(B_99, C_100)), C_100))), inference(superposition, [status(thm), theory('equality')], [c_1642, c_16])).
% 3.09/1.50  tff(c_1694, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1328, c_1676])).
% 3.09/1.50  tff(c_1705, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1257, c_1694])).
% 3.09/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.50  
% 3.09/1.50  Inference rules
% 3.09/1.50  ----------------------
% 3.09/1.50  #Ref     : 0
% 3.09/1.50  #Sup     : 445
% 3.09/1.50  #Fact    : 0
% 3.09/1.50  #Define  : 0
% 3.09/1.50  #Split   : 1
% 3.09/1.50  #Chain   : 0
% 3.09/1.50  #Close   : 0
% 3.09/1.50  
% 3.09/1.50  Ordering : KBO
% 3.09/1.50  
% 3.09/1.50  Simplification rules
% 3.09/1.50  ----------------------
% 3.09/1.50  #Subsume      : 6
% 3.09/1.50  #Demod        : 304
% 3.09/1.50  #Tautology    : 246
% 3.09/1.50  #SimpNegUnit  : 2
% 3.09/1.50  #BackRed      : 3
% 3.09/1.50  
% 3.09/1.50  #Partial instantiations: 0
% 3.09/1.50  #Strategies tried      : 1
% 3.09/1.50  
% 3.09/1.50  Timing (in seconds)
% 3.09/1.50  ----------------------
% 3.09/1.51  Preprocessing        : 0.26
% 3.09/1.51  Parsing              : 0.14
% 3.09/1.51  CNF conversion       : 0.01
% 3.09/1.51  Main loop            : 0.47
% 3.09/1.51  Inferencing          : 0.15
% 3.09/1.51  Reduction            : 0.20
% 3.09/1.51  Demodulation         : 0.16
% 3.09/1.51  BG Simplification    : 0.02
% 3.09/1.51  Subsumption          : 0.06
% 3.09/1.51  Abstraction          : 0.03
% 3.09/1.51  MUC search           : 0.00
% 3.09/1.51  Cooper               : 0.00
% 3.09/1.51  Total                : 0.75
% 3.09/1.51  Index Insertion      : 0.00
% 3.09/1.51  Index Deletion       : 0.00
% 3.09/1.51  Index Matching       : 0.00
% 3.09/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
