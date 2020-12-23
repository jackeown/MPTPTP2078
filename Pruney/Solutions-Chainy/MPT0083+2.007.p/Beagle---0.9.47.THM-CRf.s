%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:02 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   45 (  61 expanded)
%              Number of leaves         :   19 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   46 (  64 expanded)
%              Number of equality atoms :   24 (  39 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(k3_xboole_0(C,A),k3_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_14,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_65,plain,(
    ! [B_22,A_23] : k3_xboole_0(B_22,A_23) = k3_xboole_0(A_23,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_87,plain,(
    ! [A_23] : k3_xboole_0(k1_xboole_0,A_23) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_10])).

tff(c_403,plain,(
    ! [A_47,B_48,C_49] : k4_xboole_0(k3_xboole_0(A_47,B_48),C_49) = k3_xboole_0(A_47,k4_xboole_0(B_48,C_49)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_441,plain,(
    ! [A_23,C_49] : k3_xboole_0(k1_xboole_0,k4_xboole_0(A_23,C_49)) = k4_xboole_0(k1_xboole_0,C_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_403])).

tff(c_460,plain,(
    ! [C_49] : k4_xboole_0(k1_xboole_0,C_49) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_441])).

tff(c_26,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_199,plain,(
    ! [A_29,B_30] :
      ( k3_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_xboole_0(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_207,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_199])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1862,plain,(
    ! [B_93,A_94,C_95] : k4_xboole_0(k3_xboole_0(B_93,A_94),C_95) = k3_xboole_0(A_94,k4_xboole_0(B_93,C_95)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_403])).

tff(c_1955,plain,(
    ! [C_95] : k3_xboole_0('#skF_2',k4_xboole_0('#skF_1',C_95)) = k4_xboole_0(k1_xboole_0,C_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_1862])).

tff(c_2002,plain,(
    ! [C_96] : k3_xboole_0('#skF_2',k4_xboole_0('#skF_1',C_96)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_1955])).

tff(c_2059,plain,(
    ! [B_10] : k3_xboole_0('#skF_2',k3_xboole_0('#skF_1',B_10)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2002])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_315,plain,(
    ! [A_36,C_37,B_38] :
      ( r1_xboole_0(A_36,C_37)
      | ~ r1_xboole_0(A_36,k2_xboole_0(B_38,C_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_504,plain,(
    ! [A_51,A_52,B_53] :
      ( r1_xboole_0(A_51,k3_xboole_0(A_52,B_53))
      | ~ r1_xboole_0(A_51,A_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_315])).

tff(c_792,plain,(
    ! [A_62,B_63,A_64] :
      ( r1_xboole_0(A_62,k3_xboole_0(B_63,A_64))
      | ~ r1_xboole_0(A_62,A_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_504])).

tff(c_24,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_3','#skF_1'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_27,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_24])).

tff(c_830,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_792,c_27])).

tff(c_889,plain,(
    k3_xboole_0(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_830])).

tff(c_891,plain,(
    k3_xboole_0('#skF_2',k3_xboole_0('#skF_1','#skF_3')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_889])).

tff(c_2151,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2059,c_891])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:38:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.21/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.51  
% 3.21/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.52  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.36/1.52  
% 3.36/1.52  %Foreground sorts:
% 3.36/1.52  
% 3.36/1.52  
% 3.36/1.52  %Background operators:
% 3.36/1.52  
% 3.36/1.52  
% 3.36/1.52  %Foreground operators:
% 3.36/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.36/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.36/1.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.36/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.36/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.36/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.36/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.36/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.36/1.52  
% 3.36/1.53  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.36/1.53  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.36/1.53  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.36/1.53  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.36/1.53  tff(f_62, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(k3_xboole_0(C, A), k3_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_xboole_1)).
% 3.36/1.53  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.36/1.53  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 3.36/1.53  tff(f_57, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.36/1.53  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.36/1.53  tff(c_65, plain, (![B_22, A_23]: (k3_xboole_0(B_22, A_23)=k3_xboole_0(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.36/1.53  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.36/1.53  tff(c_87, plain, (![A_23]: (k3_xboole_0(k1_xboole_0, A_23)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_65, c_10])).
% 3.36/1.53  tff(c_403, plain, (![A_47, B_48, C_49]: (k4_xboole_0(k3_xboole_0(A_47, B_48), C_49)=k3_xboole_0(A_47, k4_xboole_0(B_48, C_49)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.36/1.53  tff(c_441, plain, (![A_23, C_49]: (k3_xboole_0(k1_xboole_0, k4_xboole_0(A_23, C_49))=k4_xboole_0(k1_xboole_0, C_49))), inference(superposition, [status(thm), theory('equality')], [c_87, c_403])).
% 3.36/1.53  tff(c_460, plain, (![C_49]: (k4_xboole_0(k1_xboole_0, C_49)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_87, c_441])).
% 3.36/1.53  tff(c_26, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.36/1.53  tff(c_199, plain, (![A_29, B_30]: (k3_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.36/1.53  tff(c_207, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_199])).
% 3.36/1.53  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.36/1.53  tff(c_1862, plain, (![B_93, A_94, C_95]: (k4_xboole_0(k3_xboole_0(B_93, A_94), C_95)=k3_xboole_0(A_94, k4_xboole_0(B_93, C_95)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_403])).
% 3.36/1.53  tff(c_1955, plain, (![C_95]: (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', C_95))=k4_xboole_0(k1_xboole_0, C_95))), inference(superposition, [status(thm), theory('equality')], [c_207, c_1862])).
% 3.36/1.53  tff(c_2002, plain, (![C_96]: (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', C_96))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_460, c_1955])).
% 3.36/1.53  tff(c_2059, plain, (![B_10]: (k3_xboole_0('#skF_2', k3_xboole_0('#skF_1', B_10))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_2002])).
% 3.36/1.53  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.36/1.53  tff(c_8, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k3_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.36/1.53  tff(c_315, plain, (![A_36, C_37, B_38]: (r1_xboole_0(A_36, C_37) | ~r1_xboole_0(A_36, k2_xboole_0(B_38, C_37)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.36/1.53  tff(c_504, plain, (![A_51, A_52, B_53]: (r1_xboole_0(A_51, k3_xboole_0(A_52, B_53)) | ~r1_xboole_0(A_51, A_52))), inference(superposition, [status(thm), theory('equality')], [c_8, c_315])).
% 3.36/1.53  tff(c_792, plain, (![A_62, B_63, A_64]: (r1_xboole_0(A_62, k3_xboole_0(B_63, A_64)) | ~r1_xboole_0(A_62, A_64))), inference(superposition, [status(thm), theory('equality')], [c_2, c_504])).
% 3.36/1.53  tff(c_24, plain, (~r1_xboole_0(k3_xboole_0('#skF_3', '#skF_1'), k3_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.36/1.53  tff(c_27, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_24])).
% 3.36/1.53  tff(c_830, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_792, c_27])).
% 3.36/1.53  tff(c_889, plain, (k3_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_830])).
% 3.36/1.53  tff(c_891, plain, (k3_xboole_0('#skF_2', k3_xboole_0('#skF_1', '#skF_3'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_889])).
% 3.36/1.53  tff(c_2151, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2059, c_891])).
% 3.36/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.53  
% 3.36/1.53  Inference rules
% 3.36/1.53  ----------------------
% 3.36/1.53  #Ref     : 0
% 3.36/1.53  #Sup     : 526
% 3.36/1.53  #Fact    : 0
% 3.36/1.53  #Define  : 0
% 3.36/1.53  #Split   : 0
% 3.36/1.53  #Chain   : 0
% 3.36/1.53  #Close   : 0
% 3.36/1.53  
% 3.36/1.53  Ordering : KBO
% 3.36/1.53  
% 3.36/1.53  Simplification rules
% 3.36/1.53  ----------------------
% 3.36/1.53  #Subsume      : 15
% 3.36/1.53  #Demod        : 431
% 3.36/1.53  #Tautology    : 405
% 3.36/1.53  #SimpNegUnit  : 0
% 3.36/1.53  #BackRed      : 1
% 3.36/1.53  
% 3.36/1.53  #Partial instantiations: 0
% 3.36/1.53  #Strategies tried      : 1
% 3.36/1.53  
% 3.36/1.53  Timing (in seconds)
% 3.36/1.53  ----------------------
% 3.36/1.53  Preprocessing        : 0.29
% 3.36/1.53  Parsing              : 0.16
% 3.36/1.53  CNF conversion       : 0.02
% 3.36/1.53  Main loop            : 0.48
% 3.36/1.53  Inferencing          : 0.16
% 3.36/1.53  Reduction            : 0.20
% 3.36/1.53  Demodulation         : 0.16
% 3.36/1.53  BG Simplification    : 0.02
% 3.36/1.53  Subsumption          : 0.07
% 3.36/1.53  Abstraction          : 0.02
% 3.36/1.53  MUC search           : 0.00
% 3.36/1.53  Cooper               : 0.00
% 3.36/1.53  Total                : 0.79
% 3.36/1.53  Index Insertion      : 0.00
% 3.36/1.53  Index Deletion       : 0.00
% 3.36/1.53  Index Matching       : 0.00
% 3.36/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
