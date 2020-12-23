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
% DateTime   : Thu Dec  3 09:43:41 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   59 (  90 expanded)
%              Number of leaves         :   24 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :   61 ( 115 expanded)
%              Number of equality atoms :   28 (  57 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,B)
          & r1_xboole_0(A,B)
          & r1_xboole_0(C,B) )
       => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_24,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    k2_xboole_0('#skF_5','#skF_4') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_31,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_30])).

tff(c_50,plain,(
    ! [B_27,A_28] : k2_xboole_0(B_27,A_28) = k2_xboole_0(A_28,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_22,B_23] : r1_tarski(A_22,k2_xboole_0(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_89,plain,(
    ! [A_29,B_30] : r1_tarski(A_29,k2_xboole_0(B_30,A_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_22])).

tff(c_98,plain,(
    r1_tarski('#skF_5',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_89])).

tff(c_14,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_26,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_116,plain,(
    ! [A_34,B_35,C_36] :
      ( ~ r1_xboole_0(A_34,B_35)
      | ~ r2_hidden(C_36,k3_xboole_0(A_34,B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_122,plain,(
    ! [A_37,B_38] :
      ( ~ r1_xboole_0(A_37,B_38)
      | k3_xboole_0(A_37,B_38) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_116])).

tff(c_129,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_122])).

tff(c_140,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k3_xboole_0(A_39,B_40)) = k4_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_149,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) = k4_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_140])).

tff(c_152,plain,(
    k4_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_149])).

tff(c_384,plain,(
    ! [A_47,B_48,C_49] :
      ( r1_tarski(k4_xboole_0(A_47,B_48),C_49)
      | ~ r1_tarski(A_47,k2_xboole_0(B_48,C_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_572,plain,(
    ! [C_56] :
      ( r1_tarski('#skF_5',C_56)
      | ~ r1_tarski('#skF_5',k2_xboole_0('#skF_4',C_56)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_384])).

tff(c_599,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_572])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( k2_xboole_0(A_10,B_11) = B_11
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_607,plain,(
    k2_xboole_0('#skF_5','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_599,c_10])).

tff(c_624,plain,(
    k2_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_607])).

tff(c_65,plain,(
    ! [A_28,B_27] : r1_tarski(A_28,k2_xboole_0(B_27,A_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_22])).

tff(c_28,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_130,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_122])).

tff(c_18,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k3_xboole_0(A_18,B_19)) = k4_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_163,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_18])).

tff(c_169,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_163])).

tff(c_756,plain,(
    ! [C_60] :
      ( r1_tarski('#skF_3',C_60)
      | ~ r1_tarski('#skF_3',k2_xboole_0('#skF_4',C_60)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_384])).

tff(c_783,plain,
    ( r1_tarski('#skF_3','#skF_5')
    | ~ r1_tarski('#skF_3',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_756])).

tff(c_787,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_783])).

tff(c_790,plain,(
    k2_xboole_0('#skF_3','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_787,c_10])).

tff(c_792,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_790])).

tff(c_794,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_792])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:18:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.34  
% 2.29/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.34  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.29/1.34  
% 2.29/1.34  %Foreground sorts:
% 2.29/1.34  
% 2.29/1.34  
% 2.29/1.34  %Background operators:
% 2.29/1.34  
% 2.29/1.34  
% 2.29/1.34  %Foreground operators:
% 2.29/1.34  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.29/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.29/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.29/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.29/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.29/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.29/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.29/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.29/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.29/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.29/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.29/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.29/1.34  
% 2.60/1.36  tff(f_76, negated_conjecture, ~(![A, B, C]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, B)) & r1_xboole_0(A, B)) & r1_xboole_0(C, B)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_xboole_1)).
% 2.60/1.36  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.60/1.36  tff(f_67, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.60/1.36  tff(f_57, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.60/1.36  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.60/1.36  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.60/1.36  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.60/1.36  tff(f_61, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.60/1.36  tff(f_53, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.60/1.36  tff(c_24, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.60/1.36  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.60/1.36  tff(c_30, plain, (k2_xboole_0('#skF_5', '#skF_4')=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.60/1.36  tff(c_31, plain, (k2_xboole_0('#skF_4', '#skF_5')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_30])).
% 2.60/1.36  tff(c_50, plain, (![B_27, A_28]: (k2_xboole_0(B_27, A_28)=k2_xboole_0(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.60/1.36  tff(c_22, plain, (![A_22, B_23]: (r1_tarski(A_22, k2_xboole_0(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.60/1.36  tff(c_89, plain, (![A_29, B_30]: (r1_tarski(A_29, k2_xboole_0(B_30, A_29)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_22])).
% 2.60/1.36  tff(c_98, plain, (r1_tarski('#skF_5', k2_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_31, c_89])).
% 2.60/1.36  tff(c_14, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.60/1.36  tff(c_26, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.60/1.36  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.60/1.36  tff(c_116, plain, (![A_34, B_35, C_36]: (~r1_xboole_0(A_34, B_35) | ~r2_hidden(C_36, k3_xboole_0(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.60/1.36  tff(c_122, plain, (![A_37, B_38]: (~r1_xboole_0(A_37, B_38) | k3_xboole_0(A_37, B_38)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_116])).
% 2.60/1.36  tff(c_129, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_122])).
% 2.60/1.36  tff(c_140, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k3_xboole_0(A_39, B_40))=k4_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.60/1.36  tff(c_149, plain, (k4_xboole_0('#skF_5', k1_xboole_0)=k4_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_129, c_140])).
% 2.60/1.36  tff(c_152, plain, (k4_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_149])).
% 2.60/1.36  tff(c_384, plain, (![A_47, B_48, C_49]: (r1_tarski(k4_xboole_0(A_47, B_48), C_49) | ~r1_tarski(A_47, k2_xboole_0(B_48, C_49)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.60/1.36  tff(c_572, plain, (![C_56]: (r1_tarski('#skF_5', C_56) | ~r1_tarski('#skF_5', k2_xboole_0('#skF_4', C_56)))), inference(superposition, [status(thm), theory('equality')], [c_152, c_384])).
% 2.60/1.36  tff(c_599, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_98, c_572])).
% 2.60/1.36  tff(c_10, plain, (![A_10, B_11]: (k2_xboole_0(A_10, B_11)=B_11 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.60/1.36  tff(c_607, plain, (k2_xboole_0('#skF_5', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_599, c_10])).
% 2.60/1.36  tff(c_624, plain, (k2_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2, c_607])).
% 2.60/1.36  tff(c_65, plain, (![A_28, B_27]: (r1_tarski(A_28, k2_xboole_0(B_27, A_28)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_22])).
% 2.60/1.36  tff(c_28, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.60/1.36  tff(c_130, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_122])).
% 2.60/1.36  tff(c_18, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k3_xboole_0(A_18, B_19))=k4_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.60/1.36  tff(c_163, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_130, c_18])).
% 2.60/1.36  tff(c_169, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_163])).
% 2.60/1.36  tff(c_756, plain, (![C_60]: (r1_tarski('#skF_3', C_60) | ~r1_tarski('#skF_3', k2_xboole_0('#skF_4', C_60)))), inference(superposition, [status(thm), theory('equality')], [c_169, c_384])).
% 2.60/1.36  tff(c_783, plain, (r1_tarski('#skF_3', '#skF_5') | ~r1_tarski('#skF_3', k2_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_31, c_756])).
% 2.60/1.36  tff(c_787, plain, (r1_tarski('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_783])).
% 2.60/1.36  tff(c_790, plain, (k2_xboole_0('#skF_3', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_787, c_10])).
% 2.60/1.36  tff(c_792, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_624, c_790])).
% 2.60/1.36  tff(c_794, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_792])).
% 2.60/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.36  
% 2.60/1.36  Inference rules
% 2.60/1.36  ----------------------
% 2.60/1.36  #Ref     : 0
% 2.60/1.36  #Sup     : 200
% 2.60/1.36  #Fact    : 0
% 2.60/1.36  #Define  : 0
% 2.60/1.36  #Split   : 0
% 2.60/1.36  #Chain   : 0
% 2.60/1.36  #Close   : 0
% 2.60/1.36  
% 2.60/1.36  Ordering : KBO
% 2.60/1.36  
% 2.60/1.36  Simplification rules
% 2.60/1.36  ----------------------
% 2.60/1.36  #Subsume      : 6
% 2.60/1.36  #Demod        : 100
% 2.60/1.36  #Tautology    : 130
% 2.60/1.36  #SimpNegUnit  : 6
% 2.60/1.36  #BackRed      : 1
% 2.60/1.36  
% 2.60/1.36  #Partial instantiations: 0
% 2.60/1.36  #Strategies tried      : 1
% 2.60/1.36  
% 2.60/1.36  Timing (in seconds)
% 2.60/1.36  ----------------------
% 2.60/1.36  Preprocessing        : 0.29
% 2.60/1.36  Parsing              : 0.16
% 2.60/1.36  CNF conversion       : 0.02
% 2.60/1.36  Main loop            : 0.31
% 2.60/1.36  Inferencing          : 0.11
% 2.60/1.36  Reduction            : 0.12
% 2.60/1.36  Demodulation         : 0.09
% 2.60/1.36  BG Simplification    : 0.01
% 2.60/1.36  Subsumption          : 0.04
% 2.60/1.36  Abstraction          : 0.01
% 2.60/1.36  MUC search           : 0.00
% 2.60/1.36  Cooper               : 0.00
% 2.66/1.36  Total                : 0.63
% 2.66/1.36  Index Insertion      : 0.00
% 2.66/1.36  Index Deletion       : 0.00
% 2.66/1.36  Index Matching       : 0.00
% 2.66/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
