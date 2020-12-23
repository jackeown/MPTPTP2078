%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:31 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   49 (  56 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :   60 (  78 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ~ ( r1_tarski(C,A)
            & r1_tarski(C,B)
            & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_53,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_26,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_22,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_129,plain,(
    ! [A_33,C_34,B_35] :
      ( r1_xboole_0(A_33,C_34)
      | ~ r1_xboole_0(B_35,C_34)
      | ~ r1_tarski(A_33,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_142,plain,(
    ! [A_37] :
      ( r1_xboole_0(A_37,'#skF_4')
      | ~ r1_tarski(A_37,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_129])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_156,plain,(
    ! [A_39] :
      ( r1_xboole_0('#skF_4',A_39)
      | ~ r1_tarski(A_39,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_142,c_6])).

tff(c_18,plain,(
    ! [A_16,C_18,B_17] :
      ( r1_xboole_0(A_16,C_18)
      | ~ r1_xboole_0(B_17,C_18)
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_428,plain,(
    ! [A_71,A_72] :
      ( r1_xboole_0(A_71,A_72)
      | ~ r1_tarski(A_71,'#skF_4')
      | ~ r1_tarski(A_72,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_156,c_18])).

tff(c_14,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_57,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_72,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_57])).

tff(c_76,plain,(
    ! [A_28] : k4_xboole_0(A_28,A_28) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_72])).

tff(c_16,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_81,plain,(
    ! [A_28] : k4_xboole_0(A_28,k1_xboole_0) = k3_xboole_0(A_28,A_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_16])).

tff(c_93,plain,(
    ! [A_28] : k3_xboole_0(A_28,A_28) = A_28 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_81])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_116,plain,(
    ! [A_30,B_31,C_32] :
      ( ~ r1_xboole_0(A_30,B_31)
      | ~ r2_hidden(C_32,k3_xboole_0(A_30,B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_280,plain,(
    ! [A_57,B_58] :
      ( ~ r1_xboole_0(A_57,B_58)
      | v1_xboole_0(k3_xboole_0(A_57,B_58)) ) ),
    inference(resolution,[status(thm)],[c_4,c_116])).

tff(c_286,plain,(
    ! [A_28] :
      ( ~ r1_xboole_0(A_28,A_28)
      | v1_xboole_0(A_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_280])).

tff(c_452,plain,(
    ! [A_75] :
      ( v1_xboole_0(A_75)
      | ~ r1_tarski(A_75,'#skF_4')
      | ~ r1_tarski(A_75,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_428,c_286])).

tff(c_455,plain,
    ( v1_xboole_0('#skF_5')
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_452])).

tff(c_458,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_455])).

tff(c_460,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_458])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:06:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.32  
% 2.12/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.33  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.12/1.33  
% 2.12/1.33  %Foreground sorts:
% 2.12/1.33  
% 2.12/1.33  
% 2.12/1.33  %Background operators:
% 2.12/1.33  
% 2.12/1.33  
% 2.12/1.33  %Foreground operators:
% 2.12/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.12/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.12/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.12/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.12/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.12/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.12/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.12/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.12/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.12/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.12/1.33  
% 2.12/1.34  tff(f_72, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_xboole_1)).
% 2.12/1.34  tff(f_61, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.12/1.34  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.12/1.34  tff(f_53, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.12/1.34  tff(f_51, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.12/1.34  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.12/1.34  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.12/1.34  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.12/1.34  tff(c_26, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.12/1.34  tff(c_22, plain, (r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.12/1.34  tff(c_24, plain, (r1_tarski('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.12/1.34  tff(c_20, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.12/1.34  tff(c_129, plain, (![A_33, C_34, B_35]: (r1_xboole_0(A_33, C_34) | ~r1_xboole_0(B_35, C_34) | ~r1_tarski(A_33, B_35))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.12/1.34  tff(c_142, plain, (![A_37]: (r1_xboole_0(A_37, '#skF_4') | ~r1_tarski(A_37, '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_129])).
% 2.12/1.34  tff(c_6, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.12/1.34  tff(c_156, plain, (![A_39]: (r1_xboole_0('#skF_4', A_39) | ~r1_tarski(A_39, '#skF_3'))), inference(resolution, [status(thm)], [c_142, c_6])).
% 2.12/1.34  tff(c_18, plain, (![A_16, C_18, B_17]: (r1_xboole_0(A_16, C_18) | ~r1_xboole_0(B_17, C_18) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.12/1.34  tff(c_428, plain, (![A_71, A_72]: (r1_xboole_0(A_71, A_72) | ~r1_tarski(A_71, '#skF_4') | ~r1_tarski(A_72, '#skF_3'))), inference(resolution, [status(thm)], [c_156, c_18])).
% 2.12/1.34  tff(c_14, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.12/1.34  tff(c_12, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.12/1.34  tff(c_57, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.12/1.34  tff(c_72, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_57])).
% 2.12/1.34  tff(c_76, plain, (![A_28]: (k4_xboole_0(A_28, A_28)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_72])).
% 2.12/1.34  tff(c_16, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.12/1.34  tff(c_81, plain, (![A_28]: (k4_xboole_0(A_28, k1_xboole_0)=k3_xboole_0(A_28, A_28))), inference(superposition, [status(thm), theory('equality')], [c_76, c_16])).
% 2.12/1.34  tff(c_93, plain, (![A_28]: (k3_xboole_0(A_28, A_28)=A_28)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_81])).
% 2.12/1.34  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.12/1.34  tff(c_116, plain, (![A_30, B_31, C_32]: (~r1_xboole_0(A_30, B_31) | ~r2_hidden(C_32, k3_xboole_0(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.12/1.34  tff(c_280, plain, (![A_57, B_58]: (~r1_xboole_0(A_57, B_58) | v1_xboole_0(k3_xboole_0(A_57, B_58)))), inference(resolution, [status(thm)], [c_4, c_116])).
% 2.12/1.34  tff(c_286, plain, (![A_28]: (~r1_xboole_0(A_28, A_28) | v1_xboole_0(A_28))), inference(superposition, [status(thm), theory('equality')], [c_93, c_280])).
% 2.12/1.34  tff(c_452, plain, (![A_75]: (v1_xboole_0(A_75) | ~r1_tarski(A_75, '#skF_4') | ~r1_tarski(A_75, '#skF_3'))), inference(resolution, [status(thm)], [c_428, c_286])).
% 2.12/1.34  tff(c_455, plain, (v1_xboole_0('#skF_5') | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_24, c_452])).
% 2.12/1.34  tff(c_458, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_455])).
% 2.12/1.34  tff(c_460, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_458])).
% 2.12/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.34  
% 2.12/1.34  Inference rules
% 2.12/1.34  ----------------------
% 2.12/1.34  #Ref     : 0
% 2.12/1.34  #Sup     : 102
% 2.12/1.34  #Fact    : 0
% 2.12/1.34  #Define  : 0
% 2.12/1.34  #Split   : 5
% 2.12/1.34  #Chain   : 0
% 2.12/1.34  #Close   : 0
% 2.12/1.34  
% 2.12/1.34  Ordering : KBO
% 2.12/1.34  
% 2.12/1.34  Simplification rules
% 2.12/1.34  ----------------------
% 2.12/1.34  #Subsume      : 25
% 2.12/1.34  #Demod        : 20
% 2.12/1.34  #Tautology    : 33
% 2.12/1.34  #SimpNegUnit  : 2
% 2.12/1.34  #BackRed      : 0
% 2.12/1.34  
% 2.12/1.34  #Partial instantiations: 0
% 2.12/1.34  #Strategies tried      : 1
% 2.12/1.34  
% 2.12/1.34  Timing (in seconds)
% 2.12/1.34  ----------------------
% 2.12/1.34  Preprocessing        : 0.26
% 2.12/1.34  Parsing              : 0.15
% 2.12/1.34  CNF conversion       : 0.02
% 2.12/1.34  Main loop            : 0.26
% 2.12/1.34  Inferencing          : 0.11
% 2.12/1.34  Reduction            : 0.07
% 2.12/1.34  Demodulation         : 0.05
% 2.12/1.34  BG Simplification    : 0.01
% 2.12/1.34  Subsumption          : 0.05
% 2.12/1.34  Abstraction          : 0.01
% 2.12/1.34  MUC search           : 0.00
% 2.12/1.34  Cooper               : 0.00
% 2.12/1.34  Total                : 0.55
% 2.12/1.34  Index Insertion      : 0.00
% 2.12/1.34  Index Deletion       : 0.00
% 2.12/1.34  Index Matching       : 0.00
% 2.12/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
