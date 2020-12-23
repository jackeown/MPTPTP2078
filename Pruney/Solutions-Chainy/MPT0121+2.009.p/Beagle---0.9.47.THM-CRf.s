%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:34 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   50 (  87 expanded)
%              Number of leaves         :   17 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :   63 ( 181 expanded)
%              Number of equality atoms :   18 (  32 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_xboole_0(A,D)
          & r1_xboole_0(B,D)
          & r1_xboole_0(C,D) )
       => r1_xboole_0(k2_xboole_0(k2_xboole_0(A,B),C),D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_89,plain,(
    ! [A_23,B_24,C_25] :
      ( ~ r1_xboole_0(A_23,B_24)
      | ~ r2_hidden(C_25,B_24)
      | ~ r2_hidden(C_25,A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_102,plain,(
    ! [C_26] :
      ( ~ r2_hidden(C_26,'#skF_5')
      | ~ r2_hidden(C_26,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_89])).

tff(c_135,plain,(
    ! [B_29] :
      ( ~ r2_hidden('#skF_1'('#skF_5',B_29),'#skF_4')
      | r1_xboole_0('#skF_5',B_29) ) ),
    inference(resolution,[status(thm)],[c_6,c_102])).

tff(c_140,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_135])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = A_9
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_147,plain,(
    k4_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_140,c_10])).

tff(c_20,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_124,plain,(
    ! [C_28] :
      ( ~ r2_hidden(C_28,'#skF_5')
      | ~ r2_hidden(C_28,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_89])).

tff(c_228,plain,(
    ! [B_37] :
      ( ~ r2_hidden('#skF_1'('#skF_5',B_37),'#skF_3')
      | r1_xboole_0('#skF_5',B_37) ) ),
    inference(resolution,[status(thm)],[c_6,c_124])).

tff(c_233,plain,(
    r1_xboole_0('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_228])).

tff(c_240,plain,(
    k4_xboole_0('#skF_5','#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_233,c_10])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] : k4_xboole_0(k4_xboole_0(A_6,B_7),C_8) = k4_xboole_0(A_6,k2_xboole_0(B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_244,plain,(
    ! [C_8] : k4_xboole_0('#skF_5',k2_xboole_0('#skF_3',C_8)) = k4_xboole_0('#skF_5',C_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_8])).

tff(c_22,plain,(
    r1_xboole_0('#skF_2','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_113,plain,(
    ! [C_27] :
      ( ~ r2_hidden(C_27,'#skF_5')
      | ~ r2_hidden(C_27,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_89])).

tff(c_294,plain,(
    ! [B_43] :
      ( ~ r2_hidden('#skF_1'('#skF_5',B_43),'#skF_2')
      | r1_xboole_0('#skF_5',B_43) ) ),
    inference(resolution,[status(thm)],[c_6,c_113])).

tff(c_299,plain,(
    r1_xboole_0('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_294])).

tff(c_306,plain,(
    k4_xboole_0('#skF_5','#skF_2') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_299,c_10])).

tff(c_310,plain,(
    ! [C_8] : k4_xboole_0('#skF_5',k2_xboole_0('#skF_2',C_8)) = k4_xboole_0('#skF_5',C_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_8])).

tff(c_166,plain,(
    ! [A_31,B_32,C_33] : k4_xboole_0(k4_xboole_0(A_31,B_32),C_33) = k4_xboole_0(A_31,k2_xboole_0(B_32,C_33)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_178,plain,(
    ! [A_6,B_7,C_8,C_33] : k4_xboole_0(k4_xboole_0(A_6,k2_xboole_0(B_7,C_8)),C_33) = k4_xboole_0(k4_xboole_0(A_6,B_7),k2_xboole_0(C_8,C_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_166])).

tff(c_196,plain,(
    ! [A_6,B_7,C_8,C_33] : k4_xboole_0(A_6,k2_xboole_0(k2_xboole_0(B_7,C_8),C_33)) = k4_xboole_0(A_6,k2_xboole_0(B_7,k2_xboole_0(C_8,C_33))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_178])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( r1_xboole_0(A_9,B_10)
      | k4_xboole_0(A_9,B_10) != A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_287,plain,(
    ! [C_40,B_41,A_42] :
      ( ~ r2_hidden(C_40,B_41)
      | ~ r2_hidden(C_40,A_42)
      | k4_xboole_0(A_42,B_41) != A_42 ) ),
    inference(resolution,[status(thm)],[c_12,c_89])).

tff(c_439,plain,(
    ! [A_56,B_57,A_58] :
      ( ~ r2_hidden('#skF_1'(A_56,B_57),A_58)
      | k4_xboole_0(A_58,A_56) != A_58
      | r1_xboole_0(A_56,B_57) ) ),
    inference(resolution,[status(thm)],[c_6,c_287])).

tff(c_463,plain,(
    ! [B_60,A_61] :
      ( k4_xboole_0(B_60,A_61) != B_60
      | r1_xboole_0(A_61,B_60) ) ),
    inference(resolution,[status(thm)],[c_4,c_439])).

tff(c_16,plain,(
    ~ r1_xboole_0(k2_xboole_0(k2_xboole_0('#skF_2','#skF_3'),'#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_474,plain,(
    k4_xboole_0('#skF_5',k2_xboole_0(k2_xboole_0('#skF_2','#skF_3'),'#skF_4')) != '#skF_5' ),
    inference(resolution,[status(thm)],[c_463,c_16])).

tff(c_525,plain,(
    k4_xboole_0('#skF_5',k2_xboole_0('#skF_2',k2_xboole_0('#skF_3','#skF_4'))) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_474])).

tff(c_528,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_244,c_310,c_525])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:32:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.46  
% 2.70/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.47  %$ r2_hidden > r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.70/1.47  
% 2.70/1.47  %Foreground sorts:
% 2.70/1.47  
% 2.70/1.47  
% 2.70/1.47  %Background operators:
% 2.70/1.47  
% 2.70/1.47  
% 2.70/1.47  %Foreground operators:
% 2.70/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.70/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.70/1.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.70/1.47  tff('#skF_5', type, '#skF_5': $i).
% 2.70/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.70/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.70/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.70/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.70/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.70/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.70/1.47  
% 2.70/1.48  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.70/1.48  tff(f_60, negated_conjecture, ~(![A, B, C, D]: (((r1_xboole_0(A, D) & r1_xboole_0(B, D)) & r1_xboole_0(C, D)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(A, B), C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_xboole_1)).
% 2.70/1.48  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.70/1.48  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.70/1.48  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.70/1.48  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.70/1.48  tff(c_18, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.70/1.48  tff(c_89, plain, (![A_23, B_24, C_25]: (~r1_xboole_0(A_23, B_24) | ~r2_hidden(C_25, B_24) | ~r2_hidden(C_25, A_23))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.70/1.48  tff(c_102, plain, (![C_26]: (~r2_hidden(C_26, '#skF_5') | ~r2_hidden(C_26, '#skF_4'))), inference(resolution, [status(thm)], [c_18, c_89])).
% 2.70/1.48  tff(c_135, plain, (![B_29]: (~r2_hidden('#skF_1'('#skF_5', B_29), '#skF_4') | r1_xboole_0('#skF_5', B_29))), inference(resolution, [status(thm)], [c_6, c_102])).
% 2.70/1.48  tff(c_140, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_4, c_135])).
% 2.70/1.48  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=A_9 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.70/1.48  tff(c_147, plain, (k4_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_140, c_10])).
% 2.70/1.48  tff(c_20, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.70/1.48  tff(c_124, plain, (![C_28]: (~r2_hidden(C_28, '#skF_5') | ~r2_hidden(C_28, '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_89])).
% 2.70/1.48  tff(c_228, plain, (![B_37]: (~r2_hidden('#skF_1'('#skF_5', B_37), '#skF_3') | r1_xboole_0('#skF_5', B_37))), inference(resolution, [status(thm)], [c_6, c_124])).
% 2.70/1.48  tff(c_233, plain, (r1_xboole_0('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_4, c_228])).
% 2.70/1.48  tff(c_240, plain, (k4_xboole_0('#skF_5', '#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_233, c_10])).
% 2.70/1.48  tff(c_8, plain, (![A_6, B_7, C_8]: (k4_xboole_0(k4_xboole_0(A_6, B_7), C_8)=k4_xboole_0(A_6, k2_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.70/1.48  tff(c_244, plain, (![C_8]: (k4_xboole_0('#skF_5', k2_xboole_0('#skF_3', C_8))=k4_xboole_0('#skF_5', C_8))), inference(superposition, [status(thm), theory('equality')], [c_240, c_8])).
% 2.70/1.48  tff(c_22, plain, (r1_xboole_0('#skF_2', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.70/1.48  tff(c_113, plain, (![C_27]: (~r2_hidden(C_27, '#skF_5') | ~r2_hidden(C_27, '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_89])).
% 2.70/1.48  tff(c_294, plain, (![B_43]: (~r2_hidden('#skF_1'('#skF_5', B_43), '#skF_2') | r1_xboole_0('#skF_5', B_43))), inference(resolution, [status(thm)], [c_6, c_113])).
% 2.70/1.48  tff(c_299, plain, (r1_xboole_0('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_4, c_294])).
% 2.70/1.48  tff(c_306, plain, (k4_xboole_0('#skF_5', '#skF_2')='#skF_5'), inference(resolution, [status(thm)], [c_299, c_10])).
% 2.70/1.48  tff(c_310, plain, (![C_8]: (k4_xboole_0('#skF_5', k2_xboole_0('#skF_2', C_8))=k4_xboole_0('#skF_5', C_8))), inference(superposition, [status(thm), theory('equality')], [c_306, c_8])).
% 2.70/1.48  tff(c_166, plain, (![A_31, B_32, C_33]: (k4_xboole_0(k4_xboole_0(A_31, B_32), C_33)=k4_xboole_0(A_31, k2_xboole_0(B_32, C_33)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.70/1.48  tff(c_178, plain, (![A_6, B_7, C_8, C_33]: (k4_xboole_0(k4_xboole_0(A_6, k2_xboole_0(B_7, C_8)), C_33)=k4_xboole_0(k4_xboole_0(A_6, B_7), k2_xboole_0(C_8, C_33)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_166])).
% 2.70/1.48  tff(c_196, plain, (![A_6, B_7, C_8, C_33]: (k4_xboole_0(A_6, k2_xboole_0(k2_xboole_0(B_7, C_8), C_33))=k4_xboole_0(A_6, k2_xboole_0(B_7, k2_xboole_0(C_8, C_33))))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_178])).
% 2.70/1.48  tff(c_12, plain, (![A_9, B_10]: (r1_xboole_0(A_9, B_10) | k4_xboole_0(A_9, B_10)!=A_9)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.70/1.48  tff(c_287, plain, (![C_40, B_41, A_42]: (~r2_hidden(C_40, B_41) | ~r2_hidden(C_40, A_42) | k4_xboole_0(A_42, B_41)!=A_42)), inference(resolution, [status(thm)], [c_12, c_89])).
% 2.70/1.48  tff(c_439, plain, (![A_56, B_57, A_58]: (~r2_hidden('#skF_1'(A_56, B_57), A_58) | k4_xboole_0(A_58, A_56)!=A_58 | r1_xboole_0(A_56, B_57))), inference(resolution, [status(thm)], [c_6, c_287])).
% 2.70/1.48  tff(c_463, plain, (![B_60, A_61]: (k4_xboole_0(B_60, A_61)!=B_60 | r1_xboole_0(A_61, B_60))), inference(resolution, [status(thm)], [c_4, c_439])).
% 2.70/1.48  tff(c_16, plain, (~r1_xboole_0(k2_xboole_0(k2_xboole_0('#skF_2', '#skF_3'), '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.70/1.48  tff(c_474, plain, (k4_xboole_0('#skF_5', k2_xboole_0(k2_xboole_0('#skF_2', '#skF_3'), '#skF_4'))!='#skF_5'), inference(resolution, [status(thm)], [c_463, c_16])).
% 2.70/1.48  tff(c_525, plain, (k4_xboole_0('#skF_5', k2_xboole_0('#skF_2', k2_xboole_0('#skF_3', '#skF_4')))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_196, c_474])).
% 2.70/1.48  tff(c_528, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_147, c_244, c_310, c_525])).
% 2.70/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.48  
% 2.70/1.48  Inference rules
% 2.70/1.48  ----------------------
% 2.70/1.48  #Ref     : 0
% 2.70/1.48  #Sup     : 139
% 2.70/1.48  #Fact    : 0
% 2.70/1.48  #Define  : 0
% 2.70/1.48  #Split   : 0
% 2.70/1.48  #Chain   : 0
% 2.70/1.48  #Close   : 0
% 2.70/1.48  
% 2.70/1.48  Ordering : KBO
% 2.70/1.48  
% 2.70/1.48  Simplification rules
% 2.70/1.48  ----------------------
% 2.70/1.48  #Subsume      : 4
% 2.70/1.48  #Demod        : 36
% 2.70/1.48  #Tautology    : 64
% 2.70/1.48  #SimpNegUnit  : 0
% 2.70/1.48  #BackRed      : 1
% 2.70/1.48  
% 2.70/1.48  #Partial instantiations: 0
% 2.70/1.48  #Strategies tried      : 1
% 2.70/1.48  
% 2.70/1.48  Timing (in seconds)
% 2.70/1.48  ----------------------
% 2.70/1.48  Preprocessing        : 0.25
% 2.70/1.48  Parsing              : 0.14
% 2.70/1.48  CNF conversion       : 0.02
% 2.70/1.49  Main loop            : 0.38
% 2.70/1.49  Inferencing          : 0.16
% 2.70/1.49  Reduction            : 0.11
% 2.70/1.49  Demodulation         : 0.08
% 2.70/1.49  BG Simplification    : 0.01
% 2.70/1.49  Subsumption          : 0.07
% 2.70/1.49  Abstraction          : 0.02
% 2.70/1.49  MUC search           : 0.00
% 2.70/1.49  Cooper               : 0.00
% 2.70/1.49  Total                : 0.68
% 2.70/1.49  Index Insertion      : 0.00
% 2.70/1.49  Index Deletion       : 0.00
% 2.70/1.49  Index Matching       : 0.00
% 2.70/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
