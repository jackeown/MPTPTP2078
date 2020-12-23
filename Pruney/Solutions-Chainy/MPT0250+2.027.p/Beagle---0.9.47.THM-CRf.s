%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:35 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   49 (  51 expanded)
%              Number of leaves         :   26 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :   54 (  57 expanded)
%              Number of equality atoms :   16 (  17 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_62,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_78,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_48,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_44,plain,(
    ! [A_24,B_25] :
      ( r1_xboole_0(k1_tarski(A_24),B_25)
      | r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_55,plain,(
    ! [A_33] : k2_tarski(A_33,A_33) = k1_tarski(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_20,plain,(
    ! [D_15,A_10] : r2_hidden(D_15,k2_tarski(A_10,D_15)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_61,plain,(
    ! [A_33] : r2_hidden(A_33,k1_tarski(A_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_20])).

tff(c_14,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_132,plain,(
    ! [A_43,B_44] : k3_tarski(k2_tarski(A_43,B_44)) = k2_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_180,plain,(
    ! [A_49,B_50] : k3_tarski(k2_tarski(A_49,B_50)) = k2_xboole_0(B_50,A_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_132])).

tff(c_46,plain,(
    ! [A_26,B_27] : k3_tarski(k2_tarski(A_26,B_27)) = k2_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_186,plain,(
    ! [B_50,A_49] : k2_xboole_0(B_50,A_49) = k2_xboole_0(A_49,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_46])).

tff(c_50,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_3'),'#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_206,plain,(
    r1_tarski(k2_xboole_0('#skF_4',k1_tarski('#skF_3')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_50])).

tff(c_276,plain,(
    ! [B_58,A_59] :
      ( B_58 = A_59
      | ~ r1_tarski(B_58,A_59)
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_278,plain,
    ( k2_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_xboole_0('#skF_4',k1_tarski('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_206,c_276])).

tff(c_289,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_278])).

tff(c_10,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,C_5)
      | ~ r1_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_334,plain,(
    ! [A_63] :
      ( r1_xboole_0(A_63,k1_tarski('#skF_3'))
      | ~ r1_xboole_0(A_63,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_10])).

tff(c_42,plain,(
    ! [A_22,B_23] :
      ( ~ r2_hidden(A_22,B_23)
      | ~ r1_xboole_0(k1_tarski(A_22),B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_376,plain,(
    ! [A_71] :
      ( ~ r2_hidden(A_71,k1_tarski('#skF_3'))
      | ~ r1_xboole_0(k1_tarski(A_71),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_334,c_42])).

tff(c_381,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_61,c_376])).

tff(c_384,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_381])).

tff(c_388,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_384])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:11:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.26  
% 2.18/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.26  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.18/1.26  
% 2.18/1.26  %Foreground sorts:
% 2.18/1.26  
% 2.18/1.26  
% 2.18/1.26  %Background operators:
% 2.18/1.26  
% 2.18/1.26  
% 2.18/1.26  %Foreground operators:
% 2.18/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.18/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.18/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.18/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.18/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.18/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.18/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.18/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.18/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.18/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.18/1.26  
% 2.18/1.27  tff(f_83, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.18/1.27  tff(f_76, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.18/1.27  tff(f_62, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.18/1.27  tff(f_60, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.18/1.27  tff(f_49, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.18/1.27  tff(f_51, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.18/1.27  tff(f_78, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.18/1.27  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.18/1.27  tff(f_47, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 2.18/1.27  tff(f_71, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.18/1.27  tff(c_48, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.18/1.27  tff(c_44, plain, (![A_24, B_25]: (r1_xboole_0(k1_tarski(A_24), B_25) | r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.18/1.27  tff(c_55, plain, (![A_33]: (k2_tarski(A_33, A_33)=k1_tarski(A_33))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.18/1.27  tff(c_20, plain, (![D_15, A_10]: (r2_hidden(D_15, k2_tarski(A_10, D_15)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.18/1.27  tff(c_61, plain, (![A_33]: (r2_hidden(A_33, k1_tarski(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_55, c_20])).
% 2.18/1.27  tff(c_14, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.18/1.27  tff(c_16, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.18/1.27  tff(c_132, plain, (![A_43, B_44]: (k3_tarski(k2_tarski(A_43, B_44))=k2_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.18/1.27  tff(c_180, plain, (![A_49, B_50]: (k3_tarski(k2_tarski(A_49, B_50))=k2_xboole_0(B_50, A_49))), inference(superposition, [status(thm), theory('equality')], [c_16, c_132])).
% 2.18/1.27  tff(c_46, plain, (![A_26, B_27]: (k3_tarski(k2_tarski(A_26, B_27))=k2_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.18/1.27  tff(c_186, plain, (![B_50, A_49]: (k2_xboole_0(B_50, A_49)=k2_xboole_0(A_49, B_50))), inference(superposition, [status(thm), theory('equality')], [c_180, c_46])).
% 2.18/1.27  tff(c_50, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_3'), '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.18/1.27  tff(c_206, plain, (r1_tarski(k2_xboole_0('#skF_4', k1_tarski('#skF_3')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_186, c_50])).
% 2.18/1.27  tff(c_276, plain, (![B_58, A_59]: (B_58=A_59 | ~r1_tarski(B_58, A_59) | ~r1_tarski(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.18/1.27  tff(c_278, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', k2_xboole_0('#skF_4', k1_tarski('#skF_3')))), inference(resolution, [status(thm)], [c_206, c_276])).
% 2.18/1.27  tff(c_289, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_278])).
% 2.18/1.27  tff(c_10, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, C_5) | ~r1_xboole_0(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.18/1.27  tff(c_334, plain, (![A_63]: (r1_xboole_0(A_63, k1_tarski('#skF_3')) | ~r1_xboole_0(A_63, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_289, c_10])).
% 2.18/1.27  tff(c_42, plain, (![A_22, B_23]: (~r2_hidden(A_22, B_23) | ~r1_xboole_0(k1_tarski(A_22), B_23))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.18/1.27  tff(c_376, plain, (![A_71]: (~r2_hidden(A_71, k1_tarski('#skF_3')) | ~r1_xboole_0(k1_tarski(A_71), '#skF_4'))), inference(resolution, [status(thm)], [c_334, c_42])).
% 2.18/1.27  tff(c_381, plain, (~r1_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_61, c_376])).
% 2.18/1.27  tff(c_384, plain, (r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_381])).
% 2.18/1.27  tff(c_388, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_384])).
% 2.18/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.27  
% 2.18/1.27  Inference rules
% 2.18/1.27  ----------------------
% 2.18/1.27  #Ref     : 0
% 2.18/1.27  #Sup     : 81
% 2.18/1.27  #Fact    : 0
% 2.18/1.27  #Define  : 0
% 2.18/1.27  #Split   : 1
% 2.18/1.27  #Chain   : 0
% 2.18/1.27  #Close   : 0
% 2.18/1.27  
% 2.18/1.27  Ordering : KBO
% 2.18/1.27  
% 2.18/1.27  Simplification rules
% 2.18/1.27  ----------------------
% 2.18/1.27  #Subsume      : 8
% 2.18/1.27  #Demod        : 20
% 2.18/1.27  #Tautology    : 52
% 2.18/1.27  #SimpNegUnit  : 1
% 2.18/1.27  #BackRed      : 2
% 2.18/1.27  
% 2.18/1.27  #Partial instantiations: 0
% 2.18/1.27  #Strategies tried      : 1
% 2.18/1.27  
% 2.18/1.27  Timing (in seconds)
% 2.18/1.27  ----------------------
% 2.18/1.28  Preprocessing        : 0.30
% 2.18/1.28  Parsing              : 0.16
% 2.18/1.28  CNF conversion       : 0.02
% 2.18/1.28  Main loop            : 0.21
% 2.18/1.28  Inferencing          : 0.07
% 2.18/1.28  Reduction            : 0.08
% 2.18/1.28  Demodulation         : 0.06
% 2.18/1.28  BG Simplification    : 0.01
% 2.18/1.28  Subsumption          : 0.04
% 2.18/1.28  Abstraction          : 0.01
% 2.18/1.28  MUC search           : 0.00
% 2.18/1.28  Cooper               : 0.00
% 2.18/1.28  Total                : 0.54
% 2.18/1.28  Index Insertion      : 0.00
% 2.18/1.28  Index Deletion       : 0.00
% 2.18/1.28  Index Matching       : 0.00
% 2.18/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
