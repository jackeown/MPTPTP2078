%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:39 EST 2020

% Result     : Theorem 6.43s
% Output     : CNFRefutation 6.43s
% Verified   : 
% Statistics : Number of formulae       :   40 (  62 expanded)
%              Number of leaves         :   16 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   63 ( 128 expanded)
%              Number of equality atoms :    1 (   3 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_xboole_1)).

tff(c_33,plain,(
    ! [A_18,B_19] :
      ( r2_hidden('#skF_1'(A_18,B_19),A_18)
      | r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_91,plain,(
    ! [A_32,B_33,B_34] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_32,B_33),B_34),A_32)
      | r1_tarski(k3_xboole_0(A_32,B_33),B_34) ) ),
    inference(resolution,[status(thm)],[c_33,c_12])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_107,plain,(
    ! [A_32,B_33] : r1_tarski(k3_xboole_0(A_32,B_33),A_32) ),
    inference(resolution,[status(thm)],[c_91,c_4])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_111,plain,(
    ! [A_37,B_38,B_39] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_37,B_38),B_39),B_38)
      | r1_tarski(k3_xboole_0(A_37,B_38),B_39) ) ),
    inference(resolution,[status(thm)],[c_33,c_10])).

tff(c_127,plain,(
    ! [A_37,B_38] : r1_tarski(k3_xboole_0(A_37,B_38),B_38) ),
    inference(resolution,[status(thm)],[c_111,c_4])).

tff(c_30,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_51,plain,(
    ! [C_23,B_24,A_25] :
      ( r2_hidden(C_23,B_24)
      | ~ r2_hidden(C_23,A_25)
      | ~ r1_tarski(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_72,plain,(
    ! [A_29,B_30,B_31] :
      ( r2_hidden('#skF_1'(A_29,B_30),B_31)
      | ~ r1_tarski(A_29,B_31)
      | r1_tarski(A_29,B_30) ) ),
    inference(resolution,[status(thm)],[c_6,c_51])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_222,plain,(
    ! [A_60,B_61,B_62,B_63] :
      ( r2_hidden('#skF_1'(A_60,B_61),B_62)
      | ~ r1_tarski(B_63,B_62)
      | ~ r1_tarski(A_60,B_63)
      | r1_tarski(A_60,B_61) ) ),
    inference(resolution,[status(thm)],[c_72,c_2])).

tff(c_237,plain,(
    ! [A_60,B_61] :
      ( r2_hidden('#skF_1'(A_60,B_61),'#skF_5')
      | ~ r1_tarski(A_60,'#skF_4')
      | r1_tarski(A_60,B_61) ) ),
    inference(resolution,[status(thm)],[c_30,c_222])).

tff(c_28,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_236,plain,(
    ! [A_60,B_61] :
      ( r2_hidden('#skF_1'(A_60,B_61),'#skF_7')
      | ~ r1_tarski(A_60,'#skF_6')
      | r1_tarski(A_60,B_61) ) ),
    inference(resolution,[status(thm)],[c_28,c_222])).

tff(c_55,plain,(
    ! [D_26,A_27,B_28] :
      ( r2_hidden(D_26,k3_xboole_0(A_27,B_28))
      | ~ r2_hidden(D_26,B_28)
      | ~ r2_hidden(D_26,A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3029,plain,(
    ! [A_309,A_310,B_311] :
      ( r1_tarski(A_309,k3_xboole_0(A_310,B_311))
      | ~ r2_hidden('#skF_1'(A_309,k3_xboole_0(A_310,B_311)),B_311)
      | ~ r2_hidden('#skF_1'(A_309,k3_xboole_0(A_310,B_311)),A_310) ) ),
    inference(resolution,[status(thm)],[c_55,c_4])).

tff(c_4580,plain,(
    ! [A_352,A_353] :
      ( ~ r2_hidden('#skF_1'(A_352,k3_xboole_0(A_353,'#skF_7')),A_353)
      | ~ r1_tarski(A_352,'#skF_6')
      | r1_tarski(A_352,k3_xboole_0(A_353,'#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_236,c_3029])).

tff(c_4758,plain,(
    ! [A_355] :
      ( ~ r1_tarski(A_355,'#skF_6')
      | ~ r1_tarski(A_355,'#skF_4')
      | r1_tarski(A_355,k3_xboole_0('#skF_5','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_237,c_4580])).

tff(c_26,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_6'),k3_xboole_0('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4808,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_6'),'#skF_6')
    | ~ r1_tarski(k3_xboole_0('#skF_4','#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_4758,c_26])).

tff(c_4836,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_127,c_4808])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:26:51 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.43/2.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.43/2.29  
% 6.43/2.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.43/2.29  %$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 6.43/2.29  
% 6.43/2.29  %Foreground sorts:
% 6.43/2.29  
% 6.43/2.29  
% 6.43/2.29  %Background operators:
% 6.43/2.29  
% 6.43/2.29  
% 6.43/2.29  %Foreground operators:
% 6.43/2.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.43/2.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.43/2.29  tff('#skF_7', type, '#skF_7': $i).
% 6.43/2.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.43/2.29  tff('#skF_5', type, '#skF_5': $i).
% 6.43/2.29  tff('#skF_6', type, '#skF_6': $i).
% 6.43/2.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.43/2.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.43/2.29  tff('#skF_4', type, '#skF_4': $i).
% 6.43/2.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.43/2.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.43/2.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.43/2.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.43/2.29  
% 6.43/2.30  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.43/2.30  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 6.43/2.30  tff(f_48, negated_conjecture, ~(![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k3_xboole_0(A, C), k3_xboole_0(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_xboole_1)).
% 6.43/2.30  tff(c_33, plain, (![A_18, B_19]: (r2_hidden('#skF_1'(A_18, B_19), A_18) | r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.43/2.30  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.43/2.30  tff(c_91, plain, (![A_32, B_33, B_34]: (r2_hidden('#skF_1'(k3_xboole_0(A_32, B_33), B_34), A_32) | r1_tarski(k3_xboole_0(A_32, B_33), B_34))), inference(resolution, [status(thm)], [c_33, c_12])).
% 6.43/2.30  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.43/2.30  tff(c_107, plain, (![A_32, B_33]: (r1_tarski(k3_xboole_0(A_32, B_33), A_32))), inference(resolution, [status(thm)], [c_91, c_4])).
% 6.43/2.30  tff(c_10, plain, (![D_11, B_7, A_6]: (r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.43/2.30  tff(c_111, plain, (![A_37, B_38, B_39]: (r2_hidden('#skF_1'(k3_xboole_0(A_37, B_38), B_39), B_38) | r1_tarski(k3_xboole_0(A_37, B_38), B_39))), inference(resolution, [status(thm)], [c_33, c_10])).
% 6.43/2.30  tff(c_127, plain, (![A_37, B_38]: (r1_tarski(k3_xboole_0(A_37, B_38), B_38))), inference(resolution, [status(thm)], [c_111, c_4])).
% 6.43/2.30  tff(c_30, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.43/2.30  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.43/2.30  tff(c_51, plain, (![C_23, B_24, A_25]: (r2_hidden(C_23, B_24) | ~r2_hidden(C_23, A_25) | ~r1_tarski(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.43/2.30  tff(c_72, plain, (![A_29, B_30, B_31]: (r2_hidden('#skF_1'(A_29, B_30), B_31) | ~r1_tarski(A_29, B_31) | r1_tarski(A_29, B_30))), inference(resolution, [status(thm)], [c_6, c_51])).
% 6.43/2.30  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.43/2.30  tff(c_222, plain, (![A_60, B_61, B_62, B_63]: (r2_hidden('#skF_1'(A_60, B_61), B_62) | ~r1_tarski(B_63, B_62) | ~r1_tarski(A_60, B_63) | r1_tarski(A_60, B_61))), inference(resolution, [status(thm)], [c_72, c_2])).
% 6.43/2.30  tff(c_237, plain, (![A_60, B_61]: (r2_hidden('#skF_1'(A_60, B_61), '#skF_5') | ~r1_tarski(A_60, '#skF_4') | r1_tarski(A_60, B_61))), inference(resolution, [status(thm)], [c_30, c_222])).
% 6.43/2.30  tff(c_28, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.43/2.30  tff(c_236, plain, (![A_60, B_61]: (r2_hidden('#skF_1'(A_60, B_61), '#skF_7') | ~r1_tarski(A_60, '#skF_6') | r1_tarski(A_60, B_61))), inference(resolution, [status(thm)], [c_28, c_222])).
% 6.43/2.30  tff(c_55, plain, (![D_26, A_27, B_28]: (r2_hidden(D_26, k3_xboole_0(A_27, B_28)) | ~r2_hidden(D_26, B_28) | ~r2_hidden(D_26, A_27))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.43/2.30  tff(c_3029, plain, (![A_309, A_310, B_311]: (r1_tarski(A_309, k3_xboole_0(A_310, B_311)) | ~r2_hidden('#skF_1'(A_309, k3_xboole_0(A_310, B_311)), B_311) | ~r2_hidden('#skF_1'(A_309, k3_xboole_0(A_310, B_311)), A_310))), inference(resolution, [status(thm)], [c_55, c_4])).
% 6.43/2.30  tff(c_4580, plain, (![A_352, A_353]: (~r2_hidden('#skF_1'(A_352, k3_xboole_0(A_353, '#skF_7')), A_353) | ~r1_tarski(A_352, '#skF_6') | r1_tarski(A_352, k3_xboole_0(A_353, '#skF_7')))), inference(resolution, [status(thm)], [c_236, c_3029])).
% 6.43/2.30  tff(c_4758, plain, (![A_355]: (~r1_tarski(A_355, '#skF_6') | ~r1_tarski(A_355, '#skF_4') | r1_tarski(A_355, k3_xboole_0('#skF_5', '#skF_7')))), inference(resolution, [status(thm)], [c_237, c_4580])).
% 6.43/2.30  tff(c_26, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_6'), k3_xboole_0('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.43/2.30  tff(c_4808, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_6'), '#skF_6') | ~r1_tarski(k3_xboole_0('#skF_4', '#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_4758, c_26])).
% 6.43/2.30  tff(c_4836, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_127, c_4808])).
% 6.43/2.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.43/2.30  
% 6.43/2.30  Inference rules
% 6.43/2.30  ----------------------
% 6.43/2.30  #Ref     : 0
% 6.43/2.30  #Sup     : 1308
% 6.43/2.31  #Fact    : 0
% 6.43/2.31  #Define  : 0
% 6.43/2.31  #Split   : 5
% 6.43/2.31  #Chain   : 0
% 6.43/2.31  #Close   : 0
% 6.43/2.31  
% 6.43/2.31  Ordering : KBO
% 6.43/2.31  
% 6.43/2.31  Simplification rules
% 6.43/2.31  ----------------------
% 6.43/2.31  #Subsume      : 457
% 6.43/2.31  #Demod        : 103
% 6.43/2.31  #Tautology    : 42
% 6.43/2.31  #SimpNegUnit  : 0
% 6.43/2.31  #BackRed      : 1
% 6.43/2.31  
% 6.43/2.31  #Partial instantiations: 0
% 6.43/2.31  #Strategies tried      : 1
% 6.43/2.31  
% 6.43/2.31  Timing (in seconds)
% 6.43/2.31  ----------------------
% 6.78/2.31  Preprocessing        : 0.26
% 6.78/2.31  Parsing              : 0.14
% 6.78/2.31  CNF conversion       : 0.02
% 6.78/2.31  Main loop            : 1.29
% 6.78/2.31  Inferencing          : 0.36
% 6.78/2.31  Reduction            : 0.28
% 6.78/2.31  Demodulation         : 0.18
% 6.78/2.31  BG Simplification    : 0.04
% 6.78/2.31  Subsumption          : 0.53
% 6.78/2.31  Abstraction          : 0.06
% 6.78/2.31  MUC search           : 0.00
% 6.78/2.31  Cooper               : 0.00
% 6.78/2.31  Total                : 1.58
% 6.78/2.31  Index Insertion      : 0.00
% 6.78/2.31  Index Deletion       : 0.00
% 6.78/2.31  Index Matching       : 0.00
% 6.78/2.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
