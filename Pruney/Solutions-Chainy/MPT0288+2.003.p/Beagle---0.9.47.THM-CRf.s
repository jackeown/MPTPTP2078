%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:31 EST 2020

% Result     : Theorem 3.90s
% Output     : CNFRefutation 3.99s
% Verified   : 
% Statistics : Number of formulae       :   39 (  46 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  66 expanded)
%              Number of equality atoms :    6 (   9 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(c_44,plain,(
    ~ r1_tarski(k3_tarski('#skF_4'),k3_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_42,plain,(
    ! [A_20,B_21] :
      ( r2_hidden('#skF_3'(A_20,B_21),A_20)
      | r1_tarski(k3_tarski(A_20),B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_46,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_89,plain,(
    ! [A_31,B_32] :
      ( k4_xboole_0(A_31,B_32) = k1_xboole_0
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_109,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_89])).

tff(c_988,plain,(
    ! [D_83,A_84,B_85] :
      ( r2_hidden(D_83,k4_xboole_0(A_84,B_85))
      | r2_hidden(D_83,B_85)
      | ~ r2_hidden(D_83,A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1056,plain,(
    ! [D_89] :
      ( r2_hidden(D_89,k1_xboole_0)
      | r2_hidden(D_89,'#skF_5')
      | ~ r2_hidden(D_89,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_988])).

tff(c_26,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_107,plain,(
    ! [B_10] : k4_xboole_0(B_10,B_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_89])).

tff(c_188,plain,(
    ! [D_39,A_40,B_41] :
      ( r2_hidden(D_39,A_40)
      | ~ r2_hidden(D_39,k4_xboole_0(A_40,B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_197,plain,(
    ! [D_39,B_10] :
      ( r2_hidden(D_39,B_10)
      | ~ r2_hidden(D_39,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_188])).

tff(c_1062,plain,(
    ! [D_89,B_10] :
      ( r2_hidden(D_89,B_10)
      | r2_hidden(D_89,'#skF_5')
      | ~ r2_hidden(D_89,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1056,c_197])).

tff(c_1457,plain,(
    ! [D_89] :
      ( ~ r2_hidden(D_89,'#skF_4')
      | r2_hidden(D_89,'#skF_5') ) ),
    inference(factorization,[status(thm),theory(equality)],[c_1062])).

tff(c_38,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,k3_tarski(B_19))
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_572,plain,(
    ! [A_64,B_65] :
      ( ~ r1_tarski('#skF_3'(A_64,B_65),B_65)
      | r1_tarski(k3_tarski(A_64),B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2876,plain,(
    ! [A_160,B_161] :
      ( r1_tarski(k3_tarski(A_160),k3_tarski(B_161))
      | ~ r2_hidden('#skF_3'(A_160,k3_tarski(B_161)),B_161) ) ),
    inference(resolution,[status(thm)],[c_38,c_572])).

tff(c_3086,plain,(
    ! [A_164] :
      ( r1_tarski(k3_tarski(A_164),k3_tarski('#skF_5'))
      | ~ r2_hidden('#skF_3'(A_164,k3_tarski('#skF_5')),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1457,c_2876])).

tff(c_3093,plain,(
    r1_tarski(k3_tarski('#skF_4'),k3_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_42,c_3086])).

tff(c_3097,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_44,c_3093])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:23:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.90/1.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.99/1.69  
% 3.99/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.99/1.69  %$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 3.99/1.69  
% 3.99/1.69  %Foreground sorts:
% 3.99/1.69  
% 3.99/1.69  
% 3.99/1.69  %Background operators:
% 3.99/1.69  
% 3.99/1.69  
% 3.99/1.69  %Foreground operators:
% 3.99/1.69  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.99/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.99/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.99/1.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.99/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.99/1.69  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.99/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.99/1.69  tff('#skF_5', type, '#skF_5': $i).
% 3.99/1.69  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.99/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.99/1.69  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.99/1.69  tff('#skF_4', type, '#skF_4': $i).
% 3.99/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.99/1.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.99/1.69  
% 3.99/1.70  tff(f_69, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 3.99/1.70  tff(f_64, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 3.99/1.70  tff(f_47, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.99/1.70  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.99/1.70  tff(f_43, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.99/1.70  tff(f_57, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 3.99/1.70  tff(c_44, plain, (~r1_tarski(k3_tarski('#skF_4'), k3_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.99/1.70  tff(c_42, plain, (![A_20, B_21]: (r2_hidden('#skF_3'(A_20, B_21), A_20) | r1_tarski(k3_tarski(A_20), B_21))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.99/1.70  tff(c_46, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.99/1.70  tff(c_89, plain, (![A_31, B_32]: (k4_xboole_0(A_31, B_32)=k1_xboole_0 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.99/1.70  tff(c_109, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_89])).
% 3.99/1.70  tff(c_988, plain, (![D_83, A_84, B_85]: (r2_hidden(D_83, k4_xboole_0(A_84, B_85)) | r2_hidden(D_83, B_85) | ~r2_hidden(D_83, A_84))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.99/1.70  tff(c_1056, plain, (![D_89]: (r2_hidden(D_89, k1_xboole_0) | r2_hidden(D_89, '#skF_5') | ~r2_hidden(D_89, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_988])).
% 3.99/1.70  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.99/1.70  tff(c_107, plain, (![B_10]: (k4_xboole_0(B_10, B_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_89])).
% 3.99/1.70  tff(c_188, plain, (![D_39, A_40, B_41]: (r2_hidden(D_39, A_40) | ~r2_hidden(D_39, k4_xboole_0(A_40, B_41)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.99/1.70  tff(c_197, plain, (![D_39, B_10]: (r2_hidden(D_39, B_10) | ~r2_hidden(D_39, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_107, c_188])).
% 3.99/1.70  tff(c_1062, plain, (![D_89, B_10]: (r2_hidden(D_89, B_10) | r2_hidden(D_89, '#skF_5') | ~r2_hidden(D_89, '#skF_4'))), inference(resolution, [status(thm)], [c_1056, c_197])).
% 3.99/1.70  tff(c_1457, plain, (![D_89]: (~r2_hidden(D_89, '#skF_4') | r2_hidden(D_89, '#skF_5'))), inference(factorization, [status(thm), theory('equality')], [c_1062])).
% 3.99/1.70  tff(c_38, plain, (![A_18, B_19]: (r1_tarski(A_18, k3_tarski(B_19)) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.99/1.70  tff(c_572, plain, (![A_64, B_65]: (~r1_tarski('#skF_3'(A_64, B_65), B_65) | r1_tarski(k3_tarski(A_64), B_65))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.99/1.70  tff(c_2876, plain, (![A_160, B_161]: (r1_tarski(k3_tarski(A_160), k3_tarski(B_161)) | ~r2_hidden('#skF_3'(A_160, k3_tarski(B_161)), B_161))), inference(resolution, [status(thm)], [c_38, c_572])).
% 3.99/1.70  tff(c_3086, plain, (![A_164]: (r1_tarski(k3_tarski(A_164), k3_tarski('#skF_5')) | ~r2_hidden('#skF_3'(A_164, k3_tarski('#skF_5')), '#skF_4'))), inference(resolution, [status(thm)], [c_1457, c_2876])).
% 3.99/1.70  tff(c_3093, plain, (r1_tarski(k3_tarski('#skF_4'), k3_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_42, c_3086])).
% 3.99/1.70  tff(c_3097, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_44, c_3093])).
% 3.99/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.99/1.70  
% 3.99/1.70  Inference rules
% 3.99/1.70  ----------------------
% 3.99/1.70  #Ref     : 0
% 3.99/1.70  #Sup     : 703
% 3.99/1.70  #Fact    : 2
% 3.99/1.70  #Define  : 0
% 3.99/1.70  #Split   : 3
% 3.99/1.70  #Chain   : 0
% 3.99/1.70  #Close   : 0
% 3.99/1.70  
% 3.99/1.70  Ordering : KBO
% 3.99/1.70  
% 3.99/1.70  Simplification rules
% 3.99/1.70  ----------------------
% 3.99/1.70  #Subsume      : 150
% 3.99/1.70  #Demod        : 471
% 3.99/1.70  #Tautology    : 366
% 3.99/1.70  #SimpNegUnit  : 1
% 3.99/1.70  #BackRed      : 14
% 3.99/1.70  
% 3.99/1.70  #Partial instantiations: 0
% 3.99/1.70  #Strategies tried      : 1
% 3.99/1.70  
% 3.99/1.70  Timing (in seconds)
% 3.99/1.70  ----------------------
% 3.99/1.70  Preprocessing        : 0.30
% 3.99/1.70  Parsing              : 0.16
% 3.99/1.70  CNF conversion       : 0.02
% 3.99/1.70  Main loop            : 0.65
% 3.99/1.70  Inferencing          : 0.23
% 3.99/1.70  Reduction            : 0.23
% 3.99/1.70  Demodulation         : 0.18
% 3.99/1.70  BG Simplification    : 0.03
% 3.99/1.70  Subsumption          : 0.12
% 3.99/1.70  Abstraction          : 0.03
% 3.99/1.70  MUC search           : 0.00
% 3.99/1.70  Cooper               : 0.00
% 3.99/1.70  Total                : 0.97
% 3.99/1.70  Index Insertion      : 0.00
% 3.99/1.70  Index Deletion       : 0.00
% 3.99/1.70  Index Matching       : 0.00
% 3.99/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
