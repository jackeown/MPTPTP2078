%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:51 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :   43 (  51 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 (  71 expanded)
%              Number of equality atoms :   15 (  24 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(k1_mcart_1(A),B)
          & r2_hidden(k2_mcart_1(A),C) )
       => ( ! [D,E] : A != k4_tarski(D,E)
          | r2_hidden(A,k2_zfmisc_1(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_mcart_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
    <=> ( A = C
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_38,plain,(
    k4_tarski('#skF_6','#skF_7') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_47,plain,(
    ! [A_20,B_21] : k2_mcart_1(k4_tarski(A_20,B_21)) = B_21 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_56,plain,(
    k2_mcart_1('#skF_3') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_47])).

tff(c_40,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_71,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_40])).

tff(c_59,plain,(
    ! [A_22,B_23] : k1_mcart_1(k4_tarski(A_22,B_23)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_68,plain,(
    k1_mcart_1('#skF_3') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_59])).

tff(c_42,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_76,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_42])).

tff(c_109,plain,(
    ! [C_47,B_48,D_49] :
      ( r2_hidden(k4_tarski(C_47,B_48),k2_zfmisc_1(k1_tarski(C_47),D_49))
      | ~ r2_hidden(B_48,D_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_118,plain,(
    ! [D_49] :
      ( r2_hidden('#skF_3',k2_zfmisc_1(k1_tarski('#skF_6'),D_49))
      | ~ r2_hidden('#skF_7',D_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_109])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(k1_tarski(A_7),B_8) = B_8
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_144,plain,(
    ! [A_54,C_55,B_56] : k2_xboole_0(k2_zfmisc_1(A_54,C_55),k2_zfmisc_1(B_56,C_55)) = k2_zfmisc_1(k2_xboole_0(A_54,B_56),C_55) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( ~ r2_hidden(D_6,A_1)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_398,plain,(
    ! [D_78,A_79,C_80,B_81] :
      ( ~ r2_hidden(D_78,k2_zfmisc_1(A_79,C_80))
      | r2_hidden(D_78,k2_zfmisc_1(k2_xboole_0(A_79,B_81),C_80)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_6])).

tff(c_1371,plain,(
    ! [D_169,A_170,C_171,B_172] :
      ( ~ r2_hidden(D_169,k2_zfmisc_1(k1_tarski(A_170),C_171))
      | r2_hidden(D_169,k2_zfmisc_1(B_172,C_171))
      | ~ r2_hidden(A_170,B_172) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_398])).

tff(c_1400,plain,(
    ! [B_173,D_174] :
      ( r2_hidden('#skF_3',k2_zfmisc_1(B_173,D_174))
      | ~ r2_hidden('#skF_6',B_173)
      | ~ r2_hidden('#skF_7',D_174) ) ),
    inference(resolution,[status(thm)],[c_118,c_1371])).

tff(c_36,plain,(
    ~ r2_hidden('#skF_3',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1439,plain,
    ( ~ r2_hidden('#skF_6','#skF_4')
    | ~ r2_hidden('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_1400,c_36])).

tff(c_1472,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_76,c_1439])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:58:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.46/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.55  
% 3.46/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.56  %$ r2_hidden > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.46/1.56  
% 3.46/1.56  %Foreground sorts:
% 3.46/1.56  
% 3.46/1.56  
% 3.46/1.56  %Background operators:
% 3.46/1.56  
% 3.46/1.56  
% 3.46/1.56  %Foreground operators:
% 3.46/1.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.46/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.46/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.46/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.46/1.56  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.46/1.56  tff('#skF_7', type, '#skF_7': $i).
% 3.46/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.46/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.46/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.46/1.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.46/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.46/1.56  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.46/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.46/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.46/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.46/1.56  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.46/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.46/1.56  
% 3.46/1.56  tff(f_63, negated_conjecture, ~(![A, B, C]: ((r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)) => ((![D, E]: ~(A = k4_tarski(D, E))) | r2_hidden(A, k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_mcart_1)).
% 3.46/1.56  tff(f_52, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.46/1.56  tff(f_48, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 3.46/1.56  tff(f_38, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 3.46/1.56  tff(f_42, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 3.46/1.56  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.46/1.56  tff(c_38, plain, (k4_tarski('#skF_6', '#skF_7')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.46/1.56  tff(c_47, plain, (![A_20, B_21]: (k2_mcart_1(k4_tarski(A_20, B_21))=B_21)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.46/1.56  tff(c_56, plain, (k2_mcart_1('#skF_3')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_38, c_47])).
% 3.46/1.56  tff(c_40, plain, (r2_hidden(k2_mcart_1('#skF_3'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.46/1.56  tff(c_71, plain, (r2_hidden('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_40])).
% 3.46/1.56  tff(c_59, plain, (![A_22, B_23]: (k1_mcart_1(k4_tarski(A_22, B_23))=A_22)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.46/1.56  tff(c_68, plain, (k1_mcart_1('#skF_3')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_38, c_59])).
% 3.46/1.56  tff(c_42, plain, (r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.46/1.56  tff(c_76, plain, (r2_hidden('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_42])).
% 3.46/1.56  tff(c_109, plain, (![C_47, B_48, D_49]: (r2_hidden(k4_tarski(C_47, B_48), k2_zfmisc_1(k1_tarski(C_47), D_49)) | ~r2_hidden(B_48, D_49))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.46/1.56  tff(c_118, plain, (![D_49]: (r2_hidden('#skF_3', k2_zfmisc_1(k1_tarski('#skF_6'), D_49)) | ~r2_hidden('#skF_7', D_49))), inference(superposition, [status(thm), theory('equality')], [c_38, c_109])).
% 3.46/1.56  tff(c_20, plain, (![A_7, B_8]: (k2_xboole_0(k1_tarski(A_7), B_8)=B_8 | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.46/1.56  tff(c_144, plain, (![A_54, C_55, B_56]: (k2_xboole_0(k2_zfmisc_1(A_54, C_55), k2_zfmisc_1(B_56, C_55))=k2_zfmisc_1(k2_xboole_0(A_54, B_56), C_55))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.46/1.56  tff(c_6, plain, (![D_6, A_1, B_2]: (~r2_hidden(D_6, A_1) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.46/1.56  tff(c_398, plain, (![D_78, A_79, C_80, B_81]: (~r2_hidden(D_78, k2_zfmisc_1(A_79, C_80)) | r2_hidden(D_78, k2_zfmisc_1(k2_xboole_0(A_79, B_81), C_80)))), inference(superposition, [status(thm), theory('equality')], [c_144, c_6])).
% 3.46/1.56  tff(c_1371, plain, (![D_169, A_170, C_171, B_172]: (~r2_hidden(D_169, k2_zfmisc_1(k1_tarski(A_170), C_171)) | r2_hidden(D_169, k2_zfmisc_1(B_172, C_171)) | ~r2_hidden(A_170, B_172))), inference(superposition, [status(thm), theory('equality')], [c_20, c_398])).
% 3.46/1.56  tff(c_1400, plain, (![B_173, D_174]: (r2_hidden('#skF_3', k2_zfmisc_1(B_173, D_174)) | ~r2_hidden('#skF_6', B_173) | ~r2_hidden('#skF_7', D_174))), inference(resolution, [status(thm)], [c_118, c_1371])).
% 3.46/1.56  tff(c_36, plain, (~r2_hidden('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.46/1.56  tff(c_1439, plain, (~r2_hidden('#skF_6', '#skF_4') | ~r2_hidden('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_1400, c_36])).
% 3.46/1.56  tff(c_1472, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_76, c_1439])).
% 3.46/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.56  
% 3.46/1.56  Inference rules
% 3.46/1.56  ----------------------
% 3.46/1.56  #Ref     : 0
% 3.46/1.56  #Sup     : 366
% 3.46/1.56  #Fact    : 2
% 3.46/1.56  #Define  : 0
% 3.46/1.56  #Split   : 0
% 3.46/1.56  #Chain   : 0
% 3.46/1.56  #Close   : 0
% 3.46/1.57  
% 3.46/1.57  Ordering : KBO
% 3.46/1.57  
% 3.46/1.57  Simplification rules
% 3.46/1.57  ----------------------
% 3.46/1.57  #Subsume      : 69
% 3.46/1.57  #Demod        : 18
% 3.46/1.57  #Tautology    : 44
% 3.46/1.57  #SimpNegUnit  : 0
% 3.46/1.57  #BackRed      : 2
% 3.46/1.57  
% 3.46/1.57  #Partial instantiations: 0
% 3.46/1.57  #Strategies tried      : 1
% 3.46/1.57  
% 3.46/1.57  Timing (in seconds)
% 3.46/1.57  ----------------------
% 3.46/1.57  Preprocessing        : 0.28
% 3.46/1.57  Parsing              : 0.15
% 3.46/1.57  CNF conversion       : 0.02
% 3.46/1.57  Main loop            : 0.52
% 3.46/1.57  Inferencing          : 0.20
% 3.46/1.57  Reduction            : 0.15
% 3.46/1.57  Demodulation         : 0.11
% 3.46/1.57  BG Simplification    : 0.03
% 3.46/1.57  Subsumption          : 0.11
% 3.46/1.57  Abstraction          : 0.03
% 3.46/1.57  MUC search           : 0.00
% 3.46/1.57  Cooper               : 0.00
% 3.46/1.57  Total                : 0.83
% 3.46/1.57  Index Insertion      : 0.00
% 3.46/1.57  Index Deletion       : 0.00
% 3.46/1.57  Index Matching       : 0.00
% 3.46/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
