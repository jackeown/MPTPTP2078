%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:22 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   38 (  47 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   45 (  67 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_24,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_28,plain,(
    ! [A_18,B_19] :
      ( k2_xboole_0(A_18,B_19) = B_19
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_32,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_26,c_28])).

tff(c_53,plain,(
    ! [A_28,B_29] :
      ( r2_hidden('#skF_1'(A_28,B_29),A_28)
      | r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [C_15,A_11] :
      ( r1_tarski(C_15,A_11)
      | ~ r2_hidden(C_15,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_431,plain,(
    ! [A_59,B_60] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(A_59),B_60),A_59)
      | r1_tarski(k1_zfmisc_1(A_59),B_60) ) ),
    inference(resolution,[status(thm)],[c_53,c_12])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_586,plain,(
    ! [A_78,B_79] :
      ( k2_xboole_0('#skF_1'(k1_zfmisc_1(A_78),B_79),A_78) = A_78
      | r1_tarski(k1_zfmisc_1(A_78),B_79) ) ),
    inference(resolution,[status(thm)],[c_431,c_10])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_64,plain,(
    ! [A_30] : r1_tarski(A_30,A_30) ),
    inference(resolution,[status(thm)],[c_53,c_4])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(k2_xboole_0(A_6,B_7),C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_92,plain,(
    ! [A_32,B_33] : r1_tarski(A_32,k2_xboole_0(A_32,B_33)) ),
    inference(resolution,[status(thm)],[c_64,c_8])).

tff(c_111,plain,(
    ! [A_6,B_7,B_33] : r1_tarski(A_6,k2_xboole_0(k2_xboole_0(A_6,B_7),B_33)) ),
    inference(resolution,[status(thm)],[c_92,c_8])).

tff(c_832,plain,(
    ! [A_104,B_105,B_106] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(A_104),B_105),k2_xboole_0(A_104,B_106))
      | r1_tarski(k1_zfmisc_1(A_104),B_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_586,c_111])).

tff(c_14,plain,(
    ! [C_15,A_11] :
      ( r2_hidden(C_15,k1_zfmisc_1(A_11))
      | ~ r1_tarski(C_15,A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_42,plain,(
    ! [A_22,B_23] :
      ( ~ r2_hidden('#skF_1'(A_22,B_23),B_23)
      | r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_47,plain,(
    ! [A_22,A_11] :
      ( r1_tarski(A_22,k1_zfmisc_1(A_11))
      | ~ r1_tarski('#skF_1'(A_22,k1_zfmisc_1(A_11)),A_11) ) ),
    inference(resolution,[status(thm)],[c_14,c_42])).

tff(c_863,plain,(
    ! [A_107,B_108] : r1_tarski(k1_zfmisc_1(A_107),k1_zfmisc_1(k2_xboole_0(A_107,B_108))) ),
    inference(resolution,[status(thm)],[c_832,c_47])).

tff(c_889,plain,(
    r1_tarski(k1_zfmisc_1('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_863])).

tff(c_895,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_889])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:17:26 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.31  
% 2.16/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.31  %$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 2.16/1.31  
% 2.16/1.31  %Foreground sorts:
% 2.16/1.31  
% 2.16/1.31  
% 2.16/1.31  %Background operators:
% 2.16/1.31  
% 2.16/1.31  
% 2.16/1.31  %Foreground operators:
% 2.16/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.31  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.16/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.16/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.16/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.16/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.16/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.16/1.31  
% 2.16/1.32  tff(f_52, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.16/1.32  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.16/1.32  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.16/1.32  tff(f_47, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.16/1.32  tff(f_36, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.16/1.32  tff(c_24, plain, (~r1_tarski(k1_zfmisc_1('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.16/1.32  tff(c_26, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.16/1.32  tff(c_28, plain, (![A_18, B_19]: (k2_xboole_0(A_18, B_19)=B_19 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.16/1.32  tff(c_32, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_26, c_28])).
% 2.16/1.32  tff(c_53, plain, (![A_28, B_29]: (r2_hidden('#skF_1'(A_28, B_29), A_28) | r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.16/1.32  tff(c_12, plain, (![C_15, A_11]: (r1_tarski(C_15, A_11) | ~r2_hidden(C_15, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.16/1.32  tff(c_431, plain, (![A_59, B_60]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_59), B_60), A_59) | r1_tarski(k1_zfmisc_1(A_59), B_60))), inference(resolution, [status(thm)], [c_53, c_12])).
% 2.16/1.32  tff(c_10, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.16/1.32  tff(c_586, plain, (![A_78, B_79]: (k2_xboole_0('#skF_1'(k1_zfmisc_1(A_78), B_79), A_78)=A_78 | r1_tarski(k1_zfmisc_1(A_78), B_79))), inference(resolution, [status(thm)], [c_431, c_10])).
% 2.16/1.32  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.16/1.32  tff(c_64, plain, (![A_30]: (r1_tarski(A_30, A_30))), inference(resolution, [status(thm)], [c_53, c_4])).
% 2.16/1.32  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(k2_xboole_0(A_6, B_7), C_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.16/1.32  tff(c_92, plain, (![A_32, B_33]: (r1_tarski(A_32, k2_xboole_0(A_32, B_33)))), inference(resolution, [status(thm)], [c_64, c_8])).
% 2.16/1.32  tff(c_111, plain, (![A_6, B_7, B_33]: (r1_tarski(A_6, k2_xboole_0(k2_xboole_0(A_6, B_7), B_33)))), inference(resolution, [status(thm)], [c_92, c_8])).
% 2.16/1.32  tff(c_832, plain, (![A_104, B_105, B_106]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_104), B_105), k2_xboole_0(A_104, B_106)) | r1_tarski(k1_zfmisc_1(A_104), B_105))), inference(superposition, [status(thm), theory('equality')], [c_586, c_111])).
% 2.16/1.32  tff(c_14, plain, (![C_15, A_11]: (r2_hidden(C_15, k1_zfmisc_1(A_11)) | ~r1_tarski(C_15, A_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.16/1.32  tff(c_42, plain, (![A_22, B_23]: (~r2_hidden('#skF_1'(A_22, B_23), B_23) | r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.16/1.32  tff(c_47, plain, (![A_22, A_11]: (r1_tarski(A_22, k1_zfmisc_1(A_11)) | ~r1_tarski('#skF_1'(A_22, k1_zfmisc_1(A_11)), A_11))), inference(resolution, [status(thm)], [c_14, c_42])).
% 2.16/1.32  tff(c_863, plain, (![A_107, B_108]: (r1_tarski(k1_zfmisc_1(A_107), k1_zfmisc_1(k2_xboole_0(A_107, B_108))))), inference(resolution, [status(thm)], [c_832, c_47])).
% 2.16/1.32  tff(c_889, plain, (r1_tarski(k1_zfmisc_1('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_863])).
% 2.16/1.32  tff(c_895, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_889])).
% 2.16/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.32  
% 2.16/1.32  Inference rules
% 2.16/1.32  ----------------------
% 2.16/1.32  #Ref     : 0
% 2.16/1.32  #Sup     : 196
% 2.16/1.32  #Fact    : 0
% 2.16/1.32  #Define  : 0
% 2.16/1.32  #Split   : 0
% 2.16/1.32  #Chain   : 0
% 2.16/1.32  #Close   : 0
% 2.16/1.32  
% 2.16/1.32  Ordering : KBO
% 2.16/1.33  
% 2.16/1.33  Simplification rules
% 2.16/1.33  ----------------------
% 2.16/1.33  #Subsume      : 21
% 2.16/1.33  #Demod        : 102
% 2.16/1.33  #Tautology    : 102
% 2.16/1.33  #SimpNegUnit  : 1
% 2.16/1.33  #BackRed      : 0
% 2.16/1.33  
% 2.16/1.33  #Partial instantiations: 0
% 2.16/1.33  #Strategies tried      : 1
% 2.16/1.33  
% 2.16/1.33  Timing (in seconds)
% 2.16/1.33  ----------------------
% 2.61/1.33  Preprocessing        : 0.25
% 2.61/1.33  Parsing              : 0.14
% 2.61/1.33  CNF conversion       : 0.02
% 2.61/1.33  Main loop            : 0.33
% 2.61/1.33  Inferencing          : 0.13
% 2.61/1.33  Reduction            : 0.10
% 2.61/1.33  Demodulation         : 0.08
% 2.61/1.33  BG Simplification    : 0.02
% 2.61/1.33  Subsumption          : 0.06
% 2.61/1.33  Abstraction          : 0.02
% 2.61/1.33  MUC search           : 0.00
% 2.61/1.33  Cooper               : 0.00
% 2.61/1.33  Total                : 0.61
% 2.61/1.33  Index Insertion      : 0.00
% 2.61/1.33  Index Deletion       : 0.00
% 2.61/1.33  Index Matching       : 0.00
% 2.61/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
