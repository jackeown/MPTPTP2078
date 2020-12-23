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
% DateTime   : Thu Dec  3 10:09:56 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   33 (  47 expanded)
%              Number of leaves         :   16 (  25 expanded)
%              Depth                    :    5
%              Number of atoms          :   37 (  68 expanded)
%              Number of equality atoms :   21 (  40 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(B,C))
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_mcart_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(c_10,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_11,plain,(
    k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_8])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( k4_tarski('#skF_1'(A_1,B_2,C_3),'#skF_2'(A_1,B_2,C_3)) = A_1
      | ~ r2_hidden(A_1,k2_zfmisc_1(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [A_15,B_16,C_17] :
      ( k4_tarski('#skF_1'(A_15,B_16,C_17),'#skF_2'(A_15,B_16,C_17)) = A_15
      | ~ r2_hidden(A_15,k2_zfmisc_1(B_16,C_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6,plain,(
    ! [B_9,C_10] : k1_mcart_1(k4_tarski(B_9,C_10)) != k4_tarski(B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_33,plain,(
    ! [A_18,B_19,C_20] :
      ( k4_tarski('#skF_1'(A_18,B_19,C_20),'#skF_2'(A_18,B_19,C_20)) != k1_mcart_1(A_18)
      | ~ r2_hidden(A_18,k2_zfmisc_1(B_19,C_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_6])).

tff(c_37,plain,(
    ! [A_21,B_22,C_23] :
      ( k1_mcart_1(A_21) != A_21
      | ~ r2_hidden(A_21,k2_zfmisc_1(B_22,C_23))
      | ~ r2_hidden(A_21,k2_zfmisc_1(B_22,C_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_33])).

tff(c_39,plain,
    ( k1_mcart_1('#skF_3') != '#skF_3'
    | ~ r2_hidden('#skF_3',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_10,c_37])).

tff(c_43,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_11,c_39])).

tff(c_44,plain,(
    k2_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_52,plain,(
    ! [A_28,B_29,C_30] :
      ( k4_tarski('#skF_1'(A_28,B_29,C_30),'#skF_2'(A_28,B_29,C_30)) = A_28
      | ~ r2_hidden(A_28,k2_zfmisc_1(B_29,C_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [B_9,C_10] : k2_mcart_1(k4_tarski(B_9,C_10)) != k4_tarski(B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_67,plain,(
    ! [A_31,B_32,C_33] :
      ( k4_tarski('#skF_1'(A_31,B_32,C_33),'#skF_2'(A_31,B_32,C_33)) != k2_mcart_1(A_31)
      | ~ r2_hidden(A_31,k2_zfmisc_1(B_32,C_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_4])).

tff(c_71,plain,(
    ! [A_34,B_35,C_36] :
      ( k2_mcart_1(A_34) != A_34
      | ~ r2_hidden(A_34,k2_zfmisc_1(B_35,C_36))
      | ~ r2_hidden(A_34,k2_zfmisc_1(B_35,C_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_67])).

tff(c_73,plain,
    ( k2_mcart_1('#skF_3') != '#skF_3'
    | ~ r2_hidden('#skF_3',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_10,c_71])).

tff(c_77,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_44,c_73])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 21:03:30 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.11  
% 1.61/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.12  %$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 1.61/1.12  
% 1.61/1.12  %Foreground sorts:
% 1.61/1.12  
% 1.61/1.12  
% 1.61/1.12  %Background operators:
% 1.61/1.12  
% 1.61/1.12  
% 1.61/1.12  %Foreground operators:
% 1.61/1.12  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.61/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.61/1.12  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.61/1.12  tff('#skF_5', type, '#skF_5': $i).
% 1.61/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.61/1.12  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.61/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.12  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.61/1.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.61/1.12  tff('#skF_4', type, '#skF_4': $i).
% 1.61/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.12  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.61/1.12  
% 1.61/1.13  tff(f_50, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_mcart_1)).
% 1.61/1.13  tff(f_32, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 1.61/1.13  tff(f_41, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 1.61/1.13  tff(c_10, plain, (r2_hidden('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.61/1.13  tff(c_8, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.61/1.13  tff(c_11, plain, (k1_mcart_1('#skF_3')='#skF_3'), inference(splitLeft, [status(thm)], [c_8])).
% 1.61/1.13  tff(c_2, plain, (![A_1, B_2, C_3]: (k4_tarski('#skF_1'(A_1, B_2, C_3), '#skF_2'(A_1, B_2, C_3))=A_1 | ~r2_hidden(A_1, k2_zfmisc_1(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.61/1.13  tff(c_18, plain, (![A_15, B_16, C_17]: (k4_tarski('#skF_1'(A_15, B_16, C_17), '#skF_2'(A_15, B_16, C_17))=A_15 | ~r2_hidden(A_15, k2_zfmisc_1(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.61/1.13  tff(c_6, plain, (![B_9, C_10]: (k1_mcart_1(k4_tarski(B_9, C_10))!=k4_tarski(B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.61/1.13  tff(c_33, plain, (![A_18, B_19, C_20]: (k4_tarski('#skF_1'(A_18, B_19, C_20), '#skF_2'(A_18, B_19, C_20))!=k1_mcart_1(A_18) | ~r2_hidden(A_18, k2_zfmisc_1(B_19, C_20)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_6])).
% 1.61/1.13  tff(c_37, plain, (![A_21, B_22, C_23]: (k1_mcart_1(A_21)!=A_21 | ~r2_hidden(A_21, k2_zfmisc_1(B_22, C_23)) | ~r2_hidden(A_21, k2_zfmisc_1(B_22, C_23)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_33])).
% 1.61/1.13  tff(c_39, plain, (k1_mcart_1('#skF_3')!='#skF_3' | ~r2_hidden('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_10, c_37])).
% 1.61/1.13  tff(c_43, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_11, c_39])).
% 1.61/1.13  tff(c_44, plain, (k2_mcart_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_8])).
% 1.61/1.13  tff(c_52, plain, (![A_28, B_29, C_30]: (k4_tarski('#skF_1'(A_28, B_29, C_30), '#skF_2'(A_28, B_29, C_30))=A_28 | ~r2_hidden(A_28, k2_zfmisc_1(B_29, C_30)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.61/1.13  tff(c_4, plain, (![B_9, C_10]: (k2_mcart_1(k4_tarski(B_9, C_10))!=k4_tarski(B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.61/1.13  tff(c_67, plain, (![A_31, B_32, C_33]: (k4_tarski('#skF_1'(A_31, B_32, C_33), '#skF_2'(A_31, B_32, C_33))!=k2_mcart_1(A_31) | ~r2_hidden(A_31, k2_zfmisc_1(B_32, C_33)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_4])).
% 1.61/1.13  tff(c_71, plain, (![A_34, B_35, C_36]: (k2_mcart_1(A_34)!=A_34 | ~r2_hidden(A_34, k2_zfmisc_1(B_35, C_36)) | ~r2_hidden(A_34, k2_zfmisc_1(B_35, C_36)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_67])).
% 1.61/1.13  tff(c_73, plain, (k2_mcart_1('#skF_3')!='#skF_3' | ~r2_hidden('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_10, c_71])).
% 1.61/1.13  tff(c_77, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_44, c_73])).
% 1.61/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.13  
% 1.61/1.13  Inference rules
% 1.61/1.13  ----------------------
% 1.61/1.13  #Ref     : 0
% 1.61/1.13  #Sup     : 16
% 1.61/1.13  #Fact    : 0
% 1.61/1.13  #Define  : 0
% 1.61/1.13  #Split   : 1
% 1.61/1.13  #Chain   : 0
% 1.61/1.13  #Close   : 0
% 1.61/1.13  
% 1.61/1.13  Ordering : KBO
% 1.61/1.13  
% 1.61/1.13  Simplification rules
% 1.61/1.13  ----------------------
% 1.61/1.13  #Subsume      : 0
% 1.61/1.13  #Demod        : 4
% 1.61/1.13  #Tautology    : 8
% 1.61/1.13  #SimpNegUnit  : 0
% 1.61/1.13  #BackRed      : 0
% 1.61/1.13  
% 1.61/1.13  #Partial instantiations: 0
% 1.61/1.13  #Strategies tried      : 1
% 1.61/1.13  
% 1.61/1.13  Timing (in seconds)
% 1.61/1.13  ----------------------
% 1.61/1.13  Preprocessing        : 0.27
% 1.61/1.13  Parsing              : 0.15
% 1.61/1.13  CNF conversion       : 0.02
% 1.61/1.13  Main loop            : 0.10
% 1.61/1.13  Inferencing          : 0.04
% 1.61/1.13  Reduction            : 0.02
% 1.61/1.13  Demodulation         : 0.02
% 1.61/1.13  BG Simplification    : 0.01
% 1.61/1.13  Subsumption          : 0.01
% 1.61/1.13  Abstraction          : 0.01
% 1.61/1.13  MUC search           : 0.00
% 1.61/1.13  Cooper               : 0.00
% 1.61/1.13  Total                : 0.40
% 1.61/1.13  Index Insertion      : 0.00
% 1.61/1.13  Index Deletion       : 0.00
% 1.61/1.13  Index Matching       : 0.00
% 1.61/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
