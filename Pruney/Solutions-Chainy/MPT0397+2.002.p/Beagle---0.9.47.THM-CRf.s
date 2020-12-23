%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:31 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   32 (  36 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  64 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_setfam_1 > r2_hidden > r1_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(r2_setfam_1,type,(
    r2_setfam_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_setfam_1(B,A)
       => ( A = k1_xboole_0
          | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_setfam_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(B,C) )
     => ( A = k1_xboole_0
        | r1_tarski(B,k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,B)
            & ! [D] :
                ~ ( r2_hidden(D,A)
                  & r1_tarski(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_setfam_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(k1_setfam_1(B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    r2_setfam_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_3'(A_13,B_14),A_13)
      | r1_tarski(B_14,k1_setfam_1(A_13))
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_1,B_2,C_11] :
      ( r2_hidden('#skF_2'(A_1,B_2,C_11),A_1)
      | ~ r2_hidden(C_11,B_2)
      | ~ r2_setfam_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,(
    ! [A_31,B_32,C_33] :
      ( r1_tarski('#skF_2'(A_31,B_32,C_33),C_33)
      | ~ r2_hidden(C_33,B_32)
      | ~ r2_setfam_1(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [B_17,C_18,A_16] :
      ( r1_tarski(k1_setfam_1(B_17),C_18)
      | ~ r1_tarski(A_16,C_18)
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_36,plain,(
    ! [B_37,C_38,A_39,B_40] :
      ( r1_tarski(k1_setfam_1(B_37),C_38)
      | ~ r2_hidden('#skF_2'(A_39,B_40,C_38),B_37)
      | ~ r2_hidden(C_38,B_40)
      | ~ r2_setfam_1(A_39,B_40) ) ),
    inference(resolution,[status(thm)],[c_26,c_14])).

tff(c_41,plain,(
    ! [A_41,C_42,B_43] :
      ( r1_tarski(k1_setfam_1(A_41),C_42)
      | ~ r2_hidden(C_42,B_43)
      | ~ r2_setfam_1(A_41,B_43) ) ),
    inference(resolution,[status(thm)],[c_4,c_36])).

tff(c_60,plain,(
    ! [A_50,A_51,B_52] :
      ( r1_tarski(k1_setfam_1(A_50),'#skF_3'(A_51,B_52))
      | ~ r2_setfam_1(A_50,A_51)
      | r1_tarski(B_52,k1_setfam_1(A_51))
      | k1_xboole_0 = A_51 ) ),
    inference(resolution,[status(thm)],[c_12,c_41])).

tff(c_10,plain,(
    ! [B_14,A_13] :
      ( ~ r1_tarski(B_14,'#skF_3'(A_13,B_14))
      | r1_tarski(B_14,k1_setfam_1(A_13))
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_74,plain,(
    ! [A_57,A_58] :
      ( ~ r2_setfam_1(A_57,A_58)
      | r1_tarski(k1_setfam_1(A_57),k1_setfam_1(A_58))
      | k1_xboole_0 = A_58 ) ),
    inference(resolution,[status(thm)],[c_60,c_10])).

tff(c_16,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_5'),k1_setfam_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_79,plain,
    ( ~ r2_setfam_1('#skF_5','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_74,c_16])).

tff(c_83,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_79])).

tff(c_85,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_83])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:27:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.17  
% 1.80/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.17  %$ r2_setfam_1 > r2_hidden > r1_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_4 > #skF_1
% 1.80/1.17  
% 1.80/1.17  %Foreground sorts:
% 1.80/1.17  
% 1.80/1.17  
% 1.80/1.17  %Background operators:
% 1.80/1.17  
% 1.80/1.17  
% 1.80/1.17  %Foreground operators:
% 1.80/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.80/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.80/1.17  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.80/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.80/1.17  tff('#skF_5', type, '#skF_5': $i).
% 1.80/1.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.80/1.17  tff(r2_setfam_1, type, r2_setfam_1: ($i * $i) > $o).
% 1.80/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.80/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.80/1.17  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.80/1.17  
% 1.86/1.18  tff(f_59, negated_conjecture, ~(![A, B]: (r2_setfam_1(B, A) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_setfam_1)).
% 1.86/1.18  tff(f_46, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(B, C))) => ((A = k1_xboole_0) | r1_tarski(B, k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_setfam_1)).
% 1.86/1.18  tff(f_37, axiom, (![A, B]: (r2_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, A) & r1_tarski(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_setfam_1)).
% 1.86/1.18  tff(f_52, axiom, (![A, B, C]: ((r2_hidden(A, B) & r1_tarski(A, C)) => r1_tarski(k1_setfam_1(B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_setfam_1)).
% 1.86/1.18  tff(c_18, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.86/1.18  tff(c_20, plain, (r2_setfam_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.86/1.18  tff(c_12, plain, (![A_13, B_14]: (r2_hidden('#skF_3'(A_13, B_14), A_13) | r1_tarski(B_14, k1_setfam_1(A_13)) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.86/1.18  tff(c_4, plain, (![A_1, B_2, C_11]: (r2_hidden('#skF_2'(A_1, B_2, C_11), A_1) | ~r2_hidden(C_11, B_2) | ~r2_setfam_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.86/1.18  tff(c_26, plain, (![A_31, B_32, C_33]: (r1_tarski('#skF_2'(A_31, B_32, C_33), C_33) | ~r2_hidden(C_33, B_32) | ~r2_setfam_1(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.86/1.18  tff(c_14, plain, (![B_17, C_18, A_16]: (r1_tarski(k1_setfam_1(B_17), C_18) | ~r1_tarski(A_16, C_18) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.86/1.18  tff(c_36, plain, (![B_37, C_38, A_39, B_40]: (r1_tarski(k1_setfam_1(B_37), C_38) | ~r2_hidden('#skF_2'(A_39, B_40, C_38), B_37) | ~r2_hidden(C_38, B_40) | ~r2_setfam_1(A_39, B_40))), inference(resolution, [status(thm)], [c_26, c_14])).
% 1.86/1.18  tff(c_41, plain, (![A_41, C_42, B_43]: (r1_tarski(k1_setfam_1(A_41), C_42) | ~r2_hidden(C_42, B_43) | ~r2_setfam_1(A_41, B_43))), inference(resolution, [status(thm)], [c_4, c_36])).
% 1.86/1.18  tff(c_60, plain, (![A_50, A_51, B_52]: (r1_tarski(k1_setfam_1(A_50), '#skF_3'(A_51, B_52)) | ~r2_setfam_1(A_50, A_51) | r1_tarski(B_52, k1_setfam_1(A_51)) | k1_xboole_0=A_51)), inference(resolution, [status(thm)], [c_12, c_41])).
% 1.86/1.18  tff(c_10, plain, (![B_14, A_13]: (~r1_tarski(B_14, '#skF_3'(A_13, B_14)) | r1_tarski(B_14, k1_setfam_1(A_13)) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.86/1.18  tff(c_74, plain, (![A_57, A_58]: (~r2_setfam_1(A_57, A_58) | r1_tarski(k1_setfam_1(A_57), k1_setfam_1(A_58)) | k1_xboole_0=A_58)), inference(resolution, [status(thm)], [c_60, c_10])).
% 1.86/1.18  tff(c_16, plain, (~r1_tarski(k1_setfam_1('#skF_5'), k1_setfam_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.86/1.18  tff(c_79, plain, (~r2_setfam_1('#skF_5', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_74, c_16])).
% 1.86/1.18  tff(c_83, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_79])).
% 1.86/1.18  tff(c_85, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_83])).
% 1.86/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.18  
% 1.86/1.18  Inference rules
% 1.86/1.18  ----------------------
% 1.86/1.18  #Ref     : 0
% 1.86/1.18  #Sup     : 13
% 1.86/1.18  #Fact    : 0
% 1.86/1.18  #Define  : 0
% 1.86/1.18  #Split   : 0
% 1.86/1.18  #Chain   : 0
% 1.86/1.18  #Close   : 0
% 1.86/1.18  
% 1.86/1.18  Ordering : KBO
% 1.86/1.18  
% 1.86/1.18  Simplification rules
% 1.86/1.18  ----------------------
% 1.86/1.18  #Subsume      : 0
% 1.86/1.18  #Demod        : 1
% 1.86/1.18  #Tautology    : 0
% 1.86/1.18  #SimpNegUnit  : 1
% 1.86/1.18  #BackRed      : 0
% 1.86/1.18  
% 1.86/1.18  #Partial instantiations: 0
% 1.86/1.18  #Strategies tried      : 1
% 1.86/1.18  
% 1.86/1.18  Timing (in seconds)
% 1.86/1.18  ----------------------
% 1.86/1.19  Preprocessing        : 0.29
% 1.86/1.19  Parsing              : 0.16
% 1.86/1.19  CNF conversion       : 0.02
% 1.86/1.19  Main loop            : 0.13
% 1.86/1.19  Inferencing          : 0.06
% 1.86/1.19  Reduction            : 0.03
% 1.86/1.19  Demodulation         : 0.02
% 1.86/1.19  BG Simplification    : 0.01
% 1.86/1.19  Subsumption          : 0.02
% 1.86/1.19  Abstraction          : 0.01
% 1.86/1.19  MUC search           : 0.00
% 1.86/1.19  Cooper               : 0.00
% 1.86/1.19  Total                : 0.44
% 1.86/1.19  Index Insertion      : 0.00
% 1.86/1.19  Index Deletion       : 0.00
% 1.86/1.19  Index Matching       : 0.00
% 1.86/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
