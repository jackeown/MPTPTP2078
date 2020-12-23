%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:50 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   35 (  38 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   50 (  63 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_52,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_121,plain,(
    ! [A_50,B_51] :
      ( r2_hidden('#skF_1'(A_50,B_51),B_51)
      | r2_hidden('#skF_2'(A_50,B_51),A_50)
      | B_51 = A_50 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_35,plain,(
    ! [A_26,C_27,B_28] :
      ( ~ r2_hidden(A_26,C_27)
      | ~ r1_xboole_0(k2_tarski(A_26,B_28),C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_40,plain,(
    ! [A_26] : ~ r2_hidden(A_26,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_35])).

tff(c_151,plain,(
    ! [B_51] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_51),B_51)
      | k1_xboole_0 = B_51 ) ),
    inference(resolution,[status(thm)],[c_121,c_40])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( r2_hidden('#skF_3'(A_4,B_5),B_5)
      | r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    ! [A_4,B_5] :
      ( r2_hidden('#skF_3'(A_4,B_5),A_4)
      | r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_81,plain,(
    ! [D_41,A_42,B_43] :
      ( ~ r2_hidden(D_41,'#skF_4'(A_42,B_43))
      | ~ r2_hidden(D_41,B_43)
      | ~ r2_hidden(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_209,plain,(
    ! [A_57,B_58,B_59] :
      ( ~ r2_hidden('#skF_3'('#skF_4'(A_57,B_58),B_59),B_58)
      | ~ r2_hidden(A_57,B_58)
      | r1_xboole_0('#skF_4'(A_57,B_58),B_59) ) ),
    inference(resolution,[status(thm)],[c_14,c_81])).

tff(c_221,plain,(
    ! [A_63,B_64] :
      ( ~ r2_hidden(A_63,B_64)
      | r1_xboole_0('#skF_4'(A_63,B_64),B_64) ) ),
    inference(resolution,[status(thm)],[c_12,c_209])).

tff(c_41,plain,(
    ! [A_29,B_30] :
      ( r2_hidden('#skF_4'(A_29,B_30),B_30)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_24,plain,(
    ! [B_21] :
      ( ~ r1_xboole_0(B_21,'#skF_5')
      | ~ r2_hidden(B_21,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_46,plain,(
    ! [A_29] :
      ( ~ r1_xboole_0('#skF_4'(A_29,'#skF_5'),'#skF_5')
      | ~ r2_hidden(A_29,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_41,c_24])).

tff(c_230,plain,(
    ! [A_65] : ~ r2_hidden(A_65,'#skF_5') ),
    inference(resolution,[status(thm)],[c_221,c_46])).

tff(c_238,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_151,c_230])).

tff(c_266,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_238])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:07:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.22  
% 1.75/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.22  %$ r2_hidden > r1_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 1.97/1.22  
% 1.97/1.22  %Foreground sorts:
% 1.97/1.22  
% 1.97/1.22  
% 1.97/1.22  %Background operators:
% 1.97/1.22  
% 1.97/1.22  
% 1.97/1.22  %Foreground operators:
% 1.97/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.22  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.97/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.22  tff('#skF_5', type, '#skF_5': $i).
% 1.97/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.97/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.97/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.97/1.22  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.97/1.22  
% 1.97/1.23  tff(f_81, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 1.97/1.23  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 1.97/1.23  tff(f_52, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.97/1.23  tff(f_57, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 1.97/1.23  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.97/1.23  tff(f_70, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 1.97/1.23  tff(c_26, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.97/1.23  tff(c_121, plain, (![A_50, B_51]: (r2_hidden('#skF_1'(A_50, B_51), B_51) | r2_hidden('#skF_2'(A_50, B_51), A_50) | B_51=A_50)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.97/1.23  tff(c_16, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.97/1.23  tff(c_35, plain, (![A_26, C_27, B_28]: (~r2_hidden(A_26, C_27) | ~r1_xboole_0(k2_tarski(A_26, B_28), C_27))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.97/1.23  tff(c_40, plain, (![A_26]: (~r2_hidden(A_26, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_35])).
% 1.97/1.23  tff(c_151, plain, (![B_51]: (r2_hidden('#skF_1'(k1_xboole_0, B_51), B_51) | k1_xboole_0=B_51)), inference(resolution, [status(thm)], [c_121, c_40])).
% 1.97/1.23  tff(c_12, plain, (![A_4, B_5]: (r2_hidden('#skF_3'(A_4, B_5), B_5) | r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.97/1.23  tff(c_14, plain, (![A_4, B_5]: (r2_hidden('#skF_3'(A_4, B_5), A_4) | r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.97/1.23  tff(c_81, plain, (![D_41, A_42, B_43]: (~r2_hidden(D_41, '#skF_4'(A_42, B_43)) | ~r2_hidden(D_41, B_43) | ~r2_hidden(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.97/1.23  tff(c_209, plain, (![A_57, B_58, B_59]: (~r2_hidden('#skF_3'('#skF_4'(A_57, B_58), B_59), B_58) | ~r2_hidden(A_57, B_58) | r1_xboole_0('#skF_4'(A_57, B_58), B_59))), inference(resolution, [status(thm)], [c_14, c_81])).
% 1.97/1.23  tff(c_221, plain, (![A_63, B_64]: (~r2_hidden(A_63, B_64) | r1_xboole_0('#skF_4'(A_63, B_64), B_64))), inference(resolution, [status(thm)], [c_12, c_209])).
% 1.97/1.23  tff(c_41, plain, (![A_29, B_30]: (r2_hidden('#skF_4'(A_29, B_30), B_30) | ~r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.97/1.23  tff(c_24, plain, (![B_21]: (~r1_xboole_0(B_21, '#skF_5') | ~r2_hidden(B_21, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.97/1.23  tff(c_46, plain, (![A_29]: (~r1_xboole_0('#skF_4'(A_29, '#skF_5'), '#skF_5') | ~r2_hidden(A_29, '#skF_5'))), inference(resolution, [status(thm)], [c_41, c_24])).
% 1.97/1.23  tff(c_230, plain, (![A_65]: (~r2_hidden(A_65, '#skF_5'))), inference(resolution, [status(thm)], [c_221, c_46])).
% 1.97/1.23  tff(c_238, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_151, c_230])).
% 1.97/1.23  tff(c_266, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_238])).
% 1.97/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.23  
% 1.97/1.23  Inference rules
% 1.97/1.23  ----------------------
% 1.97/1.23  #Ref     : 0
% 1.97/1.23  #Sup     : 41
% 1.97/1.23  #Fact    : 0
% 1.97/1.23  #Define  : 0
% 1.97/1.23  #Split   : 0
% 1.97/1.23  #Chain   : 0
% 1.97/1.23  #Close   : 0
% 1.97/1.23  
% 1.97/1.23  Ordering : KBO
% 1.97/1.23  
% 1.97/1.23  Simplification rules
% 1.97/1.23  ----------------------
% 1.97/1.23  #Subsume      : 10
% 1.97/1.23  #Demod        : 1
% 1.97/1.23  #Tautology    : 7
% 1.97/1.23  #SimpNegUnit  : 3
% 1.97/1.23  #BackRed      : 0
% 1.97/1.23  
% 1.97/1.23  #Partial instantiations: 0
% 1.97/1.23  #Strategies tried      : 1
% 1.97/1.23  
% 1.97/1.23  Timing (in seconds)
% 1.97/1.23  ----------------------
% 1.97/1.24  Preprocessing        : 0.27
% 1.97/1.24  Parsing              : 0.15
% 1.97/1.24  CNF conversion       : 0.02
% 1.97/1.24  Main loop            : 0.18
% 1.97/1.24  Inferencing          : 0.09
% 1.97/1.24  Reduction            : 0.04
% 1.97/1.24  Demodulation         : 0.03
% 1.97/1.24  BG Simplification    : 0.01
% 1.97/1.24  Subsumption          : 0.03
% 1.97/1.24  Abstraction          : 0.01
% 1.97/1.24  MUC search           : 0.00
% 1.97/1.24  Cooper               : 0.00
% 1.97/1.24  Total                : 0.48
% 1.97/1.24  Index Insertion      : 0.00
% 1.97/1.24  Index Deletion       : 0.00
% 1.97/1.24  Index Matching       : 0.00
% 1.97/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
