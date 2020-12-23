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
% DateTime   : Thu Dec  3 10:08:50 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   27 (  32 expanded)
%              Number of leaves         :   13 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :   42 (  63 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > #nlpp > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(f_55,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

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

tff(c_88,plain,(
    ! [D_33,A_34,B_35] :
      ( ~ r2_hidden(D_33,'#skF_2'(A_34,B_35))
      | ~ r2_hidden(D_33,B_35)
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_115,plain,(
    ! [A_44,B_45,B_46] :
      ( ~ r2_hidden('#skF_1'('#skF_2'(A_44,B_45),B_46),B_45)
      | ~ r2_hidden(A_44,B_45)
      | r1_xboole_0('#skF_2'(A_44,B_45),B_46) ) ),
    inference(resolution,[status(thm)],[c_6,c_88])).

tff(c_121,plain,(
    ! [A_47,B_48] :
      ( ~ r2_hidden(A_47,B_48)
      | r1_xboole_0('#skF_2'(A_47,B_48),B_48) ) ),
    inference(resolution,[status(thm)],[c_4,c_115])).

tff(c_38,plain,(
    ! [A_22,B_23] :
      ( r2_hidden('#skF_2'(A_22,B_23),B_23)
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    ! [B_15] :
      ( ~ r1_xboole_0(B_15,'#skF_3')
      | ~ r2_hidden(B_15,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_43,plain,(
    ! [A_22] :
      ( ~ r1_xboole_0('#skF_2'(A_22,'#skF_3'),'#skF_3')
      | ~ r2_hidden(A_22,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_16])).

tff(c_130,plain,(
    ! [A_49] : ~ r2_hidden(A_49,'#skF_3') ),
    inference(resolution,[status(thm)],[c_121,c_43])).

tff(c_150,plain,(
    ! [A_50] : r1_xboole_0(A_50,'#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_130])).

tff(c_10,plain,(
    ! [A_6] :
      ( ~ r1_xboole_0(A_6,A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_156,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_150,c_10])).

tff(c_161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_156])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:57:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.17  
% 1.82/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.17  %$ r2_hidden > r1_xboole_0 > #nlpp > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 1.82/1.17  
% 1.82/1.17  %Foreground sorts:
% 1.82/1.17  
% 1.82/1.17  
% 1.82/1.17  %Background operators:
% 1.82/1.17  
% 1.82/1.17  
% 1.82/1.17  %Foreground operators:
% 1.82/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.82/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.82/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.82/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.82/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.82/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.82/1.17  
% 1.82/1.18  tff(f_79, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 1.82/1.18  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.82/1.18  tff(f_68, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 1.82/1.18  tff(f_55, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 1.82/1.18  tff(c_18, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.82/1.18  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.82/1.18  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.82/1.18  tff(c_88, plain, (![D_33, A_34, B_35]: (~r2_hidden(D_33, '#skF_2'(A_34, B_35)) | ~r2_hidden(D_33, B_35) | ~r2_hidden(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.82/1.18  tff(c_115, plain, (![A_44, B_45, B_46]: (~r2_hidden('#skF_1'('#skF_2'(A_44, B_45), B_46), B_45) | ~r2_hidden(A_44, B_45) | r1_xboole_0('#skF_2'(A_44, B_45), B_46))), inference(resolution, [status(thm)], [c_6, c_88])).
% 1.82/1.18  tff(c_121, plain, (![A_47, B_48]: (~r2_hidden(A_47, B_48) | r1_xboole_0('#skF_2'(A_47, B_48), B_48))), inference(resolution, [status(thm)], [c_4, c_115])).
% 1.82/1.18  tff(c_38, plain, (![A_22, B_23]: (r2_hidden('#skF_2'(A_22, B_23), B_23) | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.82/1.18  tff(c_16, plain, (![B_15]: (~r1_xboole_0(B_15, '#skF_3') | ~r2_hidden(B_15, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.82/1.18  tff(c_43, plain, (![A_22]: (~r1_xboole_0('#skF_2'(A_22, '#skF_3'), '#skF_3') | ~r2_hidden(A_22, '#skF_3'))), inference(resolution, [status(thm)], [c_38, c_16])).
% 1.82/1.18  tff(c_130, plain, (![A_49]: (~r2_hidden(A_49, '#skF_3'))), inference(resolution, [status(thm)], [c_121, c_43])).
% 1.82/1.18  tff(c_150, plain, (![A_50]: (r1_xboole_0(A_50, '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_130])).
% 1.82/1.18  tff(c_10, plain, (![A_6]: (~r1_xboole_0(A_6, A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.82/1.18  tff(c_156, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_150, c_10])).
% 1.82/1.18  tff(c_161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_156])).
% 1.82/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.18  
% 1.82/1.18  Inference rules
% 1.82/1.18  ----------------------
% 1.82/1.18  #Ref     : 0
% 1.82/1.18  #Sup     : 25
% 1.82/1.18  #Fact    : 0
% 1.82/1.18  #Define  : 0
% 1.82/1.18  #Split   : 0
% 1.82/1.18  #Chain   : 0
% 1.82/1.18  #Close   : 0
% 1.82/1.18  
% 1.82/1.18  Ordering : KBO
% 1.82/1.18  
% 1.82/1.18  Simplification rules
% 1.82/1.18  ----------------------
% 1.82/1.18  #Subsume      : 9
% 1.82/1.18  #Demod        : 4
% 1.82/1.18  #Tautology    : 5
% 1.82/1.18  #SimpNegUnit  : 1
% 1.82/1.18  #BackRed      : 1
% 1.82/1.18  
% 1.82/1.18  #Partial instantiations: 0
% 1.82/1.18  #Strategies tried      : 1
% 1.82/1.18  
% 1.82/1.18  Timing (in seconds)
% 1.82/1.18  ----------------------
% 1.82/1.18  Preprocessing        : 0.27
% 1.82/1.18  Parsing              : 0.14
% 1.82/1.18  CNF conversion       : 0.02
% 1.82/1.18  Main loop            : 0.14
% 1.82/1.18  Inferencing          : 0.06
% 1.82/1.18  Reduction            : 0.03
% 1.82/1.18  Demodulation         : 0.02
% 1.82/1.18  BG Simplification    : 0.01
% 1.82/1.18  Subsumption          : 0.03
% 1.82/1.18  Abstraction          : 0.01
% 1.82/1.19  MUC search           : 0.00
% 1.82/1.19  Cooper               : 0.00
% 1.82/1.19  Total                : 0.42
% 1.82/1.19  Index Insertion      : 0.00
% 1.82/1.19  Index Deletion       : 0.00
% 1.82/1.19  Index Matching       : 0.00
% 1.82/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
