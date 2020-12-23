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
% DateTime   : Thu Dec  3 10:08:47 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   42 (  47 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   57 (  76 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_56,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(f_74,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

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

tff(c_38,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_28,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_209,plain,(
    ! [A_77,B_78] :
      ( r2_hidden('#skF_3'(A_77,B_78),A_77)
      | r2_hidden('#skF_4'(A_77,B_78),B_78)
      | k3_tarski(A_77) = B_78 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_46,plain,(
    ! [A_41,B_42] :
      ( r2_hidden('#skF_6'(A_41,B_42),B_42)
      | ~ r2_hidden(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_34,plain,(
    ! [B_34,A_33] :
      ( ~ r1_tarski(B_34,A_33)
      | ~ r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_78,plain,(
    ! [B_49,A_50] :
      ( ~ r1_tarski(B_49,'#skF_6'(A_50,B_49))
      | ~ r2_hidden(A_50,B_49) ) ),
    inference(resolution,[status(thm)],[c_46,c_34])).

tff(c_83,plain,(
    ! [A_50] : ~ r2_hidden(A_50,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_78])).

tff(c_219,plain,(
    ! [B_78] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_78),B_78)
      | k3_tarski(k1_xboole_0) = B_78 ) ),
    inference(resolution,[status(thm)],[c_209,c_83])).

tff(c_243,plain,(
    ! [B_78] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_78),B_78)
      | k1_xboole_0 = B_78 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_219])).

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

tff(c_170,plain,(
    ! [D_69,A_70,B_71] :
      ( ~ r2_hidden(D_69,'#skF_6'(A_70,B_71))
      | ~ r2_hidden(D_69,B_71)
      | ~ r2_hidden(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_672,plain,(
    ! [A_121,B_122,B_123] :
      ( ~ r2_hidden('#skF_1'('#skF_6'(A_121,B_122),B_123),B_122)
      | ~ r2_hidden(A_121,B_122)
      | r1_xboole_0('#skF_6'(A_121,B_122),B_123) ) ),
    inference(resolution,[status(thm)],[c_6,c_170])).

tff(c_706,plain,(
    ! [A_127,B_128] :
      ( ~ r2_hidden(A_127,B_128)
      | r1_xboole_0('#skF_6'(A_127,B_128),B_128) ) ),
    inference(resolution,[status(thm)],[c_4,c_672])).

tff(c_36,plain,(
    ! [B_36] :
      ( ~ r1_xboole_0(B_36,'#skF_7')
      | ~ r2_hidden(B_36,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_55,plain,(
    ! [A_41] :
      ( ~ r1_xboole_0('#skF_6'(A_41,'#skF_7'),'#skF_7')
      | ~ r2_hidden(A_41,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_46,c_36])).

tff(c_715,plain,(
    ! [A_129] : ~ r2_hidden(A_129,'#skF_7') ),
    inference(resolution,[status(thm)],[c_706,c_55])).

tff(c_727,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_243,c_715])).

tff(c_755,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_727])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 15:20:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.39  
% 2.82/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.39  %$ r2_hidden > r1_xboole_0 > r1_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 2.82/1.39  
% 2.82/1.39  %Foreground sorts:
% 2.82/1.39  
% 2.82/1.39  
% 2.82/1.39  %Background operators:
% 2.82/1.39  
% 2.82/1.39  
% 2.82/1.39  %Foreground operators:
% 2.82/1.39  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.82/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.82/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.82/1.39  tff('#skF_7', type, '#skF_7': $i).
% 2.82/1.39  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.82/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.82/1.39  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.82/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.82/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.82/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.82/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.82/1.39  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.82/1.39  
% 2.82/1.40  tff(f_85, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 2.82/1.40  tff(f_56, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.82/1.40  tff(f_55, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 2.82/1.40  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.82/1.40  tff(f_69, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 2.82/1.40  tff(f_74, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.82/1.40  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.82/1.40  tff(c_38, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.82/1.40  tff(c_28, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.82/1.40  tff(c_209, plain, (![A_77, B_78]: (r2_hidden('#skF_3'(A_77, B_78), A_77) | r2_hidden('#skF_4'(A_77, B_78), B_78) | k3_tarski(A_77)=B_78)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.82/1.40  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.82/1.40  tff(c_46, plain, (![A_41, B_42]: (r2_hidden('#skF_6'(A_41, B_42), B_42) | ~r2_hidden(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.82/1.40  tff(c_34, plain, (![B_34, A_33]: (~r1_tarski(B_34, A_33) | ~r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.82/1.40  tff(c_78, plain, (![B_49, A_50]: (~r1_tarski(B_49, '#skF_6'(A_50, B_49)) | ~r2_hidden(A_50, B_49))), inference(resolution, [status(thm)], [c_46, c_34])).
% 2.82/1.40  tff(c_83, plain, (![A_50]: (~r2_hidden(A_50, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_78])).
% 2.82/1.40  tff(c_219, plain, (![B_78]: (r2_hidden('#skF_4'(k1_xboole_0, B_78), B_78) | k3_tarski(k1_xboole_0)=B_78)), inference(resolution, [status(thm)], [c_209, c_83])).
% 2.82/1.40  tff(c_243, plain, (![B_78]: (r2_hidden('#skF_4'(k1_xboole_0, B_78), B_78) | k1_xboole_0=B_78)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_219])).
% 2.82/1.40  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.82/1.40  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.82/1.40  tff(c_170, plain, (![D_69, A_70, B_71]: (~r2_hidden(D_69, '#skF_6'(A_70, B_71)) | ~r2_hidden(D_69, B_71) | ~r2_hidden(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.82/1.40  tff(c_672, plain, (![A_121, B_122, B_123]: (~r2_hidden('#skF_1'('#skF_6'(A_121, B_122), B_123), B_122) | ~r2_hidden(A_121, B_122) | r1_xboole_0('#skF_6'(A_121, B_122), B_123))), inference(resolution, [status(thm)], [c_6, c_170])).
% 2.82/1.40  tff(c_706, plain, (![A_127, B_128]: (~r2_hidden(A_127, B_128) | r1_xboole_0('#skF_6'(A_127, B_128), B_128))), inference(resolution, [status(thm)], [c_4, c_672])).
% 2.82/1.40  tff(c_36, plain, (![B_36]: (~r1_xboole_0(B_36, '#skF_7') | ~r2_hidden(B_36, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.82/1.40  tff(c_55, plain, (![A_41]: (~r1_xboole_0('#skF_6'(A_41, '#skF_7'), '#skF_7') | ~r2_hidden(A_41, '#skF_7'))), inference(resolution, [status(thm)], [c_46, c_36])).
% 2.82/1.40  tff(c_715, plain, (![A_129]: (~r2_hidden(A_129, '#skF_7'))), inference(resolution, [status(thm)], [c_706, c_55])).
% 2.82/1.40  tff(c_727, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_243, c_715])).
% 2.82/1.40  tff(c_755, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_727])).
% 2.82/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.40  
% 2.82/1.40  Inference rules
% 2.82/1.40  ----------------------
% 2.82/1.40  #Ref     : 0
% 2.82/1.40  #Sup     : 147
% 2.82/1.40  #Fact    : 0
% 2.82/1.40  #Define  : 0
% 2.82/1.40  #Split   : 2
% 2.82/1.40  #Chain   : 0
% 2.82/1.40  #Close   : 0
% 2.82/1.40  
% 2.82/1.40  Ordering : KBO
% 2.82/1.40  
% 2.82/1.40  Simplification rules
% 2.82/1.40  ----------------------
% 2.82/1.40  #Subsume      : 17
% 2.82/1.40  #Demod        : 17
% 2.82/1.40  #Tautology    : 12
% 2.82/1.40  #SimpNegUnit  : 7
% 2.82/1.40  #BackRed      : 0
% 2.82/1.40  
% 2.82/1.40  #Partial instantiations: 0
% 2.82/1.40  #Strategies tried      : 1
% 2.82/1.40  
% 2.82/1.40  Timing (in seconds)
% 2.82/1.40  ----------------------
% 2.82/1.41  Preprocessing        : 0.29
% 2.82/1.41  Parsing              : 0.15
% 2.82/1.41  CNF conversion       : 0.02
% 2.82/1.41  Main loop            : 0.35
% 2.82/1.41  Inferencing          : 0.14
% 2.82/1.41  Reduction            : 0.09
% 2.82/1.41  Demodulation         : 0.06
% 2.82/1.41  BG Simplification    : 0.02
% 2.82/1.41  Subsumption          : 0.08
% 2.82/1.41  Abstraction          : 0.02
% 2.82/1.41  MUC search           : 0.00
% 2.82/1.41  Cooper               : 0.00
% 2.82/1.41  Total                : 0.67
% 2.82/1.41  Index Insertion      : 0.00
% 2.82/1.41  Index Deletion       : 0.00
% 2.82/1.41  Index Matching       : 0.00
% 2.82/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
