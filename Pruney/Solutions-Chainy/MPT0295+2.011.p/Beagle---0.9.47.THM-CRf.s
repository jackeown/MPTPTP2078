%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:38 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   39 (  44 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   50 (  72 expanded)
%              Number of equality atoms :    9 (  15 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(A,k2_zfmisc_1(B,C))
          & r2_hidden(D,A)
          & ! [E,F] :
              ~ ( r2_hidden(E,B)
                & r2_hidden(F,C)
                & D = k4_tarski(E,F) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_30,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(k1_tarski(A_38),B_39)
      | ~ r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_36,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_43,plain,(
    ! [A_48,C_49,B_50] :
      ( r1_tarski(A_48,C_49)
      | ~ r1_tarski(B_50,C_49)
      | ~ r1_tarski(A_48,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_51,plain,(
    ! [A_53] :
      ( r1_tarski(A_53,k2_zfmisc_1('#skF_8','#skF_9'))
      | ~ r1_tarski(A_53,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_36,c_43])).

tff(c_28,plain,(
    ! [A_38,B_39] :
      ( r2_hidden(A_38,B_39)
      | ~ r1_tarski(k1_tarski(A_38),B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_59,plain,(
    ! [A_38] :
      ( r2_hidden(A_38,k2_zfmisc_1('#skF_8','#skF_9'))
      | ~ r1_tarski(k1_tarski(A_38),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_51,c_28])).

tff(c_10,plain,(
    ! [A_4,B_5,D_31] :
      ( r2_hidden('#skF_5'(A_4,B_5,k2_zfmisc_1(A_4,B_5),D_31),A_4)
      | ~ r2_hidden(D_31,k2_zfmisc_1(A_4,B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_4,B_5,D_31] :
      ( r2_hidden('#skF_6'(A_4,B_5,k2_zfmisc_1(A_4,B_5),D_31),B_5)
      | ~ r2_hidden(D_31,k2_zfmisc_1(A_4,B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_219,plain,(
    ! [A_94,B_95,D_96] :
      ( k4_tarski('#skF_5'(A_94,B_95,k2_zfmisc_1(A_94,B_95),D_96),'#skF_6'(A_94,B_95,k2_zfmisc_1(A_94,B_95),D_96)) = D_96
      | ~ r2_hidden(D_96,k2_zfmisc_1(A_94,B_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_32,plain,(
    ! [E_42,F_43] :
      ( k4_tarski(E_42,F_43) != '#skF_10'
      | ~ r2_hidden(F_43,'#skF_9')
      | ~ r2_hidden(E_42,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_285,plain,(
    ! [D_105,A_106,B_107] :
      ( D_105 != '#skF_10'
      | ~ r2_hidden('#skF_6'(A_106,B_107,k2_zfmisc_1(A_106,B_107),D_105),'#skF_9')
      | ~ r2_hidden('#skF_5'(A_106,B_107,k2_zfmisc_1(A_106,B_107),D_105),'#skF_8')
      | ~ r2_hidden(D_105,k2_zfmisc_1(A_106,B_107)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_32])).

tff(c_292,plain,(
    ! [D_108,A_109] :
      ( D_108 != '#skF_10'
      | ~ r2_hidden('#skF_5'(A_109,'#skF_9',k2_zfmisc_1(A_109,'#skF_9'),D_108),'#skF_8')
      | ~ r2_hidden(D_108,k2_zfmisc_1(A_109,'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_8,c_285])).

tff(c_299,plain,(
    ! [D_110] :
      ( D_110 != '#skF_10'
      | ~ r2_hidden(D_110,k2_zfmisc_1('#skF_8','#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_10,c_292])).

tff(c_340,plain,(
    ! [A_111] :
      ( A_111 != '#skF_10'
      | ~ r1_tarski(k1_tarski(A_111),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_59,c_299])).

tff(c_354,plain,(
    ~ r2_hidden('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_30,c_340])).

tff(c_34,plain,(
    r2_hidden('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_356,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_354,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:32:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.45  
% 2.47/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.45  %$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 2.59/1.45  
% 2.59/1.45  %Foreground sorts:
% 2.59/1.45  
% 2.59/1.45  
% 2.59/1.45  %Background operators:
% 2.59/1.45  
% 2.59/1.45  
% 2.59/1.45  %Foreground operators:
% 2.59/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.59/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.59/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.59/1.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.59/1.45  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.59/1.45  tff('#skF_7', type, '#skF_7': $i).
% 2.59/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.59/1.45  tff('#skF_10', type, '#skF_10': $i).
% 2.59/1.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.59/1.45  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 2.59/1.45  tff('#skF_9', type, '#skF_9': $i).
% 2.59/1.45  tff('#skF_8', type, '#skF_8': $i).
% 2.59/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.45  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.59/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.59/1.45  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.59/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.45  
% 2.59/1.46  tff(f_47, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.59/1.46  tff(f_61, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(A, k2_zfmisc_1(B, C)) & r2_hidden(D, A)) & (![E, F]: ~((r2_hidden(E, B) & r2_hidden(F, C)) & (D = k4_tarski(E, F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_zfmisc_1)).
% 2.59/1.46  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.59/1.46  tff(f_43, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 2.59/1.46  tff(c_30, plain, (![A_38, B_39]: (r1_tarski(k1_tarski(A_38), B_39) | ~r2_hidden(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.59/1.46  tff(c_36, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.59/1.46  tff(c_43, plain, (![A_48, C_49, B_50]: (r1_tarski(A_48, C_49) | ~r1_tarski(B_50, C_49) | ~r1_tarski(A_48, B_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.59/1.46  tff(c_51, plain, (![A_53]: (r1_tarski(A_53, k2_zfmisc_1('#skF_8', '#skF_9')) | ~r1_tarski(A_53, '#skF_7'))), inference(resolution, [status(thm)], [c_36, c_43])).
% 2.59/1.46  tff(c_28, plain, (![A_38, B_39]: (r2_hidden(A_38, B_39) | ~r1_tarski(k1_tarski(A_38), B_39))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.59/1.46  tff(c_59, plain, (![A_38]: (r2_hidden(A_38, k2_zfmisc_1('#skF_8', '#skF_9')) | ~r1_tarski(k1_tarski(A_38), '#skF_7'))), inference(resolution, [status(thm)], [c_51, c_28])).
% 2.59/1.46  tff(c_10, plain, (![A_4, B_5, D_31]: (r2_hidden('#skF_5'(A_4, B_5, k2_zfmisc_1(A_4, B_5), D_31), A_4) | ~r2_hidden(D_31, k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.59/1.46  tff(c_8, plain, (![A_4, B_5, D_31]: (r2_hidden('#skF_6'(A_4, B_5, k2_zfmisc_1(A_4, B_5), D_31), B_5) | ~r2_hidden(D_31, k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.59/1.46  tff(c_219, plain, (![A_94, B_95, D_96]: (k4_tarski('#skF_5'(A_94, B_95, k2_zfmisc_1(A_94, B_95), D_96), '#skF_6'(A_94, B_95, k2_zfmisc_1(A_94, B_95), D_96))=D_96 | ~r2_hidden(D_96, k2_zfmisc_1(A_94, B_95)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.59/1.46  tff(c_32, plain, (![E_42, F_43]: (k4_tarski(E_42, F_43)!='#skF_10' | ~r2_hidden(F_43, '#skF_9') | ~r2_hidden(E_42, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.59/1.46  tff(c_285, plain, (![D_105, A_106, B_107]: (D_105!='#skF_10' | ~r2_hidden('#skF_6'(A_106, B_107, k2_zfmisc_1(A_106, B_107), D_105), '#skF_9') | ~r2_hidden('#skF_5'(A_106, B_107, k2_zfmisc_1(A_106, B_107), D_105), '#skF_8') | ~r2_hidden(D_105, k2_zfmisc_1(A_106, B_107)))), inference(superposition, [status(thm), theory('equality')], [c_219, c_32])).
% 2.59/1.46  tff(c_292, plain, (![D_108, A_109]: (D_108!='#skF_10' | ~r2_hidden('#skF_5'(A_109, '#skF_9', k2_zfmisc_1(A_109, '#skF_9'), D_108), '#skF_8') | ~r2_hidden(D_108, k2_zfmisc_1(A_109, '#skF_9')))), inference(resolution, [status(thm)], [c_8, c_285])).
% 2.59/1.46  tff(c_299, plain, (![D_110]: (D_110!='#skF_10' | ~r2_hidden(D_110, k2_zfmisc_1('#skF_8', '#skF_9')))), inference(resolution, [status(thm)], [c_10, c_292])).
% 2.59/1.46  tff(c_340, plain, (![A_111]: (A_111!='#skF_10' | ~r1_tarski(k1_tarski(A_111), '#skF_7'))), inference(resolution, [status(thm)], [c_59, c_299])).
% 2.59/1.46  tff(c_354, plain, (~r2_hidden('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_30, c_340])).
% 2.59/1.46  tff(c_34, plain, (r2_hidden('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.59/1.46  tff(c_356, plain, $false, inference(negUnitSimplification, [status(thm)], [c_354, c_34])).
% 2.59/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.46  
% 2.59/1.46  Inference rules
% 2.59/1.46  ----------------------
% 2.59/1.46  #Ref     : 0
% 2.59/1.46  #Sup     : 74
% 2.59/1.46  #Fact    : 0
% 2.59/1.46  #Define  : 0
% 2.59/1.46  #Split   : 1
% 2.59/1.46  #Chain   : 0
% 2.59/1.46  #Close   : 0
% 2.59/1.46  
% 2.59/1.46  Ordering : KBO
% 2.59/1.46  
% 2.59/1.46  Simplification rules
% 2.59/1.46  ----------------------
% 2.59/1.46  #Subsume      : 8
% 2.59/1.46  #Demod        : 1
% 2.59/1.46  #Tautology    : 4
% 2.59/1.46  #SimpNegUnit  : 1
% 2.59/1.46  #BackRed      : 1
% 2.59/1.46  
% 2.59/1.46  #Partial instantiations: 0
% 2.59/1.46  #Strategies tried      : 1
% 2.59/1.46  
% 2.59/1.46  Timing (in seconds)
% 2.59/1.46  ----------------------
% 2.59/1.47  Preprocessing        : 0.31
% 2.59/1.47  Parsing              : 0.16
% 2.59/1.47  CNF conversion       : 0.03
% 2.59/1.47  Main loop            : 0.31
% 2.59/1.47  Inferencing          : 0.11
% 2.59/1.47  Reduction            : 0.08
% 2.59/1.47  Demodulation         : 0.05
% 2.59/1.47  BG Simplification    : 0.02
% 2.59/1.47  Subsumption          : 0.08
% 2.59/1.47  Abstraction          : 0.02
% 2.59/1.47  MUC search           : 0.00
% 2.59/1.47  Cooper               : 0.00
% 2.59/1.47  Total                : 0.66
% 2.59/1.47  Index Insertion      : 0.00
% 2.59/1.47  Index Deletion       : 0.00
% 2.59/1.47  Index Matching       : 0.00
% 2.59/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
