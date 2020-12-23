%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:37 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   40 (  47 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   52 (  81 expanded)
%              Number of equality atoms :    7 (  13 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(A,k2_zfmisc_1(B,C))
          & r2_hidden(D,A)
          & ! [E,F] :
              ~ ( r2_hidden(E,B)
                & r2_hidden(F,C)
                & D = k4_tarski(E,F) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_14,plain,(
    ! [A_6,B_7,D_33] :
      ( r2_hidden('#skF_6'(A_6,B_7,k2_zfmisc_1(A_6,B_7),D_33),A_6)
      | ~ r2_hidden(D_33,k2_zfmisc_1(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    ! [A_6,B_7,D_33] :
      ( r2_hidden('#skF_7'(A_6,B_7,k2_zfmisc_1(A_6,B_7),D_33),B_7)
      | ~ r2_hidden(D_33,k2_zfmisc_1(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_182,plain,(
    ! [A_100,B_101,D_102] :
      ( k4_tarski('#skF_6'(A_100,B_101,k2_zfmisc_1(A_100,B_101),D_102),'#skF_7'(A_100,B_101,k2_zfmisc_1(A_100,B_101),D_102)) = D_102
      | ~ r2_hidden(D_102,k2_zfmisc_1(A_100,B_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_32,plain,(
    ! [E_42,F_43] :
      ( k4_tarski(E_42,F_43) != '#skF_11'
      | ~ r2_hidden(F_43,'#skF_10')
      | ~ r2_hidden(E_42,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_202,plain,(
    ! [D_107,A_108,B_109] :
      ( D_107 != '#skF_11'
      | ~ r2_hidden('#skF_7'(A_108,B_109,k2_zfmisc_1(A_108,B_109),D_107),'#skF_10')
      | ~ r2_hidden('#skF_6'(A_108,B_109,k2_zfmisc_1(A_108,B_109),D_107),'#skF_9')
      | ~ r2_hidden(D_107,k2_zfmisc_1(A_108,B_109)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_32])).

tff(c_214,plain,(
    ! [D_110,A_111] :
      ( D_110 != '#skF_11'
      | ~ r2_hidden('#skF_6'(A_111,'#skF_10',k2_zfmisc_1(A_111,'#skF_10'),D_110),'#skF_9')
      | ~ r2_hidden(D_110,k2_zfmisc_1(A_111,'#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_12,c_202])).

tff(c_220,plain,(
    ~ r2_hidden('#skF_11',k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_14,c_214])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_38,plain,(
    ! [A_46,B_47] :
      ( ~ r2_hidden('#skF_1'(A_46,B_47),B_47)
      | r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_43,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_38])).

tff(c_36,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_34,plain,(
    r2_hidden('#skF_11','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_45,plain,(
    ! [C_49,B_50,A_51] :
      ( r2_hidden(C_49,B_50)
      | ~ r2_hidden(C_49,A_51)
      | ~ r1_tarski(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    ! [B_52] :
      ( r2_hidden('#skF_11',B_52)
      | ~ r1_tarski('#skF_8',B_52) ) ),
    inference(resolution,[status(thm)],[c_34,c_45])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,(
    ! [B_53,B_54] :
      ( r2_hidden('#skF_11',B_53)
      | ~ r1_tarski(B_54,B_53)
      | ~ r1_tarski('#skF_8',B_54) ) ),
    inference(resolution,[status(thm)],[c_52,c_2])).

tff(c_60,plain,
    ( r2_hidden('#skF_11',k2_zfmisc_1('#skF_9','#skF_10'))
    | ~ r1_tarski('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_56])).

tff(c_64,plain,(
    r2_hidden('#skF_11',k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_60])).

tff(c_222,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_220,c_64])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:57:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.24  
% 2.07/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.24  %$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1
% 2.07/1.24  
% 2.07/1.24  %Foreground sorts:
% 2.07/1.24  
% 2.07/1.24  
% 2.07/1.24  %Background operators:
% 2.07/1.24  
% 2.07/1.24  
% 2.07/1.24  %Foreground operators:
% 2.07/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.24  tff('#skF_11', type, '#skF_11': $i).
% 2.07/1.24  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.07/1.24  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.07/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.24  tff('#skF_10', type, '#skF_10': $i).
% 2.07/1.24  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.07/1.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.07/1.24  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 2.07/1.24  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 2.07/1.24  tff('#skF_9', type, '#skF_9': $i).
% 2.07/1.24  tff('#skF_8', type, '#skF_8': $i).
% 2.07/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.07/1.24  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.07/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.07/1.24  
% 2.13/1.26  tff(f_44, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 2.13/1.26  tff(f_58, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(A, k2_zfmisc_1(B, C)) & r2_hidden(D, A)) & (![E, F]: ~((r2_hidden(E, B) & r2_hidden(F, C)) & (D = k4_tarski(E, F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_zfmisc_1)).
% 2.13/1.26  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.13/1.26  tff(c_14, plain, (![A_6, B_7, D_33]: (r2_hidden('#skF_6'(A_6, B_7, k2_zfmisc_1(A_6, B_7), D_33), A_6) | ~r2_hidden(D_33, k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.13/1.26  tff(c_12, plain, (![A_6, B_7, D_33]: (r2_hidden('#skF_7'(A_6, B_7, k2_zfmisc_1(A_6, B_7), D_33), B_7) | ~r2_hidden(D_33, k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.13/1.26  tff(c_182, plain, (![A_100, B_101, D_102]: (k4_tarski('#skF_6'(A_100, B_101, k2_zfmisc_1(A_100, B_101), D_102), '#skF_7'(A_100, B_101, k2_zfmisc_1(A_100, B_101), D_102))=D_102 | ~r2_hidden(D_102, k2_zfmisc_1(A_100, B_101)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.13/1.26  tff(c_32, plain, (![E_42, F_43]: (k4_tarski(E_42, F_43)!='#skF_11' | ~r2_hidden(F_43, '#skF_10') | ~r2_hidden(E_42, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.13/1.26  tff(c_202, plain, (![D_107, A_108, B_109]: (D_107!='#skF_11' | ~r2_hidden('#skF_7'(A_108, B_109, k2_zfmisc_1(A_108, B_109), D_107), '#skF_10') | ~r2_hidden('#skF_6'(A_108, B_109, k2_zfmisc_1(A_108, B_109), D_107), '#skF_9') | ~r2_hidden(D_107, k2_zfmisc_1(A_108, B_109)))), inference(superposition, [status(thm), theory('equality')], [c_182, c_32])).
% 2.13/1.26  tff(c_214, plain, (![D_110, A_111]: (D_110!='#skF_11' | ~r2_hidden('#skF_6'(A_111, '#skF_10', k2_zfmisc_1(A_111, '#skF_10'), D_110), '#skF_9') | ~r2_hidden(D_110, k2_zfmisc_1(A_111, '#skF_10')))), inference(resolution, [status(thm)], [c_12, c_202])).
% 2.13/1.26  tff(c_220, plain, (~r2_hidden('#skF_11', k2_zfmisc_1('#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_14, c_214])).
% 2.13/1.26  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.13/1.26  tff(c_38, plain, (![A_46, B_47]: (~r2_hidden('#skF_1'(A_46, B_47), B_47) | r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.13/1.26  tff(c_43, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_38])).
% 2.13/1.26  tff(c_36, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_9', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.13/1.26  tff(c_34, plain, (r2_hidden('#skF_11', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.13/1.26  tff(c_45, plain, (![C_49, B_50, A_51]: (r2_hidden(C_49, B_50) | ~r2_hidden(C_49, A_51) | ~r1_tarski(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.13/1.26  tff(c_52, plain, (![B_52]: (r2_hidden('#skF_11', B_52) | ~r1_tarski('#skF_8', B_52))), inference(resolution, [status(thm)], [c_34, c_45])).
% 2.13/1.26  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.13/1.26  tff(c_56, plain, (![B_53, B_54]: (r2_hidden('#skF_11', B_53) | ~r1_tarski(B_54, B_53) | ~r1_tarski('#skF_8', B_54))), inference(resolution, [status(thm)], [c_52, c_2])).
% 2.13/1.26  tff(c_60, plain, (r2_hidden('#skF_11', k2_zfmisc_1('#skF_9', '#skF_10')) | ~r1_tarski('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_36, c_56])).
% 2.13/1.26  tff(c_64, plain, (r2_hidden('#skF_11', k2_zfmisc_1('#skF_9', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_60])).
% 2.13/1.26  tff(c_222, plain, $false, inference(negUnitSimplification, [status(thm)], [c_220, c_64])).
% 2.13/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.26  
% 2.13/1.26  Inference rules
% 2.13/1.26  ----------------------
% 2.13/1.26  #Ref     : 0
% 2.13/1.26  #Sup     : 42
% 2.13/1.26  #Fact    : 0
% 2.13/1.26  #Define  : 0
% 2.13/1.26  #Split   : 1
% 2.13/1.26  #Chain   : 0
% 2.13/1.26  #Close   : 0
% 2.13/1.26  
% 2.13/1.26  Ordering : KBO
% 2.13/1.26  
% 2.13/1.26  Simplification rules
% 2.13/1.26  ----------------------
% 2.13/1.26  #Subsume      : 7
% 2.13/1.26  #Demod        : 4
% 2.13/1.26  #Tautology    : 6
% 2.13/1.26  #SimpNegUnit  : 1
% 2.13/1.26  #BackRed      : 1
% 2.13/1.26  
% 2.13/1.26  #Partial instantiations: 0
% 2.13/1.26  #Strategies tried      : 1
% 2.13/1.26  
% 2.13/1.26  Timing (in seconds)
% 2.13/1.26  ----------------------
% 2.13/1.26  Preprocessing        : 0.27
% 2.13/1.26  Parsing              : 0.14
% 2.13/1.26  CNF conversion       : 0.03
% 2.13/1.26  Main loop            : 0.22
% 2.13/1.26  Inferencing          : 0.09
% 2.13/1.26  Reduction            : 0.05
% 2.13/1.26  Demodulation         : 0.04
% 2.13/1.26  BG Simplification    : 0.02
% 2.13/1.26  Subsumption          : 0.05
% 2.13/1.26  Abstraction          : 0.01
% 2.13/1.26  MUC search           : 0.00
% 2.13/1.26  Cooper               : 0.00
% 2.13/1.26  Total                : 0.52
% 2.13/1.26  Index Insertion      : 0.00
% 2.13/1.26  Index Deletion       : 0.00
% 2.13/1.26  Index Matching       : 0.00
% 2.13/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
