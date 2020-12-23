%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:37 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   39 (  43 expanded)
%              Number of leaves         :   24 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  65 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > #skF_1 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_3 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(A,k2_zfmisc_1(B,C))
          & r2_hidden(D,A)
          & ! [E,F] :
              ~ ( r2_hidden(E,B)
                & r2_hidden(F,C)
                & D = k4_tarski(E,F) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_50,plain,(
    r1_tarski('#skF_9',k2_zfmisc_1('#skF_10','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_51,plain,(
    ! [A_47,B_48] :
      ( k3_xboole_0(A_47,B_48) = A_47
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_55,plain,(
    k3_xboole_0('#skF_9',k2_zfmisc_1('#skF_10','#skF_11')) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_50,c_51])).

tff(c_64,plain,(
    ! [D_52,B_53,A_54] :
      ( r2_hidden(D_52,B_53)
      | ~ r2_hidden(D_52,k3_xboole_0(A_54,B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_67,plain,(
    ! [D_52] :
      ( r2_hidden(D_52,k2_zfmisc_1('#skF_10','#skF_11'))
      | ~ r2_hidden(D_52,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_64])).

tff(c_28,plain,(
    ! [A_9,B_10,D_36] :
      ( r2_hidden('#skF_7'(A_9,B_10,k2_zfmisc_1(A_9,B_10),D_36),A_9)
      | ~ r2_hidden(D_36,k2_zfmisc_1(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_26,plain,(
    ! [A_9,B_10,D_36] :
      ( r2_hidden('#skF_8'(A_9,B_10,k2_zfmisc_1(A_9,B_10),D_36),B_10)
      | ~ r2_hidden(D_36,k2_zfmisc_1(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_283,plain,(
    ! [A_102,B_103,D_104] :
      ( k4_tarski('#skF_7'(A_102,B_103,k2_zfmisc_1(A_102,B_103),D_104),'#skF_8'(A_102,B_103,k2_zfmisc_1(A_102,B_103),D_104)) = D_104
      | ~ r2_hidden(D_104,k2_zfmisc_1(A_102,B_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_46,plain,(
    ! [E_45,F_46] :
      ( k4_tarski(E_45,F_46) != '#skF_12'
      | ~ r2_hidden(F_46,'#skF_11')
      | ~ r2_hidden(E_45,'#skF_10') ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_337,plain,(
    ! [D_112,A_113,B_114] :
      ( D_112 != '#skF_12'
      | ~ r2_hidden('#skF_8'(A_113,B_114,k2_zfmisc_1(A_113,B_114),D_112),'#skF_11')
      | ~ r2_hidden('#skF_7'(A_113,B_114,k2_zfmisc_1(A_113,B_114),D_112),'#skF_10')
      | ~ r2_hidden(D_112,k2_zfmisc_1(A_113,B_114)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_46])).

tff(c_344,plain,(
    ! [D_115,A_116] :
      ( D_115 != '#skF_12'
      | ~ r2_hidden('#skF_7'(A_116,'#skF_11',k2_zfmisc_1(A_116,'#skF_11'),D_115),'#skF_10')
      | ~ r2_hidden(D_115,k2_zfmisc_1(A_116,'#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_26,c_337])).

tff(c_351,plain,(
    ! [D_117] :
      ( D_117 != '#skF_12'
      | ~ r2_hidden(D_117,k2_zfmisc_1('#skF_10','#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_28,c_344])).

tff(c_458,plain,(
    ~ r2_hidden('#skF_12','#skF_9') ),
    inference(resolution,[status(thm)],[c_67,c_351])).

tff(c_48,plain,(
    r2_hidden('#skF_12','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_460,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_458,c_48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:10:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.30  
% 2.20/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.30  %$ r2_hidden > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > #skF_1 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_3 > #skF_12
% 2.20/1.30  
% 2.20/1.30  %Foreground sorts:
% 2.20/1.30  
% 2.20/1.30  
% 2.20/1.30  %Background operators:
% 2.20/1.30  
% 2.20/1.30  
% 2.20/1.30  %Foreground operators:
% 2.20/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.20/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.30  tff('#skF_11', type, '#skF_11': $i).
% 2.20/1.30  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.20/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.20/1.30  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.20/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.30  tff('#skF_10', type, '#skF_10': $i).
% 2.20/1.30  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 2.20/1.30  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.20/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.20/1.30  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 2.20/1.30  tff('#skF_9', type, '#skF_9': $i).
% 2.20/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.20/1.30  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.20/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.20/1.30  tff('#skF_12', type, '#skF_12': $i).
% 2.20/1.30  
% 2.20/1.31  tff(f_64, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(A, k2_zfmisc_1(B, C)) & r2_hidden(D, A)) & (![E, F]: ~((r2_hidden(E, B) & r2_hidden(F, C)) & (D = k4_tarski(E, F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_zfmisc_1)).
% 2.20/1.31  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.20/1.31  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.20/1.31  tff(f_50, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 2.20/1.31  tff(c_50, plain, (r1_tarski('#skF_9', k2_zfmisc_1('#skF_10', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.20/1.31  tff(c_51, plain, (![A_47, B_48]: (k3_xboole_0(A_47, B_48)=A_47 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.20/1.31  tff(c_55, plain, (k3_xboole_0('#skF_9', k2_zfmisc_1('#skF_10', '#skF_11'))='#skF_9'), inference(resolution, [status(thm)], [c_50, c_51])).
% 2.20/1.31  tff(c_64, plain, (![D_52, B_53, A_54]: (r2_hidden(D_52, B_53) | ~r2_hidden(D_52, k3_xboole_0(A_54, B_53)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.20/1.31  tff(c_67, plain, (![D_52]: (r2_hidden(D_52, k2_zfmisc_1('#skF_10', '#skF_11')) | ~r2_hidden(D_52, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_55, c_64])).
% 2.20/1.31  tff(c_28, plain, (![A_9, B_10, D_36]: (r2_hidden('#skF_7'(A_9, B_10, k2_zfmisc_1(A_9, B_10), D_36), A_9) | ~r2_hidden(D_36, k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.20/1.31  tff(c_26, plain, (![A_9, B_10, D_36]: (r2_hidden('#skF_8'(A_9, B_10, k2_zfmisc_1(A_9, B_10), D_36), B_10) | ~r2_hidden(D_36, k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.20/1.31  tff(c_283, plain, (![A_102, B_103, D_104]: (k4_tarski('#skF_7'(A_102, B_103, k2_zfmisc_1(A_102, B_103), D_104), '#skF_8'(A_102, B_103, k2_zfmisc_1(A_102, B_103), D_104))=D_104 | ~r2_hidden(D_104, k2_zfmisc_1(A_102, B_103)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.20/1.31  tff(c_46, plain, (![E_45, F_46]: (k4_tarski(E_45, F_46)!='#skF_12' | ~r2_hidden(F_46, '#skF_11') | ~r2_hidden(E_45, '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.20/1.31  tff(c_337, plain, (![D_112, A_113, B_114]: (D_112!='#skF_12' | ~r2_hidden('#skF_8'(A_113, B_114, k2_zfmisc_1(A_113, B_114), D_112), '#skF_11') | ~r2_hidden('#skF_7'(A_113, B_114, k2_zfmisc_1(A_113, B_114), D_112), '#skF_10') | ~r2_hidden(D_112, k2_zfmisc_1(A_113, B_114)))), inference(superposition, [status(thm), theory('equality')], [c_283, c_46])).
% 2.20/1.31  tff(c_344, plain, (![D_115, A_116]: (D_115!='#skF_12' | ~r2_hidden('#skF_7'(A_116, '#skF_11', k2_zfmisc_1(A_116, '#skF_11'), D_115), '#skF_10') | ~r2_hidden(D_115, k2_zfmisc_1(A_116, '#skF_11')))), inference(resolution, [status(thm)], [c_26, c_337])).
% 2.20/1.31  tff(c_351, plain, (![D_117]: (D_117!='#skF_12' | ~r2_hidden(D_117, k2_zfmisc_1('#skF_10', '#skF_11')))), inference(resolution, [status(thm)], [c_28, c_344])).
% 2.20/1.31  tff(c_458, plain, (~r2_hidden('#skF_12', '#skF_9')), inference(resolution, [status(thm)], [c_67, c_351])).
% 2.20/1.31  tff(c_48, plain, (r2_hidden('#skF_12', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.20/1.31  tff(c_460, plain, $false, inference(negUnitSimplification, [status(thm)], [c_458, c_48])).
% 2.20/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.31  
% 2.20/1.31  Inference rules
% 2.20/1.31  ----------------------
% 2.20/1.31  #Ref     : 0
% 2.20/1.31  #Sup     : 82
% 2.20/1.31  #Fact    : 0
% 2.20/1.31  #Define  : 0
% 2.20/1.31  #Split   : 0
% 2.20/1.31  #Chain   : 0
% 2.20/1.31  #Close   : 0
% 2.20/1.31  
% 2.20/1.31  Ordering : KBO
% 2.20/1.31  
% 2.20/1.31  Simplification rules
% 2.20/1.31  ----------------------
% 2.20/1.31  #Subsume      : 7
% 2.20/1.31  #Demod        : 24
% 2.20/1.31  #Tautology    : 8
% 2.20/1.31  #SimpNegUnit  : 1
% 2.20/1.31  #BackRed      : 1
% 2.20/1.31  
% 2.20/1.31  #Partial instantiations: 0
% 2.20/1.31  #Strategies tried      : 1
% 2.20/1.31  
% 2.20/1.31  Timing (in seconds)
% 2.20/1.31  ----------------------
% 2.20/1.31  Preprocessing        : 0.28
% 2.20/1.31  Parsing              : 0.14
% 2.20/1.31  CNF conversion       : 0.03
% 2.20/1.31  Main loop            : 0.27
% 2.20/1.31  Inferencing          : 0.11
% 2.20/1.31  Reduction            : 0.07
% 2.20/1.31  Demodulation         : 0.05
% 2.20/1.31  BG Simplification    : 0.02
% 2.20/1.31  Subsumption          : 0.06
% 2.20/1.31  Abstraction          : 0.02
% 2.20/1.31  MUC search           : 0.00
% 2.20/1.31  Cooper               : 0.00
% 2.20/1.31  Total                : 0.58
% 2.20/1.31  Index Insertion      : 0.00
% 2.20/1.31  Index Deletion       : 0.00
% 2.20/1.31  Index Matching       : 0.00
% 2.20/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
