%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:37 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
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
%$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > #skF_1 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_3 > #skF_12

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

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
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

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
      ( k2_xboole_0(A_47,B_48) = B_48
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_55,plain,(
    k2_xboole_0('#skF_9',k2_zfmisc_1('#skF_10','#skF_11')) = k2_zfmisc_1('#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_50,c_51])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( ~ r2_hidden(D_6,A_1)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_65,plain,(
    ! [D_6] :
      ( ~ r2_hidden(D_6,'#skF_9')
      | r2_hidden(D_6,k2_zfmisc_1('#skF_10','#skF_11')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_6])).

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

tff(c_165,plain,(
    ! [A_89,B_90,D_91] :
      ( k4_tarski('#skF_7'(A_89,B_90,k2_zfmisc_1(A_89,B_90),D_91),'#skF_8'(A_89,B_90,k2_zfmisc_1(A_89,B_90),D_91)) = D_91
      | ~ r2_hidden(D_91,k2_zfmisc_1(A_89,B_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_46,plain,(
    ! [E_45,F_46] :
      ( k4_tarski(E_45,F_46) != '#skF_12'
      | ~ r2_hidden(F_46,'#skF_11')
      | ~ r2_hidden(E_45,'#skF_10') ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_180,plain,(
    ! [D_92,A_93,B_94] :
      ( D_92 != '#skF_12'
      | ~ r2_hidden('#skF_8'(A_93,B_94,k2_zfmisc_1(A_93,B_94),D_92),'#skF_11')
      | ~ r2_hidden('#skF_7'(A_93,B_94,k2_zfmisc_1(A_93,B_94),D_92),'#skF_10')
      | ~ r2_hidden(D_92,k2_zfmisc_1(A_93,B_94)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_46])).

tff(c_187,plain,(
    ! [D_95,A_96] :
      ( D_95 != '#skF_12'
      | ~ r2_hidden('#skF_7'(A_96,'#skF_11',k2_zfmisc_1(A_96,'#skF_11'),D_95),'#skF_10')
      | ~ r2_hidden(D_95,k2_zfmisc_1(A_96,'#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_26,c_180])).

tff(c_194,plain,(
    ! [D_97] :
      ( D_97 != '#skF_12'
      | ~ r2_hidden(D_97,k2_zfmisc_1('#skF_10','#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_28,c_187])).

tff(c_239,plain,(
    ~ r2_hidden('#skF_12','#skF_9') ),
    inference(resolution,[status(thm)],[c_65,c_194])).

tff(c_48,plain,(
    r2_hidden('#skF_12','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_239,c_48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:37:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.41  
% 2.28/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.42  %$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > #skF_1 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_3 > #skF_12
% 2.28/1.42  
% 2.28/1.42  %Foreground sorts:
% 2.28/1.42  
% 2.28/1.42  
% 2.28/1.42  %Background operators:
% 2.28/1.42  
% 2.28/1.42  
% 2.28/1.42  %Foreground operators:
% 2.28/1.42  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.28/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.28/1.42  tff('#skF_11', type, '#skF_11': $i).
% 2.28/1.42  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.28/1.42  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.28/1.42  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.28/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.42  tff('#skF_10', type, '#skF_10': $i).
% 2.28/1.42  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 2.28/1.42  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.28/1.42  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.28/1.42  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 2.28/1.42  tff('#skF_9', type, '#skF_9': $i).
% 2.28/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.28/1.42  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.28/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.28/1.42  tff('#skF_12', type, '#skF_12': $i).
% 2.28/1.42  
% 2.28/1.43  tff(f_64, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(A, k2_zfmisc_1(B, C)) & r2_hidden(D, A)) & (![E, F]: ~((r2_hidden(E, B) & r2_hidden(F, C)) & (D = k4_tarski(E, F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_zfmisc_1)).
% 2.28/1.43  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.28/1.43  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.28/1.43  tff(f_50, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 2.28/1.43  tff(c_50, plain, (r1_tarski('#skF_9', k2_zfmisc_1('#skF_10', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.28/1.43  tff(c_51, plain, (![A_47, B_48]: (k2_xboole_0(A_47, B_48)=B_48 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.28/1.43  tff(c_55, plain, (k2_xboole_0('#skF_9', k2_zfmisc_1('#skF_10', '#skF_11'))=k2_zfmisc_1('#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_50, c_51])).
% 2.28/1.43  tff(c_6, plain, (![D_6, A_1, B_2]: (~r2_hidden(D_6, A_1) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.28/1.43  tff(c_65, plain, (![D_6]: (~r2_hidden(D_6, '#skF_9') | r2_hidden(D_6, k2_zfmisc_1('#skF_10', '#skF_11')))), inference(superposition, [status(thm), theory('equality')], [c_55, c_6])).
% 2.28/1.43  tff(c_28, plain, (![A_9, B_10, D_36]: (r2_hidden('#skF_7'(A_9, B_10, k2_zfmisc_1(A_9, B_10), D_36), A_9) | ~r2_hidden(D_36, k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.28/1.43  tff(c_26, plain, (![A_9, B_10, D_36]: (r2_hidden('#skF_8'(A_9, B_10, k2_zfmisc_1(A_9, B_10), D_36), B_10) | ~r2_hidden(D_36, k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.28/1.43  tff(c_165, plain, (![A_89, B_90, D_91]: (k4_tarski('#skF_7'(A_89, B_90, k2_zfmisc_1(A_89, B_90), D_91), '#skF_8'(A_89, B_90, k2_zfmisc_1(A_89, B_90), D_91))=D_91 | ~r2_hidden(D_91, k2_zfmisc_1(A_89, B_90)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.28/1.43  tff(c_46, plain, (![E_45, F_46]: (k4_tarski(E_45, F_46)!='#skF_12' | ~r2_hidden(F_46, '#skF_11') | ~r2_hidden(E_45, '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.28/1.43  tff(c_180, plain, (![D_92, A_93, B_94]: (D_92!='#skF_12' | ~r2_hidden('#skF_8'(A_93, B_94, k2_zfmisc_1(A_93, B_94), D_92), '#skF_11') | ~r2_hidden('#skF_7'(A_93, B_94, k2_zfmisc_1(A_93, B_94), D_92), '#skF_10') | ~r2_hidden(D_92, k2_zfmisc_1(A_93, B_94)))), inference(superposition, [status(thm), theory('equality')], [c_165, c_46])).
% 2.28/1.43  tff(c_187, plain, (![D_95, A_96]: (D_95!='#skF_12' | ~r2_hidden('#skF_7'(A_96, '#skF_11', k2_zfmisc_1(A_96, '#skF_11'), D_95), '#skF_10') | ~r2_hidden(D_95, k2_zfmisc_1(A_96, '#skF_11')))), inference(resolution, [status(thm)], [c_26, c_180])).
% 2.28/1.43  tff(c_194, plain, (![D_97]: (D_97!='#skF_12' | ~r2_hidden(D_97, k2_zfmisc_1('#skF_10', '#skF_11')))), inference(resolution, [status(thm)], [c_28, c_187])).
% 2.28/1.43  tff(c_239, plain, (~r2_hidden('#skF_12', '#skF_9')), inference(resolution, [status(thm)], [c_65, c_194])).
% 2.28/1.43  tff(c_48, plain, (r2_hidden('#skF_12', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.28/1.43  tff(c_241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_239, c_48])).
% 2.28/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.43  
% 2.28/1.43  Inference rules
% 2.28/1.43  ----------------------
% 2.28/1.43  #Ref     : 0
% 2.28/1.43  #Sup     : 39
% 2.28/1.43  #Fact    : 0
% 2.28/1.43  #Define  : 0
% 2.28/1.43  #Split   : 0
% 2.28/1.43  #Chain   : 0
% 2.28/1.43  #Close   : 0
% 2.28/1.43  
% 2.28/1.43  Ordering : KBO
% 2.28/1.43  
% 2.28/1.43  Simplification rules
% 2.28/1.43  ----------------------
% 2.28/1.43  #Subsume      : 1
% 2.28/1.43  #Demod        : 0
% 2.28/1.43  #Tautology    : 8
% 2.28/1.43  #SimpNegUnit  : 1
% 2.28/1.43  #BackRed      : 1
% 2.28/1.43  
% 2.28/1.43  #Partial instantiations: 0
% 2.28/1.43  #Strategies tried      : 1
% 2.28/1.43  
% 2.28/1.43  Timing (in seconds)
% 2.28/1.43  ----------------------
% 2.28/1.43  Preprocessing        : 0.35
% 2.28/1.43  Parsing              : 0.16
% 2.28/1.43  CNF conversion       : 0.03
% 2.28/1.43  Main loop            : 0.28
% 2.28/1.43  Inferencing          : 0.09
% 2.28/1.43  Reduction            : 0.07
% 2.28/1.43  Demodulation         : 0.05
% 2.28/1.43  BG Simplification    : 0.02
% 2.28/1.43  Subsumption          : 0.07
% 2.28/1.43  Abstraction          : 0.01
% 2.28/1.43  MUC search           : 0.00
% 2.28/1.43  Cooper               : 0.00
% 2.28/1.43  Total                : 0.66
% 2.28/1.43  Index Insertion      : 0.00
% 2.28/1.43  Index Deletion       : 0.00
% 2.28/1.43  Index Matching       : 0.00
% 2.28/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
