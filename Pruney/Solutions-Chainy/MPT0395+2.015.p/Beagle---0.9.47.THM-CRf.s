%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:30 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   41 (  55 expanded)
%              Number of leaves         :   21 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   49 (  77 expanded)
%              Number of equality atoms :    7 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => r1_setfam_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_setfam_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_36,plain,(
    ~ r1_setfam_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_34,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_3'(A_13,B_14),A_13)
      | r1_setfam_1(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_38,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_53,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_65,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_53])).

tff(c_203,plain,(
    ! [D_64,A_65,B_66] :
      ( r2_hidden(D_64,k4_xboole_0(A_65,B_66))
      | r2_hidden(D_64,B_66)
      | ~ r2_hidden(D_64,A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_234,plain,(
    ! [D_67] :
      ( r2_hidden(D_67,k1_xboole_0)
      | r2_hidden(D_67,'#skF_6')
      | ~ r2_hidden(D_67,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_203])).

tff(c_20,plain,(
    ! [A_7] : k2_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_48,plain,(
    ! [A_26,B_27] : r1_tarski(A_26,k2_xboole_0(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_51,plain,(
    ! [A_7] : r1_tarski(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_48])).

tff(c_63,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_51,c_53])).

tff(c_114,plain,(
    ! [D_43,B_44,A_45] :
      ( ~ r2_hidden(D_43,B_44)
      | ~ r2_hidden(D_43,k4_xboole_0(A_45,B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_135,plain,(
    ! [D_47,A_48] :
      ( ~ r2_hidden(D_47,A_48)
      | ~ r2_hidden(D_47,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_114])).

tff(c_138,plain,(
    ! [A_13,B_14] :
      ( ~ r2_hidden('#skF_3'(A_13,B_14),k1_xboole_0)
      | r1_setfam_1(A_13,B_14) ) ),
    inference(resolution,[status(thm)],[c_34,c_135])).

tff(c_596,plain,(
    ! [A_118,B_119] :
      ( r1_setfam_1(A_118,B_119)
      | r2_hidden('#skF_3'(A_118,B_119),'#skF_6')
      | ~ r2_hidden('#skF_3'(A_118,B_119),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_234,c_138])).

tff(c_607,plain,(
    ! [B_120] :
      ( r2_hidden('#skF_3'('#skF_5',B_120),'#skF_6')
      | r1_setfam_1('#skF_5',B_120) ) ),
    inference(resolution,[status(thm)],[c_34,c_596])).

tff(c_175,plain,(
    ! [A_55,B_56,D_57] :
      ( ~ r1_tarski('#skF_3'(A_55,B_56),D_57)
      | ~ r2_hidden(D_57,B_56)
      | r1_setfam_1(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_189,plain,(
    ! [A_55,B_56] :
      ( ~ r2_hidden('#skF_3'(A_55,B_56),B_56)
      | r1_setfam_1(A_55,B_56) ) ),
    inference(resolution,[status(thm)],[c_51,c_175])).

tff(c_611,plain,(
    r1_setfam_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_607,c_189])).

tff(c_617,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_36,c_611])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:55:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.30  
% 2.17/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.30  %$ r2_hidden > r1_tarski > r1_setfam_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2
% 2.48/1.30  
% 2.48/1.30  %Foreground sorts:
% 2.48/1.30  
% 2.48/1.30  
% 2.48/1.30  %Background operators:
% 2.48/1.30  
% 2.48/1.30  
% 2.48/1.30  %Foreground operators:
% 2.48/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.48/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.30  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.48/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.48/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.48/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.48/1.30  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.48/1.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.48/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.48/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.48/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.48/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.48/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.48/1.30  
% 2.48/1.31  tff(f_60, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => r1_setfam_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_setfam_1)).
% 2.48/1.31  tff(f_55, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 2.48/1.31  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.48/1.31  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.48/1.31  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.48/1.31  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.48/1.31  tff(c_36, plain, (~r1_setfam_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.48/1.31  tff(c_34, plain, (![A_13, B_14]: (r2_hidden('#skF_3'(A_13, B_14), A_13) | r1_setfam_1(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.48/1.31  tff(c_38, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.48/1.31  tff(c_53, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.48/1.31  tff(c_65, plain, (k4_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_53])).
% 2.48/1.31  tff(c_203, plain, (![D_64, A_65, B_66]: (r2_hidden(D_64, k4_xboole_0(A_65, B_66)) | r2_hidden(D_64, B_66) | ~r2_hidden(D_64, A_65))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.48/1.31  tff(c_234, plain, (![D_67]: (r2_hidden(D_67, k1_xboole_0) | r2_hidden(D_67, '#skF_6') | ~r2_hidden(D_67, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_203])).
% 2.48/1.31  tff(c_20, plain, (![A_7]: (k2_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.48/1.31  tff(c_48, plain, (![A_26, B_27]: (r1_tarski(A_26, k2_xboole_0(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.48/1.31  tff(c_51, plain, (![A_7]: (r1_tarski(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_20, c_48])).
% 2.48/1.31  tff(c_63, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_51, c_53])).
% 2.48/1.31  tff(c_114, plain, (![D_43, B_44, A_45]: (~r2_hidden(D_43, B_44) | ~r2_hidden(D_43, k4_xboole_0(A_45, B_44)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.48/1.31  tff(c_135, plain, (![D_47, A_48]: (~r2_hidden(D_47, A_48) | ~r2_hidden(D_47, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_63, c_114])).
% 2.48/1.31  tff(c_138, plain, (![A_13, B_14]: (~r2_hidden('#skF_3'(A_13, B_14), k1_xboole_0) | r1_setfam_1(A_13, B_14))), inference(resolution, [status(thm)], [c_34, c_135])).
% 2.48/1.31  tff(c_596, plain, (![A_118, B_119]: (r1_setfam_1(A_118, B_119) | r2_hidden('#skF_3'(A_118, B_119), '#skF_6') | ~r2_hidden('#skF_3'(A_118, B_119), '#skF_5'))), inference(resolution, [status(thm)], [c_234, c_138])).
% 2.48/1.31  tff(c_607, plain, (![B_120]: (r2_hidden('#skF_3'('#skF_5', B_120), '#skF_6') | r1_setfam_1('#skF_5', B_120))), inference(resolution, [status(thm)], [c_34, c_596])).
% 2.48/1.31  tff(c_175, plain, (![A_55, B_56, D_57]: (~r1_tarski('#skF_3'(A_55, B_56), D_57) | ~r2_hidden(D_57, B_56) | r1_setfam_1(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.48/1.31  tff(c_189, plain, (![A_55, B_56]: (~r2_hidden('#skF_3'(A_55, B_56), B_56) | r1_setfam_1(A_55, B_56))), inference(resolution, [status(thm)], [c_51, c_175])).
% 2.48/1.31  tff(c_611, plain, (r1_setfam_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_607, c_189])).
% 2.48/1.31  tff(c_617, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_36, c_611])).
% 2.48/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.31  
% 2.48/1.31  Inference rules
% 2.48/1.31  ----------------------
% 2.48/1.31  #Ref     : 0
% 2.48/1.31  #Sup     : 124
% 2.48/1.31  #Fact    : 0
% 2.48/1.31  #Define  : 0
% 2.48/1.31  #Split   : 1
% 2.48/1.31  #Chain   : 0
% 2.48/1.31  #Close   : 0
% 2.48/1.31  
% 2.48/1.31  Ordering : KBO
% 2.48/1.31  
% 2.48/1.31  Simplification rules
% 2.48/1.31  ----------------------
% 2.48/1.31  #Subsume      : 24
% 2.48/1.31  #Demod        : 40
% 2.48/1.31  #Tautology    : 41
% 2.48/1.31  #SimpNegUnit  : 1
% 2.48/1.31  #BackRed      : 1
% 2.48/1.31  
% 2.48/1.31  #Partial instantiations: 0
% 2.48/1.31  #Strategies tried      : 1
% 2.48/1.31  
% 2.48/1.31  Timing (in seconds)
% 2.48/1.31  ----------------------
% 2.48/1.32  Preprocessing        : 0.27
% 2.48/1.32  Parsing              : 0.14
% 2.48/1.32  CNF conversion       : 0.02
% 2.48/1.32  Main loop            : 0.30
% 2.48/1.32  Inferencing          : 0.12
% 2.48/1.32  Reduction            : 0.08
% 2.48/1.32  Demodulation         : 0.05
% 2.48/1.32  BG Simplification    : 0.02
% 2.48/1.32  Subsumption          : 0.07
% 2.48/1.32  Abstraction          : 0.01
% 2.48/1.32  MUC search           : 0.00
% 2.48/1.32  Cooper               : 0.00
% 2.48/1.32  Total                : 0.59
% 2.48/1.32  Index Insertion      : 0.00
% 2.48/1.32  Index Deletion       : 0.00
% 2.48/1.32  Index Matching       : 0.00
% 2.48/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
