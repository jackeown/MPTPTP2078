%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:30 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   39 (  48 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   49 (  70 expanded)
%              Number of equality atoms :    6 (   9 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2

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

tff(f_39,axiom,(
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

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(c_36,plain,(
    ~ r1_setfam_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_34,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_3'(A_12,B_13),A_12)
      | r1_setfam_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_38,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_53,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_65,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_53])).

tff(c_256,plain,(
    ! [D_51,A_52,B_53] :
      ( r2_hidden(D_51,k4_xboole_0(A_52,B_53))
      | r2_hidden(D_51,B_53)
      | ~ r2_hidden(D_51,A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_294,plain,(
    ! [D_57] :
      ( r2_hidden(D_57,k1_xboole_0)
      | r2_hidden(D_57,'#skF_6')
      | ~ r2_hidden(D_57,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_256])).

tff(c_26,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_224,plain,(
    ! [D_45,B_46,A_47] :
      ( ~ r2_hidden(D_45,B_46)
      | ~ r2_hidden(D_45,k4_xboole_0(A_47,B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_243,plain,(
    ! [D_45,A_11] :
      ( ~ r2_hidden(D_45,k1_xboole_0)
      | ~ r2_hidden(D_45,A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_224])).

tff(c_303,plain,(
    ! [D_58,A_59] :
      ( ~ r2_hidden(D_58,A_59)
      | r2_hidden(D_58,'#skF_6')
      | ~ r2_hidden(D_58,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_294,c_243])).

tff(c_558,plain,(
    ! [A_100,B_101] :
      ( r2_hidden('#skF_3'(A_100,B_101),'#skF_6')
      | ~ r2_hidden('#skF_3'(A_100,B_101),'#skF_5')
      | r1_setfam_1(A_100,B_101) ) ),
    inference(resolution,[status(thm)],[c_34,c_303])).

tff(c_610,plain,(
    ! [B_107] :
      ( r2_hidden('#skF_3'('#skF_5',B_107),'#skF_6')
      | r1_setfam_1('#skF_5',B_107) ) ),
    inference(resolution,[status(thm)],[c_34,c_558])).

tff(c_48,plain,(
    ! [A_25,B_26] : r1_tarski(k4_xboole_0(A_25,B_26),A_25) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_51,plain,(
    ! [A_11] : r1_tarski(A_11,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_48])).

tff(c_318,plain,(
    ! [A_62,B_63,D_64] :
      ( ~ r1_tarski('#skF_3'(A_62,B_63),D_64)
      | ~ r2_hidden(D_64,B_63)
      | r1_setfam_1(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_328,plain,(
    ! [A_62,B_63] :
      ( ~ r2_hidden('#skF_3'(A_62,B_63),B_63)
      | r1_setfam_1(A_62,B_63) ) ),
    inference(resolution,[status(thm)],[c_51,c_318])).

tff(c_617,plain,(
    r1_setfam_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_610,c_328])).

tff(c_624,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_36,c_617])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:08:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.33  
% 2.46/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.33  %$ r2_hidden > r1_tarski > r1_setfam_1 > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2
% 2.46/1.33  
% 2.46/1.33  %Foreground sorts:
% 2.46/1.33  
% 2.46/1.33  
% 2.46/1.33  %Background operators:
% 2.46/1.33  
% 2.46/1.33  
% 2.46/1.33  %Foreground operators:
% 2.46/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.46/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.33  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.46/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.46/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.46/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.46/1.33  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.46/1.33  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.46/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.46/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.46/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.46/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.46/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.33  
% 2.46/1.34  tff(f_60, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => r1_setfam_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_setfam_1)).
% 2.46/1.34  tff(f_55, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 2.46/1.34  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.46/1.34  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.46/1.34  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.46/1.34  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.46/1.34  tff(c_36, plain, (~r1_setfam_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.46/1.34  tff(c_34, plain, (![A_12, B_13]: (r2_hidden('#skF_3'(A_12, B_13), A_12) | r1_setfam_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.46/1.34  tff(c_38, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.46/1.34  tff(c_53, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.46/1.34  tff(c_65, plain, (k4_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_53])).
% 2.46/1.34  tff(c_256, plain, (![D_51, A_52, B_53]: (r2_hidden(D_51, k4_xboole_0(A_52, B_53)) | r2_hidden(D_51, B_53) | ~r2_hidden(D_51, A_52))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.46/1.34  tff(c_294, plain, (![D_57]: (r2_hidden(D_57, k1_xboole_0) | r2_hidden(D_57, '#skF_6') | ~r2_hidden(D_57, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_256])).
% 2.46/1.34  tff(c_26, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.46/1.34  tff(c_224, plain, (![D_45, B_46, A_47]: (~r2_hidden(D_45, B_46) | ~r2_hidden(D_45, k4_xboole_0(A_47, B_46)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.46/1.34  tff(c_243, plain, (![D_45, A_11]: (~r2_hidden(D_45, k1_xboole_0) | ~r2_hidden(D_45, A_11))), inference(superposition, [status(thm), theory('equality')], [c_26, c_224])).
% 2.46/1.34  tff(c_303, plain, (![D_58, A_59]: (~r2_hidden(D_58, A_59) | r2_hidden(D_58, '#skF_6') | ~r2_hidden(D_58, '#skF_5'))), inference(resolution, [status(thm)], [c_294, c_243])).
% 2.46/1.34  tff(c_558, plain, (![A_100, B_101]: (r2_hidden('#skF_3'(A_100, B_101), '#skF_6') | ~r2_hidden('#skF_3'(A_100, B_101), '#skF_5') | r1_setfam_1(A_100, B_101))), inference(resolution, [status(thm)], [c_34, c_303])).
% 2.46/1.34  tff(c_610, plain, (![B_107]: (r2_hidden('#skF_3'('#skF_5', B_107), '#skF_6') | r1_setfam_1('#skF_5', B_107))), inference(resolution, [status(thm)], [c_34, c_558])).
% 2.46/1.34  tff(c_48, plain, (![A_25, B_26]: (r1_tarski(k4_xboole_0(A_25, B_26), A_25))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.46/1.34  tff(c_51, plain, (![A_11]: (r1_tarski(A_11, A_11))), inference(superposition, [status(thm), theory('equality')], [c_26, c_48])).
% 2.46/1.34  tff(c_318, plain, (![A_62, B_63, D_64]: (~r1_tarski('#skF_3'(A_62, B_63), D_64) | ~r2_hidden(D_64, B_63) | r1_setfam_1(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.46/1.34  tff(c_328, plain, (![A_62, B_63]: (~r2_hidden('#skF_3'(A_62, B_63), B_63) | r1_setfam_1(A_62, B_63))), inference(resolution, [status(thm)], [c_51, c_318])).
% 2.46/1.34  tff(c_617, plain, (r1_setfam_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_610, c_328])).
% 2.46/1.34  tff(c_624, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_36, c_617])).
% 2.46/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.34  
% 2.46/1.34  Inference rules
% 2.46/1.34  ----------------------
% 2.46/1.34  #Ref     : 0
% 2.46/1.34  #Sup     : 134
% 2.46/1.34  #Fact    : 0
% 2.46/1.34  #Define  : 0
% 2.46/1.34  #Split   : 0
% 2.46/1.34  #Chain   : 0
% 2.46/1.34  #Close   : 0
% 2.46/1.34  
% 2.46/1.34  Ordering : KBO
% 2.46/1.34  
% 2.46/1.34  Simplification rules
% 2.46/1.34  ----------------------
% 2.46/1.34  #Subsume      : 17
% 2.46/1.34  #Demod        : 60
% 2.46/1.34  #Tautology    : 67
% 2.46/1.34  #SimpNegUnit  : 1
% 2.46/1.34  #BackRed      : 0
% 2.46/1.34  
% 2.46/1.34  #Partial instantiations: 0
% 2.46/1.34  #Strategies tried      : 1
% 2.46/1.34  
% 2.46/1.34  Timing (in seconds)
% 2.46/1.34  ----------------------
% 2.46/1.34  Preprocessing        : 0.28
% 2.46/1.34  Parsing              : 0.15
% 2.46/1.34  CNF conversion       : 0.02
% 2.46/1.34  Main loop            : 0.30
% 2.46/1.34  Inferencing          : 0.12
% 2.46/1.34  Reduction            : 0.08
% 2.46/1.34  Demodulation         : 0.06
% 2.46/1.34  BG Simplification    : 0.02
% 2.46/1.34  Subsumption          : 0.06
% 2.46/1.34  Abstraction          : 0.01
% 2.46/1.34  MUC search           : 0.00
% 2.46/1.34  Cooper               : 0.00
% 2.46/1.34  Total                : 0.60
% 2.46/1.34  Index Insertion      : 0.00
% 2.46/1.34  Index Deletion       : 0.00
% 2.46/1.34  Index Matching       : 0.00
% 2.46/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
