%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:29 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   38 (  48 expanded)
%              Number of leaves         :   19 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  75 expanded)
%              Number of equality atoms :    6 (  10 expanded)
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

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => r1_setfam_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_setfam_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_38,plain,(
    ~ r1_setfam_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_36,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_3'(A_11,B_12),A_11)
      | r1_setfam_1(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_40,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_44,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(A_26,B_27) = k1_xboole_0
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_56,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_44])).

tff(c_173,plain,(
    ! [D_53,A_54,B_55] :
      ( r2_hidden(D_53,k4_xboole_0(A_54,B_55))
      | r2_hidden(D_53,B_55)
      | ~ r2_hidden(D_53,A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_191,plain,(
    ! [D_56] :
      ( r2_hidden(D_56,k1_xboole_0)
      | r2_hidden(D_56,'#skF_6')
      | ~ r2_hidden(D_56,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_173])).

tff(c_76,plain,(
    ! [A_34,B_35] :
      ( r2_hidden('#skF_3'(A_34,B_35),A_34)
      | r1_setfam_1(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_58,plain,(
    ! [B_31] : k4_xboole_0(B_31,B_31) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_44])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_63,plain,(
    ! [D_6,B_31] :
      ( ~ r2_hidden(D_6,B_31)
      | ~ r2_hidden(D_6,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_4])).

tff(c_83,plain,(
    ! [A_34,B_35] :
      ( ~ r2_hidden('#skF_3'(A_34,B_35),k1_xboole_0)
      | r1_setfam_1(A_34,B_35) ) ),
    inference(resolution,[status(thm)],[c_76,c_63])).

tff(c_218,plain,(
    ! [A_62,B_63] :
      ( r1_setfam_1(A_62,B_63)
      | r2_hidden('#skF_3'(A_62,B_63),'#skF_6')
      | ~ r2_hidden('#skF_3'(A_62,B_63),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_191,c_83])).

tff(c_236,plain,(
    ! [B_67] :
      ( r2_hidden('#skF_3'('#skF_5',B_67),'#skF_6')
      | r1_setfam_1('#skF_5',B_67) ) ),
    inference(resolution,[status(thm)],[c_36,c_218])).

tff(c_207,plain,(
    ! [A_59,B_60,D_61] :
      ( ~ r1_tarski('#skF_3'(A_59,B_60),D_61)
      | ~ r2_hidden(D_61,B_60)
      | r1_setfam_1(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_217,plain,(
    ! [A_59,B_60] :
      ( ~ r2_hidden('#skF_3'(A_59,B_60),B_60)
      | r1_setfam_1(A_59,B_60) ) ),
    inference(resolution,[status(thm)],[c_24,c_207])).

tff(c_240,plain,(
    r1_setfam_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_236,c_217])).

tff(c_246,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_38,c_240])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:16:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.22  
% 1.93/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.22  %$ r2_hidden > r1_tarski > r1_setfam_1 > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2
% 1.93/1.22  
% 1.93/1.22  %Foreground sorts:
% 1.93/1.22  
% 1.93/1.22  
% 1.93/1.22  %Background operators:
% 1.93/1.22  
% 1.93/1.22  
% 1.93/1.22  %Foreground operators:
% 1.93/1.22  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.93/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.22  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.93/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.93/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.22  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.93/1.22  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.93/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.22  tff('#skF_5', type, '#skF_5': $i).
% 1.93/1.22  tff('#skF_6', type, '#skF_6': $i).
% 1.93/1.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.93/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.22  
% 1.93/1.23  tff(f_62, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => r1_setfam_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_setfam_1)).
% 1.93/1.23  tff(f_57, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 1.93/1.23  tff(f_45, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.93/1.23  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.93/1.23  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.93/1.23  tff(c_38, plain, (~r1_setfam_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.93/1.23  tff(c_36, plain, (![A_11, B_12]: (r2_hidden('#skF_3'(A_11, B_12), A_11) | r1_setfam_1(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.93/1.23  tff(c_40, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.93/1.23  tff(c_44, plain, (![A_26, B_27]: (k4_xboole_0(A_26, B_27)=k1_xboole_0 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.93/1.23  tff(c_56, plain, (k4_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_44])).
% 1.93/1.23  tff(c_173, plain, (![D_53, A_54, B_55]: (r2_hidden(D_53, k4_xboole_0(A_54, B_55)) | r2_hidden(D_53, B_55) | ~r2_hidden(D_53, A_54))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.93/1.23  tff(c_191, plain, (![D_56]: (r2_hidden(D_56, k1_xboole_0) | r2_hidden(D_56, '#skF_6') | ~r2_hidden(D_56, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_173])).
% 1.93/1.23  tff(c_76, plain, (![A_34, B_35]: (r2_hidden('#skF_3'(A_34, B_35), A_34) | r1_setfam_1(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.93/1.23  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.93/1.23  tff(c_58, plain, (![B_31]: (k4_xboole_0(B_31, B_31)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_44])).
% 1.93/1.23  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.93/1.23  tff(c_63, plain, (![D_6, B_31]: (~r2_hidden(D_6, B_31) | ~r2_hidden(D_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_58, c_4])).
% 1.93/1.23  tff(c_83, plain, (![A_34, B_35]: (~r2_hidden('#skF_3'(A_34, B_35), k1_xboole_0) | r1_setfam_1(A_34, B_35))), inference(resolution, [status(thm)], [c_76, c_63])).
% 1.93/1.23  tff(c_218, plain, (![A_62, B_63]: (r1_setfam_1(A_62, B_63) | r2_hidden('#skF_3'(A_62, B_63), '#skF_6') | ~r2_hidden('#skF_3'(A_62, B_63), '#skF_5'))), inference(resolution, [status(thm)], [c_191, c_83])).
% 1.93/1.23  tff(c_236, plain, (![B_67]: (r2_hidden('#skF_3'('#skF_5', B_67), '#skF_6') | r1_setfam_1('#skF_5', B_67))), inference(resolution, [status(thm)], [c_36, c_218])).
% 1.93/1.23  tff(c_207, plain, (![A_59, B_60, D_61]: (~r1_tarski('#skF_3'(A_59, B_60), D_61) | ~r2_hidden(D_61, B_60) | r1_setfam_1(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.93/1.23  tff(c_217, plain, (![A_59, B_60]: (~r2_hidden('#skF_3'(A_59, B_60), B_60) | r1_setfam_1(A_59, B_60))), inference(resolution, [status(thm)], [c_24, c_207])).
% 1.93/1.23  tff(c_240, plain, (r1_setfam_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_236, c_217])).
% 1.93/1.23  tff(c_246, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_38, c_240])).
% 1.93/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.23  
% 1.93/1.23  Inference rules
% 1.93/1.23  ----------------------
% 1.93/1.23  #Ref     : 0
% 1.93/1.23  #Sup     : 44
% 1.93/1.23  #Fact    : 0
% 1.93/1.23  #Define  : 0
% 1.93/1.23  #Split   : 1
% 1.93/1.23  #Chain   : 0
% 1.93/1.23  #Close   : 0
% 1.93/1.23  
% 1.93/1.23  Ordering : KBO
% 1.93/1.23  
% 1.93/1.23  Simplification rules
% 1.93/1.23  ----------------------
% 1.93/1.23  #Subsume      : 7
% 1.93/1.23  #Demod        : 8
% 2.04/1.23  #Tautology    : 16
% 2.04/1.23  #SimpNegUnit  : 1
% 2.04/1.23  #BackRed      : 0
% 2.04/1.23  
% 2.04/1.23  #Partial instantiations: 0
% 2.04/1.23  #Strategies tried      : 1
% 2.04/1.23  
% 2.04/1.23  Timing (in seconds)
% 2.04/1.23  ----------------------
% 2.04/1.23  Preprocessing        : 0.28
% 2.04/1.23  Parsing              : 0.15
% 2.04/1.23  CNF conversion       : 0.02
% 2.04/1.23  Main loop            : 0.20
% 2.04/1.23  Inferencing          : 0.08
% 2.04/1.23  Reduction            : 0.05
% 2.04/1.23  Demodulation         : 0.03
% 2.04/1.23  BG Simplification    : 0.02
% 2.04/1.23  Subsumption          : 0.05
% 2.04/1.23  Abstraction          : 0.01
% 2.04/1.23  MUC search           : 0.00
% 2.04/1.23  Cooper               : 0.00
% 2.04/1.23  Total                : 0.50
% 2.04/1.23  Index Insertion      : 0.00
% 2.04/1.23  Index Deletion       : 0.00
% 2.04/1.23  Index Matching       : 0.00
% 2.04/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
