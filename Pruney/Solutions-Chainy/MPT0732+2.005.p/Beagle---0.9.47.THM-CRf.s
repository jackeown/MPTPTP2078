%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:02 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   39 (  46 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 (  69 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_ordinal1 > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_ordinal1(C)
       => ( ( r2_hidden(A,B)
            & r2_hidden(B,C) )
         => r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_ordinal1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

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

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_34,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_38,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_40,plain,(
    v1_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_36,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_132,plain,(
    ! [B_35,A_36] :
      ( r1_tarski(B_35,A_36)
      | ~ r2_hidden(B_35,A_36)
      | ~ v1_ordinal1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_138,plain,
    ( r1_tarski('#skF_5','#skF_6')
    | ~ v1_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_132])).

tff(c_145,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_138])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_159,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_145,c_22])).

tff(c_260,plain,(
    ! [D_48,A_49,B_50] :
      ( r2_hidden(D_48,k4_xboole_0(A_49,B_50))
      | r2_hidden(D_48,B_50)
      | ~ r2_hidden(D_48,A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_302,plain,(
    ! [D_54] :
      ( r2_hidden(D_54,k1_xboole_0)
      | r2_hidden(D_54,'#skF_6')
      | ~ r2_hidden(D_54,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_260])).

tff(c_24,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_82,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(A_24,B_25) = k1_xboole_0
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_90,plain,(
    ! [A_9] : k4_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_82])).

tff(c_106,plain,(
    ! [D_29,B_30,A_31] :
      ( ~ r2_hidden(D_29,B_30)
      | ~ r2_hidden(D_29,k4_xboole_0(A_31,B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_115,plain,(
    ! [D_32,A_33] :
      ( ~ r2_hidden(D_32,A_33)
      | ~ r2_hidden(D_32,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_106])).

tff(c_124,plain,(
    ~ r2_hidden('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_38,c_115])).

tff(c_320,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_302,c_124])).

tff(c_338,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_320])).

tff(c_340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_338])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n014.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 20:16:07 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.28  
% 2.15/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.28  %$ r2_hidden > r1_tarski > v1_ordinal1 > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.15/1.28  
% 2.15/1.28  %Foreground sorts:
% 2.15/1.28  
% 2.15/1.28  
% 2.15/1.28  %Background operators:
% 2.15/1.28  
% 2.15/1.28  
% 2.15/1.28  %Foreground operators:
% 2.15/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.15/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.15/1.28  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 2.15/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.15/1.28  tff('#skF_6', type, '#skF_6': $i).
% 2.15/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.15/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.28  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.15/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.28  
% 2.15/1.29  tff(f_62, negated_conjecture, ~(![A, B, C]: (v1_ordinal1(C) => ((r2_hidden(A, B) & r2_hidden(B, C)) => r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_ordinal1)).
% 2.15/1.29  tff(f_48, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 2.15/1.29  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.15/1.29  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.15/1.29  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.15/1.29  tff(c_34, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.15/1.29  tff(c_38, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.15/1.29  tff(c_40, plain, (v1_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.15/1.29  tff(c_36, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.15/1.29  tff(c_132, plain, (![B_35, A_36]: (r1_tarski(B_35, A_36) | ~r2_hidden(B_35, A_36) | ~v1_ordinal1(A_36))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.15/1.29  tff(c_138, plain, (r1_tarski('#skF_5', '#skF_6') | ~v1_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_132])).
% 2.15/1.29  tff(c_145, plain, (r1_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_138])).
% 2.15/1.29  tff(c_22, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.15/1.29  tff(c_159, plain, (k4_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_145, c_22])).
% 2.15/1.29  tff(c_260, plain, (![D_48, A_49, B_50]: (r2_hidden(D_48, k4_xboole_0(A_49, B_50)) | r2_hidden(D_48, B_50) | ~r2_hidden(D_48, A_49))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.15/1.29  tff(c_302, plain, (![D_54]: (r2_hidden(D_54, k1_xboole_0) | r2_hidden(D_54, '#skF_6') | ~r2_hidden(D_54, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_159, c_260])).
% 2.15/1.29  tff(c_24, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.15/1.29  tff(c_82, plain, (![A_24, B_25]: (k4_xboole_0(A_24, B_25)=k1_xboole_0 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.15/1.29  tff(c_90, plain, (![A_9]: (k4_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_82])).
% 2.15/1.29  tff(c_106, plain, (![D_29, B_30, A_31]: (~r2_hidden(D_29, B_30) | ~r2_hidden(D_29, k4_xboole_0(A_31, B_30)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.15/1.29  tff(c_115, plain, (![D_32, A_33]: (~r2_hidden(D_32, A_33) | ~r2_hidden(D_32, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_90, c_106])).
% 2.15/1.29  tff(c_124, plain, (~r2_hidden('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_115])).
% 2.15/1.29  tff(c_320, plain, (r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_302, c_124])).
% 2.15/1.29  tff(c_338, plain, (r2_hidden('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_320])).
% 2.15/1.29  tff(c_340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_338])).
% 2.15/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.29  
% 2.15/1.29  Inference rules
% 2.15/1.29  ----------------------
% 2.15/1.29  #Ref     : 0
% 2.15/1.29  #Sup     : 66
% 2.15/1.29  #Fact    : 0
% 2.15/1.29  #Define  : 0
% 2.15/1.29  #Split   : 1
% 2.15/1.29  #Chain   : 0
% 2.15/1.29  #Close   : 0
% 2.15/1.29  
% 2.15/1.29  Ordering : KBO
% 2.15/1.29  
% 2.15/1.29  Simplification rules
% 2.15/1.29  ----------------------
% 2.15/1.29  #Subsume      : 2
% 2.15/1.29  #Demod        : 32
% 2.15/1.29  #Tautology    : 26
% 2.15/1.29  #SimpNegUnit  : 1
% 2.15/1.29  #BackRed      : 0
% 2.15/1.29  
% 2.15/1.29  #Partial instantiations: 0
% 2.15/1.29  #Strategies tried      : 1
% 2.15/1.29  
% 2.15/1.29  Timing (in seconds)
% 2.15/1.29  ----------------------
% 2.15/1.30  Preprocessing        : 0.29
% 2.15/1.30  Parsing              : 0.16
% 2.15/1.30  CNF conversion       : 0.02
% 2.15/1.30  Main loop            : 0.23
% 2.15/1.30  Inferencing          : 0.09
% 2.15/1.30  Reduction            : 0.06
% 2.15/1.30  Demodulation         : 0.05
% 2.15/1.30  BG Simplification    : 0.02
% 2.15/1.30  Subsumption          : 0.05
% 2.15/1.30  Abstraction          : 0.01
% 2.15/1.30  MUC search           : 0.00
% 2.15/1.30  Cooper               : 0.00
% 2.15/1.30  Total                : 0.55
% 2.15/1.30  Index Insertion      : 0.00
% 2.15/1.30  Index Deletion       : 0.00
% 2.15/1.30  Index Matching       : 0.00
% 2.15/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
