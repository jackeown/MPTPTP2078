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
% DateTime   : Thu Dec  3 09:42:46 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   38 (  97 expanded)
%              Number of leaves         :   15 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :   49 ( 180 expanded)
%              Number of equality atoms :   11 (  47 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k4_xboole_0(B,A))
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

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

tff(c_26,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_30,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = k1_xboole_0
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_38,plain,(
    ! [A_9] : k4_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_30])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    r1_tarski('#skF_3',k4_xboole_0('#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_37,plain,(
    k4_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_30])).

tff(c_71,plain,(
    ! [D_25,A_26,B_27] :
      ( r2_hidden(D_25,k4_xboole_0(A_26,B_27))
      | r2_hidden(D_25,B_27)
      | ~ r2_hidden(D_25,A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_90,plain,(
    ! [D_31] :
      ( r2_hidden(D_31,k1_xboole_0)
      | r2_hidden(D_31,k4_xboole_0('#skF_4','#skF_3'))
      | ~ r2_hidden(D_31,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_71])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_100,plain,(
    ! [D_31] :
      ( r2_hidden(D_31,k1_xboole_0)
      | ~ r2_hidden(D_31,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_90,c_4])).

tff(c_143,plain,(
    ! [D_35] :
      ( r2_hidden(D_35,k1_xboole_0)
      | ~ r2_hidden(D_35,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_90,c_4])).

tff(c_63,plain,(
    ! [D_20,B_21,A_22] :
      ( ~ r2_hidden(D_20,B_21)
      | ~ r2_hidden(D_20,k4_xboole_0(A_22,B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_69,plain,(
    ! [D_20,A_9] :
      ( ~ r2_hidden(D_20,A_9)
      | ~ r2_hidden(D_20,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_63])).

tff(c_154,plain,(
    ! [D_36] :
      ( ~ r2_hidden(D_36,k1_xboole_0)
      | ~ r2_hidden(D_36,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_143,c_69])).

tff(c_164,plain,(
    ! [D_31] : ~ r2_hidden(D_31,'#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_154])).

tff(c_55,plain,(
    ! [D_16,A_17,B_18] :
      ( r2_hidden(D_16,A_17)
      | ~ r2_hidden(D_16,k4_xboole_0(A_17,B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_58,plain,(
    ! [D_16] :
      ( r2_hidden(D_16,'#skF_3')
      | ~ r2_hidden(D_16,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_55])).

tff(c_176,plain,(
    ! [D_38] : ~ r2_hidden(D_38,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_58])).

tff(c_180,plain,(
    ! [B_2,C_3] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_2,C_3),C_3)
      | k4_xboole_0(k1_xboole_0,B_2) = C_3 ) ),
    inference(resolution,[status(thm)],[c_18,c_176])).

tff(c_185,plain,(
    ! [B_39,C_40] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_39,C_40),C_40)
      | k1_xboole_0 = C_40 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_180])).

tff(c_193,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_185,c_164])).

tff(c_207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_193])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:19:47 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.29  
% 1.87/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.29  %$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.87/1.29  
% 1.87/1.29  %Foreground sorts:
% 1.87/1.29  
% 1.87/1.29  
% 1.87/1.29  %Background operators:
% 1.87/1.29  
% 1.87/1.29  
% 1.87/1.29  %Foreground operators:
% 1.87/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.87/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.87/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.87/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.29  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.87/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.29  tff('#skF_4', type, '#skF_4': $i).
% 1.87/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.29  
% 1.87/1.30  tff(f_46, negated_conjecture, ~(![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 1.87/1.30  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.87/1.30  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.87/1.30  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.87/1.30  tff(c_26, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.87/1.30  tff(c_24, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.87/1.30  tff(c_30, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=k1_xboole_0 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.87/1.30  tff(c_38, plain, (![A_9]: (k4_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_30])).
% 1.87/1.30  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.87/1.30  tff(c_28, plain, (r1_tarski('#skF_3', k4_xboole_0('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.87/1.30  tff(c_37, plain, (k4_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_30])).
% 1.87/1.30  tff(c_71, plain, (![D_25, A_26, B_27]: (r2_hidden(D_25, k4_xboole_0(A_26, B_27)) | r2_hidden(D_25, B_27) | ~r2_hidden(D_25, A_26))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.87/1.30  tff(c_90, plain, (![D_31]: (r2_hidden(D_31, k1_xboole_0) | r2_hidden(D_31, k4_xboole_0('#skF_4', '#skF_3')) | ~r2_hidden(D_31, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_37, c_71])).
% 1.87/1.30  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.87/1.30  tff(c_100, plain, (![D_31]: (r2_hidden(D_31, k1_xboole_0) | ~r2_hidden(D_31, '#skF_3'))), inference(resolution, [status(thm)], [c_90, c_4])).
% 1.87/1.30  tff(c_143, plain, (![D_35]: (r2_hidden(D_35, k1_xboole_0) | ~r2_hidden(D_35, '#skF_3'))), inference(resolution, [status(thm)], [c_90, c_4])).
% 1.87/1.30  tff(c_63, plain, (![D_20, B_21, A_22]: (~r2_hidden(D_20, B_21) | ~r2_hidden(D_20, k4_xboole_0(A_22, B_21)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.87/1.30  tff(c_69, plain, (![D_20, A_9]: (~r2_hidden(D_20, A_9) | ~r2_hidden(D_20, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_63])).
% 1.87/1.30  tff(c_154, plain, (![D_36]: (~r2_hidden(D_36, k1_xboole_0) | ~r2_hidden(D_36, '#skF_3'))), inference(resolution, [status(thm)], [c_143, c_69])).
% 1.87/1.30  tff(c_164, plain, (![D_31]: (~r2_hidden(D_31, '#skF_3'))), inference(resolution, [status(thm)], [c_100, c_154])).
% 1.87/1.30  tff(c_55, plain, (![D_16, A_17, B_18]: (r2_hidden(D_16, A_17) | ~r2_hidden(D_16, k4_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.87/1.30  tff(c_58, plain, (![D_16]: (r2_hidden(D_16, '#skF_3') | ~r2_hidden(D_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_37, c_55])).
% 1.87/1.30  tff(c_176, plain, (![D_38]: (~r2_hidden(D_38, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_164, c_58])).
% 1.87/1.30  tff(c_180, plain, (![B_2, C_3]: (r2_hidden('#skF_2'(k1_xboole_0, B_2, C_3), C_3) | k4_xboole_0(k1_xboole_0, B_2)=C_3)), inference(resolution, [status(thm)], [c_18, c_176])).
% 1.87/1.30  tff(c_185, plain, (![B_39, C_40]: (r2_hidden('#skF_2'(k1_xboole_0, B_39, C_40), C_40) | k1_xboole_0=C_40)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_180])).
% 1.87/1.30  tff(c_193, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_185, c_164])).
% 1.87/1.30  tff(c_207, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_193])).
% 1.87/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.30  
% 1.87/1.30  Inference rules
% 1.87/1.30  ----------------------
% 1.87/1.30  #Ref     : 0
% 1.87/1.30  #Sup     : 38
% 1.87/1.30  #Fact    : 0
% 1.87/1.30  #Define  : 0
% 1.87/1.30  #Split   : 0
% 1.87/1.30  #Chain   : 0
% 1.87/1.30  #Close   : 0
% 1.87/1.30  
% 1.87/1.30  Ordering : KBO
% 1.87/1.30  
% 1.87/1.30  Simplification rules
% 1.87/1.30  ----------------------
% 1.87/1.30  #Subsume      : 7
% 1.87/1.30  #Demod        : 4
% 1.87/1.30  #Tautology    : 11
% 1.87/1.30  #SimpNegUnit  : 2
% 1.87/1.30  #BackRed      : 1
% 1.87/1.30  
% 1.87/1.30  #Partial instantiations: 0
% 1.87/1.30  #Strategies tried      : 1
% 1.87/1.30  
% 1.87/1.30  Timing (in seconds)
% 1.87/1.30  ----------------------
% 1.87/1.31  Preprocessing        : 0.30
% 1.87/1.31  Parsing              : 0.15
% 1.87/1.31  CNF conversion       : 0.02
% 1.87/1.31  Main loop            : 0.16
% 1.87/1.31  Inferencing          : 0.06
% 1.87/1.31  Reduction            : 0.04
% 1.87/1.31  Demodulation         : 0.03
% 1.87/1.31  BG Simplification    : 0.02
% 1.87/1.31  Subsumption          : 0.04
% 1.87/1.31  Abstraction          : 0.01
% 1.87/1.31  MUC search           : 0.00
% 1.87/1.31  Cooper               : 0.00
% 1.87/1.31  Total                : 0.49
% 1.87/1.31  Index Insertion      : 0.00
% 1.87/1.31  Index Deletion       : 0.00
% 1.87/1.31  Index Matching       : 0.00
% 1.87/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
