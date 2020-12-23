%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:12 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   39 (  47 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   63 (  87 expanded)
%              Number of equality atoms :   16 (  23 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => ( A = k1_xboole_0
          | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(B,C) )
     => ( A = k1_xboole_0
        | r1_tarski(B,k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & ! [D] :
            ( ( r1_tarski(D,B)
              & r1_tarski(D,C) )
           => r1_tarski(D,A) ) )
     => A = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(c_38,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_6'),k1_setfam_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_36,plain,(
    ! [A_15,B_16] :
      ( r2_hidden('#skF_4'(A_15,B_16),A_15)
      | r1_tarski(B_16,k1_setfam_1(A_15))
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_42,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_127,plain,(
    ! [A_48,B_49,C_50] :
      ( r1_tarski('#skF_3'(A_48,B_49,C_50),C_50)
      | k3_xboole_0(B_49,C_50) = A_48
      | ~ r1_tarski(A_48,C_50)
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_26,plain,(
    ! [A_9,B_10,C_11] :
      ( ~ r1_tarski('#skF_3'(A_9,B_10,C_11),A_9)
      | k3_xboole_0(B_10,C_11) = A_9
      | ~ r1_tarski(A_9,C_11)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_131,plain,(
    ! [B_49,C_50] :
      ( k3_xboole_0(B_49,C_50) = C_50
      | ~ r1_tarski(C_50,C_50)
      | ~ r1_tarski(C_50,B_49) ) ),
    inference(resolution,[status(thm)],[c_127,c_26])).

tff(c_143,plain,(
    ! [B_51,C_52] :
      ( k3_xboole_0(B_51,C_52) = C_52
      | ~ r1_tarski(C_52,B_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_131])).

tff(c_159,plain,(
    k3_xboole_0('#skF_6','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_42,c_143])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_191,plain,(
    ! [D_54] :
      ( r2_hidden(D_54,'#skF_6')
      | ~ r2_hidden(D_54,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_6])).

tff(c_195,plain,(
    ! [B_16] :
      ( r2_hidden('#skF_4'('#skF_5',B_16),'#skF_6')
      | r1_tarski(B_16,k1_setfam_1('#skF_5'))
      | k1_xboole_0 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_36,c_191])).

tff(c_318,plain,(
    ! [B_64] :
      ( r2_hidden('#skF_4'('#skF_5',B_64),'#skF_6')
      | r1_tarski(B_64,k1_setfam_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_195])).

tff(c_32,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_setfam_1(B_14),A_13)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_87,plain,(
    ! [B_34,A_35] :
      ( ~ r1_tarski(B_34,'#skF_4'(A_35,B_34))
      | r1_tarski(B_34,k1_setfam_1(A_35))
      | k1_xboole_0 = A_35 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_91,plain,(
    ! [B_14,A_35] :
      ( r1_tarski(k1_setfam_1(B_14),k1_setfam_1(A_35))
      | k1_xboole_0 = A_35
      | ~ r2_hidden('#skF_4'(A_35,k1_setfam_1(B_14)),B_14) ) ),
    inference(resolution,[status(thm)],[c_32,c_87])).

tff(c_322,plain,
    ( k1_xboole_0 = '#skF_5'
    | r1_tarski(k1_setfam_1('#skF_6'),k1_setfam_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_318,c_91])).

tff(c_326,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_40,c_38,c_322])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:18:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.41  
% 2.13/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.42  %$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.13/1.42  
% 2.13/1.42  %Foreground sorts:
% 2.13/1.42  
% 2.13/1.42  
% 2.13/1.42  %Background operators:
% 2.13/1.42  
% 2.13/1.42  
% 2.13/1.42  %Foreground operators:
% 2.13/1.42  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.13/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.13/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.13/1.42  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.13/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.42  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.13/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.13/1.42  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.13/1.42  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.13/1.42  
% 2.13/1.43  tff(f_73, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.13/1.43  tff(f_66, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(B, C))) => ((A = k1_xboole_0) | r1_tarski(B, k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_setfam_1)).
% 2.13/1.43  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.13/1.43  tff(f_53, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & (![D]: ((r1_tarski(D, B) & r1_tarski(D, C)) => r1_tarski(D, A)))) => (A = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_xboole_1)).
% 2.13/1.43  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.13/1.43  tff(f_57, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.13/1.43  tff(c_38, plain, (~r1_tarski(k1_setfam_1('#skF_6'), k1_setfam_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.13/1.43  tff(c_40, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.13/1.43  tff(c_36, plain, (![A_15, B_16]: (r2_hidden('#skF_4'(A_15, B_16), A_15) | r1_tarski(B_16, k1_setfam_1(A_15)) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.13/1.43  tff(c_42, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.13/1.43  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.13/1.43  tff(c_127, plain, (![A_48, B_49, C_50]: (r1_tarski('#skF_3'(A_48, B_49, C_50), C_50) | k3_xboole_0(B_49, C_50)=A_48 | ~r1_tarski(A_48, C_50) | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.13/1.43  tff(c_26, plain, (![A_9, B_10, C_11]: (~r1_tarski('#skF_3'(A_9, B_10, C_11), A_9) | k3_xboole_0(B_10, C_11)=A_9 | ~r1_tarski(A_9, C_11) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.13/1.43  tff(c_131, plain, (![B_49, C_50]: (k3_xboole_0(B_49, C_50)=C_50 | ~r1_tarski(C_50, C_50) | ~r1_tarski(C_50, B_49))), inference(resolution, [status(thm)], [c_127, c_26])).
% 2.13/1.43  tff(c_143, plain, (![B_51, C_52]: (k3_xboole_0(B_51, C_52)=C_52 | ~r1_tarski(C_52, B_51))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_131])).
% 2.13/1.43  tff(c_159, plain, (k3_xboole_0('#skF_6', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_42, c_143])).
% 2.13/1.43  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.13/1.43  tff(c_191, plain, (![D_54]: (r2_hidden(D_54, '#skF_6') | ~r2_hidden(D_54, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_159, c_6])).
% 2.13/1.43  tff(c_195, plain, (![B_16]: (r2_hidden('#skF_4'('#skF_5', B_16), '#skF_6') | r1_tarski(B_16, k1_setfam_1('#skF_5')) | k1_xboole_0='#skF_5')), inference(resolution, [status(thm)], [c_36, c_191])).
% 2.13/1.43  tff(c_318, plain, (![B_64]: (r2_hidden('#skF_4'('#skF_5', B_64), '#skF_6') | r1_tarski(B_64, k1_setfam_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_40, c_195])).
% 2.13/1.43  tff(c_32, plain, (![B_14, A_13]: (r1_tarski(k1_setfam_1(B_14), A_13) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.13/1.43  tff(c_87, plain, (![B_34, A_35]: (~r1_tarski(B_34, '#skF_4'(A_35, B_34)) | r1_tarski(B_34, k1_setfam_1(A_35)) | k1_xboole_0=A_35)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.13/1.43  tff(c_91, plain, (![B_14, A_35]: (r1_tarski(k1_setfam_1(B_14), k1_setfam_1(A_35)) | k1_xboole_0=A_35 | ~r2_hidden('#skF_4'(A_35, k1_setfam_1(B_14)), B_14))), inference(resolution, [status(thm)], [c_32, c_87])).
% 2.13/1.43  tff(c_322, plain, (k1_xboole_0='#skF_5' | r1_tarski(k1_setfam_1('#skF_6'), k1_setfam_1('#skF_5'))), inference(resolution, [status(thm)], [c_318, c_91])).
% 2.13/1.43  tff(c_326, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_40, c_38, c_322])).
% 2.13/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.43  
% 2.13/1.43  Inference rules
% 2.13/1.43  ----------------------
% 2.13/1.43  #Ref     : 0
% 2.13/1.43  #Sup     : 64
% 2.13/1.43  #Fact    : 0
% 2.13/1.43  #Define  : 0
% 2.13/1.43  #Split   : 1
% 2.13/1.43  #Chain   : 0
% 2.13/1.43  #Close   : 0
% 2.13/1.43  
% 2.13/1.43  Ordering : KBO
% 2.13/1.43  
% 2.13/1.43  Simplification rules
% 2.13/1.43  ----------------------
% 2.13/1.43  #Subsume      : 3
% 2.13/1.43  #Demod        : 6
% 2.13/1.43  #Tautology    : 32
% 2.13/1.43  #SimpNegUnit  : 2
% 2.13/1.43  #BackRed      : 0
% 2.13/1.43  
% 2.13/1.43  #Partial instantiations: 0
% 2.13/1.43  #Strategies tried      : 1
% 2.13/1.43  
% 2.13/1.43  Timing (in seconds)
% 2.13/1.43  ----------------------
% 2.13/1.43  Preprocessing        : 0.35
% 2.13/1.43  Parsing              : 0.16
% 2.13/1.43  CNF conversion       : 0.03
% 2.13/1.43  Main loop            : 0.24
% 2.13/1.43  Inferencing          : 0.08
% 2.13/1.43  Reduction            : 0.06
% 2.13/1.43  Demodulation         : 0.04
% 2.13/1.43  BG Simplification    : 0.02
% 2.13/1.43  Subsumption          : 0.06
% 2.13/1.43  Abstraction          : 0.01
% 2.13/1.43  MUC search           : 0.00
% 2.13/1.43  Cooper               : 0.00
% 2.13/1.43  Total                : 0.61
% 2.13/1.43  Index Insertion      : 0.00
% 2.13/1.43  Index Deletion       : 0.00
% 2.13/1.43  Index Matching       : 0.00
% 2.13/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
