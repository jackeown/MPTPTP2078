%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:29 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   31 (  35 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  45 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k3_xboole_0 > #nlpp > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => r1_setfam_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_setfam_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_36,plain,(
    ~ r1_setfam_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_78,plain,(
    ! [A_34,B_35] :
      ( r2_hidden('#skF_3'(A_34,B_35),A_34)
      | r1_setfam_1(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_38,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_41,plain,(
    ! [A_24,B_25] :
      ( k3_xboole_0(A_24,B_25) = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_49,plain,(
    k3_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_38,c_41])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_66,plain,(
    ! [D_6] :
      ( r2_hidden(D_6,'#skF_6')
      | ~ r2_hidden(D_6,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_4])).

tff(c_92,plain,(
    ! [B_35] :
      ( r2_hidden('#skF_3'('#skF_5',B_35),'#skF_6')
      | r1_setfam_1('#skF_5',B_35) ) ),
    inference(resolution,[status(thm)],[c_78,c_66])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_106,plain,(
    ! [A_39,B_40,D_41] :
      ( ~ r1_tarski('#skF_3'(A_39,B_40),D_41)
      | ~ r2_hidden(D_41,B_40)
      | r1_setfam_1(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_127,plain,(
    ! [A_45,B_46] :
      ( ~ r2_hidden('#skF_3'(A_45,B_46),B_46)
      | r1_setfam_1(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_24,c_106])).

tff(c_135,plain,(
    r1_setfam_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_92,c_127])).

tff(c_144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_36,c_135])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:50:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.28  
% 1.83/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.28  %$ r2_hidden > r1_tarski > r1_setfam_1 > k3_xboole_0 > #nlpp > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2
% 1.83/1.28  
% 1.83/1.28  %Foreground sorts:
% 1.83/1.28  
% 1.83/1.28  
% 1.83/1.28  %Background operators:
% 1.83/1.28  
% 1.83/1.28  
% 1.83/1.28  %Foreground operators:
% 1.83/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.83/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.28  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.83/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.83/1.28  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.83/1.28  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.83/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.83/1.28  tff('#skF_5', type, '#skF_5': $i).
% 1.83/1.28  tff('#skF_6', type, '#skF_6': $i).
% 1.83/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.83/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.83/1.28  
% 1.83/1.29  tff(f_61, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => r1_setfam_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_setfam_1)).
% 1.83/1.29  tff(f_56, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 1.83/1.29  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.83/1.29  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.83/1.29  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.83/1.29  tff(c_36, plain, (~r1_setfam_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.83/1.29  tff(c_78, plain, (![A_34, B_35]: (r2_hidden('#skF_3'(A_34, B_35), A_34) | r1_setfam_1(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.83/1.29  tff(c_38, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.83/1.29  tff(c_41, plain, (![A_24, B_25]: (k3_xboole_0(A_24, B_25)=A_24 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.83/1.29  tff(c_49, plain, (k3_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_38, c_41])).
% 1.83/1.29  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.83/1.29  tff(c_66, plain, (![D_6]: (r2_hidden(D_6, '#skF_6') | ~r2_hidden(D_6, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_49, c_4])).
% 1.83/1.29  tff(c_92, plain, (![B_35]: (r2_hidden('#skF_3'('#skF_5', B_35), '#skF_6') | r1_setfam_1('#skF_5', B_35))), inference(resolution, [status(thm)], [c_78, c_66])).
% 1.83/1.29  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.83/1.29  tff(c_106, plain, (![A_39, B_40, D_41]: (~r1_tarski('#skF_3'(A_39, B_40), D_41) | ~r2_hidden(D_41, B_40) | r1_setfam_1(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.83/1.29  tff(c_127, plain, (![A_45, B_46]: (~r2_hidden('#skF_3'(A_45, B_46), B_46) | r1_setfam_1(A_45, B_46))), inference(resolution, [status(thm)], [c_24, c_106])).
% 1.83/1.29  tff(c_135, plain, (r1_setfam_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_92, c_127])).
% 1.83/1.29  tff(c_144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_36, c_135])).
% 1.83/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.29  
% 1.83/1.29  Inference rules
% 1.83/1.29  ----------------------
% 1.83/1.29  #Ref     : 0
% 1.83/1.29  #Sup     : 23
% 1.83/1.29  #Fact    : 0
% 1.83/1.29  #Define  : 0
% 1.83/1.29  #Split   : 1
% 1.83/1.29  #Chain   : 0
% 1.83/1.29  #Close   : 0
% 1.83/1.29  
% 1.83/1.29  Ordering : KBO
% 1.83/1.29  
% 1.83/1.29  Simplification rules
% 1.83/1.29  ----------------------
% 1.83/1.29  #Subsume      : 0
% 1.83/1.29  #Demod        : 2
% 1.83/1.29  #Tautology    : 13
% 1.83/1.29  #SimpNegUnit  : 1
% 1.83/1.29  #BackRed      : 0
% 1.83/1.29  
% 1.83/1.29  #Partial instantiations: 0
% 1.83/1.29  #Strategies tried      : 1
% 1.83/1.29  
% 1.83/1.29  Timing (in seconds)
% 1.83/1.29  ----------------------
% 1.83/1.29  Preprocessing        : 0.30
% 1.83/1.29  Parsing              : 0.16
% 1.83/1.29  CNF conversion       : 0.03
% 1.83/1.29  Main loop            : 0.14
% 1.83/1.29  Inferencing          : 0.05
% 1.83/1.29  Reduction            : 0.03
% 1.83/1.29  Demodulation         : 0.02
% 1.83/1.29  BG Simplification    : 0.02
% 1.83/1.29  Subsumption          : 0.03
% 1.83/1.29  Abstraction          : 0.01
% 1.83/1.29  MUC search           : 0.00
% 1.83/1.29  Cooper               : 0.00
% 1.83/1.29  Total                : 0.46
% 1.83/1.29  Index Insertion      : 0.00
% 1.83/1.29  Index Deletion       : 0.00
% 1.83/1.29  Index Matching       : 0.00
% 1.83/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
