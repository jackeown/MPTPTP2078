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
% DateTime   : Thu Dec  3 09:57:28 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
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
%$ r2_hidden > r1_tarski > r1_setfam_1 > k2_xboole_0 > #nlpp > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => r1_setfam_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_setfam_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_44,axiom,(
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

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_36,plain,(
    ~ r1_setfam_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_34,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_3'(A_11,B_12),A_11)
      | r1_setfam_1(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_38,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_41,plain,(
    ! [A_24,B_25] :
      ( k2_xboole_0(A_24,B_25) = B_25
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_49,plain,(
    k2_xboole_0('#skF_5','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_38,c_41])).

tff(c_82,plain,(
    ! [D_34,A_35,B_36] :
      ( ~ r2_hidden(D_34,A_35)
      | r2_hidden(D_34,k2_xboole_0(A_35,B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_89,plain,(
    ! [D_37] :
      ( ~ r2_hidden(D_37,'#skF_5')
      | r2_hidden(D_37,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_82])).

tff(c_94,plain,(
    ! [B_12] :
      ( r2_hidden('#skF_3'('#skF_5',B_12),'#skF_6')
      | r1_setfam_1('#skF_5',B_12) ) ),
    inference(resolution,[status(thm)],[c_34,c_89])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_96,plain,(
    ! [A_39,B_40,D_41] :
      ( ~ r1_tarski('#skF_3'(A_39,B_40),D_41)
      | ~ r2_hidden(D_41,B_40)
      | r1_setfam_1(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_122,plain,(
    ! [A_45,B_46] :
      ( ~ r2_hidden('#skF_3'(A_45,B_46),B_46)
      | r1_setfam_1(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_24,c_96])).

tff(c_126,plain,(
    r1_setfam_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_94,c_122])).

tff(c_142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_36,c_126])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:06:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.24  
% 1.95/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.24  %$ r2_hidden > r1_tarski > r1_setfam_1 > k2_xboole_0 > #nlpp > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2
% 1.95/1.24  
% 1.95/1.24  %Foreground sorts:
% 1.95/1.24  
% 1.95/1.24  
% 1.95/1.24  %Background operators:
% 1.95/1.24  
% 1.95/1.24  
% 1.95/1.24  %Foreground operators:
% 1.95/1.24  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.95/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.24  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.95/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.24  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.95/1.24  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.95/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.24  tff('#skF_5', type, '#skF_5': $i).
% 1.95/1.24  tff('#skF_6', type, '#skF_6': $i).
% 1.95/1.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.95/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.95/1.24  
% 1.95/1.25  tff(f_61, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => r1_setfam_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_setfam_1)).
% 1.95/1.25  tff(f_56, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 1.95/1.25  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.95/1.25  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 1.95/1.25  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.95/1.25  tff(c_36, plain, (~r1_setfam_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.95/1.25  tff(c_34, plain, (![A_11, B_12]: (r2_hidden('#skF_3'(A_11, B_12), A_11) | r1_setfam_1(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.95/1.25  tff(c_38, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.95/1.25  tff(c_41, plain, (![A_24, B_25]: (k2_xboole_0(A_24, B_25)=B_25 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.95/1.25  tff(c_49, plain, (k2_xboole_0('#skF_5', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_38, c_41])).
% 1.95/1.25  tff(c_82, plain, (![D_34, A_35, B_36]: (~r2_hidden(D_34, A_35) | r2_hidden(D_34, k2_xboole_0(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.95/1.25  tff(c_89, plain, (![D_37]: (~r2_hidden(D_37, '#skF_5') | r2_hidden(D_37, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_49, c_82])).
% 1.95/1.25  tff(c_94, plain, (![B_12]: (r2_hidden('#skF_3'('#skF_5', B_12), '#skF_6') | r1_setfam_1('#skF_5', B_12))), inference(resolution, [status(thm)], [c_34, c_89])).
% 1.95/1.25  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.95/1.25  tff(c_96, plain, (![A_39, B_40, D_41]: (~r1_tarski('#skF_3'(A_39, B_40), D_41) | ~r2_hidden(D_41, B_40) | r1_setfam_1(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.95/1.25  tff(c_122, plain, (![A_45, B_46]: (~r2_hidden('#skF_3'(A_45, B_46), B_46) | r1_setfam_1(A_45, B_46))), inference(resolution, [status(thm)], [c_24, c_96])).
% 1.95/1.25  tff(c_126, plain, (r1_setfam_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_94, c_122])).
% 1.95/1.25  tff(c_142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_36, c_126])).
% 1.95/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.25  
% 1.95/1.25  Inference rules
% 1.95/1.25  ----------------------
% 1.95/1.25  #Ref     : 0
% 1.95/1.25  #Sup     : 23
% 1.95/1.25  #Fact    : 0
% 1.95/1.25  #Define  : 0
% 1.95/1.25  #Split   : 1
% 1.95/1.25  #Chain   : 0
% 1.95/1.25  #Close   : 0
% 1.95/1.25  
% 1.95/1.25  Ordering : KBO
% 1.95/1.25  
% 1.95/1.25  Simplification rules
% 1.95/1.25  ----------------------
% 1.95/1.25  #Subsume      : 0
% 1.95/1.25  #Demod        : 2
% 1.95/1.25  #Tautology    : 13
% 1.95/1.25  #SimpNegUnit  : 1
% 1.95/1.25  #BackRed      : 0
% 1.95/1.25  
% 1.95/1.25  #Partial instantiations: 0
% 1.95/1.25  #Strategies tried      : 1
% 1.95/1.25  
% 1.95/1.25  Timing (in seconds)
% 1.95/1.25  ----------------------
% 1.95/1.25  Preprocessing        : 0.30
% 1.95/1.25  Parsing              : 0.16
% 1.95/1.25  CNF conversion       : 0.02
% 1.95/1.25  Main loop            : 0.14
% 1.95/1.25  Inferencing          : 0.05
% 1.95/1.25  Reduction            : 0.03
% 1.95/1.25  Demodulation         : 0.02
% 1.95/1.25  BG Simplification    : 0.02
% 1.95/1.25  Subsumption          : 0.04
% 1.95/1.25  Abstraction          : 0.01
% 1.95/1.25  MUC search           : 0.00
% 1.95/1.25  Cooper               : 0.00
% 1.95/1.25  Total                : 0.46
% 1.95/1.25  Index Insertion      : 0.00
% 1.95/1.25  Index Deletion       : 0.00
% 1.95/1.25  Index Matching       : 0.00
% 1.95/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
