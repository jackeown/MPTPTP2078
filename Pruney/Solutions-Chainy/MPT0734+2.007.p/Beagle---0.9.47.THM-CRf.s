%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:03 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   42 (  52 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   66 ( 111 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( v1_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ! [C] :
                ( v3_ordinal1(C)
               => ( ( r1_tarski(A,B)
                    & r2_hidden(B,C) )
                 => r2_hidden(A,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_ordinal1)).

tff(f_65,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_44,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).

tff(c_26,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_54,plain,(
    ! [B_23,A_24] :
      ( ~ r1_tarski(B_23,A_24)
      | ~ r2_hidden(A_24,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_58,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_54])).

tff(c_28,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_30,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_36,plain,(
    ! [A_21] :
      ( v1_ordinal1(A_21)
      | ~ v3_ordinal1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_43,plain,(
    v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_36])).

tff(c_78,plain,(
    ! [B_32,A_33] :
      ( r1_tarski(B_32,A_33)
      | ~ r2_hidden(B_32,A_33)
      | ~ v1_ordinal1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_84,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_78])).

tff(c_88,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_84])).

tff(c_89,plain,(
    ! [A_34,C_35,B_36] :
      ( r1_tarski(A_34,C_35)
      | ~ r1_tarski(B_36,C_35)
      | ~ r1_tarski(A_34,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_97,plain,(
    ! [A_38] :
      ( r1_tarski(A_38,'#skF_4')
      | ~ r1_tarski(A_38,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_88,c_89])).

tff(c_101,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_97])).

tff(c_34,plain,(
    v1_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_102,plain,(
    ! [A_39,B_40] :
      ( r2_hidden(A_39,B_40)
      | ~ r2_xboole_0(A_39,B_40)
      | ~ v3_ordinal1(B_40)
      | ~ v1_ordinal1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_111,plain,(
    ! [A_42,B_43] :
      ( r2_hidden(A_42,B_43)
      | ~ v3_ordinal1(B_43)
      | ~ v1_ordinal1(A_42)
      | B_43 = A_42
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(resolution,[status(thm)],[c_2,c_102])).

tff(c_24,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_120,plain,
    ( ~ v3_ordinal1('#skF_4')
    | ~ v1_ordinal1('#skF_2')
    | '#skF_2' = '#skF_4'
    | ~ r1_tarski('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_111,c_24])).

tff(c_125,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_34,c_30,c_120])).

tff(c_130,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_28])).

tff(c_133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_130])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:46:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.18  
% 2.10/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.18  %$ r2_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.10/1.18  
% 2.10/1.18  %Foreground sorts:
% 2.10/1.18  
% 2.10/1.18  
% 2.10/1.18  %Background operators:
% 2.10/1.18  
% 2.10/1.18  
% 2.10/1.18  %Foreground operators:
% 2.10/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.18  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 2.10/1.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.10/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.18  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.18  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.18  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.10/1.18  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 2.10/1.18  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.10/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.18  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.18  
% 2.10/1.19  tff(f_80, negated_conjecture, ~(![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (![C]: (v3_ordinal1(C) => ((r1_tarski(A, B) & r2_hidden(B, C)) => r2_hidden(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_ordinal1)).
% 2.10/1.19  tff(f_65, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.10/1.19  tff(f_44, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 2.10/1.19  tff(f_51, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 2.10/1.19  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.10/1.19  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.10/1.19  tff(f_60, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_ordinal1)).
% 2.10/1.19  tff(c_26, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.10/1.19  tff(c_54, plain, (![B_23, A_24]: (~r1_tarski(B_23, A_24) | ~r2_hidden(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.10/1.19  tff(c_58, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_54])).
% 2.10/1.19  tff(c_28, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.10/1.19  tff(c_30, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.10/1.19  tff(c_36, plain, (![A_21]: (v1_ordinal1(A_21) | ~v3_ordinal1(A_21))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.10/1.19  tff(c_43, plain, (v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_36])).
% 2.10/1.19  tff(c_78, plain, (![B_32, A_33]: (r1_tarski(B_32, A_33) | ~r2_hidden(B_32, A_33) | ~v1_ordinal1(A_33))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.10/1.19  tff(c_84, plain, (r1_tarski('#skF_3', '#skF_4') | ~v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_78])).
% 2.10/1.19  tff(c_88, plain, (r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_43, c_84])).
% 2.10/1.19  tff(c_89, plain, (![A_34, C_35, B_36]: (r1_tarski(A_34, C_35) | ~r1_tarski(B_36, C_35) | ~r1_tarski(A_34, B_36))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.10/1.19  tff(c_97, plain, (![A_38]: (r1_tarski(A_38, '#skF_4') | ~r1_tarski(A_38, '#skF_3'))), inference(resolution, [status(thm)], [c_88, c_89])).
% 2.10/1.19  tff(c_101, plain, (r1_tarski('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_97])).
% 2.10/1.19  tff(c_34, plain, (v1_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.10/1.19  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.10/1.19  tff(c_102, plain, (![A_39, B_40]: (r2_hidden(A_39, B_40) | ~r2_xboole_0(A_39, B_40) | ~v3_ordinal1(B_40) | ~v1_ordinal1(A_39))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.10/1.20  tff(c_111, plain, (![A_42, B_43]: (r2_hidden(A_42, B_43) | ~v3_ordinal1(B_43) | ~v1_ordinal1(A_42) | B_43=A_42 | ~r1_tarski(A_42, B_43))), inference(resolution, [status(thm)], [c_2, c_102])).
% 2.10/1.20  tff(c_24, plain, (~r2_hidden('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.10/1.20  tff(c_120, plain, (~v3_ordinal1('#skF_4') | ~v1_ordinal1('#skF_2') | '#skF_2'='#skF_4' | ~r1_tarski('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_111, c_24])).
% 2.10/1.20  tff(c_125, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_101, c_34, c_30, c_120])).
% 2.10/1.20  tff(c_130, plain, (r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_125, c_28])).
% 2.10/1.20  tff(c_133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_130])).
% 2.10/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.20  
% 2.10/1.20  Inference rules
% 2.10/1.20  ----------------------
% 2.10/1.20  #Ref     : 0
% 2.10/1.20  #Sup     : 18
% 2.10/1.20  #Fact    : 0
% 2.10/1.20  #Define  : 0
% 2.10/1.20  #Split   : 0
% 2.10/1.20  #Chain   : 0
% 2.10/1.20  #Close   : 0
% 2.10/1.20  
% 2.10/1.20  Ordering : KBO
% 2.10/1.20  
% 2.10/1.20  Simplification rules
% 2.10/1.20  ----------------------
% 2.10/1.20  #Subsume      : 0
% 2.10/1.20  #Demod        : 10
% 2.10/1.20  #Tautology    : 5
% 2.10/1.20  #SimpNegUnit  : 1
% 2.10/1.20  #BackRed      : 5
% 2.10/1.20  
% 2.10/1.20  #Partial instantiations: 0
% 2.10/1.20  #Strategies tried      : 1
% 2.10/1.20  
% 2.10/1.20  Timing (in seconds)
% 2.10/1.20  ----------------------
% 2.10/1.20  Preprocessing        : 0.28
% 2.10/1.20  Parsing              : 0.15
% 2.10/1.20  CNF conversion       : 0.02
% 2.10/1.20  Main loop            : 0.16
% 2.10/1.20  Inferencing          : 0.07
% 2.10/1.20  Reduction            : 0.04
% 2.10/1.20  Demodulation         : 0.03
% 2.10/1.20  BG Simplification    : 0.01
% 2.10/1.20  Subsumption          : 0.03
% 2.10/1.20  Abstraction          : 0.01
% 2.10/1.20  MUC search           : 0.00
% 2.10/1.20  Cooper               : 0.00
% 2.10/1.20  Total                : 0.47
% 2.10/1.20  Index Insertion      : 0.00
% 2.10/1.20  Index Deletion       : 0.00
% 2.10/1.20  Index Matching       : 0.00
% 2.10/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
