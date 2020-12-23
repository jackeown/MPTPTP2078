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
% DateTime   : Thu Dec  3 10:10:36 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   33 (  35 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   48 (  64 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r8_relat_2 > r2_hidden > v8_relat_2 > v1_relat_1 > k4_tarski > #nlpp > k1_wellord2 > #skF_6 > #skF_2 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r8_relat_2,type,(
    r8_relat_2: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_56,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_58,axiom,(
    ! [A] : v8_relat_2(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_wellord2)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r8_relat_2(A,B)
        <=> ! [C,D,E] :
              ( ( r2_hidden(C,B)
                & r2_hidden(D,B)
                & r2_hidden(E,B)
                & r2_hidden(k4_tarski(C,D),A)
                & r2_hidden(k4_tarski(D,E),A) )
             => r2_hidden(k4_tarski(C,E),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_2)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v8_relat_2(A)
      <=> ! [B,C,D] :
            ( ( r2_hidden(k4_tarski(B,C),A)
              & r2_hidden(k4_tarski(C,D),A) )
           => r2_hidden(k4_tarski(B,D),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l2_wellord1)).

tff(f_61,negated_conjecture,(
    ~ ! [A] : r8_relat_2(k1_wellord2(A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_wellord2)).

tff(c_24,plain,(
    ! [A_35] : v1_relat_1(k1_wellord2(A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_26,plain,(
    ! [A_36] : v8_relat_2(k1_wellord2(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16,plain,(
    ! [A_11,B_25] :
      ( r2_hidden(k4_tarski('#skF_4'(A_11,B_25),'#skF_5'(A_11,B_25)),A_11)
      | r8_relat_2(A_11,B_25)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14,plain,(
    ! [A_11,B_25] :
      ( r2_hidden(k4_tarski('#skF_5'(A_11,B_25),'#skF_6'(A_11,B_25)),A_11)
      | r8_relat_2(A_11,B_25)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_40,plain,(
    ! [B_54,D_55,A_56,C_57] :
      ( r2_hidden(k4_tarski(B_54,D_55),A_56)
      | ~ r2_hidden(k4_tarski(C_57,D_55),A_56)
      | ~ r2_hidden(k4_tarski(B_54,C_57),A_56)
      | ~ v8_relat_2(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_53,plain,(
    ! [B_58,A_59,B_60] :
      ( r2_hidden(k4_tarski(B_58,'#skF_6'(A_59,B_60)),A_59)
      | ~ r2_hidden(k4_tarski(B_58,'#skF_5'(A_59,B_60)),A_59)
      | ~ v8_relat_2(A_59)
      | r8_relat_2(A_59,B_60)
      | ~ v1_relat_1(A_59) ) ),
    inference(resolution,[status(thm)],[c_14,c_40])).

tff(c_12,plain,(
    ! [A_11,B_25] :
      ( ~ r2_hidden(k4_tarski('#skF_4'(A_11,B_25),'#skF_6'(A_11,B_25)),A_11)
      | r8_relat_2(A_11,B_25)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_62,plain,(
    ! [A_61,B_62] :
      ( ~ r2_hidden(k4_tarski('#skF_4'(A_61,B_62),'#skF_5'(A_61,B_62)),A_61)
      | ~ v8_relat_2(A_61)
      | r8_relat_2(A_61,B_62)
      | ~ v1_relat_1(A_61) ) ),
    inference(resolution,[status(thm)],[c_53,c_12])).

tff(c_83,plain,(
    ! [A_68,B_69] :
      ( ~ v8_relat_2(A_68)
      | r8_relat_2(A_68,B_69)
      | ~ v1_relat_1(A_68) ) ),
    inference(resolution,[status(thm)],[c_16,c_62])).

tff(c_28,plain,(
    ~ r8_relat_2(k1_wellord2('#skF_7'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_86,plain,
    ( ~ v8_relat_2(k1_wellord2('#skF_7'))
    | ~ v1_relat_1(k1_wellord2('#skF_7')) ),
    inference(resolution,[status(thm)],[c_83,c_28])).

tff(c_90,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_86])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:52:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.19  
% 1.90/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.19  %$ r8_relat_2 > r2_hidden > v8_relat_2 > v1_relat_1 > k4_tarski > #nlpp > k1_wellord2 > #skF_6 > #skF_2 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_4
% 1.90/1.19  
% 1.90/1.19  %Foreground sorts:
% 1.90/1.19  
% 1.90/1.19  
% 1.90/1.19  %Background operators:
% 1.90/1.19  
% 1.90/1.19  
% 1.90/1.19  %Foreground operators:
% 1.90/1.19  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 1.90/1.19  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.90/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.19  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.90/1.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.90/1.19  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 1.90/1.19  tff('#skF_7', type, '#skF_7': $i).
% 1.90/1.19  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 1.90/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.90/1.19  tff('#skF_3', type, '#skF_3': $i > $i).
% 1.90/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.19  tff(r8_relat_2, type, r8_relat_2: ($i * $i) > $o).
% 1.90/1.19  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.90/1.19  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.90/1.19  
% 1.90/1.20  tff(f_56, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 1.90/1.20  tff(f_58, axiom, (![A]: v8_relat_2(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_wellord2)).
% 1.90/1.20  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (r8_relat_2(A, B) <=> (![C, D, E]: (((((r2_hidden(C, B) & r2_hidden(D, B)) & r2_hidden(E, B)) & r2_hidden(k4_tarski(C, D), A)) & r2_hidden(k4_tarski(D, E), A)) => r2_hidden(k4_tarski(C, E), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_2)).
% 1.90/1.20  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (v8_relat_2(A) <=> (![B, C, D]: ((r2_hidden(k4_tarski(B, C), A) & r2_hidden(k4_tarski(C, D), A)) => r2_hidden(k4_tarski(B, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l2_wellord1)).
% 1.90/1.20  tff(f_61, negated_conjecture, ~(![A]: r8_relat_2(k1_wellord2(A), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_wellord2)).
% 1.90/1.20  tff(c_24, plain, (![A_35]: (v1_relat_1(k1_wellord2(A_35)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.90/1.20  tff(c_26, plain, (![A_36]: (v8_relat_2(k1_wellord2(A_36)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.90/1.20  tff(c_16, plain, (![A_11, B_25]: (r2_hidden(k4_tarski('#skF_4'(A_11, B_25), '#skF_5'(A_11, B_25)), A_11) | r8_relat_2(A_11, B_25) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.90/1.20  tff(c_14, plain, (![A_11, B_25]: (r2_hidden(k4_tarski('#skF_5'(A_11, B_25), '#skF_6'(A_11, B_25)), A_11) | r8_relat_2(A_11, B_25) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.90/1.20  tff(c_40, plain, (![B_54, D_55, A_56, C_57]: (r2_hidden(k4_tarski(B_54, D_55), A_56) | ~r2_hidden(k4_tarski(C_57, D_55), A_56) | ~r2_hidden(k4_tarski(B_54, C_57), A_56) | ~v8_relat_2(A_56) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.90/1.20  tff(c_53, plain, (![B_58, A_59, B_60]: (r2_hidden(k4_tarski(B_58, '#skF_6'(A_59, B_60)), A_59) | ~r2_hidden(k4_tarski(B_58, '#skF_5'(A_59, B_60)), A_59) | ~v8_relat_2(A_59) | r8_relat_2(A_59, B_60) | ~v1_relat_1(A_59))), inference(resolution, [status(thm)], [c_14, c_40])).
% 1.90/1.20  tff(c_12, plain, (![A_11, B_25]: (~r2_hidden(k4_tarski('#skF_4'(A_11, B_25), '#skF_6'(A_11, B_25)), A_11) | r8_relat_2(A_11, B_25) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.90/1.20  tff(c_62, plain, (![A_61, B_62]: (~r2_hidden(k4_tarski('#skF_4'(A_61, B_62), '#skF_5'(A_61, B_62)), A_61) | ~v8_relat_2(A_61) | r8_relat_2(A_61, B_62) | ~v1_relat_1(A_61))), inference(resolution, [status(thm)], [c_53, c_12])).
% 1.90/1.20  tff(c_83, plain, (![A_68, B_69]: (~v8_relat_2(A_68) | r8_relat_2(A_68, B_69) | ~v1_relat_1(A_68))), inference(resolution, [status(thm)], [c_16, c_62])).
% 1.90/1.20  tff(c_28, plain, (~r8_relat_2(k1_wellord2('#skF_7'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.90/1.20  tff(c_86, plain, (~v8_relat_2(k1_wellord2('#skF_7')) | ~v1_relat_1(k1_wellord2('#skF_7'))), inference(resolution, [status(thm)], [c_83, c_28])).
% 1.90/1.20  tff(c_90, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_26, c_86])).
% 1.90/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.20  
% 1.90/1.20  Inference rules
% 1.90/1.20  ----------------------
% 1.90/1.20  #Ref     : 0
% 1.90/1.20  #Sup     : 13
% 1.90/1.20  #Fact    : 0
% 1.90/1.20  #Define  : 0
% 1.90/1.20  #Split   : 0
% 1.90/1.20  #Chain   : 0
% 1.90/1.20  #Close   : 0
% 1.90/1.20  
% 1.90/1.20  Ordering : KBO
% 1.90/1.20  
% 1.90/1.20  Simplification rules
% 1.90/1.20  ----------------------
% 1.90/1.20  #Subsume      : 2
% 1.90/1.20  #Demod        : 2
% 1.90/1.20  #Tautology    : 2
% 1.90/1.20  #SimpNegUnit  : 0
% 1.90/1.20  #BackRed      : 0
% 1.90/1.20  
% 1.90/1.20  #Partial instantiations: 0
% 1.90/1.20  #Strategies tried      : 1
% 1.90/1.20  
% 1.90/1.20  Timing (in seconds)
% 1.90/1.20  ----------------------
% 1.97/1.20  Preprocessing        : 0.28
% 1.97/1.20  Parsing              : 0.15
% 1.97/1.20  CNF conversion       : 0.02
% 1.97/1.20  Main loop            : 0.17
% 1.97/1.20  Inferencing          : 0.08
% 1.97/1.20  Reduction            : 0.04
% 1.97/1.20  Demodulation         : 0.03
% 1.97/1.20  BG Simplification    : 0.02
% 1.97/1.20  Subsumption          : 0.03
% 1.97/1.20  Abstraction          : 0.01
% 1.97/1.20  MUC search           : 0.00
% 1.97/1.20  Cooper               : 0.00
% 1.97/1.21  Total                : 0.47
% 1.97/1.21  Index Insertion      : 0.00
% 1.97/1.21  Index Deletion       : 0.00
% 1.97/1.21  Index Matching       : 0.00
% 1.97/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
