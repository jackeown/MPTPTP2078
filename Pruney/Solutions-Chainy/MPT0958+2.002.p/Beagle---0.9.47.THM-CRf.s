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
% DateTime   : Thu Dec  3 10:10:36 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   33 (  39 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   49 (  67 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_relat_2 > r2_hidden > v4_relat_2 > v1_relat_1 > k4_tarski > #nlpp > k1_wellord2 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r4_relat_2,type,(
    r4_relat_2: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_54,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r4_relat_2(A,B)
        <=> ! [C,D] :
              ( ( r2_hidden(C,B)
                & r2_hidden(D,B)
                & r2_hidden(k4_tarski(C,D),A)
                & r2_hidden(k4_tarski(D,C),A) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_2)).

tff(f_59,negated_conjecture,(
    ~ ! [A] : r4_relat_2(k1_wellord2(A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_wellord2)).

tff(f_56,axiom,(
    ! [A] : v4_relat_2(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_wellord2)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v4_relat_2(A)
      <=> ! [B,C] :
            ( ( r2_hidden(k4_tarski(B,C),A)
              & r2_hidden(k4_tarski(C,B),A) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_wellord1)).

tff(c_22,plain,(
    ! [A_25] : v1_relat_1(k1_wellord2(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_33,plain,(
    ! [A_35,B_36] :
      ( '#skF_3'(A_35,B_36) != '#skF_4'(A_35,B_36)
      | r4_relat_2(A_35,B_36)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26,plain,(
    ~ r4_relat_2(k1_wellord2('#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_36,plain,
    ( '#skF_3'(k1_wellord2('#skF_5'),'#skF_5') != '#skF_4'(k1_wellord2('#skF_5'),'#skF_5')
    | ~ v1_relat_1(k1_wellord2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_33,c_26])).

tff(c_39,plain,(
    '#skF_3'(k1_wellord2('#skF_5'),'#skF_5') != '#skF_4'(k1_wellord2('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_36])).

tff(c_24,plain,(
    ! [A_26] : v4_relat_2(k1_wellord2(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    ! [A_8,B_18] :
      ( r2_hidden(k4_tarski('#skF_3'(A_8,B_18),'#skF_4'(A_8,B_18)),A_8)
      | r4_relat_2(A_8,B_18)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    ! [A_8,B_18] :
      ( r2_hidden(k4_tarski('#skF_4'(A_8,B_18),'#skF_3'(A_8,B_18)),A_8)
      | r4_relat_2(A_8,B_18)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_43,plain,(
    ! [C_42,B_43,A_44] :
      ( C_42 = B_43
      | ~ r2_hidden(k4_tarski(C_42,B_43),A_44)
      | ~ r2_hidden(k4_tarski(B_43,C_42),A_44)
      | ~ v4_relat_2(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_56,plain,(
    ! [A_45,B_46] :
      ( '#skF_3'(A_45,B_46) = '#skF_4'(A_45,B_46)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_45,B_46),'#skF_4'(A_45,B_46)),A_45)
      | ~ v4_relat_2(A_45)
      | r4_relat_2(A_45,B_46)
      | ~ v1_relat_1(A_45) ) ),
    inference(resolution,[status(thm)],[c_14,c_43])).

tff(c_61,plain,(
    ! [A_47,B_48] :
      ( '#skF_3'(A_47,B_48) = '#skF_4'(A_47,B_48)
      | ~ v4_relat_2(A_47)
      | r4_relat_2(A_47,B_48)
      | ~ v1_relat_1(A_47) ) ),
    inference(resolution,[status(thm)],[c_16,c_56])).

tff(c_64,plain,
    ( '#skF_3'(k1_wellord2('#skF_5'),'#skF_5') = '#skF_4'(k1_wellord2('#skF_5'),'#skF_5')
    | ~ v4_relat_2(k1_wellord2('#skF_5'))
    | ~ v1_relat_1(k1_wellord2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_61,c_26])).

tff(c_67,plain,(
    '#skF_3'(k1_wellord2('#skF_5'),'#skF_5') = '#skF_4'(k1_wellord2('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_64])).

tff(c_69,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_67])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n020.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 15:24:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.17  
% 1.68/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.17  %$ r4_relat_2 > r2_hidden > v4_relat_2 > v1_relat_1 > k4_tarski > #nlpp > k1_wellord2 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4
% 1.68/1.17  
% 1.68/1.17  %Foreground sorts:
% 1.68/1.17  
% 1.68/1.17  
% 1.68/1.17  %Background operators:
% 1.68/1.17  
% 1.68/1.17  
% 1.68/1.17  %Foreground operators:
% 1.68/1.17  tff(r4_relat_2, type, r4_relat_2: ($i * $i) > $o).
% 1.68/1.17  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.68/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.68/1.17  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.68/1.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.68/1.17  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.68/1.17  tff(v4_relat_2, type, v4_relat_2: $i > $o).
% 1.68/1.17  tff('#skF_5', type, '#skF_5': $i).
% 1.68/1.17  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 1.68/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.68/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.17  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.68/1.17  
% 1.68/1.18  tff(f_54, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 1.68/1.18  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (r4_relat_2(A, B) <=> (![C, D]: ((((r2_hidden(C, B) & r2_hidden(D, B)) & r2_hidden(k4_tarski(C, D), A)) & r2_hidden(k4_tarski(D, C), A)) => (C = D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_2)).
% 1.68/1.18  tff(f_59, negated_conjecture, ~(![A]: r4_relat_2(k1_wellord2(A), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_wellord2)).
% 1.68/1.18  tff(f_56, axiom, (![A]: v4_relat_2(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_wellord2)).
% 1.68/1.18  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (v4_relat_2(A) <=> (![B, C]: ((r2_hidden(k4_tarski(B, C), A) & r2_hidden(k4_tarski(C, B), A)) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_wellord1)).
% 1.68/1.18  tff(c_22, plain, (![A_25]: (v1_relat_1(k1_wellord2(A_25)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.68/1.18  tff(c_33, plain, (![A_35, B_36]: ('#skF_3'(A_35, B_36)!='#skF_4'(A_35, B_36) | r4_relat_2(A_35, B_36) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.68/1.18  tff(c_26, plain, (~r4_relat_2(k1_wellord2('#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.68/1.18  tff(c_36, plain, ('#skF_3'(k1_wellord2('#skF_5'), '#skF_5')!='#skF_4'(k1_wellord2('#skF_5'), '#skF_5') | ~v1_relat_1(k1_wellord2('#skF_5'))), inference(resolution, [status(thm)], [c_33, c_26])).
% 1.68/1.18  tff(c_39, plain, ('#skF_3'(k1_wellord2('#skF_5'), '#skF_5')!='#skF_4'(k1_wellord2('#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_36])).
% 1.68/1.18  tff(c_24, plain, (![A_26]: (v4_relat_2(k1_wellord2(A_26)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.68/1.18  tff(c_16, plain, (![A_8, B_18]: (r2_hidden(k4_tarski('#skF_3'(A_8, B_18), '#skF_4'(A_8, B_18)), A_8) | r4_relat_2(A_8, B_18) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.68/1.18  tff(c_14, plain, (![A_8, B_18]: (r2_hidden(k4_tarski('#skF_4'(A_8, B_18), '#skF_3'(A_8, B_18)), A_8) | r4_relat_2(A_8, B_18) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.68/1.18  tff(c_43, plain, (![C_42, B_43, A_44]: (C_42=B_43 | ~r2_hidden(k4_tarski(C_42, B_43), A_44) | ~r2_hidden(k4_tarski(B_43, C_42), A_44) | ~v4_relat_2(A_44) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.68/1.18  tff(c_56, plain, (![A_45, B_46]: ('#skF_3'(A_45, B_46)='#skF_4'(A_45, B_46) | ~r2_hidden(k4_tarski('#skF_3'(A_45, B_46), '#skF_4'(A_45, B_46)), A_45) | ~v4_relat_2(A_45) | r4_relat_2(A_45, B_46) | ~v1_relat_1(A_45))), inference(resolution, [status(thm)], [c_14, c_43])).
% 1.68/1.18  tff(c_61, plain, (![A_47, B_48]: ('#skF_3'(A_47, B_48)='#skF_4'(A_47, B_48) | ~v4_relat_2(A_47) | r4_relat_2(A_47, B_48) | ~v1_relat_1(A_47))), inference(resolution, [status(thm)], [c_16, c_56])).
% 1.68/1.18  tff(c_64, plain, ('#skF_3'(k1_wellord2('#skF_5'), '#skF_5')='#skF_4'(k1_wellord2('#skF_5'), '#skF_5') | ~v4_relat_2(k1_wellord2('#skF_5')) | ~v1_relat_1(k1_wellord2('#skF_5'))), inference(resolution, [status(thm)], [c_61, c_26])).
% 1.68/1.18  tff(c_67, plain, ('#skF_3'(k1_wellord2('#skF_5'), '#skF_5')='#skF_4'(k1_wellord2('#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_64])).
% 1.68/1.18  tff(c_69, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39, c_67])).
% 1.68/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.18  
% 1.68/1.18  Inference rules
% 1.68/1.18  ----------------------
% 1.68/1.18  #Ref     : 0
% 1.68/1.18  #Sup     : 7
% 1.68/1.18  #Fact    : 0
% 1.68/1.18  #Define  : 0
% 1.68/1.18  #Split   : 0
% 1.68/1.18  #Chain   : 0
% 1.68/1.18  #Close   : 0
% 1.68/1.18  
% 1.68/1.18  Ordering : KBO
% 1.68/1.18  
% 1.68/1.18  Simplification rules
% 1.68/1.18  ----------------------
% 1.68/1.18  #Subsume      : 1
% 1.68/1.18  #Demod        : 3
% 1.68/1.18  #Tautology    : 2
% 1.68/1.18  #SimpNegUnit  : 1
% 1.68/1.18  #BackRed      : 0
% 1.68/1.18  
% 1.68/1.18  #Partial instantiations: 0
% 1.68/1.18  #Strategies tried      : 1
% 1.68/1.18  
% 1.68/1.18  Timing (in seconds)
% 1.68/1.18  ----------------------
% 1.87/1.18  Preprocessing        : 0.31
% 1.87/1.18  Parsing              : 0.16
% 1.87/1.18  CNF conversion       : 0.02
% 1.87/1.18  Main loop            : 0.11
% 1.87/1.18  Inferencing          : 0.05
% 1.87/1.18  Reduction            : 0.03
% 1.87/1.18  Demodulation         : 0.02
% 1.87/1.18  BG Simplification    : 0.02
% 1.87/1.19  Subsumption          : 0.02
% 1.87/1.19  Abstraction          : 0.01
% 1.87/1.19  MUC search           : 0.00
% 1.87/1.19  Cooper               : 0.00
% 1.87/1.19  Total                : 0.44
% 1.87/1.19  Index Insertion      : 0.00
% 1.87/1.19  Index Deletion       : 0.00
% 1.87/1.19  Index Matching       : 0.00
% 1.87/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
