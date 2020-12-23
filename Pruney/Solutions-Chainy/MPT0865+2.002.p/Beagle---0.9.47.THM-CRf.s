%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:20 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   33 (  47 expanded)
%              Number of leaves         :   16 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   36 (  69 expanded)
%              Number of equality atoms :   17 (  28 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,B)
         => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_14,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [A_1,B_16] :
      ( k4_tarski('#skF_2'(A_1,B_16),'#skF_3'(A_1,B_16)) = B_16
      | ~ r2_hidden(B_16,A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_37,plain,(
    ! [A_29,B_30] :
      ( k4_tarski('#skF_2'(A_29,B_30),'#skF_3'(A_29,B_30)) = B_30
      | ~ r2_hidden(B_30,A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_19,B_20] : k1_mcart_1(k4_tarski(A_19,B_20)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_79,plain,(
    ! [B_38,A_39] :
      ( k1_mcart_1(B_38) = '#skF_2'(A_39,B_38)
      | ~ r2_hidden(B_38,A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_8])).

tff(c_85,plain,
    ( k1_mcart_1('#skF_4') = '#skF_2'('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_79])).

tff(c_89,plain,(
    k1_mcart_1('#skF_4') = '#skF_2'('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_85])).

tff(c_10,plain,(
    ! [A_19,B_20] : k2_mcart_1(k4_tarski(A_19,B_20)) = B_20 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_58,plain,(
    ! [B_34,A_35] :
      ( k2_mcart_1(B_34) = '#skF_3'(A_35,B_34)
      | ~ r2_hidden(B_34,A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_10])).

tff(c_64,plain,
    ( k2_mcart_1('#skF_4') = '#skF_3'('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_58])).

tff(c_68,plain,(
    k2_mcart_1('#skF_4') = '#skF_3'('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_64])).

tff(c_12,plain,(
    k4_tarski(k1_mcart_1('#skF_4'),k2_mcart_1('#skF_4')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_69,plain,(
    k4_tarski(k1_mcart_1('#skF_4'),'#skF_3'('#skF_5','#skF_4')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_12])).

tff(c_90,plain,(
    k4_tarski('#skF_2'('#skF_5','#skF_4'),'#skF_3'('#skF_5','#skF_4')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_69])).

tff(c_97,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_90])).

tff(c_101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_97])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:29:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.13  
% 1.62/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.13  %$ r2_hidden > v1_relat_1 > k4_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 1.62/1.13  
% 1.62/1.13  %Foreground sorts:
% 1.62/1.13  
% 1.62/1.13  
% 1.62/1.13  %Background operators:
% 1.62/1.13  
% 1.62/1.13  
% 1.62/1.13  %Foreground operators:
% 1.62/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.62/1.13  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.62/1.13  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.62/1.13  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.62/1.13  tff('#skF_5', type, '#skF_5': $i).
% 1.62/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.13  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.62/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.62/1.13  tff('#skF_4', type, '#skF_4': $i).
% 1.62/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.13  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.62/1.13  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.62/1.13  
% 1.62/1.14  tff(f_46, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 1.62/1.14  tff(f_35, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 1.62/1.14  tff(f_39, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.62/1.14  tff(c_16, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.62/1.14  tff(c_14, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.62/1.14  tff(c_2, plain, (![A_1, B_16]: (k4_tarski('#skF_2'(A_1, B_16), '#skF_3'(A_1, B_16))=B_16 | ~r2_hidden(B_16, A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.62/1.14  tff(c_37, plain, (![A_29, B_30]: (k4_tarski('#skF_2'(A_29, B_30), '#skF_3'(A_29, B_30))=B_30 | ~r2_hidden(B_30, A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.62/1.14  tff(c_8, plain, (![A_19, B_20]: (k1_mcart_1(k4_tarski(A_19, B_20))=A_19)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.62/1.14  tff(c_79, plain, (![B_38, A_39]: (k1_mcart_1(B_38)='#skF_2'(A_39, B_38) | ~r2_hidden(B_38, A_39) | ~v1_relat_1(A_39))), inference(superposition, [status(thm), theory('equality')], [c_37, c_8])).
% 1.62/1.14  tff(c_85, plain, (k1_mcart_1('#skF_4')='#skF_2'('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_14, c_79])).
% 1.62/1.14  tff(c_89, plain, (k1_mcart_1('#skF_4')='#skF_2'('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_85])).
% 1.62/1.14  tff(c_10, plain, (![A_19, B_20]: (k2_mcart_1(k4_tarski(A_19, B_20))=B_20)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.62/1.14  tff(c_58, plain, (![B_34, A_35]: (k2_mcart_1(B_34)='#skF_3'(A_35, B_34) | ~r2_hidden(B_34, A_35) | ~v1_relat_1(A_35))), inference(superposition, [status(thm), theory('equality')], [c_37, c_10])).
% 1.62/1.14  tff(c_64, plain, (k2_mcart_1('#skF_4')='#skF_3'('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_14, c_58])).
% 1.62/1.14  tff(c_68, plain, (k2_mcart_1('#skF_4')='#skF_3'('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_64])).
% 1.62/1.14  tff(c_12, plain, (k4_tarski(k1_mcart_1('#skF_4'), k2_mcart_1('#skF_4'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.62/1.14  tff(c_69, plain, (k4_tarski(k1_mcart_1('#skF_4'), '#skF_3'('#skF_5', '#skF_4'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_12])).
% 1.62/1.14  tff(c_90, plain, (k4_tarski('#skF_2'('#skF_5', '#skF_4'), '#skF_3'('#skF_5', '#skF_4'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_89, c_69])).
% 1.62/1.14  tff(c_97, plain, (~r2_hidden('#skF_4', '#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2, c_90])).
% 1.62/1.14  tff(c_101, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_97])).
% 1.62/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.14  
% 1.62/1.14  Inference rules
% 1.62/1.14  ----------------------
% 1.62/1.14  #Ref     : 1
% 1.62/1.14  #Sup     : 19
% 1.62/1.14  #Fact    : 0
% 1.62/1.14  #Define  : 0
% 1.62/1.14  #Split   : 0
% 1.62/1.14  #Chain   : 0
% 1.62/1.14  #Close   : 0
% 1.62/1.14  
% 1.62/1.14  Ordering : KBO
% 1.62/1.14  
% 1.62/1.14  Simplification rules
% 1.62/1.14  ----------------------
% 1.62/1.14  #Subsume      : 0
% 1.62/1.14  #Demod        : 6
% 1.62/1.14  #Tautology    : 13
% 1.62/1.14  #SimpNegUnit  : 0
% 1.62/1.14  #BackRed      : 2
% 1.62/1.14  
% 1.62/1.14  #Partial instantiations: 0
% 1.62/1.14  #Strategies tried      : 1
% 1.62/1.14  
% 1.62/1.14  Timing (in seconds)
% 1.62/1.14  ----------------------
% 1.62/1.14  Preprocessing        : 0.26
% 1.62/1.14  Parsing              : 0.14
% 1.62/1.14  CNF conversion       : 0.02
% 1.62/1.14  Main loop            : 0.12
% 1.62/1.14  Inferencing          : 0.06
% 1.62/1.14  Reduction            : 0.03
% 1.62/1.14  Demodulation         : 0.02
% 1.62/1.14  BG Simplification    : 0.01
% 1.62/1.14  Subsumption          : 0.01
% 1.62/1.14  Abstraction          : 0.01
% 1.62/1.14  MUC search           : 0.00
% 1.62/1.14  Cooper               : 0.00
% 1.62/1.14  Total                : 0.40
% 1.62/1.14  Index Insertion      : 0.00
% 1.62/1.14  Index Deletion       : 0.00
% 1.62/1.14  Index Matching       : 0.00
% 1.62/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
