%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:58 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   32 (  40 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :   44 (  76 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => ( ( r1_tarski(k1_relat_1(C),A)
                & r1_tarski(C,B) )
             => r1_tarski(C,k7_relat_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k7_relat_1(B,A),k7_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( k5_relat_1(k6_relat_1(A_12),B_13) = B_13
      | ~ r1_tarski(k1_relat_1(B_13),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_29,plain,
    ( k5_relat_1(k6_relat_1('#skF_1'),'#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_26])).

tff(c_32,plain,(
    k5_relat_1(k6_relat_1('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_29])).

tff(c_6,plain,(
    ! [A_7,B_8] :
      ( k5_relat_1(k6_relat_1(A_7),B_8) = k7_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_36,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_6])).

tff(c_43,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_36])).

tff(c_52,plain,(
    ! [B_14,A_15,C_16] :
      ( r1_tarski(k7_relat_1(B_14,A_15),k7_relat_1(C_16,A_15))
      | ~ r1_tarski(B_14,C_16)
      | ~ v1_relat_1(C_16)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_55,plain,(
    ! [C_16] :
      ( r1_tarski('#skF_3',k7_relat_1(C_16,'#skF_1'))
      | ~ r1_tarski('#skF_3',C_16)
      | ~ v1_relat_1(C_16)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_52])).

tff(c_63,plain,(
    ! [C_17] :
      ( r1_tarski('#skF_3',k7_relat_1(C_17,'#skF_1'))
      | ~ r1_tarski('#skF_3',C_17)
      | ~ v1_relat_1(C_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_55])).

tff(c_8,plain,(
    ~ r1_tarski('#skF_3',k7_relat_1('#skF_2','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_66,plain,
    ( ~ r1_tarski('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_63,c_8])).

tff(c_73,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_10,c_66])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:44:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.11  
% 1.64/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.11  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.64/1.11  
% 1.64/1.11  %Foreground sorts:
% 1.64/1.11  
% 1.64/1.11  
% 1.64/1.11  %Background operators:
% 1.64/1.11  
% 1.64/1.11  
% 1.64/1.11  %Foreground operators:
% 1.64/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.11  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.64/1.11  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.64/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.64/1.11  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.64/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.64/1.11  
% 1.64/1.12  tff(f_56, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(C, B)) => r1_tarski(C, k7_relat_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_relat_1)).
% 1.64/1.12  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 1.64/1.12  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 1.64/1.12  tff(f_34, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k7_relat_1(B, A), k7_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_relat_1)).
% 1.64/1.12  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.64/1.12  tff(c_10, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.64/1.12  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.64/1.12  tff(c_12, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.64/1.12  tff(c_26, plain, (![A_12, B_13]: (k5_relat_1(k6_relat_1(A_12), B_13)=B_13 | ~r1_tarski(k1_relat_1(B_13), A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.64/1.12  tff(c_29, plain, (k5_relat_1(k6_relat_1('#skF_1'), '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_26])).
% 1.64/1.12  tff(c_32, plain, (k5_relat_1(k6_relat_1('#skF_1'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_29])).
% 1.64/1.12  tff(c_6, plain, (![A_7, B_8]: (k5_relat_1(k6_relat_1(A_7), B_8)=k7_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.64/1.12  tff(c_36, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_6])).
% 1.64/1.12  tff(c_43, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_36])).
% 1.64/1.12  tff(c_52, plain, (![B_14, A_15, C_16]: (r1_tarski(k7_relat_1(B_14, A_15), k7_relat_1(C_16, A_15)) | ~r1_tarski(B_14, C_16) | ~v1_relat_1(C_16) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.64/1.12  tff(c_55, plain, (![C_16]: (r1_tarski('#skF_3', k7_relat_1(C_16, '#skF_1')) | ~r1_tarski('#skF_3', C_16) | ~v1_relat_1(C_16) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_43, c_52])).
% 1.64/1.12  tff(c_63, plain, (![C_17]: (r1_tarski('#skF_3', k7_relat_1(C_17, '#skF_1')) | ~r1_tarski('#skF_3', C_17) | ~v1_relat_1(C_17))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_55])).
% 1.64/1.12  tff(c_8, plain, (~r1_tarski('#skF_3', k7_relat_1('#skF_2', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.64/1.12  tff(c_66, plain, (~r1_tarski('#skF_3', '#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_63, c_8])).
% 1.64/1.12  tff(c_73, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_10, c_66])).
% 1.64/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.12  
% 1.64/1.12  Inference rules
% 1.64/1.12  ----------------------
% 1.64/1.12  #Ref     : 0
% 1.64/1.12  #Sup     : 13
% 1.64/1.12  #Fact    : 0
% 1.64/1.12  #Define  : 0
% 1.64/1.12  #Split   : 0
% 1.64/1.12  #Chain   : 0
% 1.64/1.12  #Close   : 0
% 1.64/1.12  
% 1.64/1.12  Ordering : KBO
% 1.64/1.12  
% 1.64/1.12  Simplification rules
% 1.64/1.12  ----------------------
% 1.64/1.12  #Subsume      : 0
% 1.64/1.12  #Demod        : 8
% 1.64/1.12  #Tautology    : 7
% 1.64/1.12  #SimpNegUnit  : 0
% 1.64/1.12  #BackRed      : 0
% 1.64/1.12  
% 1.64/1.12  #Partial instantiations: 0
% 1.64/1.12  #Strategies tried      : 1
% 1.64/1.12  
% 1.64/1.12  Timing (in seconds)
% 1.64/1.12  ----------------------
% 1.64/1.12  Preprocessing        : 0.26
% 1.64/1.12  Parsing              : 0.15
% 1.64/1.12  CNF conversion       : 0.02
% 1.64/1.12  Main loop            : 0.10
% 1.64/1.12  Inferencing          : 0.05
% 1.64/1.12  Reduction            : 0.03
% 1.64/1.12  Demodulation         : 0.02
% 1.64/1.12  BG Simplification    : 0.01
% 1.64/1.12  Subsumption          : 0.01
% 1.64/1.13  Abstraction          : 0.00
% 1.64/1.13  MUC search           : 0.00
% 1.64/1.13  Cooper               : 0.00
% 1.64/1.13  Total                : 0.39
% 1.64/1.13  Index Insertion      : 0.00
% 1.64/1.13  Index Deletion       : 0.00
% 1.64/1.13  Index Matching       : 0.00
% 1.64/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
