%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:10 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   35 (  57 expanded)
%              Number of leaves         :   17 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 ( 112 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r1_tarski > v1_relat_1 > k8_relat_1 > k5_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(r3_xboole_0,type,(
    r3_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => r1_tarski(k5_relat_1(B,k8_relat_1(A,C)),k5_relat_1(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t122_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : r3_xboole_0(A,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r3_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        | r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_xboole_0)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ! [D] :
                  ( v1_relat_1(D)
                 => ( ( r1_tarski(A,B)
                      & r1_tarski(C,D) )
                   => r1_tarski(k5_relat_1(A,C),k5_relat_1(B,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(k8_relat_1(A_7,B_8),B_8)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( v1_relat_1(k8_relat_1(A_5,B_6))
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_3] : r3_xboole_0(A_3,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    ! [B_34,A_35] :
      ( r1_tarski(B_34,A_35)
      | r1_tarski(A_35,B_34)
      | ~ r3_xboole_0(A_35,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [A_3] : r1_tarski(A_3,A_3) ),
    inference(resolution,[status(thm)],[c_8,c_26])).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_39,plain,(
    ! [A_36,C_37,B_38,D_39] :
      ( r1_tarski(k5_relat_1(A_36,C_37),k5_relat_1(B_38,D_39))
      | ~ r1_tarski(C_37,D_39)
      | ~ r1_tarski(A_36,B_38)
      | ~ v1_relat_1(D_39)
      | ~ v1_relat_1(C_37)
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16,plain,(
    ~ r1_tarski(k5_relat_1('#skF_2',k8_relat_1('#skF_1','#skF_3')),k5_relat_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_42,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_39,c_16])).

tff(c_45,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_42])).

tff(c_48,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_45])).

tff(c_49,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_52,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_49])).

tff(c_56,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_52])).

tff(c_57,plain,(
    ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_61,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_57])).

tff(c_65,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_61])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:57:29 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.14  
% 1.74/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.14  %$ r3_xboole_0 > r1_tarski > v1_relat_1 > k8_relat_1 > k5_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.74/1.14  
% 1.74/1.14  %Foreground sorts:
% 1.74/1.14  
% 1.74/1.14  
% 1.74/1.14  %Background operators:
% 1.74/1.14  
% 1.74/1.14  
% 1.74/1.14  %Foreground operators:
% 1.74/1.14  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.74/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.14  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.74/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.74/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.74/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.74/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.74/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.74/1.14  tff(r3_xboole_0, type, r3_xboole_0: ($i * $i) > $o).
% 1.74/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.14  
% 1.74/1.15  tff(f_66, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(B, k8_relat_1(A, C)), k5_relat_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t122_relat_1)).
% 1.74/1.15  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 1.74/1.15  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 1.74/1.15  tff(f_33, axiom, (![A, B]: r3_xboole_0(A, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r3_xboole_0)).
% 1.74/1.15  tff(f_31, axiom, (![A, B]: (r3_xboole_0(A, B) <=> (r1_tarski(A, B) | r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_xboole_0)).
% 1.74/1.15  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k5_relat_1(A, C), k5_relat_1(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relat_1)).
% 1.74/1.15  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.74/1.15  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(k8_relat_1(A_7, B_8), B_8) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.74/1.15  tff(c_10, plain, (![A_5, B_6]: (v1_relat_1(k8_relat_1(A_5, B_6)) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.74/1.15  tff(c_8, plain, (![A_3]: (r3_xboole_0(A_3, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.74/1.15  tff(c_26, plain, (![B_34, A_35]: (r1_tarski(B_34, A_35) | r1_tarski(A_35, B_34) | ~r3_xboole_0(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.74/1.15  tff(c_38, plain, (![A_3]: (r1_tarski(A_3, A_3))), inference(resolution, [status(thm)], [c_8, c_26])).
% 1.74/1.15  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.74/1.15  tff(c_39, plain, (![A_36, C_37, B_38, D_39]: (r1_tarski(k5_relat_1(A_36, C_37), k5_relat_1(B_38, D_39)) | ~r1_tarski(C_37, D_39) | ~r1_tarski(A_36, B_38) | ~v1_relat_1(D_39) | ~v1_relat_1(C_37) | ~v1_relat_1(B_38) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.74/1.15  tff(c_16, plain, (~r1_tarski(k5_relat_1('#skF_2', k8_relat_1('#skF_1', '#skF_3')), k5_relat_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.74/1.15  tff(c_42, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_2', '#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_3')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_39, c_16])).
% 1.74/1.15  tff(c_45, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_2', '#skF_2') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_42])).
% 1.74/1.15  tff(c_48, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), '#skF_3') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_45])).
% 1.74/1.15  tff(c_49, plain, (~v1_relat_1(k8_relat_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_48])).
% 1.74/1.15  tff(c_52, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_49])).
% 1.74/1.15  tff(c_56, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_52])).
% 1.74/1.15  tff(c_57, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 1.74/1.15  tff(c_61, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_57])).
% 1.74/1.15  tff(c_65, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_61])).
% 1.74/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.15  
% 1.74/1.15  Inference rules
% 1.74/1.15  ----------------------
% 1.74/1.15  #Ref     : 0
% 1.74/1.15  #Sup     : 6
% 1.74/1.15  #Fact    : 0
% 1.74/1.15  #Define  : 0
% 1.74/1.15  #Split   : 1
% 1.74/1.15  #Chain   : 0
% 1.74/1.15  #Close   : 0
% 1.74/1.15  
% 1.74/1.15  Ordering : KBO
% 1.74/1.15  
% 1.74/1.15  Simplification rules
% 1.74/1.15  ----------------------
% 1.74/1.15  #Subsume      : 0
% 1.74/1.15  #Demod        : 5
% 1.74/1.15  #Tautology    : 2
% 1.74/1.15  #SimpNegUnit  : 0
% 1.74/1.15  #BackRed      : 0
% 1.74/1.15  
% 1.74/1.15  #Partial instantiations: 0
% 1.74/1.15  #Strategies tried      : 1
% 1.74/1.15  
% 1.74/1.15  Timing (in seconds)
% 1.74/1.15  ----------------------
% 1.74/1.16  Preprocessing        : 0.26
% 1.74/1.16  Parsing              : 0.14
% 1.74/1.16  CNF conversion       : 0.02
% 1.74/1.16  Main loop            : 0.11
% 1.74/1.16  Inferencing          : 0.05
% 1.74/1.16  Reduction            : 0.02
% 1.74/1.16  Demodulation         : 0.02
% 1.74/1.16  BG Simplification    : 0.01
% 1.74/1.16  Subsumption          : 0.02
% 1.74/1.16  Abstraction          : 0.00
% 1.74/1.16  MUC search           : 0.00
% 1.74/1.16  Cooper               : 0.00
% 1.74/1.16  Total                : 0.39
% 1.74/1.16  Index Insertion      : 0.00
% 1.74/1.16  Index Deletion       : 0.00
% 1.74/1.16  Index Matching       : 0.00
% 1.74/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
