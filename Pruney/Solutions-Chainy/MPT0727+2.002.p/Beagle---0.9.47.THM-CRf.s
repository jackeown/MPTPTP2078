%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:54 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   25 (  33 expanded)
%              Number of leaves         :   14 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  43 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_49,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r2_hidden(A,B)
          & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_26,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_24,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_31,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,B_14) = A_13
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_35,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_24,c_31])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_40,plain,(
    ! [D_8] :
      ( r2_hidden(D_8,'#skF_3')
      | ~ r2_hidden(D_8,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_6])).

tff(c_44,plain,(
    ! [D_18] :
      ( r2_hidden(D_18,'#skF_3')
      | ~ r2_hidden(D_18,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_52,plain,(
    ! [D_19] :
      ( ~ r2_hidden('#skF_3',D_19)
      | ~ r2_hidden(D_19,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_2])).

tff(c_55,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_52])).

tff(c_61,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_55])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:01:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.15  
% 1.70/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.15  %$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.70/1.15  
% 1.70/1.15  %Foreground sorts:
% 1.70/1.15  
% 1.70/1.15  
% 1.70/1.15  %Background operators:
% 1.70/1.15  
% 1.70/1.15  
% 1.70/1.15  %Foreground operators:
% 1.70/1.15  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.70/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.70/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.70/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.70/1.15  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.70/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.70/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.70/1.15  
% 1.70/1.16  tff(f_49, negated_conjecture, ~(![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.70/1.16  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.70/1.16  tff(f_39, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.70/1.16  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 1.70/1.16  tff(c_26, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.70/1.16  tff(c_24, plain, (r1_tarski('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.70/1.16  tff(c_31, plain, (![A_13, B_14]: (k3_xboole_0(A_13, B_14)=A_13 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.70/1.16  tff(c_35, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_24, c_31])).
% 1.70/1.16  tff(c_6, plain, (![D_8, B_4, A_3]: (r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.70/1.16  tff(c_40, plain, (![D_8]: (r2_hidden(D_8, '#skF_3') | ~r2_hidden(D_8, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_35, c_6])).
% 1.70/1.16  tff(c_44, plain, (![D_18]: (r2_hidden(D_18, '#skF_3') | ~r2_hidden(D_18, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_35, c_6])).
% 1.70/1.16  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.70/1.16  tff(c_52, plain, (![D_19]: (~r2_hidden('#skF_3', D_19) | ~r2_hidden(D_19, '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_2])).
% 1.70/1.16  tff(c_55, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_52])).
% 1.70/1.16  tff(c_61, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_55])).
% 1.70/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.16  
% 1.70/1.16  Inference rules
% 1.70/1.16  ----------------------
% 1.70/1.16  #Ref     : 0
% 1.70/1.16  #Sup     : 9
% 1.70/1.16  #Fact    : 0
% 1.70/1.16  #Define  : 0
% 1.70/1.16  #Split   : 0
% 1.70/1.16  #Chain   : 0
% 1.70/1.16  #Close   : 0
% 1.70/1.16  
% 1.70/1.16  Ordering : KBO
% 1.70/1.16  
% 1.70/1.16  Simplification rules
% 1.70/1.16  ----------------------
% 1.70/1.16  #Subsume      : 0
% 1.70/1.16  #Demod        : 1
% 1.70/1.16  #Tautology    : 2
% 1.70/1.16  #SimpNegUnit  : 0
% 1.70/1.16  #BackRed      : 0
% 1.70/1.16  
% 1.70/1.16  #Partial instantiations: 0
% 1.70/1.16  #Strategies tried      : 1
% 1.70/1.16  
% 1.70/1.16  Timing (in seconds)
% 1.70/1.16  ----------------------
% 1.70/1.16  Preprocessing        : 0.26
% 1.70/1.16  Parsing              : 0.14
% 1.70/1.16  CNF conversion       : 0.02
% 1.70/1.16  Main loop            : 0.09
% 1.70/1.16  Inferencing          : 0.04
% 1.70/1.16  Reduction            : 0.02
% 1.70/1.16  Demodulation         : 0.02
% 1.70/1.16  BG Simplification    : 0.01
% 1.70/1.16  Subsumption          : 0.02
% 1.70/1.16  Abstraction          : 0.00
% 1.70/1.16  MUC search           : 0.00
% 1.70/1.16  Cooper               : 0.00
% 1.70/1.16  Total                : 0.37
% 1.70/1.16  Index Insertion      : 0.00
% 1.70/1.16  Index Deletion       : 0.00
% 1.70/1.16  Index Matching       : 0.00
% 1.70/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
