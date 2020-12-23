%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:10 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   41 (  46 expanded)
%              Number of leaves         :   26 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   35 (  47 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_46,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

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

tff(c_72,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_90,plain,(
    ! [A_57,B_58] : k1_enumset1(A_57,A_57,B_58) = k2_tarski(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_36,plain,(
    ! [E_19,B_14,C_15] : r2_hidden(E_19,k1_enumset1(E_19,B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_102,plain,(
    ! [A_57,B_58] : r2_hidden(A_57,k2_tarski(A_57,B_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_36])).

tff(c_28,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_119,plain,(
    ! [A_64,B_65] :
      ( k3_xboole_0(A_64,B_65) = A_64
      | ~ r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_130,plain,(
    ! [A_11,B_12] : k3_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = A_11 ),
    inference(resolution,[status(thm)],[c_28,c_119])).

tff(c_223,plain,(
    ! [D_76,B_77,A_78] :
      ( r2_hidden(D_76,B_77)
      | ~ r2_hidden(D_76,k3_xboole_0(A_78,B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_436,plain,(
    ! [D_92,A_93,B_94] :
      ( r2_hidden(D_92,k2_xboole_0(A_93,B_94))
      | ~ r2_hidden(D_92,A_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_223])).

tff(c_74,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_129,plain,(
    k3_xboole_0(k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7'),'#skF_7') = k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_74,c_119])).

tff(c_229,plain,(
    ! [D_76] :
      ( r2_hidden(D_76,'#skF_7')
      | ~ r2_hidden(D_76,k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_223])).

tff(c_458,plain,(
    ! [D_100] :
      ( r2_hidden(D_100,'#skF_7')
      | ~ r2_hidden(D_100,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_436,c_229])).

tff(c_462,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_102,c_458])).

tff(c_470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_462])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:11:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.40  
% 2.55/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.40  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.55/1.40  
% 2.55/1.40  %Foreground sorts:
% 2.55/1.40  
% 2.55/1.40  
% 2.55/1.40  %Background operators:
% 2.55/1.40  
% 2.55/1.40  
% 2.55/1.40  %Foreground operators:
% 2.55/1.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.55/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.55/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.55/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.55/1.40  tff('#skF_7', type, '#skF_7': $i).
% 2.55/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.55/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.55/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.55/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.55/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.55/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.55/1.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.55/1.40  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.55/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.40  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.55/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.55/1.40  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.55/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.55/1.40  
% 2.55/1.41  tff(f_86, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 2.55/1.41  tff(f_71, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.55/1.41  tff(f_61, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.55/1.41  tff(f_46, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.55/1.41  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.55/1.41  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.55/1.41  tff(c_72, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.55/1.41  tff(c_90, plain, (![A_57, B_58]: (k1_enumset1(A_57, A_57, B_58)=k2_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.55/1.41  tff(c_36, plain, (![E_19, B_14, C_15]: (r2_hidden(E_19, k1_enumset1(E_19, B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.55/1.41  tff(c_102, plain, (![A_57, B_58]: (r2_hidden(A_57, k2_tarski(A_57, B_58)))), inference(superposition, [status(thm), theory('equality')], [c_90, c_36])).
% 2.55/1.41  tff(c_28, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.55/1.41  tff(c_119, plain, (![A_64, B_65]: (k3_xboole_0(A_64, B_65)=A_64 | ~r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.55/1.41  tff(c_130, plain, (![A_11, B_12]: (k3_xboole_0(A_11, k2_xboole_0(A_11, B_12))=A_11)), inference(resolution, [status(thm)], [c_28, c_119])).
% 2.55/1.41  tff(c_223, plain, (![D_76, B_77, A_78]: (r2_hidden(D_76, B_77) | ~r2_hidden(D_76, k3_xboole_0(A_78, B_77)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.55/1.41  tff(c_436, plain, (![D_92, A_93, B_94]: (r2_hidden(D_92, k2_xboole_0(A_93, B_94)) | ~r2_hidden(D_92, A_93))), inference(superposition, [status(thm), theory('equality')], [c_130, c_223])).
% 2.55/1.41  tff(c_74, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.55/1.41  tff(c_129, plain, (k3_xboole_0(k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7'), '#skF_7')=k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_74, c_119])).
% 2.55/1.41  tff(c_229, plain, (![D_76]: (r2_hidden(D_76, '#skF_7') | ~r2_hidden(D_76, k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_129, c_223])).
% 2.55/1.41  tff(c_458, plain, (![D_100]: (r2_hidden(D_100, '#skF_7') | ~r2_hidden(D_100, k2_tarski('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_436, c_229])).
% 2.55/1.41  tff(c_462, plain, (r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_102, c_458])).
% 2.55/1.41  tff(c_470, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_462])).
% 2.55/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.41  
% 2.55/1.41  Inference rules
% 2.55/1.41  ----------------------
% 2.55/1.41  #Ref     : 0
% 2.55/1.41  #Sup     : 94
% 2.55/1.41  #Fact    : 0
% 2.55/1.41  #Define  : 0
% 2.55/1.41  #Split   : 0
% 2.55/1.41  #Chain   : 0
% 2.55/1.41  #Close   : 0
% 2.55/1.41  
% 2.55/1.41  Ordering : KBO
% 2.55/1.41  
% 2.55/1.41  Simplification rules
% 2.55/1.41  ----------------------
% 2.55/1.41  #Subsume      : 2
% 2.55/1.41  #Demod        : 29
% 2.55/1.41  #Tautology    : 67
% 2.55/1.41  #SimpNegUnit  : 1
% 2.55/1.41  #BackRed      : 0
% 2.55/1.41  
% 2.55/1.41  #Partial instantiations: 0
% 2.55/1.41  #Strategies tried      : 1
% 2.55/1.41  
% 2.55/1.41  Timing (in seconds)
% 2.55/1.41  ----------------------
% 2.55/1.42  Preprocessing        : 0.36
% 2.55/1.42  Parsing              : 0.18
% 2.55/1.42  CNF conversion       : 0.03
% 2.55/1.42  Main loop            : 0.24
% 2.55/1.42  Inferencing          : 0.07
% 2.55/1.42  Reduction            : 0.09
% 2.55/1.42  Demodulation         : 0.07
% 2.55/1.42  BG Simplification    : 0.02
% 2.55/1.42  Subsumption          : 0.04
% 2.55/1.42  Abstraction          : 0.02
% 2.55/1.42  MUC search           : 0.00
% 2.55/1.42  Cooper               : 0.00
% 2.55/1.42  Total                : 0.62
% 2.55/1.42  Index Insertion      : 0.00
% 2.55/1.42  Index Deletion       : 0.00
% 2.55/1.42  Index Matching       : 0.00
% 2.55/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
