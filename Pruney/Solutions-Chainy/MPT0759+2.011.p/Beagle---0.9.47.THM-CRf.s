%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:33 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   40 (  46 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   39 (  54 expanded)
%              Number of equality atoms :   15 (  21 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_4 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_63,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(f_67,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => k4_xboole_0(k2_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A] : k6_subset_1(k1_ordinal1(A),k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_ordinal1)).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_101,plain,(
    ! [A_40,B_41] :
      ( r2_hidden('#skF_5'(A_40,B_41),B_41)
      | ~ r2_hidden(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_126,plain,(
    ! [A_45,A_46] :
      ( '#skF_5'(A_45,k1_tarski(A_46)) = A_46
      | ~ r2_hidden(A_45,k1_tarski(A_46)) ) ),
    inference(resolution,[status(thm)],[c_101,c_2])).

tff(c_135,plain,(
    ! [C_5] : '#skF_5'(C_5,k1_tarski(C_5)) = C_5 ),
    inference(resolution,[status(thm)],[c_4,c_126])).

tff(c_176,plain,(
    ! [D_53,A_54,B_55] :
      ( ~ r2_hidden(D_53,'#skF_5'(A_54,B_55))
      | ~ r2_hidden(D_53,B_55)
      | ~ r2_hidden(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_179,plain,(
    ! [D_53,C_5] :
      ( ~ r2_hidden(D_53,C_5)
      | ~ r2_hidden(D_53,k1_tarski(C_5))
      | ~ r2_hidden(C_5,k1_tarski(C_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_176])).

tff(c_187,plain,(
    ! [D_56,C_57] :
      ( ~ r2_hidden(D_56,C_57)
      | ~ r2_hidden(D_56,k1_tarski(C_57)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_179])).

tff(c_196,plain,(
    ! [C_5] : ~ r2_hidden(C_5,C_5) ),
    inference(resolution,[status(thm)],[c_4,c_187])).

tff(c_44,plain,(
    ! [A_26] : k2_xboole_0(A_26,k1_tarski(A_26)) = k1_ordinal1(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_150,plain,(
    ! [B_48,A_49] :
      ( k4_xboole_0(k2_xboole_0(B_48,k1_tarski(A_49)),k1_tarski(A_49)) = B_48
      | r2_hidden(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_162,plain,(
    ! [A_50] :
      ( k4_xboole_0(k1_ordinal1(A_50),k1_tarski(A_50)) = A_50
      | r2_hidden(A_50,A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_150])).

tff(c_42,plain,(
    ! [A_24,B_25] : k6_subset_1(A_24,B_25) = k4_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_46,plain,(
    k6_subset_1(k1_ordinal1('#skF_6'),k1_tarski('#skF_6')) != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_47,plain,(
    k4_xboole_0(k1_ordinal1('#skF_6'),k1_tarski('#skF_6')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46])).

tff(c_173,plain,(
    r2_hidden('#skF_6','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_47])).

tff(c_200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_196,c_173])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:58:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.21  
% 1.88/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.21  %$ r2_hidden > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_4 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_5
% 1.88/1.21  
% 1.88/1.21  %Foreground sorts:
% 1.88/1.21  
% 1.88/1.21  
% 1.88/1.21  %Background operators:
% 1.88/1.21  
% 1.88/1.21  
% 1.88/1.21  %Foreground operators:
% 1.88/1.21  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.88/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.88/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.88/1.21  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.88/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.88/1.21  tff('#skF_6', type, '#skF_6': $i).
% 1.88/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.88/1.21  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.88/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.88/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.88/1.21  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.88/1.21  
% 1.88/1.22  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.88/1.22  tff(f_63, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 1.88/1.22  tff(f_67, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 1.88/1.22  tff(f_50, axiom, (![A, B]: (~r2_hidden(A, B) => (k4_xboole_0(k2_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t141_zfmisc_1)).
% 1.88/1.22  tff(f_65, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.88/1.22  tff(f_70, negated_conjecture, ~(![A]: (k6_subset_1(k1_ordinal1(A), k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_ordinal1)).
% 1.88/1.22  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.88/1.22  tff(c_101, plain, (![A_40, B_41]: (r2_hidden('#skF_5'(A_40, B_41), B_41) | ~r2_hidden(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.88/1.22  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.88/1.22  tff(c_126, plain, (![A_45, A_46]: ('#skF_5'(A_45, k1_tarski(A_46))=A_46 | ~r2_hidden(A_45, k1_tarski(A_46)))), inference(resolution, [status(thm)], [c_101, c_2])).
% 1.88/1.22  tff(c_135, plain, (![C_5]: ('#skF_5'(C_5, k1_tarski(C_5))=C_5)), inference(resolution, [status(thm)], [c_4, c_126])).
% 1.88/1.22  tff(c_176, plain, (![D_53, A_54, B_55]: (~r2_hidden(D_53, '#skF_5'(A_54, B_55)) | ~r2_hidden(D_53, B_55) | ~r2_hidden(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.88/1.22  tff(c_179, plain, (![D_53, C_5]: (~r2_hidden(D_53, C_5) | ~r2_hidden(D_53, k1_tarski(C_5)) | ~r2_hidden(C_5, k1_tarski(C_5)))), inference(superposition, [status(thm), theory('equality')], [c_135, c_176])).
% 1.88/1.22  tff(c_187, plain, (![D_56, C_57]: (~r2_hidden(D_56, C_57) | ~r2_hidden(D_56, k1_tarski(C_57)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_179])).
% 1.88/1.22  tff(c_196, plain, (![C_5]: (~r2_hidden(C_5, C_5))), inference(resolution, [status(thm)], [c_4, c_187])).
% 1.88/1.22  tff(c_44, plain, (![A_26]: (k2_xboole_0(A_26, k1_tarski(A_26))=k1_ordinal1(A_26))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.88/1.22  tff(c_150, plain, (![B_48, A_49]: (k4_xboole_0(k2_xboole_0(B_48, k1_tarski(A_49)), k1_tarski(A_49))=B_48 | r2_hidden(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.88/1.22  tff(c_162, plain, (![A_50]: (k4_xboole_0(k1_ordinal1(A_50), k1_tarski(A_50))=A_50 | r2_hidden(A_50, A_50))), inference(superposition, [status(thm), theory('equality')], [c_44, c_150])).
% 1.88/1.22  tff(c_42, plain, (![A_24, B_25]: (k6_subset_1(A_24, B_25)=k4_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.88/1.22  tff(c_46, plain, (k6_subset_1(k1_ordinal1('#skF_6'), k1_tarski('#skF_6'))!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.88/1.22  tff(c_47, plain, (k4_xboole_0(k1_ordinal1('#skF_6'), k1_tarski('#skF_6'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46])).
% 1.88/1.22  tff(c_173, plain, (r2_hidden('#skF_6', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_162, c_47])).
% 1.88/1.22  tff(c_200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_196, c_173])).
% 1.88/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.22  
% 1.88/1.22  Inference rules
% 1.88/1.22  ----------------------
% 1.88/1.22  #Ref     : 0
% 1.88/1.22  #Sup     : 31
% 1.88/1.22  #Fact    : 0
% 1.88/1.22  #Define  : 0
% 1.88/1.22  #Split   : 0
% 1.88/1.22  #Chain   : 0
% 1.88/1.22  #Close   : 0
% 1.88/1.22  
% 1.88/1.22  Ordering : KBO
% 1.88/1.22  
% 1.88/1.22  Simplification rules
% 1.88/1.22  ----------------------
% 1.88/1.22  #Subsume      : 1
% 1.88/1.22  #Demod        : 6
% 1.88/1.22  #Tautology    : 20
% 1.88/1.22  #SimpNegUnit  : 2
% 1.88/1.22  #BackRed      : 2
% 1.88/1.22  
% 1.88/1.22  #Partial instantiations: 0
% 1.88/1.22  #Strategies tried      : 1
% 1.88/1.22  
% 1.88/1.22  Timing (in seconds)
% 1.88/1.22  ----------------------
% 1.88/1.22  Preprocessing        : 0.30
% 1.88/1.22  Parsing              : 0.15
% 1.88/1.22  CNF conversion       : 0.02
% 1.88/1.22  Main loop            : 0.14
% 1.88/1.22  Inferencing          : 0.05
% 1.88/1.22  Reduction            : 0.05
% 1.88/1.22  Demodulation         : 0.04
% 1.88/1.22  BG Simplification    : 0.01
% 1.88/1.22  Subsumption          : 0.02
% 1.88/1.22  Abstraction          : 0.01
% 1.88/1.22  MUC search           : 0.00
% 1.88/1.22  Cooper               : 0.00
% 1.88/1.22  Total                : 0.46
% 1.88/1.22  Index Insertion      : 0.00
% 1.88/1.22  Index Deletion       : 0.00
% 1.88/1.22  Index Matching       : 0.00
% 1.88/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
