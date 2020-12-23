%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:24 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   43 (  47 expanded)
%              Number of leaves         :   26 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  70 expanded)
%              Number of equality atoms :   18 (  22 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_40,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_46,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_71,plain,(
    ! [A_38,B_39,C_40] : k2_enumset1(A_38,A_38,B_39,C_40) = k1_enumset1(A_38,B_39,C_40) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [F_14,A_7,C_9,D_10] : r2_hidden(F_14,k2_enumset1(A_7,F_14,C_9,D_10)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_92,plain,(
    ! [A_41,B_42,C_43] : r2_hidden(A_41,k1_enumset1(A_41,B_42,C_43)) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_14])).

tff(c_96,plain,(
    ! [A_44,B_45] : r2_hidden(A_44,k2_tarski(A_44,B_45)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_92])).

tff(c_99,plain,(
    ! [A_1] : r2_hidden(A_1,k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_96])).

tff(c_183,plain,(
    ! [D_89,C_90,B_91,A_92] :
      ( r2_hidden(k1_funct_1(D_89,C_90),B_91)
      | k1_xboole_0 = B_91
      | ~ r2_hidden(C_90,A_92)
      | ~ m1_subset_1(D_89,k1_zfmisc_1(k2_zfmisc_1(A_92,B_91)))
      | ~ v1_funct_2(D_89,A_92,B_91)
      | ~ v1_funct_1(D_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_214,plain,(
    ! [D_93,A_94,B_95] :
      ( r2_hidden(k1_funct_1(D_93,A_94),B_95)
      | k1_xboole_0 = B_95
      | ~ m1_subset_1(D_93,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_94),B_95)))
      | ~ v1_funct_2(D_93,k1_tarski(A_94),B_95)
      | ~ v1_funct_1(D_93) ) ),
    inference(resolution,[status(thm)],[c_99,c_183])).

tff(c_217,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_214])).

tff(c_220,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_217])).

tff(c_222,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_220])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:37:40 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.34  
% 2.32/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.34  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4
% 2.32/1.34  
% 2.32/1.34  %Foreground sorts:
% 2.32/1.34  
% 2.32/1.34  
% 2.32/1.34  %Background operators:
% 2.32/1.34  
% 2.32/1.34  
% 2.32/1.34  %Foreground operators:
% 2.32/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.32/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.32/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.32/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.32/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.32/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.32/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.32/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.32/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.32/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.32/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.32/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.32/1.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.32/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.32/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.32/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.32/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.32/1.34  
% 2.32/1.35  tff(f_73, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 2.32/1.35  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.32/1.35  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.32/1.35  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.32/1.35  tff(f_49, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_enumset1)).
% 2.32/1.35  tff(f_61, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.32/1.35  tff(c_42, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.32/1.35  tff(c_40, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.32/1.35  tff(c_48, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.32/1.35  tff(c_46, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.32/1.35  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.32/1.35  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.32/1.35  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.32/1.35  tff(c_71, plain, (![A_38, B_39, C_40]: (k2_enumset1(A_38, A_38, B_39, C_40)=k1_enumset1(A_38, B_39, C_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.32/1.35  tff(c_14, plain, (![F_14, A_7, C_9, D_10]: (r2_hidden(F_14, k2_enumset1(A_7, F_14, C_9, D_10)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.32/1.35  tff(c_92, plain, (![A_41, B_42, C_43]: (r2_hidden(A_41, k1_enumset1(A_41, B_42, C_43)))), inference(superposition, [status(thm), theory('equality')], [c_71, c_14])).
% 2.32/1.35  tff(c_96, plain, (![A_44, B_45]: (r2_hidden(A_44, k2_tarski(A_44, B_45)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_92])).
% 2.32/1.35  tff(c_99, plain, (![A_1]: (r2_hidden(A_1, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_96])).
% 2.32/1.35  tff(c_183, plain, (![D_89, C_90, B_91, A_92]: (r2_hidden(k1_funct_1(D_89, C_90), B_91) | k1_xboole_0=B_91 | ~r2_hidden(C_90, A_92) | ~m1_subset_1(D_89, k1_zfmisc_1(k2_zfmisc_1(A_92, B_91))) | ~v1_funct_2(D_89, A_92, B_91) | ~v1_funct_1(D_89))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.32/1.35  tff(c_214, plain, (![D_93, A_94, B_95]: (r2_hidden(k1_funct_1(D_93, A_94), B_95) | k1_xboole_0=B_95 | ~m1_subset_1(D_93, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_94), B_95))) | ~v1_funct_2(D_93, k1_tarski(A_94), B_95) | ~v1_funct_1(D_93))), inference(resolution, [status(thm)], [c_99, c_183])).
% 2.32/1.35  tff(c_217, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_214])).
% 2.32/1.35  tff(c_220, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_217])).
% 2.32/1.35  tff(c_222, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_220])).
% 2.32/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.35  
% 2.32/1.35  Inference rules
% 2.32/1.35  ----------------------
% 2.32/1.35  #Ref     : 0
% 2.32/1.35  #Sup     : 39
% 2.32/1.35  #Fact    : 0
% 2.32/1.35  #Define  : 0
% 2.32/1.35  #Split   : 0
% 2.32/1.35  #Chain   : 0
% 2.32/1.35  #Close   : 0
% 2.32/1.35  
% 2.32/1.35  Ordering : KBO
% 2.32/1.35  
% 2.32/1.35  Simplification rules
% 2.32/1.35  ----------------------
% 2.32/1.35  #Subsume      : 0
% 2.32/1.35  #Demod        : 5
% 2.32/1.35  #Tautology    : 19
% 2.32/1.35  #SimpNegUnit  : 1
% 2.32/1.35  #BackRed      : 0
% 2.32/1.35  
% 2.32/1.35  #Partial instantiations: 0
% 2.32/1.35  #Strategies tried      : 1
% 2.32/1.35  
% 2.32/1.35  Timing (in seconds)
% 2.32/1.35  ----------------------
% 2.32/1.36  Preprocessing        : 0.34
% 2.32/1.36  Parsing              : 0.17
% 2.32/1.36  CNF conversion       : 0.02
% 2.32/1.36  Main loop            : 0.23
% 2.32/1.36  Inferencing          : 0.08
% 2.32/1.36  Reduction            : 0.07
% 2.32/1.36  Demodulation         : 0.05
% 2.32/1.36  BG Simplification    : 0.02
% 2.32/1.36  Subsumption          : 0.05
% 2.32/1.36  Abstraction          : 0.01
% 2.32/1.36  MUC search           : 0.00
% 2.32/1.36  Cooper               : 0.00
% 2.32/1.36  Total                : 0.59
% 2.32/1.36  Index Insertion      : 0.00
% 2.32/1.36  Index Deletion       : 0.00
% 2.32/1.36  Index Matching       : 0.00
% 2.32/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
