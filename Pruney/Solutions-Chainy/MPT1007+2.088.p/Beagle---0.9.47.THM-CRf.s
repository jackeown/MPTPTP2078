%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:23 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   39 (  43 expanded)
%              Number of leaves         :   24 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   46 (  66 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_32,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_38,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_53,plain,(
    ! [A_25,B_26] : k1_enumset1(A_25,A_25,B_26) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [E_7,B_2,C_3] : r2_hidden(E_7,k1_enumset1(E_7,B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_71,plain,(
    ! [A_27,B_28] : r2_hidden(A_27,k2_tarski(A_27,B_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_8])).

tff(c_74,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_71])).

tff(c_140,plain,(
    ! [D_57,C_58,B_59,A_60] :
      ( r2_hidden(k1_funct_1(D_57,C_58),B_59)
      | k1_xboole_0 = B_59
      | ~ r2_hidden(C_58,A_60)
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(A_60,B_59)))
      | ~ v1_funct_2(D_57,A_60,B_59)
      | ~ v1_funct_1(D_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_162,plain,(
    ! [D_61,A_62,B_63] :
      ( r2_hidden(k1_funct_1(D_61,A_62),B_63)
      | k1_xboole_0 = B_63
      | ~ m1_subset_1(D_61,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_62),B_63)))
      | ~ v1_funct_2(D_61,k1_tarski(A_62),B_63)
      | ~ v1_funct_1(D_61) ) ),
    inference(resolution,[status(thm)],[c_74,c_140])).

tff(c_165,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_162])).

tff(c_168,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_165])).

tff(c_170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_168])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:02:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.24  
% 2.12/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.24  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.12/1.24  
% 2.12/1.24  %Foreground sorts:
% 2.12/1.24  
% 2.12/1.24  
% 2.12/1.24  %Background operators:
% 2.12/1.24  
% 2.12/1.24  
% 2.12/1.24  %Foreground operators:
% 2.12/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.12/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.12/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.12/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.12/1.24  tff('#skF_5', type, '#skF_5': $i).
% 2.12/1.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.12/1.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.12/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.12/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.12/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.12/1.24  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.12/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.12/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.12/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.24  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.12/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.12/1.24  
% 2.12/1.25  tff(f_68, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 2.12/1.25  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.12/1.25  tff(f_44, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.12/1.25  tff(f_40, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.12/1.25  tff(f_56, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.12/1.25  tff(c_34, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.12/1.25  tff(c_32, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.12/1.25  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.12/1.25  tff(c_38, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.12/1.25  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.12/1.25  tff(c_26, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.12/1.25  tff(c_53, plain, (![A_25, B_26]: (k1_enumset1(A_25, A_25, B_26)=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.12/1.25  tff(c_8, plain, (![E_7, B_2, C_3]: (r2_hidden(E_7, k1_enumset1(E_7, B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.12/1.25  tff(c_71, plain, (![A_27, B_28]: (r2_hidden(A_27, k2_tarski(A_27, B_28)))), inference(superposition, [status(thm), theory('equality')], [c_53, c_8])).
% 2.12/1.25  tff(c_74, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_71])).
% 2.12/1.25  tff(c_140, plain, (![D_57, C_58, B_59, A_60]: (r2_hidden(k1_funct_1(D_57, C_58), B_59) | k1_xboole_0=B_59 | ~r2_hidden(C_58, A_60) | ~m1_subset_1(D_57, k1_zfmisc_1(k2_zfmisc_1(A_60, B_59))) | ~v1_funct_2(D_57, A_60, B_59) | ~v1_funct_1(D_57))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.12/1.25  tff(c_162, plain, (![D_61, A_62, B_63]: (r2_hidden(k1_funct_1(D_61, A_62), B_63) | k1_xboole_0=B_63 | ~m1_subset_1(D_61, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_62), B_63))) | ~v1_funct_2(D_61, k1_tarski(A_62), B_63) | ~v1_funct_1(D_61))), inference(resolution, [status(thm)], [c_74, c_140])).
% 2.12/1.25  tff(c_165, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_162])).
% 2.12/1.25  tff(c_168, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_165])).
% 2.12/1.25  tff(c_170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_168])).
% 2.12/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.25  
% 2.12/1.25  Inference rules
% 2.12/1.25  ----------------------
% 2.12/1.25  #Ref     : 0
% 2.12/1.25  #Sup     : 28
% 2.12/1.25  #Fact    : 0
% 2.12/1.25  #Define  : 0
% 2.12/1.25  #Split   : 0
% 2.12/1.25  #Chain   : 0
% 2.12/1.25  #Close   : 0
% 2.12/1.25  
% 2.12/1.25  Ordering : KBO
% 2.12/1.25  
% 2.12/1.25  Simplification rules
% 2.12/1.25  ----------------------
% 2.12/1.25  #Subsume      : 0
% 2.12/1.25  #Demod        : 4
% 2.12/1.25  #Tautology    : 12
% 2.12/1.25  #SimpNegUnit  : 1
% 2.12/1.25  #BackRed      : 0
% 2.12/1.25  
% 2.12/1.25  #Partial instantiations: 0
% 2.12/1.25  #Strategies tried      : 1
% 2.12/1.25  
% 2.12/1.25  Timing (in seconds)
% 2.12/1.25  ----------------------
% 2.12/1.26  Preprocessing        : 0.31
% 2.12/1.26  Parsing              : 0.15
% 2.12/1.26  CNF conversion       : 0.02
% 2.12/1.26  Main loop            : 0.19
% 2.12/1.26  Inferencing          : 0.07
% 2.12/1.26  Reduction            : 0.06
% 2.12/1.26  Demodulation         : 0.04
% 2.12/1.26  BG Simplification    : 0.01
% 2.12/1.26  Subsumption          : 0.04
% 2.12/1.26  Abstraction          : 0.01
% 2.12/1.26  MUC search           : 0.00
% 2.12/1.26  Cooper               : 0.00
% 2.12/1.26  Total                : 0.52
% 2.12/1.26  Index Insertion      : 0.00
% 2.12/1.26  Index Deletion       : 0.00
% 2.12/1.26  Index Matching       : 0.00
% 2.12/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
