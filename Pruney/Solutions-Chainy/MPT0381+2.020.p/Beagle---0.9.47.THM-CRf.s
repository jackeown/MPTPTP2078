%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:04 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   37 (  42 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :    5
%              Number of atoms          :   40 (  48 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

tff(c_28,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_89,plain,(
    ! [A_34,B_35] :
      ( k2_xboole_0(k1_tarski(A_34),B_35) = B_35
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_13,B_14] : k2_xboole_0(k1_tarski(A_13),B_14) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_101,plain,(
    ! [B_36,A_37] :
      ( k1_xboole_0 != B_36
      | ~ r2_hidden(A_37,B_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_14])).

tff(c_109,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(resolution,[status(thm)],[c_28,c_101])).

tff(c_39,plain,(
    ! [B_22,A_23] :
      ( ~ r2_hidden(B_22,A_23)
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_43,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_39])).

tff(c_69,plain,(
    ! [B_31,A_32] :
      ( m1_subset_1(B_31,A_32)
      | ~ r2_hidden(B_31,A_32)
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_75,plain,
    ( m1_subset_1('#skF_2','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_69])).

tff(c_79,plain,(
    m1_subset_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_75])).

tff(c_142,plain,(
    ! [B_44,A_45] :
      ( m1_subset_1(k1_tarski(B_44),k1_zfmisc_1(A_45))
      | k1_xboole_0 = A_45
      | ~ m1_subset_1(B_44,A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_26,plain,(
    ~ m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_148,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_142,c_26])).

tff(c_152,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_148])).

tff(c_154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_152])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:11:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.20  
% 1.95/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.20  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 1.95/1.20  
% 1.95/1.20  %Foreground sorts:
% 1.95/1.20  
% 1.95/1.20  
% 1.95/1.20  %Background operators:
% 1.95/1.20  
% 1.95/1.20  
% 1.95/1.20  %Foreground operators:
% 1.95/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.95/1.20  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.95/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.95/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.95/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.95/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.95/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.95/1.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.95/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.95/1.20  
% 2.01/1.21  tff(f_69, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 2.01/1.21  tff(f_41, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 2.01/1.21  tff(f_44, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.01/1.21  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.01/1.21  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.01/1.21  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 2.01/1.21  tff(c_28, plain, (r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.01/1.21  tff(c_89, plain, (![A_34, B_35]: (k2_xboole_0(k1_tarski(A_34), B_35)=B_35 | ~r2_hidden(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.01/1.21  tff(c_14, plain, (![A_13, B_14]: (k2_xboole_0(k1_tarski(A_13), B_14)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.01/1.21  tff(c_101, plain, (![B_36, A_37]: (k1_xboole_0!=B_36 | ~r2_hidden(A_37, B_36))), inference(superposition, [status(thm), theory('equality')], [c_89, c_14])).
% 2.01/1.21  tff(c_109, plain, (k1_xboole_0!='#skF_3'), inference(resolution, [status(thm)], [c_28, c_101])).
% 2.01/1.21  tff(c_39, plain, (![B_22, A_23]: (~r2_hidden(B_22, A_23) | ~v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.01/1.21  tff(c_43, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_28, c_39])).
% 2.01/1.21  tff(c_69, plain, (![B_31, A_32]: (m1_subset_1(B_31, A_32) | ~r2_hidden(B_31, A_32) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.01/1.21  tff(c_75, plain, (m1_subset_1('#skF_2', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_28, c_69])).
% 2.01/1.21  tff(c_79, plain, (m1_subset_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_43, c_75])).
% 2.01/1.21  tff(c_142, plain, (![B_44, A_45]: (m1_subset_1(k1_tarski(B_44), k1_zfmisc_1(A_45)) | k1_xboole_0=A_45 | ~m1_subset_1(B_44, A_45))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.01/1.21  tff(c_26, plain, (~m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.01/1.21  tff(c_148, plain, (k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_142, c_26])).
% 2.01/1.21  tff(c_152, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_79, c_148])).
% 2.01/1.21  tff(c_154, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_152])).
% 2.01/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.21  
% 2.01/1.21  Inference rules
% 2.01/1.21  ----------------------
% 2.01/1.21  #Ref     : 0
% 2.01/1.21  #Sup     : 26
% 2.01/1.21  #Fact    : 0
% 2.01/1.21  #Define  : 0
% 2.01/1.21  #Split   : 1
% 2.01/1.21  #Chain   : 0
% 2.01/1.21  #Close   : 0
% 2.01/1.21  
% 2.01/1.21  Ordering : KBO
% 2.01/1.21  
% 2.01/1.21  Simplification rules
% 2.01/1.21  ----------------------
% 2.01/1.21  #Subsume      : 3
% 2.01/1.21  #Demod        : 1
% 2.01/1.21  #Tautology    : 13
% 2.01/1.21  #SimpNegUnit  : 2
% 2.01/1.21  #BackRed      : 0
% 2.01/1.21  
% 2.01/1.21  #Partial instantiations: 0
% 2.01/1.21  #Strategies tried      : 1
% 2.01/1.21  
% 2.01/1.21  Timing (in seconds)
% 2.01/1.21  ----------------------
% 2.01/1.21  Preprocessing        : 0.30
% 2.01/1.21  Parsing              : 0.16
% 2.01/1.21  CNF conversion       : 0.02
% 2.01/1.21  Main loop            : 0.14
% 2.01/1.21  Inferencing          : 0.06
% 2.01/1.21  Reduction            : 0.04
% 2.01/1.21  Demodulation         : 0.02
% 2.01/1.21  BG Simplification    : 0.01
% 2.01/1.21  Subsumption          : 0.03
% 2.01/1.21  Abstraction          : 0.01
% 2.01/1.21  MUC search           : 0.00
% 2.01/1.21  Cooper               : 0.00
% 2.01/1.21  Total                : 0.46
% 2.01/1.21  Index Insertion      : 0.00
% 2.01/1.21  Index Deletion       : 0.00
% 2.01/1.21  Index Matching       : 0.00
% 2.01/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
