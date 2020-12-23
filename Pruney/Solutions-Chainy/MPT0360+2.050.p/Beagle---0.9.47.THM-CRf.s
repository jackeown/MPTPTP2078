%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:25 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :   39 (  46 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   48 (  70 expanded)
%              Number of equality atoms :   15 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_50,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_34,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_32,plain,(
    r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_36,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_89,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(A_33,B_34) = k3_subset_1(A_33,B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_93,plain,(
    k4_xboole_0('#skF_5','#skF_7') = k3_subset_1('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_89])).

tff(c_26,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_4'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_67,plain,(
    ! [C_27,B_28,A_29] :
      ( r2_hidden(C_27,B_28)
      | ~ r2_hidden(C_27,A_29)
      | ~ r1_tarski(A_29,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_73,plain,(
    ! [A_12,B_28] :
      ( r2_hidden('#skF_4'(A_12),B_28)
      | ~ r1_tarski(A_12,B_28)
      | k1_xboole_0 = A_12 ) ),
    inference(resolution,[status(thm)],[c_26,c_67])).

tff(c_75,plain,(
    ! [A_31,B_32] :
      ( r2_hidden('#skF_4'(A_31),B_32)
      | ~ r1_tarski(A_31,B_32)
      | k1_xboole_0 = A_31 ) ),
    inference(resolution,[status(thm)],[c_26,c_67])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_747,plain,(
    ! [A_93,B_94,A_95] :
      ( ~ r2_hidden('#skF_4'(A_93),B_94)
      | ~ r1_tarski(A_93,k4_xboole_0(A_95,B_94))
      | k1_xboole_0 = A_93 ) ),
    inference(resolution,[status(thm)],[c_75,c_10])).

tff(c_799,plain,(
    ! [A_99,A_100,B_101] :
      ( ~ r1_tarski(A_99,k4_xboole_0(A_100,B_101))
      | ~ r1_tarski(A_99,B_101)
      | k1_xboole_0 = A_99 ) ),
    inference(resolution,[status(thm)],[c_73,c_747])).

tff(c_822,plain,(
    ! [A_102] :
      ( ~ r1_tarski(A_102,k3_subset_1('#skF_5','#skF_7'))
      | ~ r1_tarski(A_102,'#skF_7')
      | k1_xboole_0 = A_102 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_799])).

tff(c_833,plain,
    ( ~ r1_tarski('#skF_6','#skF_7')
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_32,c_822])).

tff(c_842,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_833])).

tff(c_844,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_842])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:16:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.48  
% 2.94/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.48  %$ r2_hidden > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1
% 2.94/1.48  
% 2.94/1.48  %Foreground sorts:
% 2.94/1.48  
% 2.94/1.48  
% 2.94/1.48  %Background operators:
% 2.94/1.48  
% 2.94/1.48  
% 2.94/1.48  %Foreground operators:
% 2.94/1.48  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.94/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.94/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.94/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.94/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.94/1.48  tff('#skF_7', type, '#skF_7': $i).
% 2.94/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.94/1.48  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.94/1.48  tff('#skF_5', type, '#skF_5': $i).
% 2.94/1.48  tff('#skF_6', type, '#skF_6': $i).
% 2.94/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.94/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.94/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.94/1.48  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.94/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.94/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.94/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.94/1.48  
% 2.94/1.49  tff(f_63, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 2.94/1.49  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.94/1.49  tff(f_50, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.94/1.49  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.94/1.49  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.94/1.49  tff(c_30, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.94/1.49  tff(c_34, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.94/1.49  tff(c_32, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.94/1.49  tff(c_36, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.94/1.49  tff(c_89, plain, (![A_33, B_34]: (k4_xboole_0(A_33, B_34)=k3_subset_1(A_33, B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.94/1.49  tff(c_93, plain, (k4_xboole_0('#skF_5', '#skF_7')=k3_subset_1('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_36, c_89])).
% 2.94/1.49  tff(c_26, plain, (![A_12]: (r2_hidden('#skF_4'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.94/1.49  tff(c_67, plain, (![C_27, B_28, A_29]: (r2_hidden(C_27, B_28) | ~r2_hidden(C_27, A_29) | ~r1_tarski(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.94/1.49  tff(c_73, plain, (![A_12, B_28]: (r2_hidden('#skF_4'(A_12), B_28) | ~r1_tarski(A_12, B_28) | k1_xboole_0=A_12)), inference(resolution, [status(thm)], [c_26, c_67])).
% 2.94/1.49  tff(c_75, plain, (![A_31, B_32]: (r2_hidden('#skF_4'(A_31), B_32) | ~r1_tarski(A_31, B_32) | k1_xboole_0=A_31)), inference(resolution, [status(thm)], [c_26, c_67])).
% 2.94/1.49  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.94/1.49  tff(c_747, plain, (![A_93, B_94, A_95]: (~r2_hidden('#skF_4'(A_93), B_94) | ~r1_tarski(A_93, k4_xboole_0(A_95, B_94)) | k1_xboole_0=A_93)), inference(resolution, [status(thm)], [c_75, c_10])).
% 2.94/1.49  tff(c_799, plain, (![A_99, A_100, B_101]: (~r1_tarski(A_99, k4_xboole_0(A_100, B_101)) | ~r1_tarski(A_99, B_101) | k1_xboole_0=A_99)), inference(resolution, [status(thm)], [c_73, c_747])).
% 2.94/1.49  tff(c_822, plain, (![A_102]: (~r1_tarski(A_102, k3_subset_1('#skF_5', '#skF_7')) | ~r1_tarski(A_102, '#skF_7') | k1_xboole_0=A_102)), inference(superposition, [status(thm), theory('equality')], [c_93, c_799])).
% 2.94/1.49  tff(c_833, plain, (~r1_tarski('#skF_6', '#skF_7') | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_32, c_822])).
% 2.94/1.49  tff(c_842, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_833])).
% 2.94/1.49  tff(c_844, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_842])).
% 2.94/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.49  
% 2.94/1.49  Inference rules
% 2.94/1.49  ----------------------
% 2.94/1.49  #Ref     : 0
% 2.94/1.49  #Sup     : 172
% 2.94/1.49  #Fact    : 0
% 2.94/1.49  #Define  : 0
% 2.94/1.49  #Split   : 4
% 2.94/1.49  #Chain   : 0
% 2.94/1.49  #Close   : 0
% 2.94/1.49  
% 2.94/1.49  Ordering : KBO
% 2.94/1.49  
% 2.94/1.49  Simplification rules
% 2.94/1.49  ----------------------
% 2.94/1.49  #Subsume      : 28
% 2.94/1.49  #Demod        : 36
% 2.94/1.49  #Tautology    : 40
% 2.94/1.49  #SimpNegUnit  : 10
% 2.94/1.49  #BackRed      : 7
% 2.94/1.49  
% 2.94/1.49  #Partial instantiations: 0
% 2.94/1.49  #Strategies tried      : 1
% 2.94/1.49  
% 2.94/1.49  Timing (in seconds)
% 2.94/1.49  ----------------------
% 2.94/1.49  Preprocessing        : 0.29
% 2.94/1.49  Parsing              : 0.14
% 2.94/1.49  CNF conversion       : 0.02
% 2.94/1.49  Main loop            : 0.43
% 2.94/1.49  Inferencing          : 0.16
% 2.94/1.49  Reduction            : 0.12
% 2.94/1.49  Demodulation         : 0.08
% 2.94/1.49  BG Simplification    : 0.02
% 2.94/1.49  Subsumption          : 0.10
% 2.94/1.49  Abstraction          : 0.02
% 2.94/1.49  MUC search           : 0.00
% 2.94/1.49  Cooper               : 0.00
% 2.94/1.49  Total                : 0.74
% 2.94/1.49  Index Insertion      : 0.00
% 2.94/1.49  Index Deletion       : 0.00
% 2.94/1.49  Index Matching       : 0.00
% 2.94/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
