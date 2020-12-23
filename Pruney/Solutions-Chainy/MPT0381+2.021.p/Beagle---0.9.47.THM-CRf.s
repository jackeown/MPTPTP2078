%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:04 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   40 (  49 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   42 (  57 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_33,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_30,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_41,plain,(
    ! [B_24,A_25] :
      ( ~ r2_hidden(B_24,A_25)
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_45,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_41])).

tff(c_83,plain,(
    ! [B_36,A_37] :
      ( m1_subset_1(B_36,A_37)
      | ~ r2_hidden(B_36,A_37)
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_89,plain,
    ( m1_subset_1('#skF_2','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_83])).

tff(c_93,plain,(
    m1_subset_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_89])).

tff(c_127,plain,(
    ! [B_44,A_45] :
      ( m1_subset_1(k1_tarski(B_44),k1_zfmisc_1(A_45))
      | k1_xboole_0 = A_45
      | ~ m1_subset_1(B_44,A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_28,plain,(
    ~ m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_133,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_127,c_28])).

tff(c_137,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_133])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_71,plain,(
    ! [A_33,B_34] :
      ( ~ r2_hidden(A_33,B_34)
      | ~ r1_xboole_0(k1_tarski(A_33),B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_77,plain,(
    ! [A_35] : ~ r2_hidden(A_35,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_71])).

tff(c_82,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_77])).

tff(c_139,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_82])).

tff(c_143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_139])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:01:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.16  
% 1.87/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.16  %$ r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 1.87/1.16  
% 1.87/1.16  %Foreground sorts:
% 1.87/1.16  
% 1.87/1.16  
% 1.87/1.16  %Background operators:
% 1.87/1.16  
% 1.87/1.16  
% 1.87/1.16  %Foreground operators:
% 1.87/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.87/1.16  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.87/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.87/1.16  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.87/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.87/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.87/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.87/1.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.87/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.87/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.87/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.87/1.16  
% 1.87/1.17  tff(f_71, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 1.87/1.17  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.87/1.17  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 1.87/1.17  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 1.87/1.17  tff(f_33, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.87/1.17  tff(f_46, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.87/1.17  tff(c_30, plain, (r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.87/1.17  tff(c_41, plain, (![B_24, A_25]: (~r2_hidden(B_24, A_25) | ~v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.17  tff(c_45, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_30, c_41])).
% 1.87/1.17  tff(c_83, plain, (![B_36, A_37]: (m1_subset_1(B_36, A_37) | ~r2_hidden(B_36, A_37) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.87/1.17  tff(c_89, plain, (m1_subset_1('#skF_2', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_30, c_83])).
% 1.87/1.17  tff(c_93, plain, (m1_subset_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_45, c_89])).
% 1.87/1.17  tff(c_127, plain, (![B_44, A_45]: (m1_subset_1(k1_tarski(B_44), k1_zfmisc_1(A_45)) | k1_xboole_0=A_45 | ~m1_subset_1(B_44, A_45))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.87/1.17  tff(c_28, plain, (~m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.87/1.17  tff(c_133, plain, (k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_127, c_28])).
% 1.87/1.17  tff(c_137, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_93, c_133])).
% 1.87/1.17  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.17  tff(c_6, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.87/1.17  tff(c_71, plain, (![A_33, B_34]: (~r2_hidden(A_33, B_34) | ~r1_xboole_0(k1_tarski(A_33), B_34))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.87/1.17  tff(c_77, plain, (![A_35]: (~r2_hidden(A_35, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_71])).
% 1.87/1.17  tff(c_82, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_77])).
% 1.87/1.17  tff(c_139, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_82])).
% 1.87/1.17  tff(c_143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_139])).
% 1.87/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.17  
% 1.87/1.17  Inference rules
% 1.87/1.17  ----------------------
% 1.87/1.17  #Ref     : 0
% 1.87/1.17  #Sup     : 21
% 1.87/1.17  #Fact    : 0
% 1.87/1.17  #Define  : 0
% 1.87/1.17  #Split   : 1
% 1.87/1.17  #Chain   : 0
% 1.87/1.17  #Close   : 0
% 1.87/1.17  
% 1.87/1.17  Ordering : KBO
% 1.87/1.17  
% 1.87/1.17  Simplification rules
% 1.87/1.17  ----------------------
% 1.87/1.17  #Subsume      : 1
% 1.87/1.17  #Demod        : 6
% 1.87/1.17  #Tautology    : 12
% 1.87/1.17  #SimpNegUnit  : 2
% 1.87/1.17  #BackRed      : 4
% 1.87/1.17  
% 1.87/1.17  #Partial instantiations: 0
% 1.87/1.17  #Strategies tried      : 1
% 1.87/1.17  
% 1.87/1.17  Timing (in seconds)
% 1.87/1.17  ----------------------
% 1.87/1.17  Preprocessing        : 0.29
% 1.87/1.17  Parsing              : 0.15
% 1.87/1.17  CNF conversion       : 0.02
% 1.87/1.17  Main loop            : 0.13
% 1.87/1.17  Inferencing          : 0.05
% 1.87/1.17  Reduction            : 0.04
% 1.87/1.17  Demodulation         : 0.02
% 1.87/1.17  BG Simplification    : 0.01
% 1.87/1.17  Subsumption          : 0.02
% 1.87/1.17  Abstraction          : 0.01
% 1.87/1.17  MUC search           : 0.00
% 1.87/1.17  Cooper               : 0.00
% 1.87/1.17  Total                : 0.44
% 1.87/1.17  Index Insertion      : 0.00
% 1.87/1.17  Index Deletion       : 0.00
% 1.87/1.17  Index Matching       : 0.00
% 1.87/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
