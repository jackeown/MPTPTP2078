%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:06 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   37 (  94 expanded)
%              Number of leaves         :   19 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :   51 ( 159 expanded)
%              Number of equality atoms :    4 (  12 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_37,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_50,axiom,(
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

tff(f_59,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_32,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_34,plain,(
    ! [B_16,A_17] :
      ( ~ v1_xboole_0(B_16)
      | ~ r2_hidden(A_17,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_38,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_34])).

tff(c_60,plain,(
    ! [B_25,A_26] :
      ( m1_subset_1(B_25,A_26)
      | ~ r2_hidden(B_25,A_26)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_66,plain,
    ( m1_subset_1('#skF_1','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_60])).

tff(c_70,plain,(
    m1_subset_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_66])).

tff(c_75,plain,(
    ! [B_27,A_28] :
      ( m1_subset_1(k1_tarski(B_27),k1_zfmisc_1(A_28))
      | k1_xboole_0 = A_28
      | ~ m1_subset_1(B_27,A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_30,plain,(
    ~ m1_subset_1(k1_tarski('#skF_1'),k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_81,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ m1_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_75,c_30])).

tff(c_85,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_81])).

tff(c_26,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_87,plain,(
    ! [A_12] : m1_subset_1('#skF_2',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_26])).

tff(c_98,plain,(
    ! [C_30,A_31,B_32] :
      ( r2_hidden(C_30,A_31)
      | ~ r2_hidden(C_30,B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_102,plain,(
    ! [A_31] :
      ( r2_hidden('#skF_1',A_31)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(A_31)) ) ),
    inference(resolution,[status(thm)],[c_32,c_98])).

tff(c_106,plain,(
    ! [A_31] : r2_hidden('#skF_1',A_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_102])).

tff(c_236,plain,(
    ! [A_65,C_66,B_67] :
      ( ~ r2_hidden(A_65,C_66)
      | ~ r2_hidden(A_65,B_67)
      | ~ r2_hidden(A_65,k5_xboole_0(B_67,C_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_258,plain,(
    ! [C_66,B_67] :
      ( ~ r2_hidden('#skF_1',C_66)
      | ~ r2_hidden('#skF_1',B_67) ) ),
    inference(resolution,[status(thm)],[c_106,c_236])).

tff(c_267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_106,c_258])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.31  % Computer   : n010.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % DateTime   : Tue Dec  1 18:58:59 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.17/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.18  
% 1.99/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.19  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.99/1.19  
% 1.99/1.19  %Foreground sorts:
% 1.99/1.19  
% 1.99/1.19  
% 1.99/1.19  %Background operators:
% 1.99/1.19  
% 1.99/1.19  
% 1.99/1.19  %Foreground operators:
% 1.99/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.99/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.99/1.19  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.99/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.99/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.99/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.99/1.19  
% 1.99/1.20  tff(f_71, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 1.99/1.20  tff(f_37, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 1.99/1.20  tff(f_50, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 1.99/1.20  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 1.99/1.20  tff(f_59, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 1.99/1.20  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 1.99/1.20  tff(f_32, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 1.99/1.20  tff(c_32, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.99/1.20  tff(c_34, plain, (![B_16, A_17]: (~v1_xboole_0(B_16) | ~r2_hidden(A_17, B_16))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.99/1.20  tff(c_38, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_34])).
% 1.99/1.20  tff(c_60, plain, (![B_25, A_26]: (m1_subset_1(B_25, A_26) | ~r2_hidden(B_25, A_26) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.99/1.20  tff(c_66, plain, (m1_subset_1('#skF_1', '#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_60])).
% 1.99/1.20  tff(c_70, plain, (m1_subset_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_38, c_66])).
% 1.99/1.20  tff(c_75, plain, (![B_27, A_28]: (m1_subset_1(k1_tarski(B_27), k1_zfmisc_1(A_28)) | k1_xboole_0=A_28 | ~m1_subset_1(B_27, A_28))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.99/1.20  tff(c_30, plain, (~m1_subset_1(k1_tarski('#skF_1'), k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.99/1.20  tff(c_81, plain, (k1_xboole_0='#skF_2' | ~m1_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_75, c_30])).
% 1.99/1.20  tff(c_85, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_81])).
% 1.99/1.20  tff(c_26, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.99/1.20  tff(c_87, plain, (![A_12]: (m1_subset_1('#skF_2', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_26])).
% 1.99/1.20  tff(c_98, plain, (![C_30, A_31, B_32]: (r2_hidden(C_30, A_31) | ~r2_hidden(C_30, B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.99/1.20  tff(c_102, plain, (![A_31]: (r2_hidden('#skF_1', A_31) | ~m1_subset_1('#skF_2', k1_zfmisc_1(A_31)))), inference(resolution, [status(thm)], [c_32, c_98])).
% 1.99/1.20  tff(c_106, plain, (![A_31]: (r2_hidden('#skF_1', A_31))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_102])).
% 1.99/1.20  tff(c_236, plain, (![A_65, C_66, B_67]: (~r2_hidden(A_65, C_66) | ~r2_hidden(A_65, B_67) | ~r2_hidden(A_65, k5_xboole_0(B_67, C_66)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.99/1.20  tff(c_258, plain, (![C_66, B_67]: (~r2_hidden('#skF_1', C_66) | ~r2_hidden('#skF_1', B_67))), inference(resolution, [status(thm)], [c_106, c_236])).
% 1.99/1.20  tff(c_267, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_106, c_258])).
% 1.99/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.20  
% 1.99/1.20  Inference rules
% 1.99/1.20  ----------------------
% 1.99/1.20  #Ref     : 0
% 1.99/1.20  #Sup     : 47
% 1.99/1.20  #Fact    : 0
% 1.99/1.20  #Define  : 0
% 1.99/1.20  #Split   : 1
% 1.99/1.20  #Chain   : 0
% 1.99/1.20  #Close   : 0
% 1.99/1.20  
% 1.99/1.20  Ordering : KBO
% 1.99/1.20  
% 1.99/1.20  Simplification rules
% 1.99/1.20  ----------------------
% 1.99/1.20  #Subsume      : 13
% 1.99/1.20  #Demod        : 15
% 1.99/1.20  #Tautology    : 20
% 1.99/1.20  #SimpNegUnit  : 6
% 1.99/1.20  #BackRed      : 4
% 1.99/1.20  
% 1.99/1.20  #Partial instantiations: 0
% 1.99/1.20  #Strategies tried      : 1
% 1.99/1.20  
% 1.99/1.20  Timing (in seconds)
% 1.99/1.20  ----------------------
% 1.99/1.20  Preprocessing        : 0.27
% 1.99/1.20  Parsing              : 0.15
% 1.99/1.20  CNF conversion       : 0.02
% 1.99/1.20  Main loop            : 0.20
% 1.99/1.20  Inferencing          : 0.08
% 1.99/1.20  Reduction            : 0.05
% 1.99/1.20  Demodulation         : 0.03
% 1.99/1.20  BG Simplification    : 0.01
% 1.99/1.20  Subsumption          : 0.04
% 1.99/1.20  Abstraction          : 0.01
% 1.99/1.20  MUC search           : 0.00
% 1.99/1.20  Cooper               : 0.00
% 1.99/1.20  Total                : 0.49
% 1.99/1.20  Index Insertion      : 0.00
% 1.99/1.20  Index Deletion       : 0.00
% 1.99/1.20  Index Matching       : 0.00
% 1.99/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
