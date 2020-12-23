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
% DateTime   : Thu Dec  3 09:57:03 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   48 (  57 expanded)
%              Number of leaves         :   29 (  34 expanded)
%              Depth                    :    6
%              Number of atoms          :   51 (  66 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_42,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_52,plain,(
    ! [B_46,A_47] :
      ( ~ r2_hidden(B_46,A_47)
      | ~ v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_52])).

tff(c_106,plain,(
    ! [B_60,A_61] :
      ( m1_subset_1(B_60,A_61)
      | ~ r2_hidden(B_60,A_61)
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_112,plain,
    ( m1_subset_1('#skF_3','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_106])).

tff(c_116,plain,(
    m1_subset_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_112])).

tff(c_175,plain,(
    ! [B_74,A_75] :
      ( m1_subset_1(k1_tarski(B_74),k1_zfmisc_1(A_75))
      | k1_xboole_0 = A_75
      | ~ m1_subset_1(B_74,A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_40,plain,(
    ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_181,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_175,c_40])).

tff(c_185,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_181])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_97,plain,(
    ! [A_57,B_58,C_59] :
      ( ~ r1_xboole_0(A_57,B_58)
      | ~ r2_hidden(C_59,k3_xboole_0(A_57,B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_126,plain,(
    ! [A_63,C_64] :
      ( ~ r1_xboole_0(A_63,A_63)
      | ~ r2_hidden(C_64,A_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_97])).

tff(c_144,plain,(
    ! [C_67] : ~ r2_hidden(C_67,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_126])).

tff(c_154,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_144])).

tff(c_187,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_154])).

tff(c_192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_187])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:55:44 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.32  
% 2.10/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.32  %$ r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.10/1.32  
% 2.10/1.32  %Foreground sorts:
% 2.10/1.32  
% 2.10/1.32  
% 2.10/1.32  %Background operators:
% 2.10/1.32  
% 2.10/1.32  
% 2.10/1.32  %Foreground operators:
% 2.10/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.10/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.10/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.10/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.10/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.10/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.10/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.10/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.10/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.10/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.10/1.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.10/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.10/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.10/1.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.10/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.10/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.10/1.32  
% 2.10/1.33  tff(f_98, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 2.10/1.33  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.10/1.33  tff(f_86, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.10/1.33  tff(f_93, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 2.10/1.33  tff(f_59, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.10/1.33  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.10/1.33  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.10/1.33  tff(c_42, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.10/1.33  tff(c_52, plain, (![B_46, A_47]: (~r2_hidden(B_46, A_47) | ~v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.33  tff(c_56, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_52])).
% 2.10/1.33  tff(c_106, plain, (![B_60, A_61]: (m1_subset_1(B_60, A_61) | ~r2_hidden(B_60, A_61) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.10/1.33  tff(c_112, plain, (m1_subset_1('#skF_3', '#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_106])).
% 2.10/1.33  tff(c_116, plain, (m1_subset_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_56, c_112])).
% 2.10/1.33  tff(c_175, plain, (![B_74, A_75]: (m1_subset_1(k1_tarski(B_74), k1_zfmisc_1(A_75)) | k1_xboole_0=A_75 | ~m1_subset_1(B_74, A_75))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.10/1.33  tff(c_40, plain, (~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.10/1.33  tff(c_181, plain, (k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_175, c_40])).
% 2.10/1.33  tff(c_185, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_181])).
% 2.10/1.33  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.33  tff(c_12, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.10/1.33  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.10/1.33  tff(c_97, plain, (![A_57, B_58, C_59]: (~r1_xboole_0(A_57, B_58) | ~r2_hidden(C_59, k3_xboole_0(A_57, B_58)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.10/1.33  tff(c_126, plain, (![A_63, C_64]: (~r1_xboole_0(A_63, A_63) | ~r2_hidden(C_64, A_63))), inference(superposition, [status(thm), theory('equality')], [c_6, c_97])).
% 2.10/1.33  tff(c_144, plain, (![C_67]: (~r2_hidden(C_67, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_126])).
% 2.10/1.33  tff(c_154, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_144])).
% 2.10/1.33  tff(c_187, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_185, c_154])).
% 2.10/1.33  tff(c_192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_187])).
% 2.10/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.33  
% 2.10/1.33  Inference rules
% 2.10/1.33  ----------------------
% 2.10/1.33  #Ref     : 0
% 2.10/1.33  #Sup     : 29
% 2.10/1.33  #Fact    : 0
% 2.10/1.33  #Define  : 0
% 2.10/1.33  #Split   : 1
% 2.10/1.33  #Chain   : 0
% 2.10/1.33  #Close   : 0
% 2.10/1.33  
% 2.10/1.33  Ordering : KBO
% 2.10/1.33  
% 2.10/1.33  Simplification rules
% 2.10/1.33  ----------------------
% 2.10/1.33  #Subsume      : 1
% 2.10/1.33  #Demod        : 9
% 2.10/1.33  #Tautology    : 16
% 2.10/1.33  #SimpNegUnit  : 2
% 2.10/1.33  #BackRed      : 5
% 2.10/1.33  
% 2.10/1.33  #Partial instantiations: 0
% 2.10/1.33  #Strategies tried      : 1
% 2.10/1.33  
% 2.10/1.33  Timing (in seconds)
% 2.10/1.33  ----------------------
% 2.10/1.33  Preprocessing        : 0.35
% 2.10/1.33  Parsing              : 0.19
% 2.10/1.33  CNF conversion       : 0.02
% 2.10/1.33  Main loop            : 0.19
% 2.10/1.33  Inferencing          : 0.07
% 2.10/1.33  Reduction            : 0.05
% 2.10/1.33  Demodulation         : 0.03
% 2.10/1.33  BG Simplification    : 0.02
% 2.10/1.33  Subsumption          : 0.03
% 2.10/1.33  Abstraction          : 0.01
% 2.10/1.33  MUC search           : 0.00
% 2.10/1.33  Cooper               : 0.00
% 2.10/1.33  Total                : 0.57
% 2.10/1.33  Index Insertion      : 0.00
% 2.10/1.33  Index Deletion       : 0.00
% 2.10/1.33  Index Matching       : 0.00
% 2.10/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
