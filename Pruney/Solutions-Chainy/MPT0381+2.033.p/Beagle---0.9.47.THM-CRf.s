%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:05 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   30 (  31 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  34 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_54,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(c_32,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(k1_tarski(A_7),B_8)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_28,plain,(
    ! [A_11] : ~ v1_xboole_0(k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [C_6,A_2] :
      ( r2_hidden(C_6,k1_zfmisc_1(A_2))
      | ~ r1_tarski(C_6,A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_79,plain,(
    ! [B_30,A_31] :
      ( m1_subset_1(B_30,A_31)
      | ~ r2_hidden(B_30,A_31)
      | v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_85,plain,(
    ! [C_6,A_2] :
      ( m1_subset_1(C_6,k1_zfmisc_1(A_2))
      | v1_xboole_0(k1_zfmisc_1(A_2))
      | ~ r1_tarski(C_6,A_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_79])).

tff(c_105,plain,(
    ! [C_34,A_35] :
      ( m1_subset_1(C_34,k1_zfmisc_1(A_35))
      | ~ r1_tarski(C_34,A_35) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_85])).

tff(c_30,plain,(
    ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_117,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_105,c_30])).

tff(c_120,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_117])).

tff(c_124,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_120])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:06:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.17  
% 1.73/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.17  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.73/1.17  
% 1.73/1.17  %Foreground sorts:
% 1.73/1.17  
% 1.73/1.17  
% 1.73/1.17  %Background operators:
% 1.73/1.17  
% 1.73/1.17  
% 1.73/1.17  %Foreground operators:
% 1.73/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.73/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.73/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.73/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.73/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.73/1.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.73/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.73/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.73/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.73/1.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.73/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.73/1.17  
% 1.73/1.18  tff(f_59, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 1.73/1.18  tff(f_38, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.73/1.18  tff(f_54, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.73/1.18  tff(f_34, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.73/1.18  tff(f_51, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 1.73/1.18  tff(c_32, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.73/1.18  tff(c_18, plain, (![A_7, B_8]: (r1_tarski(k1_tarski(A_7), B_8) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.73/1.18  tff(c_28, plain, (![A_11]: (~v1_xboole_0(k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.73/1.18  tff(c_6, plain, (![C_6, A_2]: (r2_hidden(C_6, k1_zfmisc_1(A_2)) | ~r1_tarski(C_6, A_2))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.73/1.18  tff(c_79, plain, (![B_30, A_31]: (m1_subset_1(B_30, A_31) | ~r2_hidden(B_30, A_31) | v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.73/1.18  tff(c_85, plain, (![C_6, A_2]: (m1_subset_1(C_6, k1_zfmisc_1(A_2)) | v1_xboole_0(k1_zfmisc_1(A_2)) | ~r1_tarski(C_6, A_2))), inference(resolution, [status(thm)], [c_6, c_79])).
% 1.73/1.18  tff(c_105, plain, (![C_34, A_35]: (m1_subset_1(C_34, k1_zfmisc_1(A_35)) | ~r1_tarski(C_34, A_35))), inference(negUnitSimplification, [status(thm)], [c_28, c_85])).
% 1.73/1.18  tff(c_30, plain, (~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.73/1.18  tff(c_117, plain, (~r1_tarski(k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_105, c_30])).
% 1.73/1.18  tff(c_120, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_18, c_117])).
% 1.73/1.18  tff(c_124, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_120])).
% 1.73/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.18  
% 1.73/1.18  Inference rules
% 1.73/1.18  ----------------------
% 1.73/1.18  #Ref     : 0
% 1.73/1.18  #Sup     : 17
% 1.73/1.18  #Fact    : 0
% 1.73/1.18  #Define  : 0
% 1.73/1.18  #Split   : 1
% 1.73/1.18  #Chain   : 0
% 1.73/1.18  #Close   : 0
% 1.73/1.18  
% 1.73/1.18  Ordering : KBO
% 1.73/1.18  
% 1.73/1.18  Simplification rules
% 1.73/1.18  ----------------------
% 1.73/1.18  #Subsume      : 3
% 1.73/1.18  #Demod        : 1
% 1.73/1.18  #Tautology    : 7
% 1.73/1.18  #SimpNegUnit  : 2
% 1.73/1.18  #BackRed      : 0
% 1.73/1.18  
% 1.73/1.18  #Partial instantiations: 0
% 1.73/1.18  #Strategies tried      : 1
% 1.73/1.18  
% 1.73/1.18  Timing (in seconds)
% 1.73/1.18  ----------------------
% 1.93/1.18  Preprocessing        : 0.30
% 1.93/1.18  Parsing              : 0.15
% 1.93/1.18  CNF conversion       : 0.02
% 1.93/1.18  Main loop            : 0.13
% 1.93/1.18  Inferencing          : 0.05
% 1.93/1.18  Reduction            : 0.03
% 1.93/1.18  Demodulation         : 0.02
% 1.93/1.18  BG Simplification    : 0.02
% 1.93/1.18  Subsumption          : 0.02
% 1.93/1.18  Abstraction          : 0.01
% 1.93/1.18  MUC search           : 0.00
% 1.93/1.18  Cooper               : 0.00
% 1.93/1.18  Total                : 0.45
% 1.93/1.18  Index Insertion      : 0.00
% 1.93/1.18  Index Deletion       : 0.00
% 1.93/1.18  Index Matching       : 0.00
% 1.93/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
