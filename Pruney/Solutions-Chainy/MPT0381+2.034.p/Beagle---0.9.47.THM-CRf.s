%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:05 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   29 (  30 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  34 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(c_30,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k1_tarski(A_6),B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_26,plain,(
    ! [A_10] : ~ v1_xboole_0(k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [C_5,A_1] :
      ( r2_hidden(C_5,k1_zfmisc_1(A_1))
      | ~ r1_tarski(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_54,plain,(
    ! [B_24,A_25] :
      ( m1_subset_1(B_24,A_25)
      | ~ r2_hidden(B_24,A_25)
      | v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_57,plain,(
    ! [C_5,A_1] :
      ( m1_subset_1(C_5,k1_zfmisc_1(A_1))
      | v1_xboole_0(k1_zfmisc_1(A_1))
      | ~ r1_tarski(C_5,A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_54])).

tff(c_66,plain,(
    ! [C_26,A_27] :
      ( m1_subset_1(C_26,k1_zfmisc_1(A_27))
      | ~ r1_tarski(C_26,A_27) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_57])).

tff(c_28,plain,(
    ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_74,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_28])).

tff(c_77,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_74])).

tff(c_81,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_77])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:33:24 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.58/1.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.05  
% 1.58/1.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.05  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.58/1.05  
% 1.58/1.05  %Foreground sorts:
% 1.58/1.05  
% 1.58/1.05  
% 1.58/1.05  %Background operators:
% 1.58/1.05  
% 1.58/1.05  
% 1.58/1.05  %Foreground operators:
% 1.58/1.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.58/1.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.58/1.05  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.58/1.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.58/1.05  tff('#skF_3', type, '#skF_3': $i).
% 1.58/1.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.58/1.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.58/1.05  tff('#skF_4', type, '#skF_4': $i).
% 1.58/1.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.58/1.05  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.58/1.05  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.58/1.05  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.58/1.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.58/1.05  
% 1.58/1.06  tff(f_57, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 1.58/1.06  tff(f_36, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 1.58/1.06  tff(f_52, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.58/1.06  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.58/1.06  tff(f_49, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 1.58/1.06  tff(c_30, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.58/1.06  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(k1_tarski(A_6), B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.58/1.06  tff(c_26, plain, (![A_10]: (~v1_xboole_0(k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.58/1.06  tff(c_4, plain, (![C_5, A_1]: (r2_hidden(C_5, k1_zfmisc_1(A_1)) | ~r1_tarski(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.58/1.06  tff(c_54, plain, (![B_24, A_25]: (m1_subset_1(B_24, A_25) | ~r2_hidden(B_24, A_25) | v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.58/1.06  tff(c_57, plain, (![C_5, A_1]: (m1_subset_1(C_5, k1_zfmisc_1(A_1)) | v1_xboole_0(k1_zfmisc_1(A_1)) | ~r1_tarski(C_5, A_1))), inference(resolution, [status(thm)], [c_4, c_54])).
% 1.58/1.06  tff(c_66, plain, (![C_26, A_27]: (m1_subset_1(C_26, k1_zfmisc_1(A_27)) | ~r1_tarski(C_26, A_27))), inference(negUnitSimplification, [status(thm)], [c_26, c_57])).
% 1.58/1.06  tff(c_28, plain, (~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.58/1.06  tff(c_74, plain, (~r1_tarski(k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_66, c_28])).
% 1.58/1.06  tff(c_77, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_16, c_74])).
% 1.58/1.06  tff(c_81, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_77])).
% 1.58/1.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.06  
% 1.58/1.06  Inference rules
% 1.58/1.06  ----------------------
% 1.58/1.06  #Ref     : 0
% 1.58/1.06  #Sup     : 9
% 1.58/1.06  #Fact    : 0
% 1.58/1.06  #Define  : 0
% 1.58/1.06  #Split   : 1
% 1.58/1.06  #Chain   : 0
% 1.58/1.06  #Close   : 0
% 1.58/1.06  
% 1.58/1.06  Ordering : KBO
% 1.58/1.06  
% 1.58/1.06  Simplification rules
% 1.58/1.06  ----------------------
% 1.58/1.06  #Subsume      : 2
% 1.58/1.06  #Demod        : 1
% 1.58/1.06  #Tautology    : 3
% 1.58/1.06  #SimpNegUnit  : 1
% 1.58/1.06  #BackRed      : 0
% 1.58/1.06  
% 1.58/1.06  #Partial instantiations: 0
% 1.58/1.06  #Strategies tried      : 1
% 1.58/1.06  
% 1.58/1.06  Timing (in seconds)
% 1.58/1.06  ----------------------
% 1.58/1.06  Preprocessing        : 0.27
% 1.58/1.06  Parsing              : 0.15
% 1.58/1.06  CNF conversion       : 0.02
% 1.58/1.06  Main loop            : 0.10
% 1.58/1.06  Inferencing          : 0.04
% 1.58/1.06  Reduction            : 0.03
% 1.58/1.06  Demodulation         : 0.01
% 1.58/1.06  BG Simplification    : 0.01
% 1.58/1.06  Subsumption          : 0.02
% 1.58/1.06  Abstraction          : 0.00
% 1.58/1.06  MUC search           : 0.00
% 1.58/1.06  Cooper               : 0.00
% 1.58/1.06  Total                : 0.39
% 1.58/1.06  Index Insertion      : 0.00
% 1.58/1.06  Index Deletion       : 0.00
% 1.58/1.06  Index Matching       : 0.00
% 1.58/1.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
