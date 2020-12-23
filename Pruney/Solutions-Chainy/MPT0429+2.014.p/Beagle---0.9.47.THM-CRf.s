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
% DateTime   : Thu Dec  3 09:58:07 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   23 (  23 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    4
%              Number of atoms          :   16 (  16 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_41,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [C_6,A_2] :
      ( r2_hidden(C_6,k1_zfmisc_1(A_2))
      | ~ r1_tarski(C_6,A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k1_tarski(A_14),k1_zfmisc_1(B_15))
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_18,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_30,plain,(
    ~ r2_hidden(k1_xboole_0,k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_26,c_18])).

tff(c_38,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_30])).

tff(c_42,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:21:29 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.08  
% 1.59/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.09  %$ r2_hidden > r1_tarski > m1_subset_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 1.59/1.09  
% 1.59/1.09  %Foreground sorts:
% 1.59/1.09  
% 1.59/1.09  
% 1.59/1.09  %Background operators:
% 1.59/1.09  
% 1.59/1.09  
% 1.59/1.09  %Foreground operators:
% 1.59/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.59/1.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.59/1.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.59/1.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.59/1.09  tff('#skF_3', type, '#skF_3': $i).
% 1.59/1.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.59/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.09  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.59/1.09  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.59/1.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.59/1.09  
% 1.59/1.09  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.59/1.09  tff(f_34, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.59/1.09  tff(f_38, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 1.59/1.09  tff(f_41, negated_conjecture, ~(![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_setfam_1)).
% 1.59/1.09  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.59/1.09  tff(c_6, plain, (![C_6, A_2]: (r2_hidden(C_6, k1_zfmisc_1(A_2)) | ~r1_tarski(C_6, A_2))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.59/1.09  tff(c_26, plain, (![A_14, B_15]: (m1_subset_1(k1_tarski(A_14), k1_zfmisc_1(B_15)) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.59/1.09  tff(c_18, plain, (~m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.59/1.09  tff(c_30, plain, (~r2_hidden(k1_xboole_0, k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_18])).
% 1.59/1.09  tff(c_38, plain, (~r1_tarski(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_6, c_30])).
% 1.59/1.09  tff(c_42, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_38])).
% 1.59/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.09  
% 1.59/1.09  Inference rules
% 1.59/1.09  ----------------------
% 1.59/1.09  #Ref     : 0
% 1.59/1.09  #Sup     : 4
% 1.59/1.09  #Fact    : 0
% 1.59/1.09  #Define  : 0
% 1.59/1.09  #Split   : 0
% 1.59/1.09  #Chain   : 0
% 1.59/1.09  #Close   : 0
% 1.59/1.09  
% 1.59/1.09  Ordering : KBO
% 1.59/1.10  
% 1.59/1.10  Simplification rules
% 1.59/1.10  ----------------------
% 1.59/1.10  #Subsume      : 0
% 1.59/1.10  #Demod        : 1
% 1.59/1.10  #Tautology    : 1
% 1.59/1.10  #SimpNegUnit  : 0
% 1.59/1.10  #BackRed      : 0
% 1.59/1.10  
% 1.59/1.10  #Partial instantiations: 0
% 1.59/1.10  #Strategies tried      : 1
% 1.59/1.10  
% 1.59/1.10  Timing (in seconds)
% 1.59/1.10  ----------------------
% 1.59/1.10  Preprocessing        : 0.25
% 1.59/1.10  Parsing              : 0.14
% 1.59/1.10  CNF conversion       : 0.02
% 1.59/1.10  Main loop            : 0.07
% 1.59/1.10  Inferencing          : 0.03
% 1.59/1.10  Reduction            : 0.02
% 1.59/1.10  Demodulation         : 0.02
% 1.59/1.10  BG Simplification    : 0.01
% 1.59/1.10  Subsumption          : 0.01
% 1.59/1.10  Abstraction          : 0.00
% 1.59/1.10  MUC search           : 0.00
% 1.59/1.10  Cooper               : 0.00
% 1.59/1.10  Total                : 0.36
% 1.59/1.10  Index Insertion      : 0.00
% 1.59/1.10  Index Deletion       : 0.00
% 1.59/1.10  Index Matching       : 0.00
% 1.59/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
