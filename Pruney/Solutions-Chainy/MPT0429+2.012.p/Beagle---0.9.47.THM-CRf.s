%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:07 EST 2020

% Result     : Theorem 1.47s
% Output     : CNFRefutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   27 (  27 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  21 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_36,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [C_7,A_3] :
      ( r2_hidden(C_7,k1_zfmisc_1(A_3))
      | ~ r1_tarski(C_7,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_53,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(k1_tarski(A_22),B_23)
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_43,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_26,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_47,plain,(
    ~ r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_43,c_26])).

tff(c_57,plain,(
    ~ r2_hidden(k1_xboole_0,k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_53,c_47])).

tff(c_60,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_57])).

tff(c_64,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.08  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.06/0.26  % Computer   : n003.cluster.edu
% 0.06/0.26  % Model      : x86_64 x86_64
% 0.06/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.26  % Memory     : 8042.1875MB
% 0.06/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.26  % CPULimit   : 60
% 0.06/0.26  % DateTime   : Tue Dec  1 19:50:12 EST 2020
% 0.06/0.26  % CPUTime    : 
% 0.06/0.27  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.47/0.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.47/0.98  
% 1.47/0.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.47/0.98  %$ r2_hidden > r1_tarski > m1_subset_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 1.47/0.98  
% 1.47/0.98  %Foreground sorts:
% 1.47/0.98  
% 1.47/0.98  
% 1.47/0.98  %Background operators:
% 1.47/0.98  
% 1.47/0.98  
% 1.47/0.98  %Foreground operators:
% 1.47/0.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.47/0.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.47/0.98  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.47/0.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.47/0.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.47/0.98  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.47/0.98  tff('#skF_3', type, '#skF_3': $i).
% 1.47/0.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.47/0.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.47/0.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.47/0.98  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.47/0.98  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.47/0.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.47/0.98  
% 1.47/0.98  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.47/0.98  tff(f_36, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.47/0.98  tff(f_40, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.47/0.98  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.47/0.98  tff(f_47, negated_conjecture, ~(![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_setfam_1)).
% 1.47/0.98  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.47/0.98  tff(c_8, plain, (![C_7, A_3]: (r2_hidden(C_7, k1_zfmisc_1(A_3)) | ~r1_tarski(C_7, A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.47/0.98  tff(c_53, plain, (![A_22, B_23]: (r1_tarski(k1_tarski(A_22), B_23) | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.47/0.98  tff(c_43, plain, (![A_18, B_19]: (m1_subset_1(A_18, k1_zfmisc_1(B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.47/0.98  tff(c_26, plain, (~m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.47/0.98  tff(c_47, plain, (~r1_tarski(k1_tarski(k1_xboole_0), k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_43, c_26])).
% 1.47/0.98  tff(c_57, plain, (~r2_hidden(k1_xboole_0, k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_53, c_47])).
% 1.47/0.98  tff(c_60, plain, (~r1_tarski(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_8, c_57])).
% 1.47/0.98  tff(c_64, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_60])).
% 1.47/0.98  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.47/0.98  
% 1.47/0.98  Inference rules
% 1.47/0.98  ----------------------
% 1.47/0.99  #Ref     : 0
% 1.47/0.99  #Sup     : 7
% 1.47/0.99  #Fact    : 0
% 1.47/0.99  #Define  : 0
% 1.47/0.99  #Split   : 0
% 1.47/0.99  #Chain   : 0
% 1.47/0.99  #Close   : 0
% 1.47/0.99  
% 1.47/0.99  Ordering : KBO
% 1.47/0.99  
% 1.47/0.99  Simplification rules
% 1.47/0.99  ----------------------
% 1.47/0.99  #Subsume      : 0
% 1.47/0.99  #Demod        : 1
% 1.47/0.99  #Tautology    : 4
% 1.47/0.99  #SimpNegUnit  : 0
% 1.47/0.99  #BackRed      : 0
% 1.47/0.99  
% 1.47/0.99  #Partial instantiations: 0
% 1.47/0.99  #Strategies tried      : 1
% 1.47/0.99  
% 1.47/0.99  Timing (in seconds)
% 1.47/0.99  ----------------------
% 1.47/0.99  Preprocessing        : 0.29
% 1.47/0.99  Parsing              : 0.15
% 1.47/0.99  CNF conversion       : 0.02
% 1.47/0.99  Main loop            : 0.07
% 1.47/0.99  Inferencing          : 0.03
% 1.47/0.99  Reduction            : 0.02
% 1.47/0.99  Demodulation         : 0.02
% 1.47/0.99  BG Simplification    : 0.01
% 1.47/0.99  Subsumption          : 0.01
% 1.47/0.99  Abstraction          : 0.01
% 1.47/0.99  MUC search           : 0.00
% 1.47/0.99  Cooper               : 0.00
% 1.47/0.99  Total                : 0.38
% 1.47/0.99  Index Insertion      : 0.00
% 1.47/0.99  Index Deletion       : 0.00
% 1.47/0.99  Index Matching       : 0.00
% 1.47/0.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
