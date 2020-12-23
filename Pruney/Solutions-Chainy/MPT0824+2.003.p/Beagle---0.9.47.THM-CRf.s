%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:13 EST 2020

% Result     : Theorem 1.44s
% Output     : CNFRefutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   18 (  18 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    3
%              Number of atoms          :   10 (  10 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A,B))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relset_1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_11,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_17,plain,(
    ~ r1_tarski(k1_xboole_0,k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_11,c_8])).

tff(c_22,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n018.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 15:24:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.44/1.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.44/1.01  
% 1.44/1.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.44/1.02  %$ r1_tarski > m1_subset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.44/1.02  
% 1.44/1.02  %Foreground sorts:
% 1.44/1.02  
% 1.44/1.02  
% 1.44/1.02  %Background operators:
% 1.44/1.02  
% 1.44/1.02  
% 1.44/1.02  %Foreground operators:
% 1.44/1.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.44/1.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.44/1.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.44/1.02  tff('#skF_2', type, '#skF_2': $i).
% 1.44/1.02  tff('#skF_1', type, '#skF_1': $i).
% 1.44/1.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.44/1.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.44/1.02  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.44/1.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.44/1.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.44/1.02  
% 1.54/1.02  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.54/1.02  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.54/1.02  tff(f_34, negated_conjecture, ~(![A, B]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relset_1)).
% 1.54/1.02  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.54/1.02  tff(c_11, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.54/1.02  tff(c_8, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.54/1.02  tff(c_17, plain, (~r1_tarski(k1_xboole_0, k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_11, c_8])).
% 1.54/1.02  tff(c_22, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_17])).
% 1.54/1.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.54/1.02  
% 1.54/1.02  Inference rules
% 1.54/1.02  ----------------------
% 1.54/1.02  #Ref     : 0
% 1.54/1.02  #Sup     : 2
% 1.54/1.02  #Fact    : 0
% 1.54/1.02  #Define  : 0
% 1.54/1.02  #Split   : 0
% 1.54/1.02  #Chain   : 0
% 1.54/1.02  #Close   : 0
% 1.54/1.02  
% 1.54/1.02  Ordering : KBO
% 1.54/1.02  
% 1.54/1.02  Simplification rules
% 1.54/1.02  ----------------------
% 1.54/1.02  #Subsume      : 0
% 1.54/1.02  #Demod        : 1
% 1.54/1.02  #Tautology    : 1
% 1.54/1.02  #SimpNegUnit  : 0
% 1.54/1.02  #BackRed      : 0
% 1.54/1.02  
% 1.54/1.02  #Partial instantiations: 0
% 1.54/1.02  #Strategies tried      : 1
% 1.54/1.02  
% 1.54/1.02  Timing (in seconds)
% 1.54/1.02  ----------------------
% 1.54/1.02  Preprocessing        : 0.23
% 1.54/1.03  Parsing              : 0.13
% 1.54/1.03  CNF conversion       : 0.01
% 1.54/1.03  Main loop            : 0.06
% 1.54/1.03  Inferencing          : 0.02
% 1.54/1.03  Reduction            : 0.02
% 1.54/1.03  Demodulation         : 0.01
% 1.54/1.03  BG Simplification    : 0.01
% 1.54/1.03  Subsumption          : 0.01
% 1.54/1.03  Abstraction          : 0.00
% 1.54/1.03  MUC search           : 0.00
% 1.54/1.03  Cooper               : 0.00
% 1.54/1.03  Total                : 0.32
% 1.54/1.03  Index Insertion      : 0.00
% 1.54/1.03  Index Deletion       : 0.00
% 1.54/1.03  Index Matching       : 0.00
% 1.54/1.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
