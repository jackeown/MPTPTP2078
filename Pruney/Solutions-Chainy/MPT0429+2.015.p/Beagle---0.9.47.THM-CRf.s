%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:08 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   27 (  27 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    4
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

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_53,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_setfam_1)).

tff(c_16,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_37,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ m1_subset_1(A_17,k1_zfmisc_1(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_41,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(resolution,[status(thm)],[c_16,c_37])).

tff(c_6,plain,(
    ! [C_6,A_2] :
      ( r2_hidden(C_6,k1_zfmisc_1(A_2))
      | ~ r1_tarski(C_6,A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_58,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(k1_tarski(A_26),k1_zfmisc_1(B_27))
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_26,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_66,plain,(
    ~ r2_hidden(k1_xboole_0,k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_58,c_26])).

tff(c_69,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_66])).

tff(c_73,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_69])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:44:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.12  
% 1.67/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.12  %$ r2_hidden > r1_tarski > m1_subset_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 1.67/1.12  
% 1.67/1.12  %Foreground sorts:
% 1.67/1.12  
% 1.67/1.12  
% 1.67/1.12  %Background operators:
% 1.67/1.12  
% 1.67/1.12  
% 1.67/1.12  %Foreground operators:
% 1.67/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.67/1.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.67/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.67/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.67/1.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.67/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.67/1.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.67/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.12  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.67/1.12  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.67/1.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.67/1.12  
% 1.67/1.13  tff(f_36, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 1.67/1.13  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.67/1.13  tff(f_34, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.67/1.13  tff(f_40, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 1.67/1.13  tff(f_53, negated_conjecture, ~(![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_setfam_1)).
% 1.67/1.13  tff(c_16, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.67/1.13  tff(c_37, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~m1_subset_1(A_17, k1_zfmisc_1(B_18)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.67/1.13  tff(c_41, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(resolution, [status(thm)], [c_16, c_37])).
% 1.67/1.13  tff(c_6, plain, (![C_6, A_2]: (r2_hidden(C_6, k1_zfmisc_1(A_2)) | ~r1_tarski(C_6, A_2))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.67/1.13  tff(c_58, plain, (![A_26, B_27]: (m1_subset_1(k1_tarski(A_26), k1_zfmisc_1(B_27)) | ~r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.67/1.13  tff(c_26, plain, (~m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.67/1.13  tff(c_66, plain, (~r2_hidden(k1_xboole_0, k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_58, c_26])).
% 1.67/1.13  tff(c_69, plain, (~r1_tarski(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_6, c_66])).
% 1.67/1.13  tff(c_73, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_41, c_69])).
% 1.67/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.13  
% 1.67/1.13  Inference rules
% 1.67/1.13  ----------------------
% 1.67/1.13  #Ref     : 0
% 1.67/1.13  #Sup     : 9
% 1.67/1.13  #Fact    : 0
% 1.67/1.13  #Define  : 0
% 1.67/1.13  #Split   : 0
% 1.67/1.13  #Chain   : 0
% 1.67/1.13  #Close   : 0
% 1.67/1.13  
% 1.67/1.13  Ordering : KBO
% 1.67/1.13  
% 1.67/1.13  Simplification rules
% 1.67/1.13  ----------------------
% 1.67/1.13  #Subsume      : 0
% 1.67/1.13  #Demod        : 1
% 1.67/1.13  #Tautology    : 4
% 1.67/1.13  #SimpNegUnit  : 0
% 1.67/1.13  #BackRed      : 0
% 1.67/1.13  
% 1.67/1.13  #Partial instantiations: 0
% 1.67/1.13  #Strategies tried      : 1
% 1.67/1.13  
% 1.67/1.13  Timing (in seconds)
% 1.67/1.13  ----------------------
% 1.67/1.13  Preprocessing        : 0.29
% 1.67/1.13  Parsing              : 0.15
% 1.67/1.13  CNF conversion       : 0.02
% 1.67/1.13  Main loop            : 0.08
% 1.67/1.13  Inferencing          : 0.03
% 1.67/1.13  Reduction            : 0.02
% 1.67/1.13  Demodulation         : 0.02
% 1.67/1.13  BG Simplification    : 0.01
% 1.67/1.13  Subsumption          : 0.01
% 1.67/1.13  Abstraction          : 0.01
% 1.67/1.13  MUC search           : 0.00
% 1.67/1.13  Cooper               : 0.00
% 1.67/1.13  Total                : 0.39
% 1.67/1.13  Index Insertion      : 0.00
% 1.67/1.13  Index Deletion       : 0.00
% 1.67/1.13  Index Matching       : 0.00
% 1.67/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
