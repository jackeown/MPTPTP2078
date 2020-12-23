%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:09 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   35 (  35 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   26 (  26 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_46,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_67,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_setfam_1)).

tff(c_20,plain,(
    ! [A_31] : ~ v1_xboole_0(k1_zfmisc_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_22,plain,(
    ! [A_32] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_78,plain,(
    ! [A_54,B_55] :
      ( r2_hidden(A_54,B_55)
      | v1_xboole_0(B_55)
      | ~ m1_subset_1(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(k1_tarski(A_29),B_30)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_65,plain,(
    ! [A_52,B_53] :
      ( m1_subset_1(A_52,k1_zfmisc_1(B_53))
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_32,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_73,plain,(
    ~ r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_65,c_32])).

tff(c_77,plain,(
    ~ r2_hidden(k1_xboole_0,k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_18,c_73])).

tff(c_81,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_78,c_77])).

tff(c_84,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_81])).

tff(c_86,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_84])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:06:14 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.17  
% 2.02/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.17  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1
% 2.02/1.17  
% 2.02/1.17  %Foreground sorts:
% 2.02/1.17  
% 2.02/1.17  
% 2.02/1.17  %Background operators:
% 2.02/1.17  
% 2.02/1.17  
% 2.02/1.17  %Foreground operators:
% 2.02/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.02/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.17  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.02/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.02/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.02/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.02/1.17  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.17  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.02/1.17  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.17  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.02/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.02/1.17  
% 2.02/1.18  tff(f_46, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.02/1.18  tff(f_48, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.02/1.18  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.02/1.18  tff(f_43, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.02/1.18  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.02/1.18  tff(f_67, negated_conjecture, ~(![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_setfam_1)).
% 2.02/1.18  tff(c_20, plain, (![A_31]: (~v1_xboole_0(k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.02/1.18  tff(c_22, plain, (![A_32]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.02/1.18  tff(c_78, plain, (![A_54, B_55]: (r2_hidden(A_54, B_55) | v1_xboole_0(B_55) | ~m1_subset_1(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.02/1.18  tff(c_18, plain, (![A_29, B_30]: (r1_tarski(k1_tarski(A_29), B_30) | ~r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.02/1.18  tff(c_65, plain, (![A_52, B_53]: (m1_subset_1(A_52, k1_zfmisc_1(B_53)) | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.02/1.18  tff(c_32, plain, (~m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.02/1.18  tff(c_73, plain, (~r1_tarski(k1_tarski(k1_xboole_0), k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_65, c_32])).
% 2.02/1.18  tff(c_77, plain, (~r2_hidden(k1_xboole_0, k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_73])).
% 2.02/1.18  tff(c_81, plain, (v1_xboole_0(k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_78, c_77])).
% 2.02/1.18  tff(c_84, plain, (v1_xboole_0(k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_81])).
% 2.02/1.18  tff(c_86, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_84])).
% 2.02/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.18  
% 2.02/1.18  Inference rules
% 2.02/1.18  ----------------------
% 2.02/1.18  #Ref     : 0
% 2.02/1.18  #Sup     : 10
% 2.02/1.18  #Fact    : 0
% 2.02/1.18  #Define  : 0
% 2.02/1.18  #Split   : 0
% 2.02/1.18  #Chain   : 0
% 2.02/1.18  #Close   : 0
% 2.02/1.18  
% 2.02/1.18  Ordering : KBO
% 2.02/1.18  
% 2.02/1.18  Simplification rules
% 2.02/1.18  ----------------------
% 2.02/1.18  #Subsume      : 0
% 2.02/1.18  #Demod        : 1
% 2.02/1.18  #Tautology    : 6
% 2.02/1.18  #SimpNegUnit  : 1
% 2.02/1.18  #BackRed      : 0
% 2.02/1.18  
% 2.02/1.18  #Partial instantiations: 0
% 2.02/1.18  #Strategies tried      : 1
% 2.02/1.18  
% 2.02/1.18  Timing (in seconds)
% 2.02/1.18  ----------------------
% 2.02/1.18  Preprocessing        : 0.33
% 2.02/1.18  Parsing              : 0.18
% 2.02/1.18  CNF conversion       : 0.02
% 2.02/1.18  Main loop            : 0.10
% 2.02/1.18  Inferencing          : 0.04
% 2.02/1.18  Reduction            : 0.03
% 2.02/1.18  Demodulation         : 0.02
% 2.02/1.19  BG Simplification    : 0.01
% 2.02/1.19  Subsumption          : 0.01
% 2.02/1.19  Abstraction          : 0.01
% 2.02/1.19  MUC search           : 0.00
% 2.02/1.19  Cooper               : 0.00
% 2.02/1.19  Total                : 0.46
% 2.02/1.19  Index Insertion      : 0.00
% 2.02/1.19  Index Deletion       : 0.00
% 2.02/1.19  Index Matching       : 0.00
% 2.02/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
