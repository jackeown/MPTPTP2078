%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:08 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   35 (  35 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   24 (  24 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_1

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_46,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_41,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k1_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_59,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_setfam_1)).

tff(c_20,plain,(
    ! [A_31] : ~ v1_xboole_0(k1_zfmisc_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_16,plain,(
    ! [A_29] : k1_subset_1(A_29) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_30] : m1_subset_1(k1_subset_1(A_30),k1_zfmisc_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_27,plain,(
    ! [A_30] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_30)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_24,plain,(
    ! [A_34,B_35] :
      ( r2_hidden(A_34,B_35)
      | v1_xboole_0(B_35)
      | ~ m1_subset_1(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_56,plain,(
    ! [A_44,B_45] :
      ( m1_subset_1(k1_tarski(A_44),k1_zfmisc_1(B_45))
      | ~ r2_hidden(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_26,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_60,plain,(
    ~ r2_hidden(k1_xboole_0,k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_56,c_26])).

tff(c_63,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_60])).

tff(c_66,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_63])).

tff(c_68,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_66])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:24:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.19  
% 1.78/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.19  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_1
% 1.78/1.19  
% 1.78/1.19  %Foreground sorts:
% 1.78/1.19  
% 1.78/1.19  
% 1.78/1.19  %Background operators:
% 1.78/1.19  
% 1.78/1.19  
% 1.78/1.19  %Foreground operators:
% 1.78/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.78/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.78/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.78/1.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.78/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.78/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.78/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.78/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.78/1.19  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.78/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.78/1.19  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.78/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.19  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 1.78/1.19  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.78/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.78/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.78/1.19  
% 1.78/1.20  tff(f_46, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.78/1.20  tff(f_41, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 1.78/1.20  tff(f_43, axiom, (![A]: m1_subset_1(k1_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 1.78/1.20  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 1.78/1.20  tff(f_50, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 1.78/1.20  tff(f_59, negated_conjecture, ~(![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_setfam_1)).
% 1.78/1.20  tff(c_20, plain, (![A_31]: (~v1_xboole_0(k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.78/1.20  tff(c_16, plain, (![A_29]: (k1_subset_1(A_29)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.78/1.20  tff(c_18, plain, (![A_30]: (m1_subset_1(k1_subset_1(A_30), k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.78/1.20  tff(c_27, plain, (![A_30]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_30)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18])).
% 1.78/1.20  tff(c_24, plain, (![A_34, B_35]: (r2_hidden(A_34, B_35) | v1_xboole_0(B_35) | ~m1_subset_1(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.78/1.20  tff(c_56, plain, (![A_44, B_45]: (m1_subset_1(k1_tarski(A_44), k1_zfmisc_1(B_45)) | ~r2_hidden(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.78/1.20  tff(c_26, plain, (~m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.78/1.20  tff(c_60, plain, (~r2_hidden(k1_xboole_0, k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_56, c_26])).
% 1.78/1.20  tff(c_63, plain, (v1_xboole_0(k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_60])).
% 1.78/1.20  tff(c_66, plain, (v1_xboole_0(k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_27, c_63])).
% 1.78/1.20  tff(c_68, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_66])).
% 1.78/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.20  
% 1.78/1.20  Inference rules
% 1.78/1.20  ----------------------
% 1.78/1.20  #Ref     : 0
% 1.78/1.20  #Sup     : 8
% 1.78/1.20  #Fact    : 0
% 1.78/1.20  #Define  : 0
% 1.78/1.20  #Split   : 0
% 1.78/1.20  #Chain   : 0
% 1.78/1.20  #Close   : 0
% 1.78/1.20  
% 1.78/1.20  Ordering : KBO
% 1.78/1.20  
% 1.78/1.20  Simplification rules
% 1.78/1.20  ----------------------
% 1.78/1.20  #Subsume      : 0
% 1.78/1.20  #Demod        : 2
% 1.78/1.20  #Tautology    : 6
% 1.78/1.20  #SimpNegUnit  : 1
% 1.78/1.20  #BackRed      : 0
% 1.78/1.20  
% 1.78/1.20  #Partial instantiations: 0
% 1.78/1.20  #Strategies tried      : 1
% 1.78/1.20  
% 1.78/1.20  Timing (in seconds)
% 1.78/1.20  ----------------------
% 1.78/1.20  Preprocessing        : 0.30
% 1.78/1.20  Parsing              : 0.17
% 1.78/1.20  CNF conversion       : 0.02
% 1.78/1.20  Main loop            : 0.08
% 1.78/1.20  Inferencing          : 0.03
% 1.78/1.20  Reduction            : 0.03
% 1.78/1.20  Demodulation         : 0.02
% 1.78/1.20  BG Simplification    : 0.01
% 1.78/1.20  Subsumption          : 0.01
% 1.78/1.20  Abstraction          : 0.01
% 1.78/1.20  MUC search           : 0.00
% 1.78/1.20  Cooper               : 0.00
% 1.78/1.20  Total                : 0.41
% 1.78/1.20  Index Insertion      : 0.00
% 1.78/1.20  Index Deletion       : 0.00
% 1.78/1.21  Index Matching       : 0.00
% 1.78/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
