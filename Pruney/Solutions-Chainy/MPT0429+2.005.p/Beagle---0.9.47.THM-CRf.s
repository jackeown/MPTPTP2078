%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:06 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   44 (  53 expanded)
%              Number of leaves         :   27 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   40 (  54 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_55,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_setfam_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_36,plain,(
    ! [A_36] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_71,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,B_55)
      | ~ m1_subset_1(A_54,k1_zfmisc_1(B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_75,plain,(
    ! [A_36] : r1_tarski(k1_xboole_0,A_36) ),
    inference(resolution,[status(thm)],[c_36,c_71])).

tff(c_114,plain,(
    ! [C_64,B_65,A_66] :
      ( ~ v1_xboole_0(C_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(C_64))
      | ~ r2_hidden(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_120,plain,(
    ! [A_36,A_66] :
      ( ~ v1_xboole_0(A_36)
      | ~ r2_hidden(A_66,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_36,c_114])).

tff(c_130,plain,(
    ! [A_66] : ~ r2_hidden(A_66,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_153,plain,(
    ! [B_85,A_86] :
      ( m1_subset_1(k1_tarski(B_85),k1_zfmisc_1(A_86))
      | k1_xboole_0 = A_86
      | ~ m1_subset_1(B_85,A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_48,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_163,plain,
    ( k1_zfmisc_1('#skF_3') = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_153,c_48])).

tff(c_169,plain,(
    k1_zfmisc_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_163])).

tff(c_26,plain,(
    ! [C_35,A_31] :
      ( r2_hidden(C_35,k1_zfmisc_1(A_31))
      | ~ r1_tarski(C_35,A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_186,plain,(
    ! [C_35] :
      ( r2_hidden(C_35,k1_xboole_0)
      | ~ r1_tarski(C_35,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_26])).

tff(c_215,plain,(
    ! [C_91] : ~ r1_tarski(C_91,'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_186])).

tff(c_223,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_75,c_215])).

tff(c_224,plain,(
    ! [A_36] : ~ v1_xboole_0(A_36) ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_226,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:02:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.31  
% 1.90/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.31  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 1.90/1.31  
% 1.90/1.31  %Foreground sorts:
% 1.90/1.31  
% 1.90/1.31  
% 1.90/1.31  %Background operators:
% 1.90/1.31  
% 1.90/1.31  
% 1.90/1.31  %Foreground operators:
% 1.90/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.90/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.90/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.90/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.90/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.90/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.90/1.31  tff('#skF_3', type, '#skF_3': $i).
% 1.90/1.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.90/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.90/1.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.90/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.90/1.31  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.90/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.90/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.90/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.90/1.31  
% 1.90/1.32  tff(f_55, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 1.90/1.32  tff(f_66, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.90/1.32  tff(f_79, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 1.90/1.32  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 1.90/1.32  tff(f_82, negated_conjecture, ~(![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_setfam_1)).
% 1.90/1.32  tff(f_53, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.90/1.32  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.90/1.32  tff(c_36, plain, (![A_36]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.90/1.32  tff(c_71, plain, (![A_54, B_55]: (r1_tarski(A_54, B_55) | ~m1_subset_1(A_54, k1_zfmisc_1(B_55)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.90/1.32  tff(c_75, plain, (![A_36]: (r1_tarski(k1_xboole_0, A_36))), inference(resolution, [status(thm)], [c_36, c_71])).
% 1.90/1.32  tff(c_114, plain, (![C_64, B_65, A_66]: (~v1_xboole_0(C_64) | ~m1_subset_1(B_65, k1_zfmisc_1(C_64)) | ~r2_hidden(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.90/1.32  tff(c_120, plain, (![A_36, A_66]: (~v1_xboole_0(A_36) | ~r2_hidden(A_66, k1_xboole_0))), inference(resolution, [status(thm)], [c_36, c_114])).
% 1.90/1.32  tff(c_130, plain, (![A_66]: (~r2_hidden(A_66, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_120])).
% 1.90/1.32  tff(c_153, plain, (![B_85, A_86]: (m1_subset_1(k1_tarski(B_85), k1_zfmisc_1(A_86)) | k1_xboole_0=A_86 | ~m1_subset_1(B_85, A_86))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.90/1.32  tff(c_48, plain, (~m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.90/1.32  tff(c_163, plain, (k1_zfmisc_1('#skF_3')=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_153, c_48])).
% 1.90/1.32  tff(c_169, plain, (k1_zfmisc_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_163])).
% 1.90/1.32  tff(c_26, plain, (![C_35, A_31]: (r2_hidden(C_35, k1_zfmisc_1(A_31)) | ~r1_tarski(C_35, A_31))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.90/1.32  tff(c_186, plain, (![C_35]: (r2_hidden(C_35, k1_xboole_0) | ~r1_tarski(C_35, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_169, c_26])).
% 1.90/1.32  tff(c_215, plain, (![C_91]: (~r1_tarski(C_91, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_130, c_186])).
% 1.90/1.32  tff(c_223, plain, $false, inference(resolution, [status(thm)], [c_75, c_215])).
% 1.90/1.32  tff(c_224, plain, (![A_36]: (~v1_xboole_0(A_36))), inference(splitRight, [status(thm)], [c_120])).
% 1.90/1.32  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.90/1.32  tff(c_226, plain, $false, inference(negUnitSimplification, [status(thm)], [c_224, c_2])).
% 1.90/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.32  
% 1.90/1.32  Inference rules
% 1.90/1.32  ----------------------
% 1.90/1.32  #Ref     : 0
% 1.90/1.32  #Sup     : 41
% 1.90/1.32  #Fact    : 0
% 1.90/1.32  #Define  : 0
% 1.90/1.32  #Split   : 1
% 1.90/1.32  #Chain   : 0
% 1.90/1.32  #Close   : 0
% 1.90/1.32  
% 1.90/1.32  Ordering : KBO
% 1.90/1.32  
% 1.90/1.32  Simplification rules
% 1.90/1.32  ----------------------
% 1.90/1.32  #Subsume      : 3
% 1.90/1.32  #Demod        : 7
% 1.90/1.32  #Tautology    : 16
% 1.90/1.32  #SimpNegUnit  : 2
% 1.90/1.32  #BackRed      : 3
% 1.90/1.32  
% 1.90/1.32  #Partial instantiations: 0
% 1.90/1.32  #Strategies tried      : 1
% 1.90/1.32  
% 1.90/1.32  Timing (in seconds)
% 1.90/1.32  ----------------------
% 1.90/1.32  Preprocessing        : 0.37
% 1.90/1.32  Parsing              : 0.18
% 1.90/1.32  CNF conversion       : 0.02
% 1.90/1.32  Main loop            : 0.16
% 1.90/1.32  Inferencing          : 0.05
% 1.90/1.33  Reduction            : 0.05
% 1.90/1.33  Demodulation         : 0.04
% 1.90/1.33  BG Simplification    : 0.02
% 1.90/1.33  Subsumption          : 0.03
% 1.90/1.33  Abstraction          : 0.01
% 1.90/1.33  MUC search           : 0.00
% 1.90/1.33  Cooper               : 0.00
% 1.90/1.33  Total                : 0.55
% 1.90/1.33  Index Insertion      : 0.00
% 1.90/1.33  Index Deletion       : 0.00
% 1.90/1.33  Index Matching       : 0.00
% 1.90/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
