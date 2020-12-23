%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:08 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   35 (  35 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   30 (  30 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_48,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_setfam_1)).

tff(c_105,plain,(
    ! [A_34,B_35] :
      ( r2_hidden('#skF_1'(A_34,B_35),A_34)
      | r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_66,plain,(
    ! [A_23,B_24] : ~ r2_hidden(A_23,k2_zfmisc_1(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_72,plain,(
    ! [A_12] : ~ r2_hidden(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_66])).

tff(c_110,plain,(
    ! [B_35] : r1_tarski(k1_xboole_0,B_35) ),
    inference(resolution,[status(thm)],[c_105,c_72])).

tff(c_22,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_130,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(k1_zfmisc_1(A_42),k1_zfmisc_1(B_43))
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_133,plain,(
    ! [B_43] :
      ( r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(B_43))
      | ~ r1_tarski(k1_xboole_0,B_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_130])).

tff(c_138,plain,(
    ! [B_43] : r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(B_43)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_133])).

tff(c_83,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(A_28,k1_zfmisc_1(B_29))
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_30,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_90,plain,(
    ~ r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_83,c_30])).

tff(c_141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_90])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:12:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.21  
% 1.75/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.21  %$ r2_hidden > r1_tarski > m1_subset_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.75/1.21  
% 1.75/1.21  %Foreground sorts:
% 1.75/1.21  
% 1.75/1.21  
% 1.75/1.21  %Background operators:
% 1.75/1.21  
% 1.75/1.21  
% 1.75/1.21  %Foreground operators:
% 1.75/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.75/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.75/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.75/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.75/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.75/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.75/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.75/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.75/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.75/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.75/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.75/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.75/1.21  
% 1.93/1.22  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.93/1.22  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.93/1.22  tff(f_47, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.93/1.22  tff(f_48, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 1.93/1.22  tff(f_52, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 1.93/1.22  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.93/1.22  tff(f_59, negated_conjecture, ~(![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_setfam_1)).
% 1.93/1.22  tff(c_105, plain, (![A_34, B_35]: (r2_hidden('#skF_1'(A_34, B_35), A_34) | r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.93/1.22  tff(c_16, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.93/1.22  tff(c_66, plain, (![A_23, B_24]: (~r2_hidden(A_23, k2_zfmisc_1(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.93/1.22  tff(c_72, plain, (![A_12]: (~r2_hidden(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_66])).
% 1.93/1.22  tff(c_110, plain, (![B_35]: (r1_tarski(k1_xboole_0, B_35))), inference(resolution, [status(thm)], [c_105, c_72])).
% 1.93/1.22  tff(c_22, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.93/1.22  tff(c_130, plain, (![A_42, B_43]: (r1_tarski(k1_zfmisc_1(A_42), k1_zfmisc_1(B_43)) | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.93/1.22  tff(c_133, plain, (![B_43]: (r1_tarski(k1_tarski(k1_xboole_0), k1_zfmisc_1(B_43)) | ~r1_tarski(k1_xboole_0, B_43))), inference(superposition, [status(thm), theory('equality')], [c_22, c_130])).
% 1.93/1.22  tff(c_138, plain, (![B_43]: (r1_tarski(k1_tarski(k1_xboole_0), k1_zfmisc_1(B_43)))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_133])).
% 1.93/1.22  tff(c_83, plain, (![A_28, B_29]: (m1_subset_1(A_28, k1_zfmisc_1(B_29)) | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.93/1.22  tff(c_30, plain, (~m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.93/1.22  tff(c_90, plain, (~r1_tarski(k1_tarski(k1_xboole_0), k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_83, c_30])).
% 1.93/1.22  tff(c_141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_138, c_90])).
% 1.93/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.22  
% 1.93/1.22  Inference rules
% 1.93/1.22  ----------------------
% 1.93/1.22  #Ref     : 0
% 1.93/1.22  #Sup     : 25
% 1.93/1.22  #Fact    : 0
% 1.93/1.22  #Define  : 0
% 1.93/1.22  #Split   : 0
% 1.93/1.22  #Chain   : 0
% 1.93/1.22  #Close   : 0
% 1.93/1.22  
% 1.93/1.22  Ordering : KBO
% 1.93/1.22  
% 1.93/1.22  Simplification rules
% 1.93/1.22  ----------------------
% 1.93/1.22  #Subsume      : 1
% 1.93/1.22  #Demod        : 2
% 1.93/1.22  #Tautology    : 16
% 1.93/1.22  #SimpNegUnit  : 0
% 1.93/1.22  #BackRed      : 1
% 1.93/1.22  
% 1.93/1.22  #Partial instantiations: 0
% 1.93/1.22  #Strategies tried      : 1
% 1.93/1.22  
% 1.93/1.22  Timing (in seconds)
% 1.93/1.22  ----------------------
% 1.93/1.23  Preprocessing        : 0.30
% 1.93/1.23  Parsing              : 0.16
% 1.93/1.23  CNF conversion       : 0.02
% 1.93/1.23  Main loop            : 0.12
% 1.93/1.23  Inferencing          : 0.04
% 1.93/1.23  Reduction            : 0.04
% 1.93/1.23  Demodulation         : 0.03
% 1.93/1.23  BG Simplification    : 0.01
% 1.93/1.23  Subsumption          : 0.02
% 1.93/1.23  Abstraction          : 0.01
% 1.93/1.23  MUC search           : 0.00
% 1.93/1.23  Cooper               : 0.00
% 1.93/1.23  Total                : 0.44
% 1.93/1.23  Index Insertion      : 0.00
% 1.93/1.23  Index Deletion       : 0.00
% 1.93/1.23  Index Matching       : 0.00
% 1.93/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
