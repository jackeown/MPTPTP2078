%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:08 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   39 (  39 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   29 (  29 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_1

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_50,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_45,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k1_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

tff(f_56,axiom,(
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

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_63,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_setfam_1)).

tff(c_24,plain,(
    ! [A_33] : ~ v1_xboole_0(k1_zfmisc_1(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_20,plain,(
    ! [A_31] : k1_subset_1(A_31) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [A_32] : m1_subset_1(k1_subset_1(A_32),k1_zfmisc_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_33,plain,(
    ! [A_32] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_32)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_86,plain,(
    ! [A_53,B_54] :
      ( r2_hidden(A_53,B_54)
      | v1_xboole_0(B_54)
      | ~ m1_subset_1(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_58,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(k1_tarski(A_46),B_47)
      | ~ r2_hidden(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_52,plain,(
    ! [A_42,B_43] :
      ( m1_subset_1(A_42,k1_zfmisc_1(B_43))
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_32,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_56,plain,(
    ~ r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_52,c_32])).

tff(c_66,plain,(
    ~ r2_hidden(k1_xboole_0,k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_58,c_56])).

tff(c_89,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_86,c_66])).

tff(c_92,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_89])).

tff(c_94,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_92])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:28:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.13  
% 1.72/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.14  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_1
% 1.72/1.14  
% 1.72/1.14  %Foreground sorts:
% 1.72/1.14  
% 1.72/1.14  
% 1.72/1.14  %Background operators:
% 1.72/1.14  
% 1.72/1.14  
% 1.72/1.14  %Foreground operators:
% 1.72/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.72/1.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.72/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.72/1.14  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.72/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.72/1.14  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.72/1.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.72/1.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.72/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.72/1.14  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.72/1.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.72/1.14  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.72/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.14  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 1.72/1.14  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.72/1.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.72/1.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.72/1.14  
% 1.72/1.14  tff(f_50, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.72/1.14  tff(f_45, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 1.72/1.14  tff(f_47, axiom, (![A]: m1_subset_1(k1_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 1.72/1.14  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 1.72/1.14  tff(f_43, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.72/1.14  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.72/1.14  tff(f_63, negated_conjecture, ~(![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_setfam_1)).
% 1.72/1.14  tff(c_24, plain, (![A_33]: (~v1_xboole_0(k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.72/1.14  tff(c_20, plain, (![A_31]: (k1_subset_1(A_31)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.72/1.14  tff(c_22, plain, (![A_32]: (m1_subset_1(k1_subset_1(A_32), k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.72/1.14  tff(c_33, plain, (![A_32]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_32)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 1.72/1.14  tff(c_86, plain, (![A_53, B_54]: (r2_hidden(A_53, B_54) | v1_xboole_0(B_54) | ~m1_subset_1(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.72/1.14  tff(c_58, plain, (![A_46, B_47]: (r1_tarski(k1_tarski(A_46), B_47) | ~r2_hidden(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.72/1.14  tff(c_52, plain, (![A_42, B_43]: (m1_subset_1(A_42, k1_zfmisc_1(B_43)) | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.72/1.14  tff(c_32, plain, (~m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.72/1.14  tff(c_56, plain, (~r1_tarski(k1_tarski(k1_xboole_0), k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_52, c_32])).
% 1.72/1.14  tff(c_66, plain, (~r2_hidden(k1_xboole_0, k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_58, c_56])).
% 1.72/1.14  tff(c_89, plain, (v1_xboole_0(k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_86, c_66])).
% 1.72/1.14  tff(c_92, plain, (v1_xboole_0(k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_33, c_89])).
% 1.72/1.14  tff(c_94, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_92])).
% 1.72/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.14  
% 1.72/1.14  Inference rules
% 1.72/1.14  ----------------------
% 1.72/1.14  #Ref     : 0
% 1.72/1.14  #Sup     : 12
% 1.72/1.14  #Fact    : 0
% 1.72/1.14  #Define  : 0
% 1.72/1.15  #Split   : 0
% 1.72/1.15  #Chain   : 0
% 1.72/1.15  #Close   : 0
% 1.72/1.15  
% 1.72/1.15  Ordering : KBO
% 1.72/1.15  
% 1.72/1.15  Simplification rules
% 1.72/1.15  ----------------------
% 1.72/1.15  #Subsume      : 0
% 1.72/1.15  #Demod        : 2
% 1.72/1.15  #Tautology    : 8
% 1.72/1.15  #SimpNegUnit  : 1
% 1.72/1.15  #BackRed      : 0
% 1.72/1.15  
% 1.72/1.15  #Partial instantiations: 0
% 1.72/1.15  #Strategies tried      : 1
% 1.72/1.15  
% 1.72/1.15  Timing (in seconds)
% 1.72/1.15  ----------------------
% 1.72/1.15  Preprocessing        : 0.30
% 1.72/1.15  Parsing              : 0.16
% 1.72/1.15  CNF conversion       : 0.02
% 1.72/1.15  Main loop            : 0.10
% 1.72/1.15  Inferencing          : 0.04
% 1.72/1.15  Reduction            : 0.03
% 1.72/1.15  Demodulation         : 0.02
% 1.72/1.15  BG Simplification    : 0.01
% 1.72/1.15  Subsumption          : 0.01
% 1.72/1.15  Abstraction          : 0.01
% 1.72/1.15  MUC search           : 0.00
% 1.72/1.15  Cooper               : 0.00
% 1.72/1.15  Total                : 0.41
% 1.72/1.15  Index Insertion      : 0.00
% 1.72/1.15  Index Deletion       : 0.00
% 1.72/1.15  Index Matching       : 0.00
% 1.72/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
