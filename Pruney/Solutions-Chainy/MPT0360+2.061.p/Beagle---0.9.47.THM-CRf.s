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
% DateTime   : Thu Dec  3 09:56:26 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   36 (  39 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 (  50 expanded)
%              Number of equality atoms :    8 (  11 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ~ ( r1_tarski(C,A)
          & r1_tarski(C,B)
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_12,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_30,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = k3_subset_1(A_16,B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_34,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_30])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_xboole_0(k4_xboole_0(A_7,B_8),B_8) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_42,plain,(
    ! [A_18,B_19,C_20] :
      ( ~ r1_xboole_0(A_18,B_19)
      | ~ r1_tarski(C_20,B_19)
      | ~ r1_tarski(C_20,A_18)
      | v1_xboole_0(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_49,plain,(
    ! [C_21,B_22,A_23] :
      ( ~ r1_tarski(C_21,B_22)
      | ~ r1_tarski(C_21,k4_xboole_0(A_23,B_22))
      | v1_xboole_0(C_21) ) ),
    inference(resolution,[status(thm)],[c_8,c_42])).

tff(c_53,plain,(
    ! [C_24] :
      ( ~ r1_tarski(C_24,'#skF_3')
      | ~ r1_tarski(C_24,k3_subset_1('#skF_1','#skF_3'))
      | v1_xboole_0(C_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_49])).

tff(c_56,plain,
    ( ~ r1_tarski('#skF_2','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_53])).

tff(c_59,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_56])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_62,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_59,c_2])).

tff(c_66,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:22:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.11  
% 1.72/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.11  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.72/1.11  
% 1.72/1.11  %Foreground sorts:
% 1.72/1.11  
% 1.72/1.11  
% 1.72/1.11  %Background operators:
% 1.72/1.11  
% 1.72/1.11  
% 1.72/1.11  %Foreground operators:
% 1.72/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.72/1.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.72/1.11  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.72/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.72/1.11  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.72/1.11  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.72/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.72/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.72/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.72/1.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.72/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.72/1.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.72/1.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.72/1.11  
% 1.72/1.12  tff(f_56, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_subset_1)).
% 1.72/1.12  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 1.72/1.12  tff(f_43, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.72/1.12  tff(f_41, axiom, (![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_xboole_1)).
% 1.72/1.12  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.72/1.12  tff(c_12, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.72/1.12  tff(c_16, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.72/1.12  tff(c_14, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.72/1.12  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.72/1.12  tff(c_30, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=k3_subset_1(A_16, B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.72/1.12  tff(c_34, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_18, c_30])).
% 1.72/1.12  tff(c_8, plain, (![A_7, B_8]: (r1_xboole_0(k4_xboole_0(A_7, B_8), B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.72/1.12  tff(c_42, plain, (![A_18, B_19, C_20]: (~r1_xboole_0(A_18, B_19) | ~r1_tarski(C_20, B_19) | ~r1_tarski(C_20, A_18) | v1_xboole_0(C_20))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.72/1.12  tff(c_49, plain, (![C_21, B_22, A_23]: (~r1_tarski(C_21, B_22) | ~r1_tarski(C_21, k4_xboole_0(A_23, B_22)) | v1_xboole_0(C_21))), inference(resolution, [status(thm)], [c_8, c_42])).
% 1.72/1.12  tff(c_53, plain, (![C_24]: (~r1_tarski(C_24, '#skF_3') | ~r1_tarski(C_24, k3_subset_1('#skF_1', '#skF_3')) | v1_xboole_0(C_24))), inference(superposition, [status(thm), theory('equality')], [c_34, c_49])).
% 1.72/1.12  tff(c_56, plain, (~r1_tarski('#skF_2', '#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_14, c_53])).
% 1.72/1.12  tff(c_59, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_56])).
% 1.72/1.12  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.72/1.12  tff(c_62, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_59, c_2])).
% 1.72/1.12  tff(c_66, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_62])).
% 1.72/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.12  
% 1.72/1.12  Inference rules
% 1.72/1.12  ----------------------
% 1.72/1.12  #Ref     : 0
% 1.72/1.12  #Sup     : 11
% 1.72/1.12  #Fact    : 0
% 1.72/1.12  #Define  : 0
% 1.72/1.12  #Split   : 0
% 1.72/1.12  #Chain   : 0
% 1.72/1.12  #Close   : 0
% 1.72/1.12  
% 1.72/1.12  Ordering : KBO
% 1.72/1.12  
% 1.72/1.12  Simplification rules
% 1.72/1.12  ----------------------
% 1.72/1.12  #Subsume      : 0
% 1.72/1.12  #Demod        : 1
% 1.72/1.12  #Tautology    : 4
% 1.72/1.12  #SimpNegUnit  : 1
% 1.72/1.12  #BackRed      : 0
% 1.72/1.12  
% 1.72/1.12  #Partial instantiations: 0
% 1.72/1.12  #Strategies tried      : 1
% 1.72/1.12  
% 1.72/1.12  Timing (in seconds)
% 1.72/1.12  ----------------------
% 1.72/1.12  Preprocessing        : 0.28
% 1.72/1.12  Parsing              : 0.15
% 1.72/1.12  CNF conversion       : 0.02
% 1.72/1.12  Main loop            : 0.09
% 1.72/1.12  Inferencing          : 0.04
% 1.72/1.12  Reduction            : 0.03
% 1.72/1.12  Demodulation         : 0.02
% 1.72/1.12  BG Simplification    : 0.01
% 1.72/1.12  Subsumption          : 0.01
% 1.72/1.12  Abstraction          : 0.00
% 1.72/1.12  MUC search           : 0.00
% 1.72/1.12  Cooper               : 0.00
% 1.72/1.12  Total                : 0.39
% 1.72/1.12  Index Insertion      : 0.00
% 1.72/1.12  Index Deletion       : 0.00
% 1.72/1.12  Index Matching       : 0.00
% 1.72/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
