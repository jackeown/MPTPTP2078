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
% DateTime   : Thu Dec  3 10:20:36 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   38 (  72 expanded)
%              Number of leaves         :   19 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   41 ( 101 expanded)
%              Number of equality atoms :   10 (  28 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_53,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => k1_tops_1(A,k1_struct_0(A)) = k1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tops_1)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k1_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_struct_0)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_14,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_17,plain,(
    ! [A_10] :
      ( k1_struct_0(A_10) = k1_xboole_0
      | ~ l1_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    ! [A_11] :
      ( k1_struct_0(A_11) = k1_xboole_0
      | ~ l1_pre_topc(A_11) ) ),
    inference(resolution,[status(thm)],[c_8,c_17])).

tff(c_26,plain,(
    k1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_22])).

tff(c_12,plain,(
    k1_tops_1('#skF_1',k1_struct_0('#skF_1')) != k1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_27,plain,(
    k1_tops_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_12])).

tff(c_32,plain,(
    ! [A_12] :
      ( m1_subset_1(k1_struct_0(A_12),k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_35,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_32])).

tff(c_36,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_35])).

tff(c_39,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_36])).

tff(c_43,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_39])).

tff(c_44,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_35])).

tff(c_51,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(k1_tops_1(A_13,B_14),B_14)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_53,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k1_xboole_0),k1_xboole_0)
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_51])).

tff(c_58,plain,(
    r1_tarski(k1_tops_1('#skF_1',k1_xboole_0),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_53])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_62,plain,(
    k1_tops_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_2])).

tff(c_66,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27,c_62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:38:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.10  
% 1.62/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.10  %$ r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1
% 1.62/1.10  
% 1.62/1.10  %Foreground sorts:
% 1.62/1.10  
% 1.62/1.10  
% 1.62/1.10  %Background operators:
% 1.62/1.10  
% 1.62/1.10  
% 1.62/1.10  %Foreground operators:
% 1.62/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.62/1.10  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.62/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.62/1.10  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 1.62/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.62/1.10  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.62/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.10  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 1.62/1.10  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.62/1.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.62/1.10  
% 1.62/1.11  tff(f_53, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (k1_tops_1(A, k1_struct_0(A)) = k1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_tops_1)).
% 1.62/1.11  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 1.62/1.11  tff(f_33, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_struct_0)).
% 1.62/1.11  tff(f_37, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k1_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_struct_0)).
% 1.62/1.11  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 1.62/1.11  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.62/1.11  tff(c_14, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.62/1.11  tff(c_8, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.62/1.11  tff(c_17, plain, (![A_10]: (k1_struct_0(A_10)=k1_xboole_0 | ~l1_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.62/1.11  tff(c_22, plain, (![A_11]: (k1_struct_0(A_11)=k1_xboole_0 | ~l1_pre_topc(A_11))), inference(resolution, [status(thm)], [c_8, c_17])).
% 1.62/1.11  tff(c_26, plain, (k1_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_22])).
% 1.62/1.11  tff(c_12, plain, (k1_tops_1('#skF_1', k1_struct_0('#skF_1'))!=k1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.62/1.11  tff(c_27, plain, (k1_tops_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_12])).
% 1.62/1.11  tff(c_32, plain, (![A_12]: (m1_subset_1(k1_struct_0(A_12), k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.62/1.11  tff(c_35, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_26, c_32])).
% 1.62/1.11  tff(c_36, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_35])).
% 1.62/1.11  tff(c_39, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_36])).
% 1.62/1.11  tff(c_43, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_39])).
% 1.62/1.11  tff(c_44, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_35])).
% 1.62/1.11  tff(c_51, plain, (![A_13, B_14]: (r1_tarski(k1_tops_1(A_13, B_14), B_14) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.62/1.11  tff(c_53, plain, (r1_tarski(k1_tops_1('#skF_1', k1_xboole_0), k1_xboole_0) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_51])).
% 1.62/1.11  tff(c_58, plain, (r1_tarski(k1_tops_1('#skF_1', k1_xboole_0), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_53])).
% 1.62/1.11  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.62/1.11  tff(c_62, plain, (k1_tops_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_2])).
% 1.62/1.11  tff(c_66, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27, c_62])).
% 1.62/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.11  
% 1.62/1.11  Inference rules
% 1.62/1.11  ----------------------
% 1.62/1.11  #Ref     : 0
% 1.62/1.11  #Sup     : 10
% 1.62/1.11  #Fact    : 0
% 1.62/1.11  #Define  : 0
% 1.62/1.11  #Split   : 1
% 1.62/1.11  #Chain   : 0
% 1.62/1.11  #Close   : 0
% 1.62/1.11  
% 1.62/1.11  Ordering : KBO
% 1.62/1.11  
% 1.62/1.11  Simplification rules
% 1.62/1.11  ----------------------
% 1.62/1.11  #Subsume      : 0
% 1.62/1.11  #Demod        : 5
% 1.62/1.11  #Tautology    : 3
% 1.62/1.11  #SimpNegUnit  : 1
% 1.62/1.11  #BackRed      : 1
% 1.62/1.11  
% 1.62/1.11  #Partial instantiations: 0
% 1.62/1.11  #Strategies tried      : 1
% 1.62/1.11  
% 1.62/1.11  Timing (in seconds)
% 1.62/1.11  ----------------------
% 1.62/1.11  Preprocessing        : 0.25
% 1.62/1.11  Parsing              : 0.14
% 1.62/1.11  CNF conversion       : 0.02
% 1.62/1.11  Main loop            : 0.10
% 1.62/1.11  Inferencing          : 0.05
% 1.62/1.11  Reduction            : 0.03
% 1.62/1.11  Demodulation         : 0.02
% 1.62/1.11  BG Simplification    : 0.01
% 1.62/1.11  Subsumption          : 0.01
% 1.62/1.11  Abstraction          : 0.00
% 1.62/1.11  MUC search           : 0.00
% 1.62/1.11  Cooper               : 0.00
% 1.62/1.11  Total                : 0.38
% 1.62/1.11  Index Insertion      : 0.00
% 1.62/1.11  Index Deletion       : 0.00
% 1.62/1.11  Index Matching       : 0.00
% 1.62/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
