%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:36 EST 2020

% Result     : Theorem 1.54s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   34 (  45 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :    5
%              Number of atoms          :   34 (  53 expanded)
%              Number of equality atoms :   11 (  18 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_57,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => k1_tops_1(A,k1_struct_0(A)) = k1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tops_1)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_31,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_16,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [A_14] :
      ( k1_struct_0(A_14) = k1_xboole_0
      | ~ l1_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_25,plain,(
    ! [A_15] :
      ( k1_struct_0(A_15) = k1_xboole_0
      | ~ l1_pre_topc(A_15) ) ),
    inference(resolution,[status(thm)],[c_10,c_20])).

tff(c_29,plain,(
    k1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_25])).

tff(c_14,plain,(
    k1_tops_1('#skF_1',k1_struct_0('#skF_1')) != k1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    k1_tops_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_29,c_14])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(k1_tops_1(A_21,B_22),B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_45,plain,(
    ! [A_23] :
      ( r1_tarski(k1_tops_1(A_23,k1_xboole_0),k1_xboole_0)
      | ~ l1_pre_topc(A_23) ) ),
    inference(resolution,[status(thm)],[c_4,c_40])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_50,plain,(
    ! [A_24] :
      ( k1_tops_1(A_24,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_24) ) ),
    inference(resolution,[status(thm)],[c_45,c_2])).

tff(c_53,plain,(
    k1_tops_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_50])).

tff(c_57,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n011.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 11:49:12 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.54/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.08  
% 1.65/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.09  %$ r2_hidden > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1
% 1.65/1.09  
% 1.65/1.09  %Foreground sorts:
% 1.65/1.09  
% 1.65/1.09  
% 1.65/1.09  %Background operators:
% 1.65/1.09  
% 1.65/1.09  
% 1.65/1.09  %Foreground operators:
% 1.65/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.65/1.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.65/1.09  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.65/1.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.65/1.09  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 1.65/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.65/1.09  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.65/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.09  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 1.65/1.09  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.65/1.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.65/1.09  
% 1.65/1.10  tff(f_57, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (k1_tops_1(A, k1_struct_0(A)) = k1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_tops_1)).
% 1.65/1.10  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 1.65/1.10  tff(f_41, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_struct_0)).
% 1.65/1.10  tff(f_31, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 1.65/1.10  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 1.65/1.10  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.65/1.10  tff(c_16, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.65/1.10  tff(c_10, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.65/1.10  tff(c_20, plain, (![A_14]: (k1_struct_0(A_14)=k1_xboole_0 | ~l1_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.65/1.10  tff(c_25, plain, (![A_15]: (k1_struct_0(A_15)=k1_xboole_0 | ~l1_pre_topc(A_15))), inference(resolution, [status(thm)], [c_10, c_20])).
% 1.65/1.10  tff(c_29, plain, (k1_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_25])).
% 1.65/1.10  tff(c_14, plain, (k1_tops_1('#skF_1', k1_struct_0('#skF_1'))!=k1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.65/1.10  tff(c_30, plain, (k1_tops_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_29, c_29, c_14])).
% 1.65/1.10  tff(c_4, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.65/1.10  tff(c_40, plain, (![A_21, B_22]: (r1_tarski(k1_tops_1(A_21, B_22), B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.65/1.10  tff(c_45, plain, (![A_23]: (r1_tarski(k1_tops_1(A_23, k1_xboole_0), k1_xboole_0) | ~l1_pre_topc(A_23))), inference(resolution, [status(thm)], [c_4, c_40])).
% 1.65/1.10  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.65/1.10  tff(c_50, plain, (![A_24]: (k1_tops_1(A_24, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_24))), inference(resolution, [status(thm)], [c_45, c_2])).
% 1.65/1.10  tff(c_53, plain, (k1_tops_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_50])).
% 1.65/1.10  tff(c_57, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_53])).
% 1.65/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.10  
% 1.65/1.10  Inference rules
% 1.65/1.10  ----------------------
% 1.65/1.10  #Ref     : 0
% 1.65/1.10  #Sup     : 8
% 1.65/1.10  #Fact    : 0
% 1.65/1.10  #Define  : 0
% 1.65/1.10  #Split   : 0
% 1.65/1.10  #Chain   : 0
% 1.65/1.10  #Close   : 0
% 1.65/1.10  
% 1.65/1.10  Ordering : KBO
% 1.65/1.10  
% 1.65/1.10  Simplification rules
% 1.65/1.10  ----------------------
% 1.65/1.10  #Subsume      : 0
% 1.65/1.10  #Demod        : 2
% 1.65/1.10  #Tautology    : 2
% 1.65/1.10  #SimpNegUnit  : 1
% 1.65/1.10  #BackRed      : 1
% 1.65/1.10  
% 1.65/1.10  #Partial instantiations: 0
% 1.65/1.10  #Strategies tried      : 1
% 1.65/1.10  
% 1.65/1.10  Timing (in seconds)
% 1.65/1.10  ----------------------
% 1.65/1.10  Preprocessing        : 0.25
% 1.65/1.10  Parsing              : 0.14
% 1.65/1.10  CNF conversion       : 0.01
% 1.65/1.10  Main loop            : 0.10
% 1.65/1.10  Inferencing          : 0.05
% 1.65/1.10  Reduction            : 0.03
% 1.65/1.10  Demodulation         : 0.02
% 1.65/1.10  BG Simplification    : 0.01
% 1.65/1.10  Subsumption          : 0.01
% 1.65/1.10  Abstraction          : 0.00
% 1.65/1.10  MUC search           : 0.00
% 1.65/1.10  Cooper               : 0.00
% 1.65/1.10  Total                : 0.38
% 1.65/1.10  Index Insertion      : 0.00
% 1.65/1.10  Index Deletion       : 0.00
% 1.65/1.10  Index Matching       : 0.00
% 1.65/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
