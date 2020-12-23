%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:37 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   42 (  69 expanded)
%              Number of leaves         :   22 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 ( 101 expanded)
%              Number of equality atoms :   12 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => k1_tops_1(A,k1_struct_0(A)) = k1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tops_1)).

tff(f_32,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_30,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ~ ( B != k1_struct_0(A)
              & ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ~ r2_hidden(C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_pre_topc)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_20,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [A_2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_33,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(k1_tops_1(A_27,B_28),B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_38,plain,(
    ! [A_29] :
      ( r1_tarski(k1_tops_1(A_29,k1_xboole_0),k1_xboole_0)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_6,c_33])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_43,plain,(
    ! [A_30] :
      ( k1_tops_1(A_30,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_30) ) ),
    inference(resolution,[status(thm)],[c_38,c_4])).

tff(c_47,plain,(
    k1_tops_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_43])).

tff(c_23,plain,(
    ! [C_20,B_21,A_22] :
      ( ~ v1_xboole_0(C_20)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(C_20))
      | ~ r2_hidden(A_22,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    ! [A_2,A_22] :
      ( ~ v1_xboole_0(A_2)
      | ~ r2_hidden(A_22,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_23])).

tff(c_27,plain,(
    ! [A_22] : ~ r2_hidden(A_22,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_62,plain,(
    ! [A_31,B_32] :
      ( r2_hidden('#skF_1'(A_31,B_32),B_32)
      | k1_struct_0(A_31) = B_32
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_65,plain,(
    ! [A_31] :
      ( r2_hidden('#skF_1'(A_31,k1_xboole_0),k1_xboole_0)
      | k1_struct_0(A_31) = k1_xboole_0
      | ~ l1_pre_topc(A_31) ) ),
    inference(resolution,[status(thm)],[c_6,c_62])).

tff(c_70,plain,(
    ! [A_35] :
      ( k1_struct_0(A_35) = k1_xboole_0
      | ~ l1_pre_topc(A_35) ) ),
    inference(negUnitSimplification,[status(thm)],[c_27,c_65])).

tff(c_74,plain,(
    k1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_70])).

tff(c_18,plain,(
    k1_tops_1('#skF_2',k1_struct_0('#skF_2')) != k1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_75,plain,(
    k1_tops_1('#skF_2',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_74,c_18])).

tff(c_78,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_75])).

tff(c_79,plain,(
    ! [A_2] : ~ v1_xboole_0(A_2) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_81,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:16:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.18  
% 1.79/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.19  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_1
% 1.79/1.19  
% 1.79/1.19  %Foreground sorts:
% 1.79/1.19  
% 1.79/1.19  
% 1.79/1.19  %Background operators:
% 1.79/1.19  
% 1.79/1.19  
% 1.79/1.19  %Foreground operators:
% 1.79/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.79/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.79/1.19  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.79/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.79/1.19  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 1.79/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.79/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.79/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.19  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 1.79/1.19  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.79/1.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.79/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.79/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.79/1.19  
% 1.79/1.20  tff(f_72, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (k1_tops_1(A, k1_struct_0(A)) = k1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_tops_1)).
% 1.79/1.20  tff(f_32, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 1.79/1.20  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 1.79/1.20  tff(f_30, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.79/1.20  tff(f_45, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 1.79/1.20  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(~(B = k1_struct_0(A)) & (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~r2_hidden(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_pre_topc)).
% 1.79/1.20  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.79/1.20  tff(c_20, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.79/1.20  tff(c_6, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.79/1.20  tff(c_33, plain, (![A_27, B_28]: (r1_tarski(k1_tops_1(A_27, B_28), B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.79/1.20  tff(c_38, plain, (![A_29]: (r1_tarski(k1_tops_1(A_29, k1_xboole_0), k1_xboole_0) | ~l1_pre_topc(A_29))), inference(resolution, [status(thm)], [c_6, c_33])).
% 1.79/1.20  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.79/1.20  tff(c_43, plain, (![A_30]: (k1_tops_1(A_30, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_30))), inference(resolution, [status(thm)], [c_38, c_4])).
% 1.79/1.20  tff(c_47, plain, (k1_tops_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_43])).
% 1.79/1.20  tff(c_23, plain, (![C_20, B_21, A_22]: (~v1_xboole_0(C_20) | ~m1_subset_1(B_21, k1_zfmisc_1(C_20)) | ~r2_hidden(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.79/1.20  tff(c_26, plain, (![A_2, A_22]: (~v1_xboole_0(A_2) | ~r2_hidden(A_22, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_23])).
% 1.79/1.20  tff(c_27, plain, (![A_22]: (~r2_hidden(A_22, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_26])).
% 1.79/1.20  tff(c_62, plain, (![A_31, B_32]: (r2_hidden('#skF_1'(A_31, B_32), B_32) | k1_struct_0(A_31)=B_32 | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.79/1.20  tff(c_65, plain, (![A_31]: (r2_hidden('#skF_1'(A_31, k1_xboole_0), k1_xboole_0) | k1_struct_0(A_31)=k1_xboole_0 | ~l1_pre_topc(A_31))), inference(resolution, [status(thm)], [c_6, c_62])).
% 1.79/1.20  tff(c_70, plain, (![A_35]: (k1_struct_0(A_35)=k1_xboole_0 | ~l1_pre_topc(A_35))), inference(negUnitSimplification, [status(thm)], [c_27, c_65])).
% 1.79/1.20  tff(c_74, plain, (k1_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_70])).
% 1.79/1.20  tff(c_18, plain, (k1_tops_1('#skF_2', k1_struct_0('#skF_2'))!=k1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.79/1.20  tff(c_75, plain, (k1_tops_1('#skF_2', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_74, c_74, c_18])).
% 1.79/1.20  tff(c_78, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_47, c_75])).
% 1.79/1.20  tff(c_79, plain, (![A_2]: (~v1_xboole_0(A_2))), inference(splitRight, [status(thm)], [c_26])).
% 1.79/1.20  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.79/1.20  tff(c_81, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_2])).
% 1.79/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.20  
% 1.79/1.20  Inference rules
% 1.79/1.20  ----------------------
% 1.79/1.20  #Ref     : 0
% 1.79/1.20  #Sup     : 11
% 1.79/1.20  #Fact    : 0
% 1.79/1.20  #Define  : 0
% 1.79/1.20  #Split   : 1
% 1.79/1.20  #Chain   : 0
% 1.79/1.20  #Close   : 0
% 1.79/1.20  
% 1.79/1.20  Ordering : KBO
% 1.79/1.20  
% 1.79/1.20  Simplification rules
% 1.79/1.20  ----------------------
% 1.79/1.20  #Subsume      : 2
% 1.79/1.20  #Demod        : 4
% 1.79/1.20  #Tautology    : 3
% 1.79/1.20  #SimpNegUnit  : 2
% 1.79/1.20  #BackRed      : 2
% 1.79/1.20  
% 1.79/1.20  #Partial instantiations: 0
% 1.79/1.20  #Strategies tried      : 1
% 1.79/1.20  
% 1.79/1.20  Timing (in seconds)
% 1.79/1.20  ----------------------
% 1.79/1.20  Preprocessing        : 0.26
% 1.79/1.20  Parsing              : 0.14
% 1.79/1.20  CNF conversion       : 0.02
% 1.79/1.20  Main loop            : 0.16
% 1.79/1.20  Inferencing          : 0.08
% 1.79/1.20  Reduction            : 0.03
% 1.79/1.20  Demodulation         : 0.02
% 1.79/1.20  BG Simplification    : 0.01
% 1.79/1.20  Subsumption          : 0.02
% 1.79/1.20  Abstraction          : 0.00
% 1.79/1.20  MUC search           : 0.00
% 1.79/1.20  Cooper               : 0.00
% 1.79/1.20  Total                : 0.45
% 1.79/1.20  Index Insertion      : 0.00
% 1.79/1.20  Index Deletion       : 0.00
% 1.79/1.20  Index Matching       : 0.00
% 1.79/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
