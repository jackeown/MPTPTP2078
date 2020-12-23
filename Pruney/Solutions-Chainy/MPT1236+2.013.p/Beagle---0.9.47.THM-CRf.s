%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:37 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   40 (  50 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   48 (  65 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => k1_tops_1(A,k1_struct_0(A)) = k1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tops_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => v1_xboole_0(k1_tops_1(A,k1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_tops_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_32,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ~ ( B != k1_struct_0(A)
              & ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ~ r2_hidden(C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_pre_topc)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_20,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_28,plain,(
    ! [A_18] :
      ( v1_xboole_0(k1_tops_1(A_18,k1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_33,plain,(
    ! [A_19] :
      ( k1_tops_1(A_19,k1_struct_0(A_19)) = k1_xboole_0
      | ~ l1_pre_topc(A_19) ) ),
    inference(resolution,[status(thm)],[c_28,c_4])).

tff(c_18,plain,(
    k1_tops_1('#skF_2',k1_struct_0('#skF_2')) != k1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_42,plain,
    ( k1_struct_0('#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_18])).

tff(c_49,plain,(
    k1_struct_0('#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_42])).

tff(c_6,plain,(
    ! [A_2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_51,plain,(
    ! [C_20,B_21,A_22] :
      ( ~ v1_xboole_0(C_20)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(C_20))
      | ~ r2_hidden(A_22,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_54,plain,(
    ! [A_2,A_22] :
      ( ~ v1_xboole_0(A_2)
      | ~ r2_hidden(A_22,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_51])).

tff(c_59,plain,(
    ! [A_22] : ~ r2_hidden(A_22,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_61,plain,(
    ! [A_27,B_28] :
      ( r2_hidden('#skF_1'(A_27,B_28),B_28)
      | k1_struct_0(A_27) = B_28
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_64,plain,(
    ! [A_27] :
      ( r2_hidden('#skF_1'(A_27,k1_xboole_0),k1_xboole_0)
      | k1_struct_0(A_27) = k1_xboole_0
      | ~ l1_pre_topc(A_27) ) ),
    inference(resolution,[status(thm)],[c_6,c_61])).

tff(c_68,plain,(
    ! [A_29] :
      ( k1_struct_0(A_29) = k1_xboole_0
      | ~ l1_pre_topc(A_29) ) ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_64])).

tff(c_71,plain,(
    k1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_68])).

tff(c_75,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_71])).

tff(c_76,plain,(
    ! [A_2] : ~ v1_xboole_0(A_2) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_84,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:12:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.12  
% 1.64/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.12  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_1
% 1.64/1.12  
% 1.64/1.12  %Foreground sorts:
% 1.64/1.12  
% 1.64/1.12  
% 1.64/1.12  %Background operators:
% 1.64/1.12  
% 1.64/1.12  
% 1.64/1.12  %Foreground operators:
% 1.64/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.64/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.64/1.12  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.64/1.12  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 1.64/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.64/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.12  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 1.64/1.12  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.64/1.12  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.64/1.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.64/1.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.64/1.12  
% 1.64/1.13  tff(f_69, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (k1_tops_1(A, k1_struct_0(A)) = k1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_tops_1)).
% 1.64/1.13  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => v1_xboole_0(k1_tops_1(A, k1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_tops_1)).
% 1.64/1.13  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.64/1.13  tff(f_32, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 1.64/1.13  tff(f_45, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 1.64/1.13  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(~(B = k1_struct_0(A)) & (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~r2_hidden(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_pre_topc)).
% 1.64/1.13  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.64/1.13  tff(c_20, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.64/1.13  tff(c_28, plain, (![A_18]: (v1_xboole_0(k1_tops_1(A_18, k1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.64/1.13  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.64/1.13  tff(c_33, plain, (![A_19]: (k1_tops_1(A_19, k1_struct_0(A_19))=k1_xboole_0 | ~l1_pre_topc(A_19))), inference(resolution, [status(thm)], [c_28, c_4])).
% 1.64/1.13  tff(c_18, plain, (k1_tops_1('#skF_2', k1_struct_0('#skF_2'))!=k1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.64/1.13  tff(c_42, plain, (k1_struct_0('#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_33, c_18])).
% 1.64/1.13  tff(c_49, plain, (k1_struct_0('#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_42])).
% 1.64/1.13  tff(c_6, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.64/1.13  tff(c_51, plain, (![C_20, B_21, A_22]: (~v1_xboole_0(C_20) | ~m1_subset_1(B_21, k1_zfmisc_1(C_20)) | ~r2_hidden(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.64/1.13  tff(c_54, plain, (![A_2, A_22]: (~v1_xboole_0(A_2) | ~r2_hidden(A_22, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_51])).
% 1.64/1.13  tff(c_59, plain, (![A_22]: (~r2_hidden(A_22, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_54])).
% 1.64/1.13  tff(c_61, plain, (![A_27, B_28]: (r2_hidden('#skF_1'(A_27, B_28), B_28) | k1_struct_0(A_27)=B_28 | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.64/1.13  tff(c_64, plain, (![A_27]: (r2_hidden('#skF_1'(A_27, k1_xboole_0), k1_xboole_0) | k1_struct_0(A_27)=k1_xboole_0 | ~l1_pre_topc(A_27))), inference(resolution, [status(thm)], [c_6, c_61])).
% 1.64/1.13  tff(c_68, plain, (![A_29]: (k1_struct_0(A_29)=k1_xboole_0 | ~l1_pre_topc(A_29))), inference(negUnitSimplification, [status(thm)], [c_59, c_64])).
% 1.64/1.13  tff(c_71, plain, (k1_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_68])).
% 1.64/1.13  tff(c_75, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_71])).
% 1.64/1.13  tff(c_76, plain, (![A_2]: (~v1_xboole_0(A_2))), inference(splitRight, [status(thm)], [c_54])).
% 1.64/1.13  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.64/1.13  tff(c_84, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_2])).
% 1.64/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.13  
% 1.64/1.13  Inference rules
% 1.64/1.13  ----------------------
% 1.64/1.13  #Ref     : 0
% 1.64/1.13  #Sup     : 11
% 1.64/1.13  #Fact    : 0
% 1.64/1.13  #Define  : 0
% 1.64/1.13  #Split   : 1
% 1.64/1.13  #Chain   : 0
% 1.64/1.13  #Close   : 0
% 1.64/1.13  
% 1.64/1.13  Ordering : KBO
% 1.64/1.13  
% 1.64/1.13  Simplification rules
% 1.64/1.13  ----------------------
% 1.64/1.13  #Subsume      : 3
% 1.64/1.13  #Demod        : 2
% 1.64/1.13  #Tautology    : 4
% 1.64/1.13  #SimpNegUnit  : 4
% 1.64/1.13  #BackRed      : 2
% 1.64/1.13  
% 1.64/1.13  #Partial instantiations: 0
% 1.64/1.13  #Strategies tried      : 1
% 1.64/1.13  
% 1.64/1.13  Timing (in seconds)
% 1.64/1.13  ----------------------
% 1.64/1.13  Preprocessing        : 0.26
% 1.64/1.13  Parsing              : 0.15
% 1.64/1.13  CNF conversion       : 0.02
% 1.64/1.13  Main loop            : 0.11
% 1.64/1.13  Inferencing          : 0.05
% 1.64/1.13  Reduction            : 0.03
% 1.64/1.13  Demodulation         : 0.02
% 1.64/1.13  BG Simplification    : 0.01
% 1.64/1.13  Subsumption          : 0.02
% 1.64/1.13  Abstraction          : 0.00
% 1.64/1.13  MUC search           : 0.00
% 1.64/1.13  Cooper               : 0.00
% 1.64/1.13  Total                : 0.40
% 1.64/1.13  Index Insertion      : 0.00
% 1.64/1.13  Index Deletion       : 0.00
% 1.64/1.13  Index Matching       : 0.00
% 1.64/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
