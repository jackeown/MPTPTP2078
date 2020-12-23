%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:37 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   38 (  57 expanded)
%              Number of leaves         :   21 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   47 (  83 expanded)
%              Number of equality atoms :   13 (  22 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => k1_tops_1(A,k1_struct_0(A)) = k1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tops_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_31,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ~ ( B != k1_struct_0(A)
              & ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ~ r2_hidden(C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_pre_topc)).

tff(f_44,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_20,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_36,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(k1_tops_1(A_28,B_29),B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_46,plain,(
    ! [A_32] :
      ( r1_tarski(k1_tops_1(A_32,k1_xboole_0),k1_xboole_0)
      | ~ l1_pre_topc(A_32) ) ),
    inference(resolution,[status(thm)],[c_6,c_36])).

tff(c_4,plain,(
    ! [A_2] :
      ( k1_xboole_0 = A_2
      | ~ r1_tarski(A_2,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_51,plain,(
    ! [A_33] :
      ( k1_tops_1(A_33,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_33) ) ),
    inference(resolution,[status(thm)],[c_46,c_4])).

tff(c_55,plain,(
    k1_tops_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_51])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_41,plain,(
    ! [A_30,B_31] :
      ( r2_hidden('#skF_1'(A_30,B_31),B_31)
      | k1_struct_0(A_30) = B_31
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_65,plain,(
    ! [A_34] :
      ( r2_hidden('#skF_1'(A_34,k1_xboole_0),k1_xboole_0)
      | k1_struct_0(A_34) = k1_xboole_0
      | ~ l1_pre_topc(A_34) ) ),
    inference(resolution,[status(thm)],[c_6,c_41])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( ~ r1_tarski(B_8,A_7)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_70,plain,(
    ! [A_34] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_1'(A_34,k1_xboole_0))
      | k1_struct_0(A_34) = k1_xboole_0
      | ~ l1_pre_topc(A_34) ) ),
    inference(resolution,[status(thm)],[c_65,c_10])).

tff(c_75,plain,(
    ! [A_35] :
      ( k1_struct_0(A_35) = k1_xboole_0
      | ~ l1_pre_topc(A_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_70])).

tff(c_79,plain,(
    k1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_75])).

tff(c_18,plain,(
    k1_tops_1('#skF_2',k1_struct_0('#skF_2')) != k1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_81,plain,(
    k1_tops_1('#skF_2',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_79,c_18])).

tff(c_84,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_81])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:31:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.11  
% 1.64/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.11  %$ r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_1
% 1.64/1.11  
% 1.64/1.11  %Foreground sorts:
% 1.64/1.11  
% 1.64/1.11  
% 1.64/1.11  %Background operators:
% 1.64/1.11  
% 1.64/1.11  
% 1.64/1.11  %Foreground operators:
% 1.64/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.64/1.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.64/1.11  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.64/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.11  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 1.64/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.64/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.11  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 1.64/1.11  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.64/1.11  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.64/1.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.64/1.11  
% 1.64/1.12  tff(f_71, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (k1_tops_1(A, k1_struct_0(A)) = k1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_tops_1)).
% 1.64/1.12  tff(f_33, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 1.64/1.12  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 1.64/1.12  tff(f_31, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.64/1.12  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.64/1.12  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(~(B = k1_struct_0(A)) & (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~r2_hidden(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_pre_topc)).
% 1.64/1.12  tff(f_44, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.64/1.12  tff(c_20, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.64/1.12  tff(c_6, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.64/1.12  tff(c_36, plain, (![A_28, B_29]: (r1_tarski(k1_tops_1(A_28, B_29), B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.64/1.12  tff(c_46, plain, (![A_32]: (r1_tarski(k1_tops_1(A_32, k1_xboole_0), k1_xboole_0) | ~l1_pre_topc(A_32))), inference(resolution, [status(thm)], [c_6, c_36])).
% 1.64/1.12  tff(c_4, plain, (![A_2]: (k1_xboole_0=A_2 | ~r1_tarski(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.64/1.12  tff(c_51, plain, (![A_33]: (k1_tops_1(A_33, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_33))), inference(resolution, [status(thm)], [c_46, c_4])).
% 1.64/1.12  tff(c_55, plain, (k1_tops_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_51])).
% 1.64/1.12  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.64/1.12  tff(c_41, plain, (![A_30, B_31]: (r2_hidden('#skF_1'(A_30, B_31), B_31) | k1_struct_0(A_30)=B_31 | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.64/1.12  tff(c_65, plain, (![A_34]: (r2_hidden('#skF_1'(A_34, k1_xboole_0), k1_xboole_0) | k1_struct_0(A_34)=k1_xboole_0 | ~l1_pre_topc(A_34))), inference(resolution, [status(thm)], [c_6, c_41])).
% 1.64/1.12  tff(c_10, plain, (![B_8, A_7]: (~r1_tarski(B_8, A_7) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.64/1.12  tff(c_70, plain, (![A_34]: (~r1_tarski(k1_xboole_0, '#skF_1'(A_34, k1_xboole_0)) | k1_struct_0(A_34)=k1_xboole_0 | ~l1_pre_topc(A_34))), inference(resolution, [status(thm)], [c_65, c_10])).
% 1.64/1.12  tff(c_75, plain, (![A_35]: (k1_struct_0(A_35)=k1_xboole_0 | ~l1_pre_topc(A_35))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_70])).
% 1.64/1.12  tff(c_79, plain, (k1_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_75])).
% 1.64/1.12  tff(c_18, plain, (k1_tops_1('#skF_2', k1_struct_0('#skF_2'))!=k1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.64/1.12  tff(c_81, plain, (k1_tops_1('#skF_2', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_79, c_79, c_18])).
% 1.64/1.12  tff(c_84, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_81])).
% 1.64/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.12  
% 1.64/1.12  Inference rules
% 1.64/1.12  ----------------------
% 1.64/1.12  #Ref     : 0
% 1.64/1.12  #Sup     : 12
% 1.64/1.12  #Fact    : 0
% 1.64/1.12  #Define  : 0
% 1.64/1.12  #Split   : 0
% 1.64/1.12  #Chain   : 0
% 1.64/1.12  #Close   : 0
% 1.64/1.12  
% 1.64/1.12  Ordering : KBO
% 1.64/1.12  
% 1.64/1.12  Simplification rules
% 1.64/1.12  ----------------------
% 1.64/1.12  #Subsume      : 1
% 1.64/1.12  #Demod        : 6
% 1.64/1.12  #Tautology    : 4
% 1.64/1.12  #SimpNegUnit  : 0
% 1.64/1.12  #BackRed      : 1
% 1.64/1.12  
% 1.64/1.12  #Partial instantiations: 0
% 1.64/1.12  #Strategies tried      : 1
% 1.64/1.12  
% 1.64/1.12  Timing (in seconds)
% 1.64/1.12  ----------------------
% 1.64/1.12  Preprocessing        : 0.26
% 1.64/1.12  Parsing              : 0.15
% 1.64/1.12  CNF conversion       : 0.02
% 1.64/1.12  Main loop            : 0.11
% 1.64/1.12  Inferencing          : 0.05
% 1.64/1.12  Reduction            : 0.03
% 1.64/1.12  Demodulation         : 0.02
% 1.64/1.12  BG Simplification    : 0.01
% 1.64/1.12  Subsumption          : 0.02
% 1.64/1.12  Abstraction          : 0.00
% 1.64/1.12  MUC search           : 0.00
% 1.64/1.12  Cooper               : 0.00
% 1.64/1.12  Total                : 0.39
% 1.64/1.12  Index Insertion      : 0.00
% 1.64/1.12  Index Deletion       : 0.00
% 1.64/1.12  Index Matching       : 0.00
% 1.64/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
