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
% DateTime   : Thu Dec  3 10:20:36 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   38 (  51 expanded)
%              Number of leaves         :   21 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   44 (  65 expanded)
%              Number of equality atoms :   12 (  19 expanded)
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

tff(f_63,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => k1_tops_1(A,k1_struct_0(A)) = k1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tops_1)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_18,plain,(
    ! [A_10] :
      ( l1_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_29,plain,(
    ! [A_17] :
      ( k1_struct_0(A_17) = k1_xboole_0
      | ~ l1_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_34,plain,(
    ! [A_18] :
      ( k1_struct_0(A_18) = k1_xboole_0
      | ~ l1_pre_topc(A_18) ) ),
    inference(resolution,[status(thm)],[c_18,c_29])).

tff(c_38,plain,(
    k1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_34])).

tff(c_22,plain,(
    k1_tops_1('#skF_1',k1_struct_0('#skF_1')) != k1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_39,plain,(
    k1_tops_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_22])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_44,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ m1_subset_1(A_19,k1_zfmisc_1(B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_48,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(resolution,[status(thm)],[c_8,c_44])).

tff(c_85,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(k1_tops_1(A_30,B_31),B_31)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_95,plain,(
    ! [A_34] :
      ( r1_tarski(k1_tops_1(A_34,k1_xboole_0),k1_xboole_0)
      | ~ l1_pre_topc(A_34) ) ),
    inference(resolution,[status(thm)],[c_8,c_85])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_100,plain,(
    ! [A_34] :
      ( k1_tops_1(A_34,k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k1_tops_1(A_34,k1_xboole_0))
      | ~ l1_pre_topc(A_34) ) ),
    inference(resolution,[status(thm)],[c_95,c_2])).

tff(c_105,plain,(
    ! [A_35] :
      ( k1_tops_1(A_35,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_100])).

tff(c_108,plain,(
    k1_tops_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_105])).

tff(c_112,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:08:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.17  
% 1.82/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.17  %$ r2_hidden > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1
% 1.82/1.17  
% 1.82/1.17  %Foreground sorts:
% 1.82/1.17  
% 1.82/1.17  
% 1.82/1.17  %Background operators:
% 1.82/1.17  
% 1.82/1.17  
% 1.82/1.17  %Foreground operators:
% 1.82/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.82/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.82/1.17  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.82/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.82/1.17  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 1.82/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.82/1.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.82/1.17  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.82/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.17  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 1.82/1.17  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.82/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.82/1.17  
% 1.82/1.19  tff(f_63, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (k1_tops_1(A, k1_struct_0(A)) = k1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_tops_1)).
% 1.82/1.19  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 1.82/1.19  tff(f_47, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_struct_0)).
% 1.82/1.19  tff(f_33, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 1.82/1.19  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.82/1.19  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 1.82/1.19  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.82/1.19  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.82/1.19  tff(c_18, plain, (![A_10]: (l1_struct_0(A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.82/1.19  tff(c_29, plain, (![A_17]: (k1_struct_0(A_17)=k1_xboole_0 | ~l1_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.82/1.19  tff(c_34, plain, (![A_18]: (k1_struct_0(A_18)=k1_xboole_0 | ~l1_pre_topc(A_18))), inference(resolution, [status(thm)], [c_18, c_29])).
% 1.82/1.19  tff(c_38, plain, (k1_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_34])).
% 1.82/1.19  tff(c_22, plain, (k1_tops_1('#skF_1', k1_struct_0('#skF_1'))!=k1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.82/1.19  tff(c_39, plain, (k1_tops_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_22])).
% 1.82/1.19  tff(c_8, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.82/1.19  tff(c_44, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~m1_subset_1(A_19, k1_zfmisc_1(B_20)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.82/1.19  tff(c_48, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(resolution, [status(thm)], [c_8, c_44])).
% 1.82/1.19  tff(c_85, plain, (![A_30, B_31]: (r1_tarski(k1_tops_1(A_30, B_31), B_31) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.82/1.19  tff(c_95, plain, (![A_34]: (r1_tarski(k1_tops_1(A_34, k1_xboole_0), k1_xboole_0) | ~l1_pre_topc(A_34))), inference(resolution, [status(thm)], [c_8, c_85])).
% 1.82/1.19  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.82/1.19  tff(c_100, plain, (![A_34]: (k1_tops_1(A_34, k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_tops_1(A_34, k1_xboole_0)) | ~l1_pre_topc(A_34))), inference(resolution, [status(thm)], [c_95, c_2])).
% 1.82/1.19  tff(c_105, plain, (![A_35]: (k1_tops_1(A_35, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_35))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_100])).
% 1.82/1.19  tff(c_108, plain, (k1_tops_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_105])).
% 1.82/1.19  tff(c_112, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39, c_108])).
% 1.82/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.19  
% 1.82/1.19  Inference rules
% 1.82/1.19  ----------------------
% 1.82/1.19  #Ref     : 0
% 1.82/1.19  #Sup     : 17
% 1.82/1.19  #Fact    : 0
% 1.82/1.19  #Define  : 0
% 1.82/1.19  #Split   : 0
% 1.82/1.19  #Chain   : 0
% 1.82/1.19  #Close   : 0
% 1.82/1.19  
% 1.82/1.19  Ordering : KBO
% 1.82/1.19  
% 1.82/1.19  Simplification rules
% 1.82/1.19  ----------------------
% 1.82/1.19  #Subsume      : 0
% 1.82/1.19  #Demod        : 5
% 1.82/1.19  #Tautology    : 7
% 1.82/1.19  #SimpNegUnit  : 1
% 1.82/1.19  #BackRed      : 1
% 1.82/1.19  
% 1.82/1.19  #Partial instantiations: 0
% 1.82/1.19  #Strategies tried      : 1
% 1.82/1.19  
% 1.82/1.19  Timing (in seconds)
% 1.82/1.19  ----------------------
% 1.82/1.19  Preprocessing        : 0.28
% 1.82/1.19  Parsing              : 0.16
% 1.82/1.19  CNF conversion       : 0.02
% 1.82/1.19  Main loop            : 0.13
% 1.82/1.19  Inferencing          : 0.05
% 1.82/1.19  Reduction            : 0.03
% 1.82/1.19  Demodulation         : 0.03
% 1.82/1.19  BG Simplification    : 0.01
% 1.82/1.19  Subsumption          : 0.02
% 1.82/1.19  Abstraction          : 0.00
% 1.82/1.19  MUC search           : 0.00
% 1.82/1.19  Cooper               : 0.00
% 1.82/1.19  Total                : 0.44
% 1.82/1.19  Index Insertion      : 0.00
% 1.82/1.19  Index Deletion       : 0.00
% 1.82/1.19  Index Matching       : 0.00
% 1.82/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
