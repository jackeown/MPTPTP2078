%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:37 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   38 (  41 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   44 (  49 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :   10 (   3 average)
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

tff(f_68,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => k1_tops_1(A,k1_struct_0(A)) = k1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tops_1)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => v1_xboole_0(k1_tops_1(A,k1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_tops_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

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
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_25,plain,(
    ! [A_21] :
      ( v1_xboole_0(k1_tops_1(A_21,k1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    ! [A_22] :
      ( k1_tops_1(A_22,k1_struct_0(A_22)) = k1_xboole_0
      | ~ l1_pre_topc(A_22) ) ),
    inference(resolution,[status(thm)],[c_25,c_2])).

tff(c_18,plain,(
    k1_tops_1('#skF_2',k1_struct_0('#skF_2')) != k1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_39,plain,
    ( k1_struct_0('#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_18])).

tff(c_45,plain,(
    k1_struct_0('#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_39])).

tff(c_4,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_66,plain,(
    ! [A_29,B_30] :
      ( r2_hidden('#skF_1'(A_29,B_30),B_30)
      | k1_struct_0(A_29) = B_30
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_72,plain,(
    ! [A_33] :
      ( r2_hidden('#skF_1'(A_33,k1_xboole_0),k1_xboole_0)
      | k1_struct_0(A_33) = k1_xboole_0
      | ~ l1_pre_topc(A_33) ) ),
    inference(resolution,[status(thm)],[c_6,c_66])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( ~ r1_tarski(B_8,A_7)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_77,plain,(
    ! [A_33] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_1'(A_33,k1_xboole_0))
      | k1_struct_0(A_33) = k1_xboole_0
      | ~ l1_pre_topc(A_33) ) ),
    inference(resolution,[status(thm)],[c_72,c_10])).

tff(c_82,plain,(
    ! [A_34] :
      ( k1_struct_0(A_34) = k1_xboole_0
      | ~ l1_pre_topc(A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_77])).

tff(c_85,plain,(
    k1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_82])).

tff(c_89,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_85])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:16:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.16  
% 1.68/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.16  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_1
% 1.68/1.16  
% 1.68/1.16  %Foreground sorts:
% 1.68/1.16  
% 1.68/1.16  
% 1.68/1.16  %Background operators:
% 1.68/1.16  
% 1.68/1.16  
% 1.68/1.16  %Foreground operators:
% 1.68/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.68/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.68/1.16  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.68/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.68/1.16  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 1.68/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.68/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.16  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 1.68/1.16  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.68/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.68/1.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.68/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.68/1.16  
% 1.79/1.17  tff(f_68, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (k1_tops_1(A, k1_struct_0(A)) = k1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_tops_1)).
% 1.79/1.17  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => v1_xboole_0(k1_tops_1(A, k1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_tops_1)).
% 1.79/1.17  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.79/1.17  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.79/1.17  tff(f_33, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 1.79/1.17  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(~(B = k1_struct_0(A)) & (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~r2_hidden(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_pre_topc)).
% 1.79/1.17  tff(f_44, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.79/1.17  tff(c_20, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.79/1.17  tff(c_25, plain, (![A_21]: (v1_xboole_0(k1_tops_1(A_21, k1_struct_0(A_21))) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.79/1.17  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.79/1.17  tff(c_30, plain, (![A_22]: (k1_tops_1(A_22, k1_struct_0(A_22))=k1_xboole_0 | ~l1_pre_topc(A_22))), inference(resolution, [status(thm)], [c_25, c_2])).
% 1.79/1.17  tff(c_18, plain, (k1_tops_1('#skF_2', k1_struct_0('#skF_2'))!=k1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.79/1.17  tff(c_39, plain, (k1_struct_0('#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_30, c_18])).
% 1.79/1.17  tff(c_45, plain, (k1_struct_0('#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_39])).
% 1.79/1.17  tff(c_4, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.79/1.17  tff(c_6, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.79/1.17  tff(c_66, plain, (![A_29, B_30]: (r2_hidden('#skF_1'(A_29, B_30), B_30) | k1_struct_0(A_29)=B_30 | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.79/1.17  tff(c_72, plain, (![A_33]: (r2_hidden('#skF_1'(A_33, k1_xboole_0), k1_xboole_0) | k1_struct_0(A_33)=k1_xboole_0 | ~l1_pre_topc(A_33))), inference(resolution, [status(thm)], [c_6, c_66])).
% 1.79/1.17  tff(c_10, plain, (![B_8, A_7]: (~r1_tarski(B_8, A_7) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.79/1.17  tff(c_77, plain, (![A_33]: (~r1_tarski(k1_xboole_0, '#skF_1'(A_33, k1_xboole_0)) | k1_struct_0(A_33)=k1_xboole_0 | ~l1_pre_topc(A_33))), inference(resolution, [status(thm)], [c_72, c_10])).
% 1.79/1.17  tff(c_82, plain, (![A_34]: (k1_struct_0(A_34)=k1_xboole_0 | ~l1_pre_topc(A_34))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_77])).
% 1.79/1.17  tff(c_85, plain, (k1_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_82])).
% 1.79/1.17  tff(c_89, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_85])).
% 1.79/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.17  
% 1.79/1.17  Inference rules
% 1.79/1.17  ----------------------
% 1.79/1.17  #Ref     : 0
% 1.79/1.17  #Sup     : 12
% 1.79/1.17  #Fact    : 0
% 1.79/1.17  #Define  : 0
% 1.79/1.17  #Split   : 1
% 1.79/1.17  #Chain   : 0
% 1.79/1.17  #Close   : 0
% 1.79/1.17  
% 1.79/1.17  Ordering : KBO
% 1.79/1.17  
% 1.79/1.17  Simplification rules
% 1.79/1.17  ----------------------
% 1.79/1.17  #Subsume      : 1
% 1.79/1.17  #Demod        : 3
% 1.79/1.17  #Tautology    : 3
% 1.79/1.17  #SimpNegUnit  : 1
% 1.79/1.17  #BackRed      : 0
% 1.79/1.17  
% 1.79/1.17  #Partial instantiations: 0
% 1.79/1.17  #Strategies tried      : 1
% 1.79/1.17  
% 1.79/1.17  Timing (in seconds)
% 1.79/1.17  ----------------------
% 1.79/1.18  Preprocessing        : 0.26
% 1.79/1.18  Parsing              : 0.14
% 1.79/1.18  CNF conversion       : 0.02
% 1.79/1.18  Main loop            : 0.11
% 1.79/1.18  Inferencing          : 0.05
% 1.79/1.18  Reduction            : 0.03
% 1.79/1.18  Demodulation         : 0.02
% 1.79/1.18  BG Simplification    : 0.01
% 1.79/1.18  Subsumption          : 0.02
% 1.79/1.18  Abstraction          : 0.00
% 1.79/1.18  MUC search           : 0.00
% 1.79/1.18  Cooper               : 0.00
% 1.79/1.18  Total                : 0.40
% 1.79/1.18  Index Insertion      : 0.00
% 1.79/1.18  Index Deletion       : 0.00
% 1.79/1.18  Index Matching       : 0.00
% 1.79/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
