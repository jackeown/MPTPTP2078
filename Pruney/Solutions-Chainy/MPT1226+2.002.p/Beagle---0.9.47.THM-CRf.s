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
% DateTime   : Thu Dec  3 10:20:28 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   33 (  41 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 (  97 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_60,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v4_pre_topc(B,A)
                    & v4_pre_topc(C,A) )
                 => v4_pre_topc(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v4_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v4_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k3_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tops_1)).

tff(c_12,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_19,plain,(
    ! [A_11,B_12,C_13] :
      ( k9_subset_1(A_11,B_12,C_13) = k3_xboole_0(B_12,C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_25,plain,(
    ! [B_12] : k9_subset_1(u1_struct_0('#skF_1'),B_12,'#skF_3') = k3_xboole_0(B_12,'#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_19])).

tff(c_6,plain,(
    ~ v4_pre_topc(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_35,plain,(
    ~ v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_6])).

tff(c_10,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_45,plain,(
    ! [B_16,C_17,A_18] :
      ( v4_pre_topc(k3_xboole_0(B_16,C_17),A_18)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ v4_pre_topc(C_17,A_18)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ v4_pre_topc(B_16,A_18)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_49,plain,(
    ! [B_16] :
      ( v4_pre_topc(k3_xboole_0(B_16,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc('#skF_3','#skF_1')
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v4_pre_topc(B_16,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_12,c_45])).

tff(c_69,plain,(
    ! [B_20] :
      ( v4_pre_topc(k3_xboole_0(B_20,'#skF_3'),'#skF_1')
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v4_pre_topc(B_20,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_8,c_49])).

tff(c_72,plain,
    ( v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_69])).

tff(c_78,plain,(
    v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_72])).

tff(c_80,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_78])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:21:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.16  
% 1.84/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.16  %$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.84/1.16  
% 1.84/1.16  %Foreground sorts:
% 1.84/1.16  
% 1.84/1.16  
% 1.84/1.16  %Background operators:
% 1.84/1.16  
% 1.84/1.16  
% 1.84/1.16  %Foreground operators:
% 1.84/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.16  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.84/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.84/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.84/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.84/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.84/1.16  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 1.84/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.16  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.84/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.84/1.16  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.84/1.16  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 1.84/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.84/1.16  
% 1.92/1.17  tff(f_60, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => v4_pre_topc(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tops_1)).
% 1.92/1.17  tff(f_29, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 1.92/1.17  tff(f_43, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v4_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v4_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k3_xboole_0(B, C), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_tops_1)).
% 1.92/1.17  tff(c_12, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.92/1.17  tff(c_19, plain, (![A_11, B_12, C_13]: (k9_subset_1(A_11, B_12, C_13)=k3_xboole_0(B_12, C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.92/1.17  tff(c_25, plain, (![B_12]: (k9_subset_1(u1_struct_0('#skF_1'), B_12, '#skF_3')=k3_xboole_0(B_12, '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_19])).
% 1.92/1.17  tff(c_6, plain, (~v4_pre_topc(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.92/1.17  tff(c_35, plain, (~v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_25, c_6])).
% 1.92/1.17  tff(c_10, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.92/1.17  tff(c_14, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.92/1.17  tff(c_18, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.92/1.17  tff(c_16, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.92/1.17  tff(c_8, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.92/1.17  tff(c_45, plain, (![B_16, C_17, A_18]: (v4_pre_topc(k3_xboole_0(B_16, C_17), A_18) | ~m1_subset_1(C_17, k1_zfmisc_1(u1_struct_0(A_18))) | ~v4_pre_topc(C_17, A_18) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_18))) | ~v4_pre_topc(B_16, A_18) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.92/1.17  tff(c_49, plain, (![B_16]: (v4_pre_topc(k3_xboole_0(B_16, '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1') | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v4_pre_topc(B_16, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_45])).
% 1.92/1.17  tff(c_69, plain, (![B_20]: (v4_pre_topc(k3_xboole_0(B_20, '#skF_3'), '#skF_1') | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v4_pre_topc(B_20, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_8, c_49])).
% 1.92/1.17  tff(c_72, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_14, c_69])).
% 1.92/1.17  tff(c_78, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_72])).
% 1.92/1.17  tff(c_80, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_78])).
% 1.92/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.17  
% 1.92/1.17  Inference rules
% 1.92/1.17  ----------------------
% 1.92/1.17  #Ref     : 0
% 1.92/1.17  #Sup     : 12
% 1.92/1.17  #Fact    : 0
% 1.92/1.17  #Define  : 0
% 1.92/1.17  #Split   : 0
% 1.92/1.17  #Chain   : 0
% 1.92/1.17  #Close   : 0
% 1.92/1.17  
% 1.92/1.17  Ordering : KBO
% 1.92/1.17  
% 1.92/1.17  Simplification rules
% 1.92/1.17  ----------------------
% 1.92/1.17  #Subsume      : 0
% 1.92/1.17  #Demod        : 10
% 1.92/1.17  #Tautology    : 4
% 1.92/1.17  #SimpNegUnit  : 1
% 1.92/1.17  #BackRed      : 1
% 1.92/1.17  
% 1.92/1.17  #Partial instantiations: 0
% 1.92/1.17  #Strategies tried      : 1
% 1.92/1.17  
% 1.92/1.17  Timing (in seconds)
% 1.92/1.17  ----------------------
% 1.92/1.17  Preprocessing        : 0.29
% 1.92/1.17  Parsing              : 0.15
% 1.92/1.17  CNF conversion       : 0.02
% 1.92/1.17  Main loop            : 0.11
% 1.92/1.17  Inferencing          : 0.05
% 1.92/1.17  Reduction            : 0.04
% 1.92/1.17  Demodulation         : 0.03
% 1.92/1.17  BG Simplification    : 0.01
% 1.92/1.17  Subsumption          : 0.01
% 1.92/1.17  Abstraction          : 0.01
% 1.92/1.17  MUC search           : 0.00
% 1.92/1.17  Cooper               : 0.00
% 1.92/1.17  Total                : 0.43
% 1.92/1.17  Index Insertion      : 0.00
% 1.92/1.17  Index Deletion       : 0.00
% 1.92/1.17  Index Matching       : 0.00
% 1.92/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
