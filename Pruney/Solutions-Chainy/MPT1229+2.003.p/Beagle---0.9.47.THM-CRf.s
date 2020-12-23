%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:29 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.18s
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
%$ v3_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

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
               => ( ( v3_pre_topc(B,A)
                    & v3_pre_topc(C,A) )
                 => v3_pre_topc(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_tops_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v3_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v3_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k3_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_tops_1)).

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
    ~ v3_pre_topc(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_35,plain,(
    ~ v3_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_6])).

tff(c_10,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
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
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_45,plain,(
    ! [B_16,C_17,A_18] :
      ( v3_pre_topc(k3_xboole_0(B_16,C_17),A_18)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ v3_pre_topc(C_17,A_18)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ v3_pre_topc(B_16,A_18)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_49,plain,(
    ! [B_16] :
      ( v3_pre_topc(k3_xboole_0(B_16,'#skF_3'),'#skF_1')
      | ~ v3_pre_topc('#skF_3','#skF_1')
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v3_pre_topc(B_16,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_12,c_45])).

tff(c_69,plain,(
    ! [B_20] :
      ( v3_pre_topc(k3_xboole_0(B_20,'#skF_3'),'#skF_1')
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v3_pre_topc(B_20,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_8,c_49])).

tff(c_72,plain,
    ( v3_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_69])).

tff(c_78,plain,(
    v3_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_72])).

tff(c_80,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_78])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:44:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.45  
% 2.02/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.45  %$ v3_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.02/1.45  
% 2.02/1.45  %Foreground sorts:
% 2.02/1.45  
% 2.02/1.45  
% 2.02/1.45  %Background operators:
% 2.02/1.45  
% 2.02/1.45  
% 2.02/1.45  %Foreground operators:
% 2.02/1.45  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.02/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.02/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.02/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.02/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.02/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.02/1.45  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.02/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.02/1.45  
% 2.18/1.47  tff(f_60, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_pre_topc(C, A)) => v3_pre_topc(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_tops_1)).
% 2.18/1.47  tff(f_29, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.18/1.47  tff(f_43, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v3_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v3_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k3_xboole_0(B, C), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_tops_1)).
% 2.18/1.47  tff(c_12, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.18/1.47  tff(c_19, plain, (![A_11, B_12, C_13]: (k9_subset_1(A_11, B_12, C_13)=k3_xboole_0(B_12, C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.18/1.47  tff(c_25, plain, (![B_12]: (k9_subset_1(u1_struct_0('#skF_1'), B_12, '#skF_3')=k3_xboole_0(B_12, '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_19])).
% 2.18/1.47  tff(c_6, plain, (~v3_pre_topc(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.18/1.47  tff(c_35, plain, (~v3_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_25, c_6])).
% 2.18/1.47  tff(c_10, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.18/1.47  tff(c_14, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.18/1.47  tff(c_18, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.18/1.47  tff(c_16, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.18/1.47  tff(c_8, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.18/1.47  tff(c_45, plain, (![B_16, C_17, A_18]: (v3_pre_topc(k3_xboole_0(B_16, C_17), A_18) | ~m1_subset_1(C_17, k1_zfmisc_1(u1_struct_0(A_18))) | ~v3_pre_topc(C_17, A_18) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_18))) | ~v3_pre_topc(B_16, A_18) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.18/1.47  tff(c_49, plain, (![B_16]: (v3_pre_topc(k3_xboole_0(B_16, '#skF_3'), '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1') | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v3_pre_topc(B_16, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_45])).
% 2.18/1.47  tff(c_69, plain, (![B_20]: (v3_pre_topc(k3_xboole_0(B_20, '#skF_3'), '#skF_1') | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v3_pre_topc(B_20, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_8, c_49])).
% 2.18/1.47  tff(c_72, plain, (v3_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_14, c_69])).
% 2.18/1.47  tff(c_78, plain, (v3_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_72])).
% 2.18/1.47  tff(c_80, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_78])).
% 2.18/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.47  
% 2.18/1.47  Inference rules
% 2.18/1.47  ----------------------
% 2.18/1.47  #Ref     : 0
% 2.18/1.47  #Sup     : 12
% 2.18/1.47  #Fact    : 0
% 2.18/1.47  #Define  : 0
% 2.18/1.47  #Split   : 0
% 2.18/1.47  #Chain   : 0
% 2.18/1.47  #Close   : 0
% 2.18/1.47  
% 2.18/1.47  Ordering : KBO
% 2.18/1.47  
% 2.18/1.47  Simplification rules
% 2.18/1.47  ----------------------
% 2.18/1.47  #Subsume      : 0
% 2.18/1.47  #Demod        : 10
% 2.18/1.47  #Tautology    : 4
% 2.18/1.47  #SimpNegUnit  : 1
% 2.18/1.47  #BackRed      : 1
% 2.18/1.47  
% 2.18/1.47  #Partial instantiations: 0
% 2.18/1.47  #Strategies tried      : 1
% 2.18/1.47  
% 2.18/1.47  Timing (in seconds)
% 2.18/1.47  ----------------------
% 2.18/1.47  Preprocessing        : 0.45
% 2.18/1.47  Parsing              : 0.24
% 2.18/1.47  CNF conversion       : 0.03
% 2.18/1.47  Main loop            : 0.18
% 2.18/1.47  Inferencing          : 0.08
% 2.18/1.47  Reduction            : 0.06
% 2.18/1.47  Demodulation         : 0.04
% 2.18/1.47  BG Simplification    : 0.01
% 2.18/1.47  Subsumption          : 0.02
% 2.18/1.47  Abstraction          : 0.01
% 2.18/1.47  MUC search           : 0.00
% 2.18/1.47  Cooper               : 0.00
% 2.18/1.47  Total                : 0.68
% 2.18/1.48  Index Insertion      : 0.00
% 2.18/1.48  Index Deletion       : 0.00
% 2.18/1.48  Index Matching       : 0.00
% 2.18/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
