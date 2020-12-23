%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:07 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   38 (  52 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   61 ( 111 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v3_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_tops_1(k2_tops_1(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_tops_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v4_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tops_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v3_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_tops_1(k2_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc16_tops_1)).

tff(c_20,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_18,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_14,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_16,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_7),B_8),A_7)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ v4_pre_topc(B_8,A_7)
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ~ v3_tops_1(k2_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_46,plain,(
    ! [A_19,B_20] :
      ( k2_tops_1(A_19,k3_subset_1(u1_struct_0(A_19),B_20)) = k2_tops_1(A_19,B_20)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_51,plain,
    ( k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_46])).

tff(c_55,plain,(
    k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_51])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k3_subset_1(A_3,B_4),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_60,plain,(
    ! [A_21,B_22] :
      ( v3_tops_1(k2_tops_1(A_21,B_22),A_21)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ v3_pre_topc(B_22,A_21)
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_90,plain,(
    ! [A_29,B_30] :
      ( v3_tops_1(k2_tops_1(A_29,k3_subset_1(u1_struct_0(A_29),B_30)),A_29)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_29),B_30),A_29)
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_29))) ) ),
    inference(resolution,[status(thm)],[c_4,c_60])).

tff(c_96,plain,
    ( v3_tops_1(k2_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_90])).

tff(c_98,plain,
    ( v3_tops_1(k2_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_20,c_18,c_96])).

tff(c_99,plain,(
    ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_98])).

tff(c_102,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_99])).

tff(c_106,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_14,c_16,c_102])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:55:55 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.19  
% 2.00/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.19  %$ v4_pre_topc > v3_tops_1 > v3_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.00/1.19  
% 2.00/1.19  %Foreground sorts:
% 2.00/1.19  
% 2.00/1.19  
% 2.00/1.19  %Background operators:
% 2.00/1.19  
% 2.00/1.19  
% 2.00/1.19  %Foreground operators:
% 2.00/1.19  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.00/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.00/1.19  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.00/1.19  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.00/1.19  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 2.00/1.19  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.00/1.19  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.19  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.00/1.19  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.00/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.19  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.00/1.19  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.00/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.00/1.19  
% 2.00/1.20  tff(f_72, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_tops_1(k2_tops_1(A, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_tops_1)).
% 2.00/1.20  tff(f_53, axiom, (![A, B]: ((((v2_pre_topc(A) & l1_pre_topc(A)) & v4_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tops_1)).
% 2.00/1.20  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_1)).
% 2.00/1.20  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.00/1.20  tff(f_43, axiom, (![A, B]: ((((v2_pre_topc(A) & l1_pre_topc(A)) & v3_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_tops_1(k2_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc16_tops_1)).
% 2.00/1.20  tff(c_20, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.00/1.20  tff(c_18, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.00/1.20  tff(c_14, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.00/1.20  tff(c_16, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.00/1.20  tff(c_8, plain, (![A_7, B_8]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_7), B_8), A_7) | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0(A_7))) | ~v4_pre_topc(B_8, A_7) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.00/1.20  tff(c_12, plain, (~v3_tops_1(k2_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.00/1.20  tff(c_46, plain, (![A_19, B_20]: (k2_tops_1(A_19, k3_subset_1(u1_struct_0(A_19), B_20))=k2_tops_1(A_19, B_20) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.00/1.20  tff(c_51, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_46])).
% 2.00/1.20  tff(c_55, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_51])).
% 2.00/1.20  tff(c_4, plain, (![A_3, B_4]: (m1_subset_1(k3_subset_1(A_3, B_4), k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.00/1.20  tff(c_60, plain, (![A_21, B_22]: (v3_tops_1(k2_tops_1(A_21, B_22), A_21) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_21))) | ~v3_pre_topc(B_22, A_21) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.00/1.20  tff(c_90, plain, (![A_29, B_30]: (v3_tops_1(k2_tops_1(A_29, k3_subset_1(u1_struct_0(A_29), B_30)), A_29) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_29), B_30), A_29) | ~l1_pre_topc(A_29) | ~v2_pre_topc(A_29) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_29))))), inference(resolution, [status(thm)], [c_4, c_60])).
% 2.00/1.20  tff(c_96, plain, (v3_tops_1(k2_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_55, c_90])).
% 2.00/1.20  tff(c_98, plain, (v3_tops_1(k2_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_20, c_18, c_96])).
% 2.00/1.20  tff(c_99, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_12, c_98])).
% 2.00/1.20  tff(c_102, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_99])).
% 2.00/1.20  tff(c_106, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_14, c_16, c_102])).
% 2.00/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.20  
% 2.00/1.20  Inference rules
% 2.00/1.20  ----------------------
% 2.00/1.20  #Ref     : 0
% 2.00/1.20  #Sup     : 21
% 2.00/1.20  #Fact    : 0
% 2.00/1.20  #Define  : 0
% 2.00/1.20  #Split   : 0
% 2.00/1.20  #Chain   : 0
% 2.00/1.20  #Close   : 0
% 2.00/1.20  
% 2.00/1.20  Ordering : KBO
% 2.00/1.20  
% 2.00/1.20  Simplification rules
% 2.00/1.20  ----------------------
% 2.00/1.20  #Subsume      : 0
% 2.00/1.20  #Demod        : 10
% 2.00/1.20  #Tautology    : 10
% 2.00/1.20  #SimpNegUnit  : 2
% 2.00/1.20  #BackRed      : 0
% 2.00/1.20  
% 2.00/1.20  #Partial instantiations: 0
% 2.00/1.20  #Strategies tried      : 1
% 2.00/1.20  
% 2.00/1.20  Timing (in seconds)
% 2.00/1.20  ----------------------
% 2.00/1.21  Preprocessing        : 0.30
% 2.00/1.21  Parsing              : 0.16
% 2.00/1.21  CNF conversion       : 0.02
% 2.00/1.21  Main loop            : 0.14
% 2.00/1.21  Inferencing          : 0.06
% 2.00/1.21  Reduction            : 0.04
% 2.00/1.21  Demodulation         : 0.03
% 2.00/1.21  BG Simplification    : 0.01
% 2.00/1.21  Subsumption          : 0.02
% 2.00/1.21  Abstraction          : 0.01
% 2.00/1.21  MUC search           : 0.00
% 2.00/1.21  Cooper               : 0.00
% 2.00/1.21  Total                : 0.46
% 2.00/1.21  Index Insertion      : 0.00
% 2.00/1.21  Index Deletion       : 0.00
% 2.00/1.21  Index Matching       : 0.00
% 2.00/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
