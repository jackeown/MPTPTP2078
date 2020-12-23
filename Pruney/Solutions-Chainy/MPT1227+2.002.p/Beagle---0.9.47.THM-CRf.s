%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:29 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   34 (  44 expanded)
%              Number of leaves         :   17 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   51 ( 109 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_subset_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_62,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v4_pre_topc(B,A)
                    & v4_pre_topc(C,A) )
                 => v4_pre_topc(k4_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tops_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v4_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v4_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_tops_1)).

tff(c_14,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_19,plain,(
    ! [A_11,B_12,C_13] :
      ( k4_subset_1(A_11,B_12,C_13) = k2_xboole_0(B_12,C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_43,plain,(
    ! [B_15] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_15,'#skF_3') = k2_xboole_0(B_15,'#skF_3')
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_12,c_19])).

tff(c_50,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_43])).

tff(c_6,plain,(
    ~ v4_pre_topc(k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_52,plain,(
    ~ v4_pre_topc(k2_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_6])).

tff(c_10,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_18,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_61,plain,(
    ! [B_16,C_17,A_18] :
      ( v4_pre_topc(k2_xboole_0(B_16,C_17),A_18)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ v4_pre_topc(C_17,A_18)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ v4_pre_topc(B_16,A_18)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_65,plain,(
    ! [B_16] :
      ( v4_pre_topc(k2_xboole_0(B_16,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc('#skF_3','#skF_1')
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v4_pre_topc(B_16,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_12,c_61])).

tff(c_85,plain,(
    ! [B_20] :
      ( v4_pre_topc(k2_xboole_0(B_20,'#skF_3'),'#skF_1')
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v4_pre_topc(B_20,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_8,c_65])).

tff(c_88,plain,
    ( v4_pre_topc(k2_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_85])).

tff(c_94,plain,(
    v4_pre_topc(k2_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_88])).

tff(c_96,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_94])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:45:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.20  
% 1.77/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.21  %$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_subset_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.77/1.21  
% 1.77/1.21  %Foreground sorts:
% 1.77/1.21  
% 1.77/1.21  
% 1.77/1.21  %Background operators:
% 1.77/1.21  
% 1.77/1.21  
% 1.77/1.21  %Foreground operators:
% 1.77/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.21  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.77/1.21  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 1.77/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.77/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.77/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.77/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.77/1.21  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 1.77/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.21  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.77/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.77/1.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.77/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.77/1.21  
% 1.77/1.22  tff(f_62, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => v4_pre_topc(k4_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tops_1)).
% 1.77/1.22  tff(f_31, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 1.77/1.22  tff(f_45, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v4_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v4_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_xboole_0(B, C), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_tops_1)).
% 1.77/1.22  tff(c_14, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.77/1.22  tff(c_12, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.77/1.22  tff(c_19, plain, (![A_11, B_12, C_13]: (k4_subset_1(A_11, B_12, C_13)=k2_xboole_0(B_12, C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(A_11)) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.77/1.22  tff(c_43, plain, (![B_15]: (k4_subset_1(u1_struct_0('#skF_1'), B_15, '#skF_3')=k2_xboole_0(B_15, '#skF_3') | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_12, c_19])).
% 1.77/1.22  tff(c_50, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_14, c_43])).
% 1.77/1.22  tff(c_6, plain, (~v4_pre_topc(k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.77/1.22  tff(c_52, plain, (~v4_pre_topc(k2_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_6])).
% 1.77/1.22  tff(c_10, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.77/1.22  tff(c_18, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.77/1.22  tff(c_16, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.77/1.22  tff(c_8, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.77/1.22  tff(c_61, plain, (![B_16, C_17, A_18]: (v4_pre_topc(k2_xboole_0(B_16, C_17), A_18) | ~m1_subset_1(C_17, k1_zfmisc_1(u1_struct_0(A_18))) | ~v4_pre_topc(C_17, A_18) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_18))) | ~v4_pre_topc(B_16, A_18) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.77/1.22  tff(c_65, plain, (![B_16]: (v4_pre_topc(k2_xboole_0(B_16, '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1') | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v4_pre_topc(B_16, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_61])).
% 1.77/1.22  tff(c_85, plain, (![B_20]: (v4_pre_topc(k2_xboole_0(B_20, '#skF_3'), '#skF_1') | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v4_pre_topc(B_20, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_8, c_65])).
% 1.77/1.22  tff(c_88, plain, (v4_pre_topc(k2_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_14, c_85])).
% 1.77/1.22  tff(c_94, plain, (v4_pre_topc(k2_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_88])).
% 1.77/1.22  tff(c_96, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_94])).
% 1.77/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.22  
% 1.77/1.22  Inference rules
% 1.77/1.22  ----------------------
% 1.77/1.22  #Ref     : 0
% 1.77/1.22  #Sup     : 20
% 1.77/1.22  #Fact    : 0
% 1.77/1.22  #Define  : 0
% 1.77/1.22  #Split   : 0
% 1.77/1.22  #Chain   : 0
% 1.77/1.22  #Close   : 0
% 1.77/1.22  
% 1.77/1.22  Ordering : KBO
% 1.77/1.22  
% 1.77/1.22  Simplification rules
% 1.77/1.22  ----------------------
% 1.77/1.22  #Subsume      : 0
% 1.77/1.22  #Demod        : 10
% 1.77/1.22  #Tautology    : 8
% 1.77/1.22  #SimpNegUnit  : 1
% 1.77/1.22  #BackRed      : 1
% 1.77/1.22  
% 1.77/1.22  #Partial instantiations: 0
% 1.77/1.22  #Strategies tried      : 1
% 1.77/1.22  
% 1.77/1.22  Timing (in seconds)
% 1.77/1.22  ----------------------
% 1.77/1.22  Preprocessing        : 0.30
% 1.77/1.22  Parsing              : 0.17
% 1.77/1.22  CNF conversion       : 0.02
% 1.77/1.22  Main loop            : 0.12
% 1.77/1.22  Inferencing          : 0.05
% 1.77/1.22  Reduction            : 0.04
% 1.77/1.22  Demodulation         : 0.03
% 1.77/1.22  BG Simplification    : 0.01
% 1.77/1.22  Subsumption          : 0.02
% 1.77/1.22  Abstraction          : 0.01
% 1.77/1.22  MUC search           : 0.00
% 1.77/1.22  Cooper               : 0.00
% 1.77/1.22  Total                : 0.45
% 1.77/1.22  Index Insertion      : 0.00
% 1.77/1.22  Index Deletion       : 0.00
% 1.77/1.22  Index Matching       : 0.00
% 1.77/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
