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
% DateTime   : Thu Dec  3 10:22:12 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   39 (  58 expanded)
%              Number of leaves         :   19 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   67 ( 155 expanded)
%              Number of equality atoms :   12 (  26 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tops_1 > v3_pre_topc > v2_tops_1 > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v3_pre_topc(B,A)
                & v3_tops_1(B,A) )
             => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_tops_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( v3_pre_topc(D,B)
                     => k1_tops_1(B,D) = D )
                    & ( k1_tops_1(A,C) = C
                     => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

tff(c_12,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_20,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_16,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_14,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_23,plain,(
    ! [B_23,A_24] :
      ( v2_tops_1(B_23,A_24)
      | ~ v3_tops_1(B_23,A_24)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_26,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_23])).

tff(c_29,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_14,c_26])).

tff(c_30,plain,(
    ! [A_25,B_26] :
      ( k1_tops_1(A_25,B_26) = k1_xboole_0
      | ~ v2_tops_1(B_26,A_25)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_33,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_30])).

tff(c_36,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_29,c_33])).

tff(c_22,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4,plain,(
    ! [B_9,D_15,C_13,A_1] :
      ( k1_tops_1(B_9,D_15) = D_15
      | ~ v3_pre_topc(D_15,B_9)
      | ~ m1_subset_1(D_15,k1_zfmisc_1(u1_struct_0(B_9)))
      | ~ m1_subset_1(C_13,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(B_9)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_49,plain,(
    ! [C_29,A_30] :
      ( ~ m1_subset_1(C_29,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30) ) ),
    inference(splitLeft,[status(thm)],[c_4])).

tff(c_52,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_49])).

tff(c_56,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_52])).

tff(c_58,plain,(
    ! [B_31,D_32] :
      ( k1_tops_1(B_31,D_32) = D_32
      | ~ v3_pre_topc(D_32,B_31)
      | ~ m1_subset_1(D_32,k1_zfmisc_1(u1_struct_0(B_31)))
      | ~ l1_pre_topc(B_31) ) ),
    inference(splitRight,[status(thm)],[c_4])).

tff(c_61,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_58])).

tff(c_64,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_36,c_61])).

tff(c_66,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_64])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:09:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.20  
% 1.90/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.20  %$ v3_tops_1 > v3_pre_topc > v2_tops_1 > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.90/1.20  
% 1.90/1.20  %Foreground sorts:
% 1.90/1.20  
% 1.90/1.20  
% 1.90/1.20  %Background operators:
% 1.90/1.20  
% 1.90/1.20  
% 1.90/1.20  %Foreground operators:
% 1.90/1.20  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 1.90/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.90/1.20  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 1.90/1.20  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.90/1.20  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 1.90/1.20  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 1.90/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.90/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.90/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.90/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.20  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.90/1.20  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.90/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.90/1.20  
% 1.90/1.21  tff(f_78, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tops_1(B, A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_tops_1)).
% 1.90/1.21  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_tops_1)).
% 1.90/1.21  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 1.90/1.21  tff(f_46, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 1.90/1.21  tff(c_12, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.90/1.21  tff(c_20, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.90/1.21  tff(c_16, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.90/1.21  tff(c_14, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.90/1.21  tff(c_18, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.90/1.21  tff(c_23, plain, (![B_23, A_24]: (v2_tops_1(B_23, A_24) | ~v3_tops_1(B_23, A_24) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.90/1.21  tff(c_26, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_23])).
% 1.90/1.21  tff(c_29, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_14, c_26])).
% 1.90/1.21  tff(c_30, plain, (![A_25, B_26]: (k1_tops_1(A_25, B_26)=k1_xboole_0 | ~v2_tops_1(B_26, A_25) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.90/1.21  tff(c_33, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_30])).
% 1.90/1.21  tff(c_36, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_29, c_33])).
% 1.90/1.21  tff(c_22, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.90/1.21  tff(c_4, plain, (![B_9, D_15, C_13, A_1]: (k1_tops_1(B_9, D_15)=D_15 | ~v3_pre_topc(D_15, B_9) | ~m1_subset_1(D_15, k1_zfmisc_1(u1_struct_0(B_9))) | ~m1_subset_1(C_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(B_9) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.90/1.21  tff(c_49, plain, (![C_29, A_30]: (~m1_subset_1(C_29, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30))), inference(splitLeft, [status(thm)], [c_4])).
% 1.90/1.21  tff(c_52, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_49])).
% 1.90/1.21  tff(c_56, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_52])).
% 1.90/1.21  tff(c_58, plain, (![B_31, D_32]: (k1_tops_1(B_31, D_32)=D_32 | ~v3_pre_topc(D_32, B_31) | ~m1_subset_1(D_32, k1_zfmisc_1(u1_struct_0(B_31))) | ~l1_pre_topc(B_31))), inference(splitRight, [status(thm)], [c_4])).
% 1.90/1.21  tff(c_61, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_58])).
% 1.90/1.21  tff(c_64, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_36, c_61])).
% 1.90/1.21  tff(c_66, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_64])).
% 1.90/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.21  
% 1.90/1.21  Inference rules
% 1.90/1.21  ----------------------
% 1.90/1.21  #Ref     : 0
% 1.90/1.21  #Sup     : 7
% 1.90/1.21  #Fact    : 0
% 1.90/1.21  #Define  : 0
% 1.90/1.21  #Split   : 1
% 1.90/1.21  #Chain   : 0
% 1.90/1.21  #Close   : 0
% 1.90/1.21  
% 1.90/1.21  Ordering : KBO
% 1.90/1.21  
% 1.90/1.21  Simplification rules
% 1.90/1.21  ----------------------
% 1.90/1.21  #Subsume      : 0
% 1.90/1.21  #Demod        : 12
% 1.90/1.21  #Tautology    : 3
% 1.90/1.21  #SimpNegUnit  : 1
% 1.90/1.21  #BackRed      : 0
% 1.90/1.21  
% 1.90/1.21  #Partial instantiations: 0
% 1.90/1.21  #Strategies tried      : 1
% 1.90/1.21  
% 1.90/1.21  Timing (in seconds)
% 1.90/1.21  ----------------------
% 1.90/1.21  Preprocessing        : 0.31
% 1.90/1.21  Parsing              : 0.17
% 1.90/1.21  CNF conversion       : 0.02
% 1.90/1.21  Main loop            : 0.10
% 1.90/1.21  Inferencing          : 0.04
% 1.90/1.21  Reduction            : 0.03
% 1.90/1.21  Demodulation         : 0.02
% 1.90/1.22  BG Simplification    : 0.01
% 1.90/1.22  Subsumption          : 0.01
% 1.90/1.22  Abstraction          : 0.00
% 1.90/1.22  MUC search           : 0.00
% 1.90/1.22  Cooper               : 0.00
% 1.90/1.22  Total                : 0.43
% 1.90/1.22  Index Insertion      : 0.00
% 1.90/1.22  Index Deletion       : 0.00
% 1.90/1.22  Index Matching       : 0.00
% 1.90/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
