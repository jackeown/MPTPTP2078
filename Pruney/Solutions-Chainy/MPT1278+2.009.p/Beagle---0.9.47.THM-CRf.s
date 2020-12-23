%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:09 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   42 (  71 expanded)
%              Number of leaves         :   19 (  35 expanded)
%              Depth                    :    6
%              Number of atoms          :   74 ( 196 expanded)
%              Number of equality atoms :   13 (  34 expanded)
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

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v3_pre_topc(B,A)
                & v3_tops_1(B,A) )
             => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_tops_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_36,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_tops_1)).

tff(f_57,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_20,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_16,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_23,plain,(
    ! [A_23,B_24] :
      ( k1_tops_1(A_23,B_24) = k1_xboole_0
      | ~ v2_tops_1(B_24,A_23)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_23])).

tff(c_29,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_26])).

tff(c_30,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_29])).

tff(c_22,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_14,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_39,plain,(
    ! [B_27,A_28] :
      ( v2_tops_1(B_27,A_28)
      | ~ v3_tops_1(B_27,A_28)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_42,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_39])).

tff(c_45,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_14,c_42])).

tff(c_47,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_45])).

tff(c_48,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_29])).

tff(c_6,plain,(
    ! [B_12,D_18,C_16,A_4] :
      ( k1_tops_1(B_12,D_18) = D_18
      | ~ v3_pre_topc(D_18,B_12)
      | ~ m1_subset_1(D_18,k1_zfmisc_1(u1_struct_0(B_12)))
      | ~ m1_subset_1(C_16,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_pre_topc(B_12)
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_69,plain,(
    ! [C_33,A_34] :
      ( ~ m1_subset_1(C_33,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34) ) ),
    inference(splitLeft,[status(thm)],[c_6])).

tff(c_72,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_69])).

tff(c_76,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_72])).

tff(c_78,plain,(
    ! [B_35,D_36] :
      ( k1_tops_1(B_35,D_36) = D_36
      | ~ v3_pre_topc(D_36,B_35)
      | ~ m1_subset_1(D_36,k1_zfmisc_1(u1_struct_0(B_35)))
      | ~ l1_pre_topc(B_35) ) ),
    inference(splitRight,[status(thm)],[c_6])).

tff(c_81,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_78])).

tff(c_84,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_48,c_81])).

tff(c_86,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_84])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:43:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.16  
% 2.04/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.16  %$ v3_tops_1 > v3_pre_topc > v2_tops_1 > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.04/1.16  
% 2.04/1.16  %Foreground sorts:
% 2.04/1.16  
% 2.04/1.16  
% 2.04/1.16  %Background operators:
% 2.04/1.16  
% 2.04/1.16  
% 2.04/1.16  %Foreground operators:
% 2.04/1.16  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.04/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.04/1.16  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 2.04/1.16  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.04/1.16  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 2.04/1.16  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.04/1.16  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.16  tff('#skF_1', type, '#skF_1': $i).
% 2.04/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.04/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.16  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.04/1.16  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.04/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.04/1.16  
% 2.04/1.17  tff(f_80, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tops_1(B, A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_tops_1)).
% 2.04/1.17  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 2.04/1.17  tff(f_36, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_tops_1)).
% 2.04/1.17  tff(f_57, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 2.04/1.17  tff(c_12, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.04/1.17  tff(c_20, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.04/1.17  tff(c_16, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.04/1.17  tff(c_18, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.04/1.17  tff(c_23, plain, (![A_23, B_24]: (k1_tops_1(A_23, B_24)=k1_xboole_0 | ~v2_tops_1(B_24, A_23) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.04/1.17  tff(c_26, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_23])).
% 2.04/1.17  tff(c_29, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_26])).
% 2.04/1.17  tff(c_30, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_29])).
% 2.04/1.17  tff(c_22, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.04/1.17  tff(c_14, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.04/1.17  tff(c_39, plain, (![B_27, A_28]: (v2_tops_1(B_27, A_28) | ~v3_tops_1(B_27, A_28) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.04/1.17  tff(c_42, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_39])).
% 2.04/1.17  tff(c_45, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_14, c_42])).
% 2.04/1.17  tff(c_47, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_45])).
% 2.04/1.17  tff(c_48, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_29])).
% 2.04/1.17  tff(c_6, plain, (![B_12, D_18, C_16, A_4]: (k1_tops_1(B_12, D_18)=D_18 | ~v3_pre_topc(D_18, B_12) | ~m1_subset_1(D_18, k1_zfmisc_1(u1_struct_0(B_12))) | ~m1_subset_1(C_16, k1_zfmisc_1(u1_struct_0(A_4))) | ~l1_pre_topc(B_12) | ~l1_pre_topc(A_4) | ~v2_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.04/1.17  tff(c_69, plain, (![C_33, A_34]: (~m1_subset_1(C_33, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34))), inference(splitLeft, [status(thm)], [c_6])).
% 2.04/1.17  tff(c_72, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_69])).
% 2.04/1.17  tff(c_76, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_72])).
% 2.04/1.17  tff(c_78, plain, (![B_35, D_36]: (k1_tops_1(B_35, D_36)=D_36 | ~v3_pre_topc(D_36, B_35) | ~m1_subset_1(D_36, k1_zfmisc_1(u1_struct_0(B_35))) | ~l1_pre_topc(B_35))), inference(splitRight, [status(thm)], [c_6])).
% 2.04/1.17  tff(c_81, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_78])).
% 2.04/1.17  tff(c_84, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_48, c_81])).
% 2.04/1.17  tff(c_86, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_84])).
% 2.04/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.17  
% 2.04/1.17  Inference rules
% 2.04/1.17  ----------------------
% 2.04/1.17  #Ref     : 0
% 2.04/1.17  #Sup     : 9
% 2.04/1.17  #Fact    : 0
% 2.04/1.17  #Define  : 0
% 2.04/1.17  #Split   : 2
% 2.04/1.17  #Chain   : 0
% 2.04/1.17  #Close   : 0
% 2.04/1.17  
% 2.04/1.17  Ordering : KBO
% 2.04/1.17  
% 2.04/1.17  Simplification rules
% 2.04/1.17  ----------------------
% 2.04/1.17  #Subsume      : 1
% 2.04/1.17  #Demod        : 17
% 2.04/1.17  #Tautology    : 4
% 2.04/1.17  #SimpNegUnit  : 3
% 2.04/1.17  #BackRed      : 0
% 2.04/1.17  
% 2.04/1.17  #Partial instantiations: 0
% 2.04/1.17  #Strategies tried      : 1
% 2.04/1.17  
% 2.04/1.17  Timing (in seconds)
% 2.04/1.17  ----------------------
% 2.04/1.17  Preprocessing        : 0.29
% 2.04/1.17  Parsing              : 0.16
% 2.04/1.17  CNF conversion       : 0.02
% 2.04/1.17  Main loop            : 0.11
% 2.04/1.17  Inferencing          : 0.04
% 2.04/1.17  Reduction            : 0.03
% 2.04/1.17  Demodulation         : 0.02
% 2.04/1.17  BG Simplification    : 0.01
% 2.04/1.17  Subsumption          : 0.02
% 2.04/1.17  Abstraction          : 0.00
% 2.04/1.17  MUC search           : 0.00
% 2.04/1.17  Cooper               : 0.00
% 2.04/1.17  Total                : 0.42
% 2.04/1.17  Index Insertion      : 0.00
% 2.04/1.17  Index Deletion       : 0.00
% 2.04/1.17  Index Matching       : 0.00
% 2.04/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
