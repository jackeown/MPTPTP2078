%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:09 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   35 (  46 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :    5
%              Number of atoms          :   60 ( 111 expanded)
%              Number of equality atoms :    8 (  16 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tops_1 > v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v3_pre_topc(B,A)
                & v3_tops_1(B,A) )
             => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_tops_1)).

tff(f_42,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( r1_tarski(C,B)
                    & v3_pre_topc(C,A) )
                 => C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_30,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_28,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    v3_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_40,plain,(
    ! [B_20,A_21] :
      ( v2_tops_1(B_20,A_21)
      | ~ v3_tops_1(B_20,A_21)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_43,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | ~ v3_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_40])).

tff(c_46,plain,(
    v2_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_22,c_43])).

tff(c_24,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_82,plain,(
    ! [C_32,A_33,B_34] :
      ( k1_xboole_0 = C_32
      | ~ v3_pre_topc(C_32,A_33)
      | ~ r1_tarski(C_32,B_34)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ v2_tops_1(B_34,A_33)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_86,plain,(
    ! [B_35,A_36] :
      ( k1_xboole_0 = B_35
      | ~ v3_pre_topc(B_35,A_36)
      | ~ v2_tops_1(B_35,A_36)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36) ) ),
    inference(resolution,[status(thm)],[c_6,c_82])).

tff(c_92,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_86])).

tff(c_96,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_46,c_24,c_92])).

tff(c_98,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_96])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:43:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.17  
% 1.86/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.17  %$ v3_tops_1 > v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.86/1.17  
% 1.86/1.17  %Foreground sorts:
% 1.86/1.17  
% 1.86/1.17  
% 1.86/1.17  %Background operators:
% 1.86/1.17  
% 1.86/1.17  
% 1.86/1.17  %Foreground operators:
% 1.86/1.17  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 1.86/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.86/1.17  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 1.86/1.17  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.86/1.17  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 1.86/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.86/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.86/1.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.86/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.17  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.86/1.17  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.86/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.86/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.86/1.18  
% 1.86/1.19  tff(f_74, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tops_1(B, A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_tops_1)).
% 1.86/1.19  tff(f_42, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_tops_1)).
% 1.86/1.19  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.86/1.19  tff(f_60, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 1.86/1.19  tff(c_20, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.86/1.19  tff(c_30, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.86/1.19  tff(c_28, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.86/1.19  tff(c_22, plain, (v3_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.86/1.19  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.86/1.19  tff(c_40, plain, (![B_20, A_21]: (v2_tops_1(B_20, A_21) | ~v3_tops_1(B_20, A_21) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.86/1.19  tff(c_43, plain, (v2_tops_1('#skF_3', '#skF_2') | ~v3_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_40])).
% 1.86/1.19  tff(c_46, plain, (v2_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_22, c_43])).
% 1.86/1.19  tff(c_24, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.86/1.19  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.86/1.19  tff(c_82, plain, (![C_32, A_33, B_34]: (k1_xboole_0=C_32 | ~v3_pre_topc(C_32, A_33) | ~r1_tarski(C_32, B_34) | ~m1_subset_1(C_32, k1_zfmisc_1(u1_struct_0(A_33))) | ~v2_tops_1(B_34, A_33) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.86/1.19  tff(c_86, plain, (![B_35, A_36]: (k1_xboole_0=B_35 | ~v3_pre_topc(B_35, A_36) | ~v2_tops_1(B_35, A_36) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36) | ~v2_pre_topc(A_36))), inference(resolution, [status(thm)], [c_6, c_82])).
% 1.86/1.19  tff(c_92, plain, (k1_xboole_0='#skF_3' | ~v3_pre_topc('#skF_3', '#skF_2') | ~v2_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_86])).
% 1.86/1.19  tff(c_96, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_46, c_24, c_92])).
% 1.86/1.19  tff(c_98, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_96])).
% 1.86/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.19  
% 1.86/1.19  Inference rules
% 1.86/1.19  ----------------------
% 1.86/1.19  #Ref     : 0
% 1.86/1.19  #Sup     : 12
% 1.86/1.19  #Fact    : 0
% 1.86/1.19  #Define  : 0
% 1.86/1.19  #Split   : 0
% 1.86/1.19  #Chain   : 0
% 1.86/1.19  #Close   : 0
% 1.86/1.19  
% 1.86/1.19  Ordering : KBO
% 1.86/1.19  
% 1.86/1.19  Simplification rules
% 1.86/1.19  ----------------------
% 1.86/1.19  #Subsume      : 0
% 1.86/1.19  #Demod        : 18
% 1.86/1.19  #Tautology    : 5
% 1.86/1.19  #SimpNegUnit  : 1
% 1.86/1.19  #BackRed      : 0
% 1.86/1.19  
% 1.86/1.19  #Partial instantiations: 0
% 1.86/1.19  #Strategies tried      : 1
% 1.86/1.19  
% 1.86/1.19  Timing (in seconds)
% 1.86/1.19  ----------------------
% 1.86/1.19  Preprocessing        : 0.29
% 1.86/1.19  Parsing              : 0.15
% 1.86/1.19  CNF conversion       : 0.02
% 1.86/1.19  Main loop            : 0.13
% 1.86/1.19  Inferencing          : 0.05
% 1.86/1.19  Reduction            : 0.04
% 1.86/1.19  Demodulation         : 0.03
% 1.86/1.19  BG Simplification    : 0.01
% 1.86/1.19  Subsumption          : 0.02
% 1.86/1.19  Abstraction          : 0.01
% 1.86/1.19  MUC search           : 0.00
% 1.86/1.19  Cooper               : 0.00
% 1.86/1.19  Total                : 0.45
% 1.86/1.19  Index Insertion      : 0.00
% 1.86/1.19  Index Deletion       : 0.00
% 1.86/1.19  Index Matching       : 0.00
% 1.86/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
