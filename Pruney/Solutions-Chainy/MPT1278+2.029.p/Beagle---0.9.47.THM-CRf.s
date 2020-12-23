%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:12 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   43 (  62 expanded)
%              Number of leaves         :   21 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   72 ( 160 expanded)
%              Number of equality atoms :   11 (  25 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tops_1 > v3_pre_topc > v2_tops_1 > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v3_pre_topc(B,A)
                & v3_tops_1(B,A) )
             => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_tops_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & v2_tops_1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v1_xboole_0(k1_tops_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_tops_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_58,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_20,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_16,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_14,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_24,plain,(
    ! [B_24,A_25] :
      ( v2_tops_1(B_24,A_25)
      | ~ v3_tops_1(B_24,A_25)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_27,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_24])).

tff(c_30,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_14,c_27])).

tff(c_31,plain,(
    ! [A_26,B_27] :
      ( v1_xboole_0(k1_tops_1(A_26,B_27))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ v2_tops_1(B_27,A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_34,plain,
    ( v1_xboole_0(k1_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_31])).

tff(c_37,plain,(
    v1_xboole_0(k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_30,c_34])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_41,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_37,c_2])).

tff(c_22,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_8,plain,(
    ! [B_12,D_18,C_16,A_4] :
      ( k1_tops_1(B_12,D_18) = D_18
      | ~ v3_pre_topc(D_18,B_12)
      | ~ m1_subset_1(D_18,k1_zfmisc_1(u1_struct_0(B_12)))
      | ~ m1_subset_1(C_16,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_pre_topc(B_12)
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_53,plain,(
    ! [C_28,A_29] :
      ( ~ m1_subset_1(C_28,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29) ) ),
    inference(splitLeft,[status(thm)],[c_8])).

tff(c_56,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_53])).

tff(c_60,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_56])).

tff(c_62,plain,(
    ! [B_30,D_31] :
      ( k1_tops_1(B_30,D_31) = D_31
      | ~ v3_pre_topc(D_31,B_30)
      | ~ m1_subset_1(D_31,k1_zfmisc_1(u1_struct_0(B_30)))
      | ~ l1_pre_topc(B_30) ) ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_65,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_62])).

tff(c_68,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_41,c_65])).

tff(c_70,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:43:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.12  
% 1.86/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.12  %$ v3_tops_1 > v3_pre_topc > v2_tops_1 > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.86/1.12  
% 1.86/1.12  %Foreground sorts:
% 1.86/1.12  
% 1.86/1.12  
% 1.86/1.12  %Background operators:
% 1.86/1.12  
% 1.86/1.12  
% 1.86/1.12  %Foreground operators:
% 1.86/1.12  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 1.86/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.86/1.12  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 1.86/1.12  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.86/1.12  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 1.86/1.12  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 1.86/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.86/1.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.86/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.12  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.86/1.12  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.86/1.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.86/1.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.86/1.12  
% 1.86/1.13  tff(f_81, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tops_1(B, A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_tops_1)).
% 1.86/1.13  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_tops_1)).
% 1.86/1.13  tff(f_37, axiom, (![A, B]: (((l1_pre_topc(A) & v2_tops_1(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v1_xboole_0(k1_tops_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc13_tops_1)).
% 1.86/1.13  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.86/1.13  tff(f_58, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 1.86/1.13  tff(c_12, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.86/1.13  tff(c_20, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.86/1.13  tff(c_16, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.86/1.13  tff(c_14, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.86/1.13  tff(c_18, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.86/1.13  tff(c_24, plain, (![B_24, A_25]: (v2_tops_1(B_24, A_25) | ~v3_tops_1(B_24, A_25) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.86/1.13  tff(c_27, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_24])).
% 1.86/1.13  tff(c_30, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_14, c_27])).
% 1.86/1.13  tff(c_31, plain, (![A_26, B_27]: (v1_xboole_0(k1_tops_1(A_26, B_27)) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_26))) | ~v2_tops_1(B_27, A_26) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.86/1.13  tff(c_34, plain, (v1_xboole_0(k1_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_31])).
% 1.86/1.13  tff(c_37, plain, (v1_xboole_0(k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_30, c_34])).
% 1.86/1.13  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.86/1.13  tff(c_41, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_37, c_2])).
% 1.86/1.13  tff(c_22, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.86/1.13  tff(c_8, plain, (![B_12, D_18, C_16, A_4]: (k1_tops_1(B_12, D_18)=D_18 | ~v3_pre_topc(D_18, B_12) | ~m1_subset_1(D_18, k1_zfmisc_1(u1_struct_0(B_12))) | ~m1_subset_1(C_16, k1_zfmisc_1(u1_struct_0(A_4))) | ~l1_pre_topc(B_12) | ~l1_pre_topc(A_4) | ~v2_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.86/1.13  tff(c_53, plain, (![C_28, A_29]: (~m1_subset_1(C_28, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29) | ~v2_pre_topc(A_29))), inference(splitLeft, [status(thm)], [c_8])).
% 1.86/1.13  tff(c_56, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_53])).
% 1.86/1.13  tff(c_60, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_56])).
% 1.86/1.13  tff(c_62, plain, (![B_30, D_31]: (k1_tops_1(B_30, D_31)=D_31 | ~v3_pre_topc(D_31, B_30) | ~m1_subset_1(D_31, k1_zfmisc_1(u1_struct_0(B_30))) | ~l1_pre_topc(B_30))), inference(splitRight, [status(thm)], [c_8])).
% 1.86/1.13  tff(c_65, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_62])).
% 1.86/1.13  tff(c_68, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_41, c_65])).
% 1.86/1.13  tff(c_70, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_68])).
% 1.86/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.13  
% 1.86/1.13  Inference rules
% 1.86/1.13  ----------------------
% 1.86/1.13  #Ref     : 0
% 1.86/1.13  #Sup     : 8
% 1.86/1.13  #Fact    : 0
% 1.86/1.13  #Define  : 0
% 1.86/1.13  #Split   : 1
% 1.86/1.13  #Chain   : 0
% 1.86/1.13  #Close   : 0
% 1.86/1.13  
% 1.86/1.13  Ordering : KBO
% 1.86/1.13  
% 1.86/1.13  Simplification rules
% 1.86/1.13  ----------------------
% 1.86/1.13  #Subsume      : 0
% 1.86/1.13  #Demod        : 10
% 1.86/1.13  #Tautology    : 3
% 1.86/1.13  #SimpNegUnit  : 1
% 1.86/1.13  #BackRed      : 1
% 1.86/1.13  
% 1.86/1.13  #Partial instantiations: 0
% 1.86/1.13  #Strategies tried      : 1
% 1.86/1.13  
% 1.86/1.13  Timing (in seconds)
% 1.86/1.13  ----------------------
% 1.86/1.13  Preprocessing        : 0.29
% 1.86/1.13  Parsing              : 0.15
% 1.86/1.13  CNF conversion       : 0.02
% 1.86/1.13  Main loop            : 0.10
% 1.86/1.13  Inferencing          : 0.04
% 1.86/1.13  Reduction            : 0.03
% 1.86/1.14  Demodulation         : 0.02
% 1.86/1.14  BG Simplification    : 0.01
% 1.86/1.14  Subsumption          : 0.01
% 1.86/1.14  Abstraction          : 0.00
% 1.86/1.14  MUC search           : 0.00
% 1.86/1.14  Cooper               : 0.00
% 1.86/1.14  Total                : 0.41
% 1.86/1.14  Index Insertion      : 0.00
% 1.86/1.14  Index Deletion       : 0.00
% 1.86/1.14  Index Matching       : 0.00
% 1.86/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
