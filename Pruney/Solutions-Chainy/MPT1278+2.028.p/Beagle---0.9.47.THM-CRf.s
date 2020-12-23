%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:12 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   46 (  65 expanded)
%              Number of leaves         :   22 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   78 ( 166 expanded)
%              Number of equality atoms :   12 (  26 expanded)
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

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v3_pre_topc(B,A)
                & v3_tops_1(B,A) )
             => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_tops_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & v2_tops_1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v1_xboole_0(k1_tops_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_tops_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_63,axiom,(
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

tff(c_14,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_18,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_16,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_35,plain,(
    ! [B_27,A_28] :
      ( v2_tops_1(B_27,A_28)
      | ~ v3_tops_1(B_27,A_28)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_38,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_35])).

tff(c_41,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_16,c_38])).

tff(c_42,plain,(
    ! [A_29,B_30] :
      ( v1_xboole_0(k1_tops_1(A_29,B_30))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ v2_tops_1(B_30,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_45,plain,
    ( v1_xboole_0(k1_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_42])).

tff(c_48,plain,(
    v1_xboole_0(k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_41,c_45])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_25,plain,(
    ! [B_24,A_25] :
      ( ~ v1_xboole_0(B_24)
      | B_24 = A_25
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_28,plain,(
    ! [A_25] :
      ( k1_xboole_0 = A_25
      | ~ v1_xboole_0(A_25) ) ),
    inference(resolution,[status(thm)],[c_2,c_25])).

tff(c_54,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_28])).

tff(c_24,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_10,plain,(
    ! [B_13,D_19,C_17,A_5] :
      ( k1_tops_1(B_13,D_19) = D_19
      | ~ v3_pre_topc(D_19,B_13)
      | ~ m1_subset_1(D_19,k1_zfmisc_1(u1_struct_0(B_13)))
      | ~ m1_subset_1(C_17,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(B_13)
      | ~ l1_pre_topc(A_5)
      | ~ v2_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_64,plain,(
    ! [C_31,A_32] :
      ( ~ m1_subset_1(C_31,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32) ) ),
    inference(splitLeft,[status(thm)],[c_10])).

tff(c_67,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_64])).

tff(c_71,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_67])).

tff(c_73,plain,(
    ! [B_33,D_34] :
      ( k1_tops_1(B_33,D_34) = D_34
      | ~ v3_pre_topc(D_34,B_33)
      | ~ m1_subset_1(D_34,k1_zfmisc_1(u1_struct_0(B_33)))
      | ~ l1_pre_topc(B_33) ) ),
    inference(splitRight,[status(thm)],[c_10])).

tff(c_76,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_73])).

tff(c_79,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_54,c_76])).

tff(c_81,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_79])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:19:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.14  
% 1.70/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.14  %$ v3_tops_1 > v3_pre_topc > v2_tops_1 > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.70/1.14  
% 1.70/1.14  %Foreground sorts:
% 1.70/1.14  
% 1.70/1.14  
% 1.70/1.14  %Background operators:
% 1.70/1.14  
% 1.70/1.14  
% 1.70/1.14  %Foreground operators:
% 1.70/1.14  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 1.70/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.70/1.14  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 1.70/1.14  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.70/1.14  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 1.70/1.14  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 1.70/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.70/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.70/1.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.70/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.14  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.70/1.14  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.70/1.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.70/1.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.70/1.14  
% 1.70/1.15  tff(f_86, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tops_1(B, A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_tops_1)).
% 1.70/1.15  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_tops_1)).
% 1.70/1.15  tff(f_42, axiom, (![A, B]: (((l1_pre_topc(A) & v2_tops_1(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v1_xboole_0(k1_tops_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc13_tops_1)).
% 1.70/1.15  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.70/1.15  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 1.70/1.15  tff(f_63, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 1.70/1.15  tff(c_14, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.70/1.15  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.70/1.15  tff(c_18, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.70/1.15  tff(c_16, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.70/1.15  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.70/1.15  tff(c_35, plain, (![B_27, A_28]: (v2_tops_1(B_27, A_28) | ~v3_tops_1(B_27, A_28) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.70/1.15  tff(c_38, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_35])).
% 1.70/1.15  tff(c_41, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_16, c_38])).
% 1.70/1.15  tff(c_42, plain, (![A_29, B_30]: (v1_xboole_0(k1_tops_1(A_29, B_30)) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_29))) | ~v2_tops_1(B_30, A_29) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.70/1.15  tff(c_45, plain, (v1_xboole_0(k1_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_42])).
% 1.70/1.15  tff(c_48, plain, (v1_xboole_0(k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_41, c_45])).
% 1.70/1.15  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.70/1.15  tff(c_25, plain, (![B_24, A_25]: (~v1_xboole_0(B_24) | B_24=A_25 | ~v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.70/1.15  tff(c_28, plain, (![A_25]: (k1_xboole_0=A_25 | ~v1_xboole_0(A_25))), inference(resolution, [status(thm)], [c_2, c_25])).
% 1.70/1.15  tff(c_54, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_28])).
% 1.70/1.15  tff(c_24, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.70/1.15  tff(c_10, plain, (![B_13, D_19, C_17, A_5]: (k1_tops_1(B_13, D_19)=D_19 | ~v3_pre_topc(D_19, B_13) | ~m1_subset_1(D_19, k1_zfmisc_1(u1_struct_0(B_13))) | ~m1_subset_1(C_17, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(B_13) | ~l1_pre_topc(A_5) | ~v2_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.70/1.15  tff(c_64, plain, (![C_31, A_32]: (~m1_subset_1(C_31, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32))), inference(splitLeft, [status(thm)], [c_10])).
% 1.70/1.15  tff(c_67, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_64])).
% 1.70/1.15  tff(c_71, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_67])).
% 1.70/1.15  tff(c_73, plain, (![B_33, D_34]: (k1_tops_1(B_33, D_34)=D_34 | ~v3_pre_topc(D_34, B_33) | ~m1_subset_1(D_34, k1_zfmisc_1(u1_struct_0(B_33))) | ~l1_pre_topc(B_33))), inference(splitRight, [status(thm)], [c_10])).
% 1.70/1.15  tff(c_76, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_73])).
% 1.70/1.15  tff(c_79, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_54, c_76])).
% 1.70/1.15  tff(c_81, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_79])).
% 1.70/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.15  
% 1.70/1.15  Inference rules
% 1.70/1.15  ----------------------
% 1.70/1.15  #Ref     : 0
% 1.70/1.15  #Sup     : 10
% 1.70/1.15  #Fact    : 0
% 1.70/1.15  #Define  : 0
% 1.70/1.15  #Split   : 1
% 1.70/1.15  #Chain   : 0
% 1.70/1.15  #Close   : 0
% 1.70/1.15  
% 1.70/1.15  Ordering : KBO
% 1.70/1.15  
% 1.70/1.15  Simplification rules
% 1.70/1.15  ----------------------
% 1.70/1.15  #Subsume      : 1
% 1.70/1.15  #Demod        : 12
% 1.70/1.15  #Tautology    : 4
% 1.70/1.15  #SimpNegUnit  : 1
% 1.70/1.15  #BackRed      : 1
% 1.70/1.15  
% 1.70/1.15  #Partial instantiations: 0
% 1.70/1.15  #Strategies tried      : 1
% 1.70/1.15  
% 1.70/1.15  Timing (in seconds)
% 1.70/1.15  ----------------------
% 1.70/1.15  Preprocessing        : 0.29
% 1.70/1.15  Parsing              : 0.16
% 1.70/1.15  CNF conversion       : 0.02
% 1.70/1.15  Main loop            : 0.10
% 1.70/1.15  Inferencing          : 0.04
% 1.70/1.15  Reduction            : 0.03
% 1.70/1.15  Demodulation         : 0.02
% 1.70/1.15  BG Simplification    : 0.01
% 1.70/1.15  Subsumption          : 0.02
% 1.70/1.15  Abstraction          : 0.00
% 1.70/1.15  MUC search           : 0.00
% 1.70/1.15  Cooper               : 0.00
% 1.70/1.15  Total                : 0.42
% 1.70/1.15  Index Insertion      : 0.00
% 1.70/1.15  Index Deletion       : 0.00
% 1.70/1.16  Index Matching       : 0.00
% 1.70/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
