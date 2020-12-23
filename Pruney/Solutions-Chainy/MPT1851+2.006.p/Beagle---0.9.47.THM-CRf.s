%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:58 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   42 (  80 expanded)
%              Number of leaves         :   18 (  36 expanded)
%              Depth                    :   14
%              Number of atoms          :   60 ( 173 expanded)
%              Number of equality atoms :   26 (  66 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > v2_tdlat_3 > l1_pre_topc > k2_tarski > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_56,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                & v2_tdlat_3(A) )
             => v2_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tex_2)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_tdlat_3(A)
      <=> u1_pre_topc(A) = k2_tarski(k1_xboole_0,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tdlat_3)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(c_20,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    v2_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ! [A_8] :
      ( k2_tarski(k1_xboole_0,u1_struct_0(A_8)) = u1_pre_topc(A_8)
      | ~ v2_tdlat_3(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    ~ v2_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [A_1] :
      ( m1_subset_1(u1_pre_topc(A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_44,plain,(
    ! [D_13,B_14,C_15,A_16] :
      ( D_13 = B_14
      | g1_pre_topc(C_15,D_13) != g1_pre_topc(A_16,B_14)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(k1_zfmisc_1(A_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_49,plain,(
    ! [B_17,A_18] :
      ( u1_pre_topc('#skF_2') = B_17
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(A_18,B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(A_18))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_44])).

tff(c_53,plain,(
    ! [A_1] :
      ( u1_pre_topc(A_1) = u1_pre_topc('#skF_2')
      | g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_49])).

tff(c_70,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_53])).

tff(c_72,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_70])).

tff(c_87,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_2])).

tff(c_91,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_87])).

tff(c_58,plain,(
    ! [C_19,A_20,D_21,B_22] :
      ( C_19 = A_20
      | g1_pre_topc(C_19,D_21) != g1_pre_topc(A_20,B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k1_zfmisc_1(A_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_62,plain,(
    ! [C_19,D_21] :
      ( u1_struct_0('#skF_2') = C_19
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_19,D_21)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_58])).

tff(c_99,plain,(
    ! [C_19,D_21] :
      ( u1_struct_0('#skF_2') = C_19
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_19,D_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_72,c_62])).

tff(c_102,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_99])).

tff(c_8,plain,(
    ! [A_8] :
      ( v2_tdlat_3(A_8)
      | k2_tarski(k1_xboole_0,u1_struct_0(A_8)) != u1_pre_topc(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_109,plain,
    ( v2_tdlat_3('#skF_2')
    | k2_tarski(k1_xboole_0,u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_8])).

tff(c_119,plain,
    ( v2_tdlat_3('#skF_2')
    | k2_tarski(k1_xboole_0,u1_struct_0('#skF_1')) != u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_72,c_109])).

tff(c_120,plain,(
    k2_tarski(k1_xboole_0,u1_struct_0('#skF_1')) != u1_pre_topc('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_119])).

tff(c_128,plain,
    ( ~ v2_tdlat_3('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_120])).

tff(c_132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_14,c_128])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:07:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.15  
% 1.63/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.15  %$ m1_subset_1 > v2_tdlat_3 > l1_pre_topc > k2_tarski > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.63/1.15  
% 1.63/1.15  %Foreground sorts:
% 1.63/1.15  
% 1.63/1.15  
% 1.63/1.15  %Background operators:
% 1.63/1.15  
% 1.63/1.15  
% 1.63/1.15  %Foreground operators:
% 1.63/1.15  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 1.63/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.15  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 1.63/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.63/1.15  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.63/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.63/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.63/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.15  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.63/1.15  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 1.63/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.63/1.15  
% 1.82/1.16  tff(f_56, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & v2_tdlat_3(A)) => v2_tdlat_3(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_tex_2)).
% 1.82/1.16  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => (v2_tdlat_3(A) <=> (u1_pre_topc(A) = k2_tarski(k1_xboole_0, u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tdlat_3)).
% 1.82/1.16  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 1.82/1.16  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 1.82/1.16  tff(c_20, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.82/1.16  tff(c_14, plain, (v2_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.82/1.16  tff(c_10, plain, (![A_8]: (k2_tarski(k1_xboole_0, u1_struct_0(A_8))=u1_pre_topc(A_8) | ~v2_tdlat_3(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.82/1.16  tff(c_12, plain, (~v2_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.82/1.16  tff(c_18, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.82/1.16  tff(c_2, plain, (![A_1]: (m1_subset_1(u1_pre_topc(A_1), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.82/1.16  tff(c_16, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.82/1.16  tff(c_44, plain, (![D_13, B_14, C_15, A_16]: (D_13=B_14 | g1_pre_topc(C_15, D_13)!=g1_pre_topc(A_16, B_14) | ~m1_subset_1(B_14, k1_zfmisc_1(k1_zfmisc_1(A_16))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.82/1.16  tff(c_49, plain, (![B_17, A_18]: (u1_pre_topc('#skF_2')=B_17 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(A_18, B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(k1_zfmisc_1(A_18))))), inference(superposition, [status(thm), theory('equality')], [c_16, c_44])).
% 1.82/1.16  tff(c_53, plain, (![A_1]: (u1_pre_topc(A_1)=u1_pre_topc('#skF_2') | g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(A_1))), inference(resolution, [status(thm)], [c_2, c_49])).
% 1.82/1.16  tff(c_70, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_53])).
% 1.82/1.16  tff(c_72, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_70])).
% 1.82/1.16  tff(c_87, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_72, c_2])).
% 1.82/1.16  tff(c_91, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_87])).
% 1.82/1.16  tff(c_58, plain, (![C_19, A_20, D_21, B_22]: (C_19=A_20 | g1_pre_topc(C_19, D_21)!=g1_pre_topc(A_20, B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(k1_zfmisc_1(A_20))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.82/1.16  tff(c_62, plain, (![C_19, D_21]: (u1_struct_0('#skF_2')=C_19 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(C_19, D_21) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_16, c_58])).
% 1.82/1.16  tff(c_99, plain, (![C_19, D_21]: (u1_struct_0('#skF_2')=C_19 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(C_19, D_21))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_72, c_62])).
% 1.82/1.16  tff(c_102, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_99])).
% 1.82/1.16  tff(c_8, plain, (![A_8]: (v2_tdlat_3(A_8) | k2_tarski(k1_xboole_0, u1_struct_0(A_8))!=u1_pre_topc(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.82/1.16  tff(c_109, plain, (v2_tdlat_3('#skF_2') | k2_tarski(k1_xboole_0, u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_102, c_8])).
% 1.82/1.16  tff(c_119, plain, (v2_tdlat_3('#skF_2') | k2_tarski(k1_xboole_0, u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_72, c_109])).
% 1.82/1.16  tff(c_120, plain, (k2_tarski(k1_xboole_0, u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_12, c_119])).
% 1.82/1.16  tff(c_128, plain, (~v2_tdlat_3('#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10, c_120])).
% 1.82/1.16  tff(c_132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_14, c_128])).
% 1.82/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.16  
% 1.82/1.16  Inference rules
% 1.82/1.16  ----------------------
% 1.82/1.16  #Ref     : 4
% 1.82/1.16  #Sup     : 22
% 1.82/1.16  #Fact    : 0
% 1.82/1.16  #Define  : 0
% 1.82/1.16  #Split   : 0
% 1.82/1.16  #Chain   : 0
% 1.82/1.16  #Close   : 0
% 1.82/1.16  
% 1.82/1.16  Ordering : KBO
% 1.82/1.16  
% 1.82/1.16  Simplification rules
% 1.82/1.16  ----------------------
% 1.82/1.16  #Subsume      : 3
% 1.82/1.16  #Demod        : 18
% 1.82/1.16  #Tautology    : 13
% 1.82/1.16  #SimpNegUnit  : 1
% 1.82/1.16  #BackRed      : 5
% 1.82/1.16  
% 1.82/1.16  #Partial instantiations: 0
% 1.82/1.16  #Strategies tried      : 1
% 1.82/1.16  
% 1.82/1.16  Timing (in seconds)
% 1.82/1.16  ----------------------
% 1.82/1.16  Preprocessing        : 0.27
% 1.82/1.16  Parsing              : 0.15
% 1.82/1.17  CNF conversion       : 0.02
% 1.82/1.17  Main loop            : 0.12
% 1.82/1.17  Inferencing          : 0.05
% 1.82/1.17  Reduction            : 0.04
% 1.82/1.17  Demodulation         : 0.03
% 1.82/1.17  BG Simplification    : 0.01
% 1.82/1.17  Subsumption          : 0.02
% 1.82/1.17  Abstraction          : 0.01
% 1.82/1.17  MUC search           : 0.00
% 1.82/1.17  Cooper               : 0.00
% 1.82/1.17  Total                : 0.42
% 1.82/1.17  Index Insertion      : 0.00
% 1.82/1.17  Index Deletion       : 0.00
% 1.82/1.17  Index Matching       : 0.00
% 1.82/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
