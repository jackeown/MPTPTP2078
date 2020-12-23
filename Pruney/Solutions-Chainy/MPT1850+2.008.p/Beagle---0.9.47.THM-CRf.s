%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:57 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 101 expanded)
%              Number of leaves         :   17 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :   67 ( 231 expanded)
%              Number of equality atoms :   30 (  95 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > v1_tdlat_3 > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k9_setfam_1 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_56,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                & v1_tdlat_3(A) )
             => v1_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tex_2)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_tdlat_3(A)
      <=> u1_pre_topc(A) = k9_setfam_1(u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tdlat_3)).

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
    v1_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ! [A_8] :
      ( k9_setfam_1(u1_struct_0(A_8)) = u1_pre_topc(A_8)
      | ~ v1_tdlat_3(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    ~ v1_tdlat_3('#skF_2') ),
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
    ! [C_13,A_14,D_15,B_16] :
      ( C_13 = A_14
      | g1_pre_topc(C_13,D_15) != g1_pre_topc(A_14,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(k1_zfmisc_1(A_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_49,plain,(
    ! [A_17,B_18] :
      ( u1_struct_0('#skF_2') = A_17
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(A_17,B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k1_zfmisc_1(A_17))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_44])).

tff(c_53,plain,(
    ! [A_1] :
      ( u1_struct_0(A_1) = u1_struct_0('#skF_2')
      | g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_49])).

tff(c_70,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_53])).

tff(c_72,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_70])).

tff(c_8,plain,(
    ! [A_8] :
      ( v1_tdlat_3(A_8)
      | k9_setfam_1(u1_struct_0(A_8)) != u1_pre_topc(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_93,plain,
    ( v1_tdlat_3('#skF_2')
    | k9_setfam_1(u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_8])).

tff(c_101,plain,
    ( v1_tdlat_3('#skF_2')
    | k9_setfam_1(u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_93])).

tff(c_102,plain,(
    k9_setfam_1(u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_101])).

tff(c_106,plain,
    ( u1_pre_topc('#skF_2') != u1_pre_topc('#skF_1')
    | ~ v1_tdlat_3('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_102])).

tff(c_108,plain,(
    u1_pre_topc('#skF_2') != u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_14,c_106])).

tff(c_58,plain,(
    ! [D_19,B_20,C_21,A_22] :
      ( D_19 = B_20
      | g1_pre_topc(C_21,D_19) != g1_pre_topc(A_22,B_20)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k1_zfmisc_1(A_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_62,plain,(
    ! [D_19,C_21] :
      ( u1_pre_topc('#skF_2') = D_19
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_21,D_19)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_58])).

tff(c_109,plain,(
    ! [D_19,C_21] :
      ( u1_pre_topc('#skF_2') = D_19
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_21,D_19)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_62])).

tff(c_110,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_90,plain,
    ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_2])).

tff(c_99,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_90])).

tff(c_111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_99])).

tff(c_112,plain,(
    ! [D_19,C_21] :
      ( u1_pre_topc('#skF_2') = D_19
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_21,D_19) ) ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_136,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_112])).

tff(c_138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n022.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 16:21:11 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.13  
% 1.67/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.14  %$ m1_subset_1 > v1_tdlat_3 > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k9_setfam_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.67/1.14  
% 1.67/1.14  %Foreground sorts:
% 1.67/1.14  
% 1.67/1.14  
% 1.67/1.14  %Background operators:
% 1.67/1.14  
% 1.67/1.14  
% 1.67/1.14  %Foreground operators:
% 1.67/1.14  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 1.67/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.14  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 1.67/1.14  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.67/1.14  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 1.67/1.14  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 1.67/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.67/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.14  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.67/1.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.67/1.14  
% 1.67/1.15  tff(f_56, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & v1_tdlat_3(A)) => v1_tdlat_3(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_tex_2)).
% 1.67/1.15  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => (v1_tdlat_3(A) <=> (u1_pre_topc(A) = k9_setfam_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tdlat_3)).
% 1.67/1.15  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 1.67/1.15  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 1.67/1.15  tff(c_20, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.67/1.15  tff(c_14, plain, (v1_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.67/1.15  tff(c_10, plain, (![A_8]: (k9_setfam_1(u1_struct_0(A_8))=u1_pre_topc(A_8) | ~v1_tdlat_3(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.67/1.15  tff(c_12, plain, (~v1_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.67/1.15  tff(c_18, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.67/1.15  tff(c_2, plain, (![A_1]: (m1_subset_1(u1_pre_topc(A_1), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.67/1.15  tff(c_16, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.67/1.15  tff(c_44, plain, (![C_13, A_14, D_15, B_16]: (C_13=A_14 | g1_pre_topc(C_13, D_15)!=g1_pre_topc(A_14, B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(k1_zfmisc_1(A_14))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.67/1.15  tff(c_49, plain, (![A_17, B_18]: (u1_struct_0('#skF_2')=A_17 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(A_17, B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(k1_zfmisc_1(A_17))))), inference(superposition, [status(thm), theory('equality')], [c_16, c_44])).
% 1.67/1.15  tff(c_53, plain, (![A_1]: (u1_struct_0(A_1)=u1_struct_0('#skF_2') | g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(A_1))), inference(resolution, [status(thm)], [c_2, c_49])).
% 1.67/1.15  tff(c_70, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_53])).
% 1.67/1.15  tff(c_72, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_70])).
% 1.67/1.15  tff(c_8, plain, (![A_8]: (v1_tdlat_3(A_8) | k9_setfam_1(u1_struct_0(A_8))!=u1_pre_topc(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.67/1.15  tff(c_93, plain, (v1_tdlat_3('#skF_2') | k9_setfam_1(u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_72, c_8])).
% 1.67/1.15  tff(c_101, plain, (v1_tdlat_3('#skF_2') | k9_setfam_1(u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_93])).
% 1.67/1.15  tff(c_102, plain, (k9_setfam_1(u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_12, c_101])).
% 1.67/1.15  tff(c_106, plain, (u1_pre_topc('#skF_2')!=u1_pre_topc('#skF_1') | ~v1_tdlat_3('#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10, c_102])).
% 1.67/1.15  tff(c_108, plain, (u1_pre_topc('#skF_2')!=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_14, c_106])).
% 1.67/1.15  tff(c_58, plain, (![D_19, B_20, C_21, A_22]: (D_19=B_20 | g1_pre_topc(C_21, D_19)!=g1_pre_topc(A_22, B_20) | ~m1_subset_1(B_20, k1_zfmisc_1(k1_zfmisc_1(A_22))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.67/1.15  tff(c_62, plain, (![D_19, C_21]: (u1_pre_topc('#skF_2')=D_19 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(C_21, D_19) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_16, c_58])).
% 1.67/1.15  tff(c_109, plain, (![D_19, C_21]: (u1_pre_topc('#skF_2')=D_19 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(C_21, D_19) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_62])).
% 1.67/1.15  tff(c_110, plain, (~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitLeft, [status(thm)], [c_109])).
% 1.67/1.15  tff(c_90, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_72, c_2])).
% 1.67/1.15  tff(c_99, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_90])).
% 1.67/1.15  tff(c_111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_99])).
% 1.67/1.15  tff(c_112, plain, (![D_19, C_21]: (u1_pre_topc('#skF_2')=D_19 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(C_21, D_19))), inference(splitRight, [status(thm)], [c_109])).
% 1.67/1.15  tff(c_136, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_112])).
% 1.67/1.15  tff(c_138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_136])).
% 1.67/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.15  
% 1.67/1.15  Inference rules
% 1.67/1.15  ----------------------
% 1.67/1.15  #Ref     : 4
% 1.67/1.15  #Sup     : 25
% 1.67/1.15  #Fact    : 0
% 1.67/1.15  #Define  : 0
% 1.67/1.15  #Split   : 1
% 1.67/1.15  #Chain   : 0
% 1.67/1.15  #Close   : 0
% 1.67/1.15  
% 1.67/1.15  Ordering : KBO
% 1.67/1.15  
% 1.67/1.15  Simplification rules
% 1.67/1.15  ----------------------
% 1.67/1.15  #Subsume      : 5
% 1.67/1.15  #Demod        : 13
% 1.67/1.15  #Tautology    : 14
% 1.67/1.15  #SimpNegUnit  : 3
% 1.67/1.15  #BackRed      : 3
% 1.67/1.15  
% 1.67/1.15  #Partial instantiations: 0
% 1.67/1.15  #Strategies tried      : 1
% 1.67/1.15  
% 1.67/1.15  Timing (in seconds)
% 1.67/1.15  ----------------------
% 1.67/1.15  Preprocessing        : 0.26
% 1.67/1.15  Parsing              : 0.14
% 1.67/1.15  CNF conversion       : 0.02
% 1.67/1.15  Main loop            : 0.14
% 1.67/1.15  Inferencing          : 0.05
% 1.67/1.15  Reduction            : 0.04
% 1.67/1.15  Demodulation         : 0.03
% 1.67/1.15  BG Simplification    : 0.01
% 1.67/1.15  Subsumption          : 0.03
% 1.67/1.15  Abstraction          : 0.01
% 1.67/1.15  MUC search           : 0.00
% 1.67/1.15  Cooper               : 0.00
% 1.67/1.15  Total                : 0.43
% 1.67/1.15  Index Insertion      : 0.00
% 1.67/1.15  Index Deletion       : 0.00
% 1.67/1.15  Index Matching       : 0.00
% 1.67/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
