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
% DateTime   : Thu Dec  3 10:28:57 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   47 (  82 expanded)
%              Number of leaves         :   18 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :   77 ( 165 expanded)
%              Number of equality atoms :   32 (  61 expanded)
%              Maximal formula depth    :    8 (   4 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tex_2)).

tff(f_29,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_tdlat_3(A)
      <=> u1_pre_topc(A) = k9_setfam_1(u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tdlat_3)).

tff(f_27,axiom,(
    ! [A] : m1_subset_1(k9_setfam_1(A),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_setfam_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    v1_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [A_2] : k9_setfam_1(A_2) = k1_zfmisc_1(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_9] :
      ( k9_setfam_1(u1_struct_0(A_9)) = u1_pre_topc(A_9)
      | ~ v1_tdlat_3(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_23,plain,(
    ! [A_9] :
      ( k1_zfmisc_1(u1_struct_0(A_9)) = u1_pre_topc(A_9)
      | ~ v1_tdlat_3(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_12])).

tff(c_14,plain,(
    ~ v1_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_20,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_36,plain,(
    ! [A_13] :
      ( k1_zfmisc_1(u1_struct_0(A_13)) = u1_pre_topc(A_13)
      | ~ v1_tdlat_3(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_12])).

tff(c_2,plain,(
    ! [A_1] : m1_subset_1(k9_setfam_1(A_1),k1_zfmisc_1(k1_zfmisc_1(A_1))) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_25,plain,(
    ! [A_1] : m1_subset_1(k1_zfmisc_1(A_1),k1_zfmisc_1(k1_zfmisc_1(A_1))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2])).

tff(c_42,plain,(
    ! [A_13] :
      ( m1_subset_1(u1_pre_topc(A_13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_13))))
      | ~ v1_tdlat_3(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_25])).

tff(c_18,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_81,plain,(
    ! [D_21,B_22,C_23,A_24] :
      ( D_21 = B_22
      | g1_pre_topc(C_23,D_21) != g1_pre_topc(A_24,B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k1_zfmisc_1(A_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_87,plain,(
    ! [B_26,A_27] :
      ( u1_pre_topc('#skF_2') = B_26
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(A_27,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(k1_zfmisc_1(A_27))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_81])).

tff(c_97,plain,(
    ! [A_13] :
      ( u1_pre_topc(A_13) = u1_pre_topc('#skF_2')
      | g1_pre_topc(u1_struct_0(A_13),u1_pre_topc(A_13)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ v1_tdlat_3(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(resolution,[status(thm)],[c_42,c_87])).

tff(c_133,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_1')
    | ~ v1_tdlat_3('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_97])).

tff(c_135,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_16,c_133])).

tff(c_64,plain,(
    ! [C_15,A_16,D_17,B_18] :
      ( C_15 = A_16
      | g1_pre_topc(C_15,D_17) != g1_pre_topc(A_16,B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k1_zfmisc_1(A_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_103,plain,(
    ! [A_29,B_30] :
      ( u1_struct_0('#skF_2') = A_29
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(A_29,B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(k1_zfmisc_1(A_29))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_64])).

tff(c_113,plain,(
    ! [A_13] :
      ( u1_struct_0(A_13) = u1_struct_0('#skF_2')
      | g1_pre_topc(u1_struct_0(A_13),u1_pre_topc(A_13)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ v1_tdlat_3(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(resolution,[status(thm)],[c_42,c_103])).

tff(c_179,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_1')
    | ~ v1_tdlat_3('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_113])).

tff(c_181,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_16,c_179])).

tff(c_10,plain,(
    ! [A_9] :
      ( v1_tdlat_3(A_9)
      | k9_setfam_1(u1_struct_0(A_9)) != u1_pre_topc(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_24,plain,(
    ! [A_9] :
      ( v1_tdlat_3(A_9)
      | k1_zfmisc_1(u1_struct_0(A_9)) != u1_pre_topc(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10])).

tff(c_201,plain,
    ( v1_tdlat_3('#skF_2')
    | k1_zfmisc_1(u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_24])).

tff(c_212,plain,
    ( v1_tdlat_3('#skF_2')
    | k1_zfmisc_1(u1_struct_0('#skF_1')) != u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_135,c_201])).

tff(c_213,plain,(
    k1_zfmisc_1(u1_struct_0('#skF_1')) != u1_pre_topc('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_212])).

tff(c_219,plain,
    ( ~ v1_tdlat_3('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_23,c_213])).

tff(c_223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_16,c_219])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:41:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.33  
% 2.06/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.33  %$ m1_subset_1 > v1_tdlat_3 > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k9_setfam_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.06/1.33  
% 2.06/1.33  %Foreground sorts:
% 2.06/1.33  
% 2.06/1.33  
% 2.06/1.33  %Background operators:
% 2.06/1.33  
% 2.06/1.33  
% 2.06/1.33  %Foreground operators:
% 2.06/1.33  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.06/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.33  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.06/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.06/1.33  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.06/1.33  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 2.06/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.06/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.06/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.06/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.06/1.33  
% 2.06/1.34  tff(f_56, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & v1_tdlat_3(A)) => v1_tdlat_3(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_tex_2)).
% 2.06/1.34  tff(f_29, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 2.06/1.34  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => (v1_tdlat_3(A) <=> (u1_pre_topc(A) = k9_setfam_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tdlat_3)).
% 2.06/1.34  tff(f_27, axiom, (![A]: m1_subset_1(k9_setfam_1(A), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_setfam_1)).
% 2.06/1.34  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 2.06/1.34  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.06/1.34  tff(c_16, plain, (v1_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.06/1.34  tff(c_4, plain, (![A_2]: (k9_setfam_1(A_2)=k1_zfmisc_1(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.06/1.34  tff(c_12, plain, (![A_9]: (k9_setfam_1(u1_struct_0(A_9))=u1_pre_topc(A_9) | ~v1_tdlat_3(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.06/1.34  tff(c_23, plain, (![A_9]: (k1_zfmisc_1(u1_struct_0(A_9))=u1_pre_topc(A_9) | ~v1_tdlat_3(A_9) | ~l1_pre_topc(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_12])).
% 2.06/1.34  tff(c_14, plain, (~v1_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.06/1.34  tff(c_20, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.06/1.34  tff(c_36, plain, (![A_13]: (k1_zfmisc_1(u1_struct_0(A_13))=u1_pre_topc(A_13) | ~v1_tdlat_3(A_13) | ~l1_pre_topc(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_12])).
% 2.06/1.34  tff(c_2, plain, (![A_1]: (m1_subset_1(k9_setfam_1(A_1), k1_zfmisc_1(k1_zfmisc_1(A_1))))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.06/1.34  tff(c_25, plain, (![A_1]: (m1_subset_1(k1_zfmisc_1(A_1), k1_zfmisc_1(k1_zfmisc_1(A_1))))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2])).
% 2.06/1.34  tff(c_42, plain, (![A_13]: (m1_subset_1(u1_pre_topc(A_13), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_13)))) | ~v1_tdlat_3(A_13) | ~l1_pre_topc(A_13))), inference(superposition, [status(thm), theory('equality')], [c_36, c_25])).
% 2.06/1.34  tff(c_18, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.06/1.34  tff(c_81, plain, (![D_21, B_22, C_23, A_24]: (D_21=B_22 | g1_pre_topc(C_23, D_21)!=g1_pre_topc(A_24, B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(k1_zfmisc_1(A_24))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.06/1.34  tff(c_87, plain, (![B_26, A_27]: (u1_pre_topc('#skF_2')=B_26 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(A_27, B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(k1_zfmisc_1(A_27))))), inference(superposition, [status(thm), theory('equality')], [c_18, c_81])).
% 2.06/1.34  tff(c_97, plain, (![A_13]: (u1_pre_topc(A_13)=u1_pre_topc('#skF_2') | g1_pre_topc(u1_struct_0(A_13), u1_pre_topc(A_13))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~v1_tdlat_3(A_13) | ~l1_pre_topc(A_13))), inference(resolution, [status(thm)], [c_42, c_87])).
% 2.06/1.34  tff(c_133, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_1') | ~v1_tdlat_3('#skF_1') | ~l1_pre_topc('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_97])).
% 2.06/1.34  tff(c_135, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_16, c_133])).
% 2.06/1.34  tff(c_64, plain, (![C_15, A_16, D_17, B_18]: (C_15=A_16 | g1_pre_topc(C_15, D_17)!=g1_pre_topc(A_16, B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(k1_zfmisc_1(A_16))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.06/1.35  tff(c_103, plain, (![A_29, B_30]: (u1_struct_0('#skF_2')=A_29 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(A_29, B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(k1_zfmisc_1(A_29))))), inference(superposition, [status(thm), theory('equality')], [c_18, c_64])).
% 2.06/1.35  tff(c_113, plain, (![A_13]: (u1_struct_0(A_13)=u1_struct_0('#skF_2') | g1_pre_topc(u1_struct_0(A_13), u1_pre_topc(A_13))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~v1_tdlat_3(A_13) | ~l1_pre_topc(A_13))), inference(resolution, [status(thm)], [c_42, c_103])).
% 2.06/1.35  tff(c_179, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1') | ~v1_tdlat_3('#skF_1') | ~l1_pre_topc('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_113])).
% 2.06/1.35  tff(c_181, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_16, c_179])).
% 2.06/1.35  tff(c_10, plain, (![A_9]: (v1_tdlat_3(A_9) | k9_setfam_1(u1_struct_0(A_9))!=u1_pre_topc(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.06/1.35  tff(c_24, plain, (![A_9]: (v1_tdlat_3(A_9) | k1_zfmisc_1(u1_struct_0(A_9))!=u1_pre_topc(A_9) | ~l1_pre_topc(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_10])).
% 2.06/1.35  tff(c_201, plain, (v1_tdlat_3('#skF_2') | k1_zfmisc_1(u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_181, c_24])).
% 2.06/1.35  tff(c_212, plain, (v1_tdlat_3('#skF_2') | k1_zfmisc_1(u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_135, c_201])).
% 2.06/1.35  tff(c_213, plain, (k1_zfmisc_1(u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_14, c_212])).
% 2.06/1.35  tff(c_219, plain, (~v1_tdlat_3('#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_23, c_213])).
% 2.06/1.35  tff(c_223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_16, c_219])).
% 2.06/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.35  
% 2.06/1.35  Inference rules
% 2.06/1.35  ----------------------
% 2.06/1.35  #Ref     : 4
% 2.06/1.35  #Sup     : 41
% 2.06/1.35  #Fact    : 0
% 2.06/1.35  #Define  : 0
% 2.06/1.35  #Split   : 1
% 2.06/1.35  #Chain   : 0
% 2.06/1.35  #Close   : 0
% 2.06/1.35  
% 2.06/1.35  Ordering : KBO
% 2.06/1.35  
% 2.06/1.35  Simplification rules
% 2.06/1.35  ----------------------
% 2.06/1.35  #Subsume      : 16
% 2.06/1.35  #Demod        : 40
% 2.06/1.35  #Tautology    : 13
% 2.06/1.35  #SimpNegUnit  : 1
% 2.06/1.35  #BackRed      : 9
% 2.06/1.35  
% 2.06/1.35  #Partial instantiations: 0
% 2.06/1.35  #Strategies tried      : 1
% 2.06/1.35  
% 2.06/1.35  Timing (in seconds)
% 2.06/1.35  ----------------------
% 2.06/1.35  Preprocessing        : 0.28
% 2.06/1.35  Parsing              : 0.15
% 2.06/1.35  CNF conversion       : 0.02
% 2.06/1.35  Main loop            : 0.19
% 2.06/1.35  Inferencing          : 0.07
% 2.06/1.35  Reduction            : 0.06
% 2.06/1.35  Demodulation         : 0.04
% 2.06/1.35  BG Simplification    : 0.01
% 2.06/1.35  Subsumption          : 0.04
% 2.06/1.35  Abstraction          : 0.01
% 2.06/1.35  MUC search           : 0.00
% 2.06/1.35  Cooper               : 0.00
% 2.06/1.35  Total                : 0.50
% 2.06/1.35  Index Insertion      : 0.00
% 2.06/1.35  Index Deletion       : 0.00
% 2.06/1.35  Index Matching       : 0.00
% 2.06/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
