%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:57 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   51 (  84 expanded)
%              Number of leaves         :   20 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :   82 ( 168 expanded)
%              Number of equality atoms :   39 (  67 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > v1_tdlat_3 > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k9_setfam_1 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_58,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                & v1_tdlat_3(A) )
             => v1_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tex_2)).

tff(f_31,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_tdlat_3(A)
      <=> u1_pre_topc(A) = k9_setfam_1(u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tdlat_3)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_18,plain,(
    v1_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [A_3] : k9_setfam_1(A_3) = k1_zfmisc_1(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_10] :
      ( k9_setfam_1(u1_struct_0(A_10)) = u1_pre_topc(A_10)
      | ~ v1_tdlat_3(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_25,plain,(
    ! [A_10] :
      ( k1_zfmisc_1(u1_struct_0(A_10)) = u1_pre_topc(A_10)
      | ~ v1_tdlat_3(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14])).

tff(c_16,plain,(
    ~ v1_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_27,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_20,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_82,plain,(
    ! [C_22,A_23,D_24,B_25] :
      ( C_22 = A_23
      | g1_pre_topc(C_22,D_24) != g1_pre_topc(A_23,B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k1_zfmisc_1(A_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_100,plain,(
    ! [A_29,B_30] :
      ( u1_struct_0('#skF_2') = A_29
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(A_29,B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(k1_zfmisc_1(A_29))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_82])).

tff(c_109,plain,(
    ! [A_31] :
      ( u1_struct_0('#skF_2') = A_31
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(A_31,k1_zfmisc_1(A_31)) ) ),
    inference(resolution,[status(thm)],[c_27,c_100])).

tff(c_112,plain,(
    ! [A_10] :
      ( u1_struct_0(A_10) = u1_struct_0('#skF_2')
      | g1_pre_topc(u1_struct_0(A_10),u1_pre_topc(A_10)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ v1_tdlat_3(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25,c_109])).

tff(c_121,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_1')
    | ~ v1_tdlat_3('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_112])).

tff(c_123,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_18,c_121])).

tff(c_12,plain,(
    ! [A_10] :
      ( v1_tdlat_3(A_10)
      | k9_setfam_1(u1_struct_0(A_10)) != u1_pre_topc(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26,plain,(
    ! [A_10] :
      ( v1_tdlat_3(A_10)
      | k1_zfmisc_1(u1_struct_0(A_10)) != u1_pre_topc(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12])).

tff(c_142,plain,
    ( v1_tdlat_3('#skF_2')
    | k1_zfmisc_1(u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_26])).

tff(c_151,plain,
    ( v1_tdlat_3('#skF_2')
    | k1_zfmisc_1(u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_142])).

tff(c_152,plain,(
    k1_zfmisc_1(u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_151])).

tff(c_158,plain,
    ( u1_pre_topc('#skF_2') != u1_pre_topc('#skF_1')
    | ~ v1_tdlat_3('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_25,c_152])).

tff(c_160,plain,(
    u1_pre_topc('#skF_2') != u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_18,c_158])).

tff(c_73,plain,(
    ! [D_18,B_19,C_20,A_21] :
      ( D_18 = B_19
      | g1_pre_topc(C_20,D_18) != g1_pre_topc(A_21,B_19)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(k1_zfmisc_1(A_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_87,plain,(
    ! [B_26,A_27] :
      ( u1_pre_topc('#skF_2') = B_26
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(A_27,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(k1_zfmisc_1(A_27))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_73])).

tff(c_166,plain,(
    ! [B_33,A_34] :
      ( u1_pre_topc('#skF_2') = B_33
      | g1_pre_topc(u1_struct_0(A_34),B_33) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_pre_topc(A_34)))
      | ~ v1_tdlat_3(A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25,c_87])).

tff(c_171,plain,(
    ! [A_34] :
      ( u1_pre_topc(A_34) = u1_pre_topc('#skF_2')
      | g1_pre_topc(u1_struct_0(A_34),u1_pre_topc(A_34)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ v1_tdlat_3(A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(resolution,[status(thm)],[c_27,c_166])).

tff(c_197,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_1')
    | ~ v1_tdlat_3('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_171])).

tff(c_199,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_18,c_197])).

tff(c_201,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_199])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:20:41 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.27  
% 1.94/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.27  %$ m1_subset_1 > v1_tdlat_3 > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k9_setfam_1 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.94/1.27  
% 1.94/1.27  %Foreground sorts:
% 1.94/1.27  
% 1.94/1.27  
% 1.94/1.27  %Background operators:
% 1.94/1.27  
% 1.94/1.27  
% 1.94/1.27  %Foreground operators:
% 1.94/1.27  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 1.94/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.27  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 1.94/1.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.94/1.27  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 1.94/1.27  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 1.94/1.27  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.27  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.94/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.94/1.27  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 1.94/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.94/1.27  
% 1.94/1.29  tff(f_58, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & v1_tdlat_3(A)) => v1_tdlat_3(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_tex_2)).
% 1.94/1.29  tff(f_31, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 1.94/1.29  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (v1_tdlat_3(A) <=> (u1_pre_topc(A) = k9_setfam_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tdlat_3)).
% 1.94/1.29  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 1.94/1.29  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 1.94/1.29  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 1.94/1.29  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.94/1.29  tff(c_18, plain, (v1_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.94/1.29  tff(c_6, plain, (![A_3]: (k9_setfam_1(A_3)=k1_zfmisc_1(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.94/1.29  tff(c_14, plain, (![A_10]: (k9_setfam_1(u1_struct_0(A_10))=u1_pre_topc(A_10) | ~v1_tdlat_3(A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.94/1.29  tff(c_25, plain, (![A_10]: (k1_zfmisc_1(u1_struct_0(A_10))=u1_pre_topc(A_10) | ~v1_tdlat_3(A_10) | ~l1_pre_topc(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14])).
% 1.94/1.29  tff(c_16, plain, (~v1_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.94/1.29  tff(c_22, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.94/1.29  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.94/1.29  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.94/1.29  tff(c_27, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 1.94/1.29  tff(c_20, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.94/1.29  tff(c_82, plain, (![C_22, A_23, D_24, B_25]: (C_22=A_23 | g1_pre_topc(C_22, D_24)!=g1_pre_topc(A_23, B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(k1_zfmisc_1(A_23))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.94/1.29  tff(c_100, plain, (![A_29, B_30]: (u1_struct_0('#skF_2')=A_29 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(A_29, B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(k1_zfmisc_1(A_29))))), inference(superposition, [status(thm), theory('equality')], [c_20, c_82])).
% 1.94/1.29  tff(c_109, plain, (![A_31]: (u1_struct_0('#skF_2')=A_31 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(A_31, k1_zfmisc_1(A_31)))), inference(resolution, [status(thm)], [c_27, c_100])).
% 1.94/1.29  tff(c_112, plain, (![A_10]: (u1_struct_0(A_10)=u1_struct_0('#skF_2') | g1_pre_topc(u1_struct_0(A_10), u1_pre_topc(A_10))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~v1_tdlat_3(A_10) | ~l1_pre_topc(A_10))), inference(superposition, [status(thm), theory('equality')], [c_25, c_109])).
% 1.94/1.29  tff(c_121, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1') | ~v1_tdlat_3('#skF_1') | ~l1_pre_topc('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_112])).
% 1.94/1.29  tff(c_123, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_18, c_121])).
% 1.94/1.29  tff(c_12, plain, (![A_10]: (v1_tdlat_3(A_10) | k9_setfam_1(u1_struct_0(A_10))!=u1_pre_topc(A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.94/1.29  tff(c_26, plain, (![A_10]: (v1_tdlat_3(A_10) | k1_zfmisc_1(u1_struct_0(A_10))!=u1_pre_topc(A_10) | ~l1_pre_topc(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_12])).
% 1.94/1.29  tff(c_142, plain, (v1_tdlat_3('#skF_2') | k1_zfmisc_1(u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_123, c_26])).
% 1.94/1.29  tff(c_151, plain, (v1_tdlat_3('#skF_2') | k1_zfmisc_1(u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_142])).
% 1.94/1.29  tff(c_152, plain, (k1_zfmisc_1(u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_16, c_151])).
% 1.94/1.29  tff(c_158, plain, (u1_pre_topc('#skF_2')!=u1_pre_topc('#skF_1') | ~v1_tdlat_3('#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_25, c_152])).
% 1.94/1.29  tff(c_160, plain, (u1_pre_topc('#skF_2')!=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_18, c_158])).
% 1.94/1.29  tff(c_73, plain, (![D_18, B_19, C_20, A_21]: (D_18=B_19 | g1_pre_topc(C_20, D_18)!=g1_pre_topc(A_21, B_19) | ~m1_subset_1(B_19, k1_zfmisc_1(k1_zfmisc_1(A_21))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.94/1.29  tff(c_87, plain, (![B_26, A_27]: (u1_pre_topc('#skF_2')=B_26 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(A_27, B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(k1_zfmisc_1(A_27))))), inference(superposition, [status(thm), theory('equality')], [c_20, c_73])).
% 1.94/1.29  tff(c_166, plain, (![B_33, A_34]: (u1_pre_topc('#skF_2')=B_33 | g1_pre_topc(u1_struct_0(A_34), B_33)!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_pre_topc(A_34))) | ~v1_tdlat_3(A_34) | ~l1_pre_topc(A_34))), inference(superposition, [status(thm), theory('equality')], [c_25, c_87])).
% 1.94/1.29  tff(c_171, plain, (![A_34]: (u1_pre_topc(A_34)=u1_pre_topc('#skF_2') | g1_pre_topc(u1_struct_0(A_34), u1_pre_topc(A_34))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~v1_tdlat_3(A_34) | ~l1_pre_topc(A_34))), inference(resolution, [status(thm)], [c_27, c_166])).
% 1.94/1.29  tff(c_197, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_1') | ~v1_tdlat_3('#skF_1') | ~l1_pre_topc('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_171])).
% 1.94/1.29  tff(c_199, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_18, c_197])).
% 1.94/1.29  tff(c_201, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160, c_199])).
% 1.94/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.29  
% 1.94/1.29  Inference rules
% 1.94/1.29  ----------------------
% 1.94/1.29  #Ref     : 4
% 1.94/1.29  #Sup     : 38
% 1.94/1.29  #Fact    : 0
% 1.94/1.29  #Define  : 0
% 1.94/1.29  #Split   : 1
% 1.94/1.29  #Chain   : 0
% 1.94/1.29  #Close   : 0
% 1.94/1.29  
% 1.94/1.29  Ordering : KBO
% 1.94/1.29  
% 1.94/1.29  Simplification rules
% 1.94/1.29  ----------------------
% 1.94/1.29  #Subsume      : 10
% 1.94/1.29  #Demod        : 23
% 1.94/1.29  #Tautology    : 15
% 1.94/1.29  #SimpNegUnit  : 2
% 1.94/1.29  #BackRed      : 5
% 1.94/1.29  
% 1.94/1.29  #Partial instantiations: 0
% 1.94/1.29  #Strategies tried      : 1
% 1.94/1.29  
% 1.94/1.29  Timing (in seconds)
% 1.94/1.29  ----------------------
% 1.94/1.29  Preprocessing        : 0.30
% 1.94/1.29  Parsing              : 0.16
% 1.94/1.29  CNF conversion       : 0.02
% 1.94/1.29  Main loop            : 0.19
% 1.94/1.29  Inferencing          : 0.07
% 1.94/1.29  Reduction            : 0.06
% 1.94/1.29  Demodulation         : 0.04
% 1.94/1.29  BG Simplification    : 0.01
% 1.94/1.29  Subsumption          : 0.05
% 1.94/1.29  Abstraction          : 0.01
% 1.94/1.29  MUC search           : 0.00
% 1.94/1.29  Cooper               : 0.00
% 1.94/1.29  Total                : 0.52
% 1.94/1.29  Index Insertion      : 0.00
% 1.94/1.29  Index Deletion       : 0.00
% 1.94/1.29  Index Matching       : 0.00
% 1.94/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
