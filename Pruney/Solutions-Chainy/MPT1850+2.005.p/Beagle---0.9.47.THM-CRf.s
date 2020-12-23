%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:57 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 179 expanded)
%              Number of leaves         :   20 (  66 expanded)
%              Depth                    :   13
%              Number of atoms          :  102 ( 409 expanded)
%              Number of equality atoms :   42 ( 171 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_tdlat_3 > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k9_setfam_1 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_64,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                & v1_tdlat_3(A) )
             => v1_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tex_2)).

tff(f_37,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_tdlat_3(A)
      <=> u1_pre_topc(A) = k9_setfam_1(u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tdlat_3)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    v1_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12,plain,(
    ! [A_5] : k9_setfam_1(A_5) = k1_zfmisc_1(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [A_12] :
      ( k9_setfam_1(u1_struct_0(A_12)) = u1_pre_topc(A_12)
      | ~ v1_tdlat_3(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_31,plain,(
    ! [A_12] :
      ( k1_zfmisc_1(u1_struct_0(A_12)) = u1_pre_topc(A_12)
      | ~ v1_tdlat_3(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_20])).

tff(c_22,plain,(
    ~ v1_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_28,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_109,plain,(
    ! [D_33,B_34,C_35,A_36] :
      ( D_33 = B_34
      | g1_pre_topc(C_35,D_33) != g1_pre_topc(A_36,B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(k1_zfmisc_1(A_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_126,plain,(
    ! [B_39,A_40] :
      ( u1_pre_topc('#skF_2') = B_39
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(A_40,B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k1_zfmisc_1(A_40))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_109])).

tff(c_134,plain,(
    ! [A_3,A_40] :
      ( u1_pre_topc('#skF_2') = A_3
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(A_40,A_3)
      | ~ r1_tarski(A_3,k1_zfmisc_1(A_40)) ) ),
    inference(resolution,[status(thm)],[c_10,c_126])).

tff(c_146,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_1')
    | ~ r1_tarski(u1_pre_topc('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_134])).

tff(c_152,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_155,plain,
    ( ~ r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v1_tdlat_3('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_152])).

tff(c_158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_6,c_155])).

tff(c_159,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_1') ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_160,plain,(
    r1_tarski(u1_pre_topc('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_178,plain,
    ( k1_zfmisc_1(u1_struct_0('#skF_1')) = u1_pre_topc('#skF_1')
    | ~ r1_tarski(k1_zfmisc_1(u1_struct_0('#skF_1')),u1_pre_topc('#skF_1')) ),
    inference(resolution,[status(thm)],[c_160,c_2])).

tff(c_210,plain,(
    ~ r1_tarski(k1_zfmisc_1(u1_struct_0('#skF_1')),u1_pre_topc('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_213,plain,
    ( ~ r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v1_tdlat_3('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_210])).

tff(c_216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_6,c_213])).

tff(c_217,plain,(
    k1_zfmisc_1(u1_struct_0('#skF_1')) = u1_pre_topc('#skF_1') ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_100,plain,(
    ! [C_29,A_30,D_31,B_32] :
      ( C_29 = A_30
      | g1_pre_topc(C_29,D_31) != g1_pre_topc(A_30,B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k1_zfmisc_1(A_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_135,plain,(
    ! [A_41,B_42] :
      ( u1_struct_0('#skF_2') = A_41
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(A_41,B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(k1_zfmisc_1(A_41))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_100])).

tff(c_143,plain,(
    ! [A_41,A_3] :
      ( u1_struct_0('#skF_2') = A_41
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(A_41,A_3)
      | ~ r1_tarski(A_3,k1_zfmisc_1(A_41)) ) ),
    inference(resolution,[status(thm)],[c_10,c_135])).

tff(c_270,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_1')
    | ~ r1_tarski(u1_pre_topc('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_143])).

tff(c_272,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_217,c_270])).

tff(c_104,plain,(
    ! [C_29,D_31] :
      ( u1_struct_0('#skF_2') = C_29
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_29,D_31)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_100])).

tff(c_181,plain,(
    ! [C_29,D_31] :
      ( u1_struct_0('#skF_2') = C_29
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_29,D_31)
      | ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_104])).

tff(c_182,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_181])).

tff(c_191,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_10,c_182])).

tff(c_279,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_191])).

tff(c_284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_217,c_279])).

tff(c_285,plain,(
    ! [C_29,D_31] :
      ( u1_struct_0('#skF_2') = C_29
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_29,D_31) ) ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_327,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_285])).

tff(c_18,plain,(
    ! [A_12] :
      ( v1_tdlat_3(A_12)
      | k9_setfam_1(u1_struct_0(A_12)) != u1_pre_topc(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_32,plain,(
    ! [A_12] :
      ( v1_tdlat_3(A_12)
      | k1_zfmisc_1(u1_struct_0(A_12)) != u1_pre_topc(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_18])).

tff(c_354,plain,
    ( v1_tdlat_3('#skF_2')
    | k1_zfmisc_1(u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_32])).

tff(c_369,plain,
    ( v1_tdlat_3('#skF_2')
    | k1_zfmisc_1(u1_struct_0('#skF_1')) != u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_159,c_354])).

tff(c_370,plain,(
    k1_zfmisc_1(u1_struct_0('#skF_1')) != u1_pre_topc('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_369])).

tff(c_376,plain,
    ( ~ v1_tdlat_3('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_370])).

tff(c_380,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_376])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:07:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.38  
% 2.32/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.39  %$ r1_tarski > m1_subset_1 > v1_tdlat_3 > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k9_setfam_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.32/1.39  
% 2.32/1.39  %Foreground sorts:
% 2.32/1.39  
% 2.32/1.39  
% 2.32/1.39  %Background operators:
% 2.32/1.39  
% 2.32/1.39  
% 2.32/1.39  %Foreground operators:
% 2.32/1.39  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.32/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.39  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.32/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.32/1.39  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.32/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.32/1.39  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 2.32/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.32/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.32/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.32/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.32/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.32/1.39  
% 2.32/1.40  tff(f_64, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & v1_tdlat_3(A)) => v1_tdlat_3(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_tex_2)).
% 2.32/1.40  tff(f_37, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 2.32/1.40  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (v1_tdlat_3(A) <=> (u1_pre_topc(A) = k9_setfam_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tdlat_3)).
% 2.32/1.40  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.32/1.40  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.32/1.40  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 2.32/1.40  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.32/1.40  tff(c_24, plain, (v1_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.32/1.40  tff(c_12, plain, (![A_5]: (k9_setfam_1(A_5)=k1_zfmisc_1(A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.32/1.40  tff(c_20, plain, (![A_12]: (k9_setfam_1(u1_struct_0(A_12))=u1_pre_topc(A_12) | ~v1_tdlat_3(A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.32/1.40  tff(c_31, plain, (![A_12]: (k1_zfmisc_1(u1_struct_0(A_12))=u1_pre_topc(A_12) | ~v1_tdlat_3(A_12) | ~l1_pre_topc(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_20])).
% 2.32/1.40  tff(c_22, plain, (~v1_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.32/1.40  tff(c_28, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.32/1.40  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.32/1.40  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.32/1.40  tff(c_26, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.32/1.40  tff(c_109, plain, (![D_33, B_34, C_35, A_36]: (D_33=B_34 | g1_pre_topc(C_35, D_33)!=g1_pre_topc(A_36, B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(k1_zfmisc_1(A_36))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.32/1.40  tff(c_126, plain, (![B_39, A_40]: (u1_pre_topc('#skF_2')=B_39 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(A_40, B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(k1_zfmisc_1(A_40))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_109])).
% 2.32/1.40  tff(c_134, plain, (![A_3, A_40]: (u1_pre_topc('#skF_2')=A_3 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(A_40, A_3) | ~r1_tarski(A_3, k1_zfmisc_1(A_40)))), inference(resolution, [status(thm)], [c_10, c_126])).
% 2.32/1.40  tff(c_146, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_1') | ~r1_tarski(u1_pre_topc('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(reflexivity, [status(thm), theory('equality')], [c_134])).
% 2.32/1.40  tff(c_152, plain, (~r1_tarski(u1_pre_topc('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_146])).
% 2.32/1.40  tff(c_155, plain, (~r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc('#skF_1')) | ~v1_tdlat_3('#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_31, c_152])).
% 2.32/1.40  tff(c_158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_24, c_6, c_155])).
% 2.32/1.40  tff(c_159, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_1')), inference(splitRight, [status(thm)], [c_146])).
% 2.32/1.40  tff(c_160, plain, (r1_tarski(u1_pre_topc('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_146])).
% 2.32/1.40  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.32/1.40  tff(c_178, plain, (k1_zfmisc_1(u1_struct_0('#skF_1'))=u1_pre_topc('#skF_1') | ~r1_tarski(k1_zfmisc_1(u1_struct_0('#skF_1')), u1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_160, c_2])).
% 2.32/1.40  tff(c_210, plain, (~r1_tarski(k1_zfmisc_1(u1_struct_0('#skF_1')), u1_pre_topc('#skF_1'))), inference(splitLeft, [status(thm)], [c_178])).
% 2.32/1.40  tff(c_213, plain, (~r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc('#skF_1')) | ~v1_tdlat_3('#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_31, c_210])).
% 2.32/1.40  tff(c_216, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_24, c_6, c_213])).
% 2.32/1.40  tff(c_217, plain, (k1_zfmisc_1(u1_struct_0('#skF_1'))=u1_pre_topc('#skF_1')), inference(splitRight, [status(thm)], [c_178])).
% 2.32/1.40  tff(c_100, plain, (![C_29, A_30, D_31, B_32]: (C_29=A_30 | g1_pre_topc(C_29, D_31)!=g1_pre_topc(A_30, B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(k1_zfmisc_1(A_30))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.32/1.40  tff(c_135, plain, (![A_41, B_42]: (u1_struct_0('#skF_2')=A_41 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(A_41, B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(k1_zfmisc_1(A_41))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_100])).
% 2.32/1.40  tff(c_143, plain, (![A_41, A_3]: (u1_struct_0('#skF_2')=A_41 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(A_41, A_3) | ~r1_tarski(A_3, k1_zfmisc_1(A_41)))), inference(resolution, [status(thm)], [c_10, c_135])).
% 2.32/1.40  tff(c_270, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1') | ~r1_tarski(u1_pre_topc('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(reflexivity, [status(thm), theory('equality')], [c_143])).
% 2.32/1.40  tff(c_272, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_217, c_270])).
% 2.32/1.40  tff(c_104, plain, (![C_29, D_31]: (u1_struct_0('#skF_2')=C_29 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(C_29, D_31) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_100])).
% 2.32/1.40  tff(c_181, plain, (![C_29, D_31]: (u1_struct_0('#skF_2')=C_29 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(C_29, D_31) | ~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_104])).
% 2.32/1.40  tff(c_182, plain, (~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_181])).
% 2.32/1.40  tff(c_191, plain, (~r1_tarski(u1_pre_topc('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_10, c_182])).
% 2.32/1.40  tff(c_279, plain, (~r1_tarski(u1_pre_topc('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_272, c_191])).
% 2.32/1.40  tff(c_284, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_217, c_279])).
% 2.32/1.40  tff(c_285, plain, (![C_29, D_31]: (u1_struct_0('#skF_2')=C_29 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(C_29, D_31))), inference(splitRight, [status(thm)], [c_181])).
% 2.32/1.40  tff(c_327, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_285])).
% 2.32/1.40  tff(c_18, plain, (![A_12]: (v1_tdlat_3(A_12) | k9_setfam_1(u1_struct_0(A_12))!=u1_pre_topc(A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.32/1.40  tff(c_32, plain, (![A_12]: (v1_tdlat_3(A_12) | k1_zfmisc_1(u1_struct_0(A_12))!=u1_pre_topc(A_12) | ~l1_pre_topc(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_18])).
% 2.32/1.40  tff(c_354, plain, (v1_tdlat_3('#skF_2') | k1_zfmisc_1(u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_327, c_32])).
% 2.32/1.40  tff(c_369, plain, (v1_tdlat_3('#skF_2') | k1_zfmisc_1(u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_159, c_354])).
% 2.32/1.40  tff(c_370, plain, (k1_zfmisc_1(u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_22, c_369])).
% 2.32/1.40  tff(c_376, plain, (~v1_tdlat_3('#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_31, c_370])).
% 2.32/1.40  tff(c_380, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_24, c_376])).
% 2.32/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.40  
% 2.32/1.40  Inference rules
% 2.32/1.40  ----------------------
% 2.32/1.40  #Ref     : 5
% 2.32/1.40  #Sup     : 74
% 2.32/1.40  #Fact    : 0
% 2.32/1.40  #Define  : 0
% 2.32/1.40  #Split   : 3
% 2.32/1.40  #Chain   : 0
% 2.32/1.40  #Close   : 0
% 2.32/1.40  
% 2.32/1.40  Ordering : KBO
% 2.32/1.40  
% 2.32/1.40  Simplification rules
% 2.32/1.40  ----------------------
% 2.32/1.40  #Subsume      : 20
% 2.32/1.40  #Demod        : 73
% 2.32/1.40  #Tautology    : 37
% 2.32/1.40  #SimpNegUnit  : 1
% 2.32/1.40  #BackRed      : 11
% 2.32/1.40  
% 2.32/1.40  #Partial instantiations: 0
% 2.32/1.40  #Strategies tried      : 1
% 2.32/1.40  
% 2.32/1.40  Timing (in seconds)
% 2.32/1.40  ----------------------
% 2.32/1.40  Preprocessing        : 0.32
% 2.32/1.40  Parsing              : 0.16
% 2.32/1.40  CNF conversion       : 0.02
% 2.32/1.40  Main loop            : 0.26
% 2.32/1.40  Inferencing          : 0.08
% 2.32/1.41  Reduction            : 0.08
% 2.32/1.41  Demodulation         : 0.06
% 2.32/1.41  BG Simplification    : 0.02
% 2.32/1.41  Subsumption          : 0.06
% 2.32/1.41  Abstraction          : 0.01
% 2.32/1.41  MUC search           : 0.00
% 2.32/1.41  Cooper               : 0.00
% 2.32/1.41  Total                : 0.60
% 2.32/1.41  Index Insertion      : 0.00
% 2.32/1.41  Index Deletion       : 0.00
% 2.32/1.41  Index Matching       : 0.00
% 2.32/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
