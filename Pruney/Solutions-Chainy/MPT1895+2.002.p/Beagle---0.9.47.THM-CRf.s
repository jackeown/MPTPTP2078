%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:30 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 120 expanded)
%              Number of leaves         :   25 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :  100 ( 312 expanded)
%              Number of equality atoms :   19 (  59 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v1_tops_1 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_pre_topc > a_2_0_tex_2 > #nlpp > u1_struct_0 > k3_tarski > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(a_2_0_tex_2,type,(
    a_2_0_tex_2: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tex_2(B,A)
             => k3_tarski(a_2_0_tex_2(A,B)) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_tex_2)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
           => v1_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tex_2)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k3_tarski(a_2_0_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tex_2)).

tff(c_20,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4,plain,(
    ! [A_2] :
      ( l1_struct_0(A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    ! [A_14] :
      ( u1_struct_0(A_14) = k2_struct_0(A_14)
      | ~ l1_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_40,plain,(
    ! [A_17] :
      ( u1_struct_0(A_17) = k2_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(resolution,[status(thm)],[c_4,c_28])).

tff(c_44,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_40])).

tff(c_14,plain,(
    k3_tarski(a_2_0_tex_2('#skF_1','#skF_2')) != u1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_45,plain,(
    k3_tarski(a_2_0_tex_2('#skF_1','#skF_2')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_14])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_33,plain,(
    ! [A_15,B_16] :
      ( k2_pre_topc(A_15,B_16) = k2_struct_0(A_15)
      | ~ v1_tops_1(B_16,A_15)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_36,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_33])).

tff(c_39,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_36])).

tff(c_56,plain,(
    ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_39])).

tff(c_16,plain,(
    v3_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_46,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_18])).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_24,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_22,plain,(
    v3_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_76,plain,(
    ! [B_22,A_23] :
      ( v1_tops_1(B_22,A_23)
      | ~ v3_tex_2(B_22,A_23)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23)
      | ~ v3_tdlat_3(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_79,plain,(
    ! [B_22] :
      ( v1_tops_1(B_22,'#skF_1')
      | ~ v3_tex_2(B_22,'#skF_1')
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v3_tdlat_3('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_76])).

tff(c_81,plain,(
    ! [B_22] :
      ( v1_tops_1(B_22,'#skF_1')
      | ~ v3_tex_2(B_22,'#skF_1')
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_79])).

tff(c_83,plain,(
    ! [B_24] :
      ( v1_tops_1(B_24,'#skF_1')
      | ~ v3_tex_2(B_24,'#skF_1')
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_81])).

tff(c_86,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v3_tex_2('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_83])).

tff(c_89,plain,(
    v1_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_86])).

tff(c_91,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_89])).

tff(c_92,plain,(
    k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_39])).

tff(c_132,plain,(
    ! [A_32,B_33] :
      ( k3_tarski(a_2_0_tex_2(A_32,B_33)) = k2_pre_topc(A_32,B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32)
      | ~ v3_tdlat_3(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_135,plain,(
    ! [B_33] :
      ( k3_tarski(a_2_0_tex_2('#skF_1',B_33)) = k2_pre_topc('#skF_1',B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v3_tdlat_3('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_132])).

tff(c_137,plain,(
    ! [B_33] :
      ( k3_tarski(a_2_0_tex_2('#skF_1',B_33)) = k2_pre_topc('#skF_1',B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_135])).

tff(c_139,plain,(
    ! [B_34] :
      ( k3_tarski(a_2_0_tex_2('#skF_1',B_34)) = k2_pre_topc('#skF_1',B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_137])).

tff(c_142,plain,(
    k3_tarski(a_2_0_tex_2('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_139])).

tff(c_144,plain,(
    k3_tarski(a_2_0_tex_2('#skF_1','#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_142])).

tff(c_146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_144])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:39:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.19  
% 1.94/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.19  %$ v3_tex_2 > v1_tops_1 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_pre_topc > a_2_0_tex_2 > #nlpp > u1_struct_0 > k3_tarski > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.94/1.19  
% 1.94/1.19  %Foreground sorts:
% 1.94/1.19  
% 1.94/1.19  
% 1.94/1.19  %Background operators:
% 1.94/1.19  
% 1.94/1.19  
% 1.94/1.19  %Foreground operators:
% 1.94/1.19  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.94/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.19  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.94/1.19  tff(a_2_0_tex_2, type, a_2_0_tex_2: ($i * $i) > $i).
% 1.94/1.19  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 1.94/1.19  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 1.94/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.94/1.19  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.94/1.19  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 1.94/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.19  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.94/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.19  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.94/1.19  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.94/1.19  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 1.94/1.19  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 1.94/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.94/1.19  
% 1.94/1.21  tff(f_89, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) => (k3_tarski(a_2_0_tex_2(A, B)) = u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_tex_2)).
% 1.94/1.21  tff(f_33, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 1.94/1.21  tff(f_29, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 1.94/1.21  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 1.94/1.21  tff(f_72, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tex_2)).
% 1.94/1.21  tff(f_56, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k3_tarski(a_2_0_tex_2(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_tex_2)).
% 1.94/1.21  tff(c_20, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.94/1.21  tff(c_4, plain, (![A_2]: (l1_struct_0(A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.94/1.21  tff(c_28, plain, (![A_14]: (u1_struct_0(A_14)=k2_struct_0(A_14) | ~l1_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.94/1.21  tff(c_40, plain, (![A_17]: (u1_struct_0(A_17)=k2_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(resolution, [status(thm)], [c_4, c_28])).
% 1.94/1.21  tff(c_44, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_40])).
% 1.94/1.21  tff(c_14, plain, (k3_tarski(a_2_0_tex_2('#skF_1', '#skF_2'))!=u1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.94/1.21  tff(c_45, plain, (k3_tarski(a_2_0_tex_2('#skF_1', '#skF_2'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_14])).
% 1.94/1.21  tff(c_18, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.94/1.21  tff(c_33, plain, (![A_15, B_16]: (k2_pre_topc(A_15, B_16)=k2_struct_0(A_15) | ~v1_tops_1(B_16, A_15) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.94/1.21  tff(c_36, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_33])).
% 1.94/1.21  tff(c_39, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_36])).
% 1.94/1.21  tff(c_56, plain, (~v1_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_39])).
% 1.94/1.21  tff(c_16, plain, (v3_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.94/1.21  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_18])).
% 1.94/1.21  tff(c_26, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.94/1.21  tff(c_24, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.94/1.21  tff(c_22, plain, (v3_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.94/1.21  tff(c_76, plain, (![B_22, A_23]: (v1_tops_1(B_22, A_23) | ~v3_tex_2(B_22, A_23) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v3_tdlat_3(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.94/1.21  tff(c_79, plain, (![B_22]: (v1_tops_1(B_22, '#skF_1') | ~v3_tex_2(B_22, '#skF_1') | ~m1_subset_1(B_22, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v3_tdlat_3('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_76])).
% 1.94/1.21  tff(c_81, plain, (![B_22]: (v1_tops_1(B_22, '#skF_1') | ~v3_tex_2(B_22, '#skF_1') | ~m1_subset_1(B_22, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_79])).
% 1.94/1.21  tff(c_83, plain, (![B_24]: (v1_tops_1(B_24, '#skF_1') | ~v3_tex_2(B_24, '#skF_1') | ~m1_subset_1(B_24, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_26, c_81])).
% 1.94/1.21  tff(c_86, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v3_tex_2('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_83])).
% 1.94/1.21  tff(c_89, plain, (v1_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_86])).
% 1.94/1.21  tff(c_91, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_89])).
% 1.94/1.21  tff(c_92, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_39])).
% 1.94/1.21  tff(c_132, plain, (![A_32, B_33]: (k3_tarski(a_2_0_tex_2(A_32, B_33))=k2_pre_topc(A_32, B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32) | ~v3_tdlat_3(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.94/1.21  tff(c_135, plain, (![B_33]: (k3_tarski(a_2_0_tex_2('#skF_1', B_33))=k2_pre_topc('#skF_1', B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v3_tdlat_3('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_132])).
% 1.94/1.21  tff(c_137, plain, (![B_33]: (k3_tarski(a_2_0_tex_2('#skF_1', B_33))=k2_pre_topc('#skF_1', B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_135])).
% 1.94/1.21  tff(c_139, plain, (![B_34]: (k3_tarski(a_2_0_tex_2('#skF_1', B_34))=k2_pre_topc('#skF_1', B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_26, c_137])).
% 1.94/1.21  tff(c_142, plain, (k3_tarski(a_2_0_tex_2('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_139])).
% 1.94/1.21  tff(c_144, plain, (k3_tarski(a_2_0_tex_2('#skF_1', '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_142])).
% 1.94/1.21  tff(c_146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_144])).
% 1.94/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.21  
% 1.94/1.21  Inference rules
% 1.94/1.21  ----------------------
% 1.94/1.21  #Ref     : 0
% 1.94/1.21  #Sup     : 20
% 1.94/1.21  #Fact    : 0
% 1.94/1.21  #Define  : 0
% 1.94/1.21  #Split   : 1
% 1.94/1.21  #Chain   : 0
% 1.94/1.21  #Close   : 0
% 1.94/1.21  
% 1.94/1.21  Ordering : KBO
% 1.94/1.21  
% 1.94/1.21  Simplification rules
% 1.94/1.21  ----------------------
% 1.94/1.21  #Subsume      : 1
% 1.94/1.21  #Demod        : 23
% 1.94/1.21  #Tautology    : 7
% 1.94/1.21  #SimpNegUnit  : 7
% 1.94/1.21  #BackRed      : 2
% 1.94/1.21  
% 1.94/1.21  #Partial instantiations: 0
% 1.94/1.21  #Strategies tried      : 1
% 1.94/1.21  
% 1.94/1.21  Timing (in seconds)
% 1.94/1.21  ----------------------
% 1.94/1.21  Preprocessing        : 0.28
% 1.94/1.21  Parsing              : 0.15
% 1.94/1.21  CNF conversion       : 0.02
% 1.94/1.21  Main loop            : 0.14
% 1.94/1.21  Inferencing          : 0.05
% 1.94/1.21  Reduction            : 0.04
% 1.94/1.21  Demodulation         : 0.03
% 1.94/1.21  BG Simplification    : 0.01
% 1.94/1.21  Subsumption          : 0.02
% 1.94/1.21  Abstraction          : 0.01
% 1.94/1.21  MUC search           : 0.00
% 1.94/1.21  Cooper               : 0.00
% 1.94/1.21  Total                : 0.45
% 1.94/1.21  Index Insertion      : 0.00
% 1.94/1.21  Index Deletion       : 0.00
% 1.94/1.21  Index Matching       : 0.00
% 1.94/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
