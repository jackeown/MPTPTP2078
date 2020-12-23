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
% DateTime   : Thu Dec  3 10:28:56 EST 2020

% Result     : Theorem 5.83s
% Output     : CNFRefutation 6.10s
% Verified   : 
% Statistics : Number of formulae       :  165 (1687 expanded)
%              Number of leaves         :   39 ( 596 expanded)
%              Depth                    :   26
%              Number of atoms          :  375 (4587 expanded)
%              Number of equality atoms :   25 ( 501 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k9_setfam_1 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

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

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_190,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                & v1_tdlat_3(A) )
             => v1_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tex_2)).

tff(f_41,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_178,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_tdlat_3(A)
      <=> u1_pre_topc(A) = k9_setfam_1(u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tdlat_3)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_140,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_118,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_172,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_tdlat_3(A)
       => v2_pre_topc(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
       => v2_pre_topc(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_pre_topc)).

tff(f_136,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( ( v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v2_pre_topc(C)
                & l1_pre_topc(C) )
             => ( B = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C))
               => ( m1_pre_topc(B,A)
                <=> m1_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tmap_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
             => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_154,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> r1_tarski(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tops_2)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v1_tops_2(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C))))
                   => ( D = B
                     => v1_tops_2(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_2)).

tff(c_60,plain,(
    ~ v1_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_66,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_68,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_62,plain,(
    v1_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_16,plain,(
    ! [A_7] : k9_setfam_1(A_7) = k1_zfmisc_1(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_58,plain,(
    ! [A_68] :
      ( k9_setfam_1(u1_struct_0(A_68)) = u1_pre_topc(A_68)
      | ~ v1_tdlat_3(A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_70,plain,(
    ! [A_68] :
      ( k1_zfmisc_1(u1_struct_0(A_68)) = u1_pre_topc(A_68)
      | ~ v1_tdlat_3(A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_58])).

tff(c_123,plain,(
    ! [A_85] :
      ( m1_subset_1(u1_pre_topc(A_85),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_85))))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_127,plain,(
    ! [A_85] :
      ( r1_tarski(u1_pre_topc(A_85),k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(resolution,[status(thm)],[c_123,c_12])).

tff(c_64,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_46,plain,(
    ! [A_52] :
      ( m1_pre_topc(A_52,A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_247,plain,(
    ! [B_97,A_98] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_97),u1_pre_topc(B_97)),A_98)
      | ~ m1_pre_topc(B_97,A_98)
      | ~ l1_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_18,plain,(
    ! [B_10,A_8] :
      ( l1_pre_topc(B_10)
      | ~ m1_pre_topc(B_10,A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_264,plain,(
    ! [B_100,A_101] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(B_100),u1_pre_topc(B_100)))
      | ~ m1_pre_topc(B_100,A_101)
      | ~ l1_pre_topc(A_101) ) ),
    inference(resolution,[status(thm)],[c_247,c_18])).

tff(c_271,plain,(
    ! [A_102] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_102),u1_pre_topc(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(resolution,[status(thm)],[c_46,c_264])).

tff(c_274,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_271])).

tff(c_276,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_274])).

tff(c_289,plain,(
    ! [B_104,A_105] :
      ( m1_pre_topc(B_104,A_105)
      | ~ m1_pre_topc(B_104,g1_pre_topc(u1_struct_0(A_105),u1_pre_topc(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_309,plain,(
    ! [A_105] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(A_105),u1_pre_topc(A_105)),A_105)
      | ~ l1_pre_topc(A_105)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_105),u1_pre_topc(A_105))) ) ),
    inference(resolution,[status(thm)],[c_46,c_289])).

tff(c_54,plain,(
    ! [A_67] :
      ( v2_pre_topc(A_67)
      | ~ v1_tdlat_3(A_67)
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_22,plain,(
    ! [A_12] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_12),u1_pre_topc(A_12)))
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_162,plain,(
    ! [A_88] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_88),u1_pre_topc(A_88)))
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_165,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_162])).

tff(c_167,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_165])).

tff(c_168,plain,(
    ~ v2_pre_topc('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_176,plain,(
    ! [A_90] :
      ( v2_pre_topc(A_90)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(A_90),u1_pre_topc(A_90)))
      | ~ l1_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_185,plain,
    ( v2_pre_topc('#skF_2')
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_176])).

tff(c_189,plain,
    ( v2_pre_topc('#skF_2')
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_185])).

tff(c_190,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_168,c_189])).

tff(c_193,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_190])).

tff(c_199,plain,(
    ~ v2_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_193])).

tff(c_209,plain,
    ( ~ v1_tdlat_3('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_199])).

tff(c_213,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_62,c_209])).

tff(c_214,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_215,plain,(
    v2_pre_topc('#skF_2') ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_1295,plain,(
    ! [C_176,A_177] :
      ( m1_pre_topc(C_176,A_177)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_176),u1_pre_topc(C_176)),A_177)
      | ~ l1_pre_topc(C_176)
      | ~ v2_pre_topc(C_176)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_176),u1_pre_topc(C_176)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_176),u1_pre_topc(C_176)))
      | ~ l1_pre_topc(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1322,plain,(
    ! [A_177] :
      ( m1_pre_topc('#skF_2',A_177)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),A_177)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_177) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_1295])).

tff(c_1429,plain,(
    ! [A_178] :
      ( m1_pre_topc('#skF_2',A_178)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),A_178)
      | ~ l1_pre_topc(A_178) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_64,c_276,c_64,c_215,c_66,c_1322])).

tff(c_1439,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_309,c_1429])).

tff(c_1466,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_68,c_1439])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_656,plain,(
    ! [C_138,A_139,B_140] :
      ( m1_subset_1(C_138,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_139))))
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_140))))
      | ~ m1_pre_topc(B_140,A_139)
      | ~ l1_pre_topc(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_668,plain,(
    ! [A_5,A_139,B_140] :
      ( m1_subset_1(A_5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_139))))
      | ~ m1_pre_topc(B_140,A_139)
      | ~ l1_pre_topc(A_139)
      | ~ r1_tarski(A_5,k1_zfmisc_1(u1_struct_0(B_140))) ) ),
    inference(resolution,[status(thm)],[c_14,c_656])).

tff(c_1479,plain,(
    ! [A_5] :
      ( m1_subset_1(A_5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_5,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_1466,c_668])).

tff(c_2588,plain,(
    ! [A_210] :
      ( m1_subset_1(A_210,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ r1_tarski(A_210,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1479])).

tff(c_2616,plain,(
    ! [A_211] :
      ( r1_tarski(A_211,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_211,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_2588,c_12])).

tff(c_2643,plain,
    ( r1_tarski(u1_pre_topc('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_127,c_2616])).

tff(c_2663,plain,(
    r1_tarski(u1_pre_topc('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2643])).

tff(c_2675,plain,
    ( r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_1'))
    | ~ v1_tdlat_3('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_2663])).

tff(c_2684,plain,(
    r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_62,c_2675])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2693,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_1')
    | ~ r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2684,c_2])).

tff(c_2801,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2693])).

tff(c_223,plain,(
    ! [A_94] :
      ( v2_pre_topc(A_94)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(A_94),u1_pre_topc(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_226,plain,
    ( v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_214,c_223])).

tff(c_238,plain,(
    v2_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_226])).

tff(c_300,plain,(
    ! [B_104] :
      ( m1_pre_topc(B_104,'#skF_2')
      | ~ m1_pre_topc(B_104,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_289])).

tff(c_310,plain,(
    ! [B_106] :
      ( m1_pre_topc(B_106,'#skF_2')
      | ~ m1_pre_topc(B_106,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_300])).

tff(c_322,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_46,c_310])).

tff(c_331,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_322])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_807,plain,(
    ! [B_159,C_160,A_161] :
      ( m1_pre_topc(B_159,C_160)
      | ~ r1_tarski(u1_struct_0(B_159),u1_struct_0(C_160))
      | ~ m1_pre_topc(C_160,A_161)
      | ~ m1_pre_topc(B_159,A_161)
      | ~ l1_pre_topc(A_161)
      | ~ v2_pre_topc(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_819,plain,(
    ! [B_162,A_163] :
      ( m1_pre_topc(B_162,B_162)
      | ~ m1_pre_topc(B_162,A_163)
      | ~ l1_pre_topc(A_163)
      | ~ v2_pre_topc(A_163) ) ),
    inference(resolution,[status(thm)],[c_6,c_807])).

tff(c_827,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_331,c_819])).

tff(c_843,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_66,c_827])).

tff(c_1301,plain,
    ( m1_pre_topc('#skF_1',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_843,c_1295])).

tff(c_1332,plain,(
    m1_pre_topc('#skF_1',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_214,c_238,c_68,c_1301])).

tff(c_1313,plain,
    ( m1_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_331,c_1295])).

tff(c_1342,plain,(
    m1_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_214,c_276,c_238,c_68,c_1313])).

tff(c_8,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_71,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_710,plain,(
    ! [B_146,A_147] :
      ( m1_subset_1(k1_zfmisc_1(u1_struct_0(B_146)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_147))))
      | ~ m1_pre_topc(B_146,A_147)
      | ~ l1_pre_topc(A_147) ) ),
    inference(resolution,[status(thm)],[c_71,c_656])).

tff(c_731,plain,(
    ! [B_146,A_147] :
      ( r1_tarski(k1_zfmisc_1(u1_struct_0(B_146)),k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ m1_pre_topc(B_146,A_147)
      | ~ l1_pre_topc(A_147) ) ),
    inference(resolution,[status(thm)],[c_710,c_12])).

tff(c_2636,plain,(
    ! [B_146] :
      ( r1_tarski(k1_zfmisc_1(u1_struct_0(B_146)),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_146,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_731,c_2616])).

tff(c_3025,plain,(
    ! [B_221] :
      ( r1_tarski(k1_zfmisc_1(u1_struct_0(B_221)),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_221,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2636])).

tff(c_3039,plain,(
    ! [B_221] :
      ( r1_tarski(k1_zfmisc_1(u1_struct_0(B_221)),u1_pre_topc('#skF_1'))
      | ~ m1_pre_topc(B_221,'#skF_2')
      | ~ v1_tdlat_3('#skF_1')
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_3025])).

tff(c_3049,plain,(
    ! [B_222] :
      ( r1_tarski(k1_zfmisc_1(u1_struct_0(B_222)),u1_pre_topc('#skF_1'))
      | ~ m1_pre_topc(B_222,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_62,c_3039])).

tff(c_128,plain,(
    ! [A_86] :
      ( r1_tarski(u1_pre_topc(A_86),k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(resolution,[status(thm)],[c_123,c_12])).

tff(c_131,plain,(
    ! [A_86] :
      ( k1_zfmisc_1(u1_struct_0(A_86)) = u1_pre_topc(A_86)
      | ~ r1_tarski(k1_zfmisc_1(u1_struct_0(A_86)),u1_pre_topc(A_86))
      | ~ l1_pre_topc(A_86) ) ),
    inference(resolution,[status(thm)],[c_128,c_2])).

tff(c_3060,plain,
    ( k1_zfmisc_1(u1_struct_0('#skF_1')) = u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_3049,c_131])).

tff(c_3074,plain,(
    k1_zfmisc_1(u1_struct_0('#skF_1')) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1342,c_68,c_3060])).

tff(c_931,plain,(
    ! [A_164,A_165,B_166] :
      ( m1_subset_1(A_164,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_165))))
      | ~ m1_pre_topc(B_166,A_165)
      | ~ l1_pre_topc(A_165)
      | ~ r1_tarski(A_164,k1_zfmisc_1(u1_struct_0(B_166))) ) ),
    inference(resolution,[status(thm)],[c_14,c_656])).

tff(c_943,plain,(
    ! [A_164] :
      ( m1_subset_1(A_164,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_164,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ) ),
    inference(resolution,[status(thm)],[c_331,c_931])).

tff(c_969,plain,(
    ! [A_167] :
      ( m1_subset_1(A_167,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ r1_tarski(A_167,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_943])).

tff(c_977,plain,(
    ! [B_146] :
      ( m1_subset_1(k1_zfmisc_1(u1_struct_0(B_146)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ m1_pre_topc(B_146,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_731,c_969])).

tff(c_1125,plain,(
    ! [B_171] :
      ( m1_subset_1(k1_zfmisc_1(u1_struct_0(B_171)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ m1_pre_topc(B_171,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_977])).

tff(c_1153,plain,(
    ! [B_171] :
      ( r1_tarski(k1_zfmisc_1(u1_struct_0(B_171)),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_171,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_1125,c_12])).

tff(c_3114,plain,
    ( r1_tarski(u1_pre_topc('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_pre_topc('#skF_1',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3074,c_1153])).

tff(c_3203,plain,(
    r1_tarski(u1_pre_topc('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1332,c_3114])).

tff(c_495,plain,(
    ! [B_126,A_127] :
      ( r1_tarski(B_126,u1_pre_topc(A_127))
      | ~ v1_tops_2(B_126,A_127)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_127))))
      | ~ l1_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_512,plain,(
    ! [A_5,A_127] :
      ( r1_tarski(A_5,u1_pre_topc(A_127))
      | ~ v1_tops_2(A_5,A_127)
      | ~ l1_pre_topc(A_127)
      | ~ r1_tarski(A_5,k1_zfmisc_1(u1_struct_0(A_127))) ) ),
    inference(resolution,[status(thm)],[c_14,c_495])).

tff(c_3346,plain,
    ( r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc('#skF_2'))
    | ~ v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_3203,c_512])).

tff(c_3359,plain,
    ( r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc('#skF_2'))
    | ~ v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3346])).

tff(c_3360,plain,(
    ~ v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_2801,c_3359])).

tff(c_2664,plain,(
    r1_tarski(k1_zfmisc_1(u1_struct_0('#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_6,c_2616])).

tff(c_2752,plain,
    ( r1_tarski(k1_zfmisc_1(u1_struct_0('#skF_2')),u1_pre_topc('#skF_1'))
    | ~ v1_tdlat_3('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_2664])).

tff(c_2763,plain,(
    r1_tarski(k1_zfmisc_1(u1_struct_0('#skF_2')),u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_62,c_2752])).

tff(c_3351,plain,
    ( k1_zfmisc_1(u1_struct_0('#skF_2')) = u1_pre_topc('#skF_1')
    | ~ r1_tarski(k1_zfmisc_1(u1_struct_0('#skF_2')),u1_pre_topc('#skF_1')) ),
    inference(resolution,[status(thm)],[c_3203,c_2])).

tff(c_3366,plain,(
    k1_zfmisc_1(u1_struct_0('#skF_2')) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2763,c_3351])).

tff(c_732,plain,(
    ! [B_148,A_149] :
      ( r1_tarski(k1_zfmisc_1(u1_struct_0(B_148)),k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ m1_pre_topc(B_148,A_149)
      | ~ l1_pre_topc(A_149) ) ),
    inference(resolution,[status(thm)],[c_710,c_12])).

tff(c_746,plain,(
    ! [B_148,A_68] :
      ( r1_tarski(k1_zfmisc_1(u1_struct_0(B_148)),u1_pre_topc(A_68))
      | ~ m1_pre_topc(B_148,A_68)
      | ~ l1_pre_topc(A_68)
      | ~ v1_tdlat_3(A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_732])).

tff(c_436,plain,(
    ! [B_118,A_119] :
      ( v1_tops_2(B_118,A_119)
      | ~ r1_tarski(B_118,u1_pre_topc(A_119))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_119))))
      | ~ l1_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_454,plain,(
    ! [A_5,A_119] :
      ( v1_tops_2(A_5,A_119)
      | ~ r1_tarski(A_5,u1_pre_topc(A_119))
      | ~ l1_pre_topc(A_119)
      | ~ r1_tarski(A_5,k1_zfmisc_1(u1_struct_0(A_119))) ) ),
    inference(resolution,[status(thm)],[c_14,c_436])).

tff(c_3157,plain,(
    ! [A_5] :
      ( v1_tops_2(A_5,'#skF_1')
      | ~ r1_tarski(A_5,u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_5,u1_pre_topc('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3074,c_454])).

tff(c_3557,plain,(
    ! [A_226] :
      ( v1_tops_2(A_226,'#skF_1')
      | ~ r1_tarski(A_226,u1_pre_topc('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3157])).

tff(c_3570,plain,(
    ! [B_148] :
      ( v1_tops_2(k1_zfmisc_1(u1_struct_0(B_148)),'#skF_1')
      | ~ m1_pre_topc(B_148,'#skF_1')
      | ~ v1_tdlat_3('#skF_1')
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_746,c_3557])).

tff(c_3586,plain,(
    ! [B_148] :
      ( v1_tops_2(k1_zfmisc_1(u1_struct_0(B_148)),'#skF_1')
      | ~ m1_pre_topc(B_148,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_62,c_3570])).

tff(c_669,plain,(
    ! [B_140,A_139] :
      ( m1_subset_1(k1_zfmisc_1(u1_struct_0(B_140)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_139))))
      | ~ m1_pre_topc(B_140,A_139)
      | ~ l1_pre_topc(A_139) ) ),
    inference(resolution,[status(thm)],[c_71,c_656])).

tff(c_1074,plain,(
    ! [D_168,C_169,A_170] :
      ( v1_tops_2(D_168,C_169)
      | ~ m1_subset_1(D_168,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_169))))
      | ~ v1_tops_2(D_168,A_170)
      | ~ m1_pre_topc(C_169,A_170)
      | ~ m1_subset_1(D_168,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_170))))
      | ~ l1_pre_topc(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_3523,plain,(
    ! [C_224,A_225] :
      ( v1_tops_2(k1_zfmisc_1(u1_struct_0(C_224)),C_224)
      | ~ v1_tops_2(k1_zfmisc_1(u1_struct_0(C_224)),A_225)
      | ~ m1_pre_topc(C_224,A_225)
      | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(C_224)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_225))))
      | ~ l1_pre_topc(A_225) ) ),
    inference(resolution,[status(thm)],[c_71,c_1074])).

tff(c_4117,plain,(
    ! [B_249,A_250] :
      ( v1_tops_2(k1_zfmisc_1(u1_struct_0(B_249)),B_249)
      | ~ v1_tops_2(k1_zfmisc_1(u1_struct_0(B_249)),A_250)
      | ~ m1_pre_topc(B_249,A_250)
      | ~ l1_pre_topc(A_250) ) ),
    inference(resolution,[status(thm)],[c_669,c_3523])).

tff(c_4121,plain,(
    ! [B_148] :
      ( v1_tops_2(k1_zfmisc_1(u1_struct_0(B_148)),B_148)
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_pre_topc(B_148,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_3586,c_4117])).

tff(c_4145,plain,(
    ! [B_251] :
      ( v1_tops_2(k1_zfmisc_1(u1_struct_0(B_251)),B_251)
      | ~ m1_pre_topc(B_251,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4121])).

tff(c_4153,plain,
    ( v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3366,c_4145])).

tff(c_4163,plain,(
    v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1466,c_4153])).

tff(c_4165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3360,c_4163])).

tff(c_4166,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2693])).

tff(c_4241,plain,
    ( k1_zfmisc_1(u1_struct_0('#skF_2')) = u1_pre_topc('#skF_2')
    | ~ r1_tarski(k1_zfmisc_1(u1_struct_0('#skF_2')),u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4166,c_131])).

tff(c_4318,plain,(
    k1_zfmisc_1(u1_struct_0('#skF_2')) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2763,c_4166,c_4241])).

tff(c_56,plain,(
    ! [A_68] :
      ( v1_tdlat_3(A_68)
      | k9_setfam_1(u1_struct_0(A_68)) != u1_pre_topc(A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_69,plain,(
    ! [A_68] :
      ( v1_tdlat_3(A_68)
      | k1_zfmisc_1(u1_struct_0(A_68)) != u1_pre_topc(A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_56])).

tff(c_4426,plain,
    ( v1_tdlat_3('#skF_2')
    | u1_pre_topc('#skF_2') != u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4318,c_69])).

tff(c_4476,plain,(
    v1_tdlat_3('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4166,c_4426])).

tff(c_4478,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_4476])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:11:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.83/2.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.83/2.11  
% 5.83/2.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.83/2.12  %$ v1_tops_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k9_setfam_1 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 5.83/2.12  
% 5.83/2.12  %Foreground sorts:
% 5.83/2.12  
% 5.83/2.12  
% 5.83/2.12  %Background operators:
% 5.83/2.12  
% 5.83/2.12  
% 5.83/2.12  %Foreground operators:
% 5.83/2.12  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 5.83/2.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.83/2.12  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 5.83/2.12  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 5.83/2.12  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.83/2.12  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 5.83/2.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.83/2.12  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 5.83/2.12  tff('#skF_2', type, '#skF_2': $i).
% 5.83/2.12  tff('#skF_1', type, '#skF_1': $i).
% 5.83/2.12  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 5.83/2.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.83/2.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.83/2.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.83/2.12  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.83/2.12  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.83/2.12  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.83/2.12  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.83/2.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.83/2.12  
% 6.10/2.17  tff(f_190, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & v1_tdlat_3(A)) => v1_tdlat_3(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_tex_2)).
% 6.10/2.17  tff(f_41, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 6.10/2.17  tff(f_178, axiom, (![A]: (l1_pre_topc(A) => (v1_tdlat_3(A) <=> (u1_pre_topc(A) = k9_setfam_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tdlat_3)).
% 6.10/2.17  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 6.10/2.17  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.10/2.17  tff(f_140, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 6.10/2.17  tff(f_118, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tmap_1)).
% 6.10/2.17  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 6.10/2.17  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 6.10/2.17  tff(f_172, axiom, (![A]: (l1_pre_topc(A) => (v1_tdlat_3(A) => v2_pre_topc(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tdlat_3)).
% 6.10/2.17  tff(f_60, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_pre_topc)).
% 6.10/2.17  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => v2_pre_topc(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_pre_topc)).
% 6.10/2.17  tff(f_136, axiom, (![A]: (l1_pre_topc(A) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((B = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) => (m1_pre_topc(B, A) <=> m1_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_tmap_1)).
% 6.10/2.17  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_tops_2)).
% 6.10/2.17  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.10/2.17  tff(f_154, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 6.10/2.17  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 6.10/2.17  tff(f_35, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 6.10/2.17  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> r1_tarski(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_tops_2)).
% 6.10/2.17  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_pre_topc(C, A) => (v1_tops_2(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C)))) => ((D = B) => v1_tops_2(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tops_2)).
% 6.10/2.17  tff(c_60, plain, (~v1_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_190])).
% 6.10/2.17  tff(c_66, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_190])).
% 6.10/2.17  tff(c_68, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_190])).
% 6.10/2.17  tff(c_62, plain, (v1_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_190])).
% 6.10/2.17  tff(c_16, plain, (![A_7]: (k9_setfam_1(A_7)=k1_zfmisc_1(A_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.10/2.17  tff(c_58, plain, (![A_68]: (k9_setfam_1(u1_struct_0(A_68))=u1_pre_topc(A_68) | ~v1_tdlat_3(A_68) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_178])).
% 6.10/2.17  tff(c_70, plain, (![A_68]: (k1_zfmisc_1(u1_struct_0(A_68))=u1_pre_topc(A_68) | ~v1_tdlat_3(A_68) | ~l1_pre_topc(A_68))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_58])).
% 6.10/2.17  tff(c_123, plain, (![A_85]: (m1_subset_1(u1_pre_topc(A_85), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_85)))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.10/2.17  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.10/2.17  tff(c_127, plain, (![A_85]: (r1_tarski(u1_pre_topc(A_85), k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(resolution, [status(thm)], [c_123, c_12])).
% 6.10/2.17  tff(c_64, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_190])).
% 6.10/2.17  tff(c_46, plain, (![A_52]: (m1_pre_topc(A_52, A_52) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.10/2.17  tff(c_247, plain, (![B_97, A_98]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_97), u1_pre_topc(B_97)), A_98) | ~m1_pre_topc(B_97, A_98) | ~l1_pre_topc(A_98))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.10/2.17  tff(c_18, plain, (![B_10, A_8]: (l1_pre_topc(B_10) | ~m1_pre_topc(B_10, A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.10/2.17  tff(c_264, plain, (![B_100, A_101]: (l1_pre_topc(g1_pre_topc(u1_struct_0(B_100), u1_pre_topc(B_100))) | ~m1_pre_topc(B_100, A_101) | ~l1_pre_topc(A_101))), inference(resolution, [status(thm)], [c_247, c_18])).
% 6.10/2.17  tff(c_271, plain, (![A_102]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_102), u1_pre_topc(A_102))) | ~l1_pre_topc(A_102))), inference(resolution, [status(thm)], [c_46, c_264])).
% 6.10/2.17  tff(c_274, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_64, c_271])).
% 6.10/2.17  tff(c_276, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_274])).
% 6.10/2.17  tff(c_289, plain, (![B_104, A_105]: (m1_pre_topc(B_104, A_105) | ~m1_pre_topc(B_104, g1_pre_topc(u1_struct_0(A_105), u1_pre_topc(A_105))) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.10/2.17  tff(c_309, plain, (![A_105]: (m1_pre_topc(g1_pre_topc(u1_struct_0(A_105), u1_pre_topc(A_105)), A_105) | ~l1_pre_topc(A_105) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_105), u1_pre_topc(A_105))))), inference(resolution, [status(thm)], [c_46, c_289])).
% 6.10/2.17  tff(c_54, plain, (![A_67]: (v2_pre_topc(A_67) | ~v1_tdlat_3(A_67) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_172])).
% 6.10/2.17  tff(c_22, plain, (![A_12]: (v2_pre_topc(g1_pre_topc(u1_struct_0(A_12), u1_pre_topc(A_12))) | ~l1_pre_topc(A_12) | ~v2_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.10/2.17  tff(c_162, plain, (![A_88]: (v2_pre_topc(g1_pre_topc(u1_struct_0(A_88), u1_pre_topc(A_88))) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.10/2.17  tff(c_165, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_64, c_162])).
% 6.10/2.17  tff(c_167, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_165])).
% 6.10/2.17  tff(c_168, plain, (~v2_pre_topc('#skF_2')), inference(splitLeft, [status(thm)], [c_167])).
% 6.10/2.17  tff(c_176, plain, (![A_90]: (v2_pre_topc(A_90) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(A_90), u1_pre_topc(A_90))) | ~l1_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.10/2.17  tff(c_185, plain, (v2_pre_topc('#skF_2') | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_64, c_176])).
% 6.10/2.17  tff(c_189, plain, (v2_pre_topc('#skF_2') | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_185])).
% 6.10/2.17  tff(c_190, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_168, c_189])).
% 6.10/2.17  tff(c_193, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_190])).
% 6.10/2.17  tff(c_199, plain, (~v2_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_193])).
% 6.10/2.17  tff(c_209, plain, (~v1_tdlat_3('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_199])).
% 6.10/2.17  tff(c_213, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_62, c_209])).
% 6.10/2.17  tff(c_214, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_167])).
% 6.10/2.17  tff(c_215, plain, (v2_pre_topc('#skF_2')), inference(splitRight, [status(thm)], [c_167])).
% 6.10/2.17  tff(c_1295, plain, (![C_176, A_177]: (m1_pre_topc(C_176, A_177) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_176), u1_pre_topc(C_176)), A_177) | ~l1_pre_topc(C_176) | ~v2_pre_topc(C_176) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_176), u1_pre_topc(C_176))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_176), u1_pre_topc(C_176))) | ~l1_pre_topc(A_177))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.10/2.17  tff(c_1322, plain, (![A_177]: (m1_pre_topc('#skF_2', A_177) | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), A_177) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_177))), inference(superposition, [status(thm), theory('equality')], [c_64, c_1295])).
% 6.10/2.17  tff(c_1429, plain, (![A_178]: (m1_pre_topc('#skF_2', A_178) | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), A_178) | ~l1_pre_topc(A_178))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_64, c_276, c_64, c_215, c_66, c_1322])).
% 6.10/2.17  tff(c_1439, plain, (m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_309, c_1429])).
% 6.10/2.17  tff(c_1466, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_276, c_68, c_1439])).
% 6.10/2.17  tff(c_14, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.10/2.17  tff(c_656, plain, (![C_138, A_139, B_140]: (m1_subset_1(C_138, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_139)))) | ~m1_subset_1(C_138, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_140)))) | ~m1_pre_topc(B_140, A_139) | ~l1_pre_topc(A_139))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.10/2.17  tff(c_668, plain, (![A_5, A_139, B_140]: (m1_subset_1(A_5, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_139)))) | ~m1_pre_topc(B_140, A_139) | ~l1_pre_topc(A_139) | ~r1_tarski(A_5, k1_zfmisc_1(u1_struct_0(B_140))))), inference(resolution, [status(thm)], [c_14, c_656])).
% 6.10/2.17  tff(c_1479, plain, (![A_5]: (m1_subset_1(A_5, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_5, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_1466, c_668])).
% 6.10/2.17  tff(c_2588, plain, (![A_210]: (m1_subset_1(A_210, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~r1_tarski(A_210, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1479])).
% 6.10/2.17  tff(c_2616, plain, (![A_211]: (r1_tarski(A_211, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_211, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_2588, c_12])).
% 6.10/2.17  tff(c_2643, plain, (r1_tarski(u1_pre_topc('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_127, c_2616])).
% 6.10/2.17  tff(c_2663, plain, (r1_tarski(u1_pre_topc('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2643])).
% 6.10/2.17  tff(c_2675, plain, (r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_1')) | ~v1_tdlat_3('#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_70, c_2663])).
% 6.10/2.17  tff(c_2684, plain, (r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_62, c_2675])).
% 6.10/2.17  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.10/2.17  tff(c_2693, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_1') | ~r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_2684, c_2])).
% 6.10/2.17  tff(c_2801, plain, (~r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc('#skF_2'))), inference(splitLeft, [status(thm)], [c_2693])).
% 6.10/2.17  tff(c_223, plain, (![A_94]: (v2_pre_topc(A_94) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(A_94), u1_pre_topc(A_94))) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.10/2.17  tff(c_226, plain, (v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_214, c_223])).
% 6.10/2.17  tff(c_238, plain, (v2_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_226])).
% 6.10/2.17  tff(c_300, plain, (![B_104]: (m1_pre_topc(B_104, '#skF_2') | ~m1_pre_topc(B_104, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_289])).
% 6.10/2.17  tff(c_310, plain, (![B_106]: (m1_pre_topc(B_106, '#skF_2') | ~m1_pre_topc(B_106, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_300])).
% 6.10/2.17  tff(c_322, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_46, c_310])).
% 6.10/2.17  tff(c_331, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_276, c_322])).
% 6.10/2.17  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.10/2.17  tff(c_807, plain, (![B_159, C_160, A_161]: (m1_pre_topc(B_159, C_160) | ~r1_tarski(u1_struct_0(B_159), u1_struct_0(C_160)) | ~m1_pre_topc(C_160, A_161) | ~m1_pre_topc(B_159, A_161) | ~l1_pre_topc(A_161) | ~v2_pre_topc(A_161))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.10/2.17  tff(c_819, plain, (![B_162, A_163]: (m1_pre_topc(B_162, B_162) | ~m1_pre_topc(B_162, A_163) | ~l1_pre_topc(A_163) | ~v2_pre_topc(A_163))), inference(resolution, [status(thm)], [c_6, c_807])).
% 6.10/2.17  tff(c_827, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_331, c_819])).
% 6.10/2.17  tff(c_843, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_66, c_827])).
% 6.10/2.17  tff(c_1301, plain, (m1_pre_topc('#skF_1', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_843, c_1295])).
% 6.10/2.17  tff(c_1332, plain, (m1_pre_topc('#skF_1', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_276, c_214, c_238, c_68, c_1301])).
% 6.10/2.17  tff(c_1313, plain, (m1_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_331, c_1295])).
% 6.10/2.17  tff(c_1342, plain, (m1_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_214, c_276, c_238, c_68, c_1313])).
% 6.10/2.17  tff(c_8, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.10/2.17  tff(c_10, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.10/2.17  tff(c_71, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 6.10/2.17  tff(c_710, plain, (![B_146, A_147]: (m1_subset_1(k1_zfmisc_1(u1_struct_0(B_146)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_147)))) | ~m1_pre_topc(B_146, A_147) | ~l1_pre_topc(A_147))), inference(resolution, [status(thm)], [c_71, c_656])).
% 6.10/2.17  tff(c_731, plain, (![B_146, A_147]: (r1_tarski(k1_zfmisc_1(u1_struct_0(B_146)), k1_zfmisc_1(u1_struct_0(A_147))) | ~m1_pre_topc(B_146, A_147) | ~l1_pre_topc(A_147))), inference(resolution, [status(thm)], [c_710, c_12])).
% 6.10/2.17  tff(c_2636, plain, (![B_146]: (r1_tarski(k1_zfmisc_1(u1_struct_0(B_146)), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_pre_topc(B_146, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_731, c_2616])).
% 6.10/2.17  tff(c_3025, plain, (![B_221]: (r1_tarski(k1_zfmisc_1(u1_struct_0(B_221)), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_pre_topc(B_221, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2636])).
% 6.10/2.17  tff(c_3039, plain, (![B_221]: (r1_tarski(k1_zfmisc_1(u1_struct_0(B_221)), u1_pre_topc('#skF_1')) | ~m1_pre_topc(B_221, '#skF_2') | ~v1_tdlat_3('#skF_1') | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_3025])).
% 6.10/2.17  tff(c_3049, plain, (![B_222]: (r1_tarski(k1_zfmisc_1(u1_struct_0(B_222)), u1_pre_topc('#skF_1')) | ~m1_pre_topc(B_222, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_62, c_3039])).
% 6.10/2.17  tff(c_128, plain, (![A_86]: (r1_tarski(u1_pre_topc(A_86), k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(resolution, [status(thm)], [c_123, c_12])).
% 6.10/2.17  tff(c_131, plain, (![A_86]: (k1_zfmisc_1(u1_struct_0(A_86))=u1_pre_topc(A_86) | ~r1_tarski(k1_zfmisc_1(u1_struct_0(A_86)), u1_pre_topc(A_86)) | ~l1_pre_topc(A_86))), inference(resolution, [status(thm)], [c_128, c_2])).
% 6.10/2.17  tff(c_3060, plain, (k1_zfmisc_1(u1_struct_0('#skF_1'))=u1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~m1_pre_topc('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_3049, c_131])).
% 6.10/2.17  tff(c_3074, plain, (k1_zfmisc_1(u1_struct_0('#skF_1'))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1342, c_68, c_3060])).
% 6.10/2.17  tff(c_931, plain, (![A_164, A_165, B_166]: (m1_subset_1(A_164, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_165)))) | ~m1_pre_topc(B_166, A_165) | ~l1_pre_topc(A_165) | ~r1_tarski(A_164, k1_zfmisc_1(u1_struct_0(B_166))))), inference(resolution, [status(thm)], [c_14, c_656])).
% 6.10/2.17  tff(c_943, plain, (![A_164]: (m1_subset_1(A_164, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_164, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))))), inference(resolution, [status(thm)], [c_331, c_931])).
% 6.10/2.17  tff(c_969, plain, (![A_167]: (m1_subset_1(A_167, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~r1_tarski(A_167, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_943])).
% 6.10/2.17  tff(c_977, plain, (![B_146]: (m1_subset_1(k1_zfmisc_1(u1_struct_0(B_146)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~m1_pre_topc(B_146, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(resolution, [status(thm)], [c_731, c_969])).
% 6.10/2.17  tff(c_1125, plain, (![B_171]: (m1_subset_1(k1_zfmisc_1(u1_struct_0(B_171)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~m1_pre_topc(B_171, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_276, c_977])).
% 6.10/2.17  tff(c_1153, plain, (![B_171]: (r1_tarski(k1_zfmisc_1(u1_struct_0(B_171)), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc(B_171, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(resolution, [status(thm)], [c_1125, c_12])).
% 6.10/2.17  tff(c_3114, plain, (r1_tarski(u1_pre_topc('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_1', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_3074, c_1153])).
% 6.10/2.17  tff(c_3203, plain, (r1_tarski(u1_pre_topc('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1332, c_3114])).
% 6.10/2.17  tff(c_495, plain, (![B_126, A_127]: (r1_tarski(B_126, u1_pre_topc(A_127)) | ~v1_tops_2(B_126, A_127) | ~m1_subset_1(B_126, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_127)))) | ~l1_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.10/2.17  tff(c_512, plain, (![A_5, A_127]: (r1_tarski(A_5, u1_pre_topc(A_127)) | ~v1_tops_2(A_5, A_127) | ~l1_pre_topc(A_127) | ~r1_tarski(A_5, k1_zfmisc_1(u1_struct_0(A_127))))), inference(resolution, [status(thm)], [c_14, c_495])).
% 6.10/2.17  tff(c_3346, plain, (r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc('#skF_2')) | ~v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_3203, c_512])).
% 6.10/2.17  tff(c_3359, plain, (r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc('#skF_2')) | ~v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3346])).
% 6.10/2.17  tff(c_3360, plain, (~v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_2801, c_3359])).
% 6.10/2.17  tff(c_2664, plain, (r1_tarski(k1_zfmisc_1(u1_struct_0('#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_2616])).
% 6.10/2.17  tff(c_2752, plain, (r1_tarski(k1_zfmisc_1(u1_struct_0('#skF_2')), u1_pre_topc('#skF_1')) | ~v1_tdlat_3('#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_70, c_2664])).
% 6.10/2.17  tff(c_2763, plain, (r1_tarski(k1_zfmisc_1(u1_struct_0('#skF_2')), u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_62, c_2752])).
% 6.10/2.17  tff(c_3351, plain, (k1_zfmisc_1(u1_struct_0('#skF_2'))=u1_pre_topc('#skF_1') | ~r1_tarski(k1_zfmisc_1(u1_struct_0('#skF_2')), u1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_3203, c_2])).
% 6.10/2.17  tff(c_3366, plain, (k1_zfmisc_1(u1_struct_0('#skF_2'))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2763, c_3351])).
% 6.10/2.17  tff(c_732, plain, (![B_148, A_149]: (r1_tarski(k1_zfmisc_1(u1_struct_0(B_148)), k1_zfmisc_1(u1_struct_0(A_149))) | ~m1_pre_topc(B_148, A_149) | ~l1_pre_topc(A_149))), inference(resolution, [status(thm)], [c_710, c_12])).
% 6.10/2.17  tff(c_746, plain, (![B_148, A_68]: (r1_tarski(k1_zfmisc_1(u1_struct_0(B_148)), u1_pre_topc(A_68)) | ~m1_pre_topc(B_148, A_68) | ~l1_pre_topc(A_68) | ~v1_tdlat_3(A_68) | ~l1_pre_topc(A_68))), inference(superposition, [status(thm), theory('equality')], [c_70, c_732])).
% 6.10/2.17  tff(c_436, plain, (![B_118, A_119]: (v1_tops_2(B_118, A_119) | ~r1_tarski(B_118, u1_pre_topc(A_119)) | ~m1_subset_1(B_118, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_119)))) | ~l1_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.10/2.17  tff(c_454, plain, (![A_5, A_119]: (v1_tops_2(A_5, A_119) | ~r1_tarski(A_5, u1_pre_topc(A_119)) | ~l1_pre_topc(A_119) | ~r1_tarski(A_5, k1_zfmisc_1(u1_struct_0(A_119))))), inference(resolution, [status(thm)], [c_14, c_436])).
% 6.10/2.17  tff(c_3157, plain, (![A_5]: (v1_tops_2(A_5, '#skF_1') | ~r1_tarski(A_5, u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_5, u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_3074, c_454])).
% 6.10/2.17  tff(c_3557, plain, (![A_226]: (v1_tops_2(A_226, '#skF_1') | ~r1_tarski(A_226, u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_3157])).
% 6.10/2.17  tff(c_3570, plain, (![B_148]: (v1_tops_2(k1_zfmisc_1(u1_struct_0(B_148)), '#skF_1') | ~m1_pre_topc(B_148, '#skF_1') | ~v1_tdlat_3('#skF_1') | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_746, c_3557])).
% 6.10/2.17  tff(c_3586, plain, (![B_148]: (v1_tops_2(k1_zfmisc_1(u1_struct_0(B_148)), '#skF_1') | ~m1_pre_topc(B_148, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_62, c_3570])).
% 6.10/2.17  tff(c_669, plain, (![B_140, A_139]: (m1_subset_1(k1_zfmisc_1(u1_struct_0(B_140)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_139)))) | ~m1_pre_topc(B_140, A_139) | ~l1_pre_topc(A_139))), inference(resolution, [status(thm)], [c_71, c_656])).
% 6.10/2.17  tff(c_1074, plain, (![D_168, C_169, A_170]: (v1_tops_2(D_168, C_169) | ~m1_subset_1(D_168, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_169)))) | ~v1_tops_2(D_168, A_170) | ~m1_pre_topc(C_169, A_170) | ~m1_subset_1(D_168, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_170)))) | ~l1_pre_topc(A_170))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.10/2.17  tff(c_3523, plain, (![C_224, A_225]: (v1_tops_2(k1_zfmisc_1(u1_struct_0(C_224)), C_224) | ~v1_tops_2(k1_zfmisc_1(u1_struct_0(C_224)), A_225) | ~m1_pre_topc(C_224, A_225) | ~m1_subset_1(k1_zfmisc_1(u1_struct_0(C_224)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_225)))) | ~l1_pre_topc(A_225))), inference(resolution, [status(thm)], [c_71, c_1074])).
% 6.10/2.17  tff(c_4117, plain, (![B_249, A_250]: (v1_tops_2(k1_zfmisc_1(u1_struct_0(B_249)), B_249) | ~v1_tops_2(k1_zfmisc_1(u1_struct_0(B_249)), A_250) | ~m1_pre_topc(B_249, A_250) | ~l1_pre_topc(A_250))), inference(resolution, [status(thm)], [c_669, c_3523])).
% 6.10/2.17  tff(c_4121, plain, (![B_148]: (v1_tops_2(k1_zfmisc_1(u1_struct_0(B_148)), B_148) | ~l1_pre_topc('#skF_1') | ~m1_pre_topc(B_148, '#skF_1'))), inference(resolution, [status(thm)], [c_3586, c_4117])).
% 6.10/2.17  tff(c_4145, plain, (![B_251]: (v1_tops_2(k1_zfmisc_1(u1_struct_0(B_251)), B_251) | ~m1_pre_topc(B_251, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_4121])).
% 6.10/2.17  tff(c_4153, plain, (v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3366, c_4145])).
% 6.10/2.17  tff(c_4163, plain, (v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1466, c_4153])).
% 6.10/2.17  tff(c_4165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3360, c_4163])).
% 6.10/2.17  tff(c_4166, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_1')), inference(splitRight, [status(thm)], [c_2693])).
% 6.10/2.17  tff(c_4241, plain, (k1_zfmisc_1(u1_struct_0('#skF_2'))=u1_pre_topc('#skF_2') | ~r1_tarski(k1_zfmisc_1(u1_struct_0('#skF_2')), u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4166, c_131])).
% 6.10/2.17  tff(c_4318, plain, (k1_zfmisc_1(u1_struct_0('#skF_2'))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2763, c_4166, c_4241])).
% 6.10/2.17  tff(c_56, plain, (![A_68]: (v1_tdlat_3(A_68) | k9_setfam_1(u1_struct_0(A_68))!=u1_pre_topc(A_68) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_178])).
% 6.10/2.17  tff(c_69, plain, (![A_68]: (v1_tdlat_3(A_68) | k1_zfmisc_1(u1_struct_0(A_68))!=u1_pre_topc(A_68) | ~l1_pre_topc(A_68))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_56])).
% 6.10/2.17  tff(c_4426, plain, (v1_tdlat_3('#skF_2') | u1_pre_topc('#skF_2')!=u1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4318, c_69])).
% 6.10/2.17  tff(c_4476, plain, (v1_tdlat_3('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_4166, c_4426])).
% 6.10/2.17  tff(c_4478, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_4476])).
% 6.10/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.10/2.17  
% 6.10/2.17  Inference rules
% 6.10/2.17  ----------------------
% 6.10/2.17  #Ref     : 0
% 6.10/2.17  #Sup     : 918
% 6.10/2.17  #Fact    : 0
% 6.10/2.17  #Define  : 0
% 6.10/2.17  #Split   : 5
% 6.10/2.17  #Chain   : 0
% 6.10/2.17  #Close   : 0
% 6.10/2.17  
% 6.10/2.17  Ordering : KBO
% 6.10/2.17  
% 6.10/2.17  Simplification rules
% 6.10/2.17  ----------------------
% 6.10/2.17  #Subsume      : 133
% 6.10/2.17  #Demod        : 1180
% 6.10/2.17  #Tautology    : 273
% 6.10/2.17  #SimpNegUnit  : 11
% 6.10/2.17  #BackRed      : 41
% 6.10/2.17  
% 6.10/2.17  #Partial instantiations: 0
% 6.10/2.17  #Strategies tried      : 1
% 6.10/2.17  
% 6.10/2.17  Timing (in seconds)
% 6.10/2.17  ----------------------
% 6.10/2.18  Preprocessing        : 0.35
% 6.10/2.18  Parsing              : 0.19
% 6.10/2.18  CNF conversion       : 0.03
% 6.10/2.18  Main loop            : 0.98
% 6.10/2.18  Inferencing          : 0.29
% 6.10/2.18  Reduction            : 0.35
% 6.10/2.18  Demodulation         : 0.25
% 6.10/2.18  BG Simplification    : 0.04
% 6.10/2.18  Subsumption          : 0.23
% 6.10/2.18  Abstraction          : 0.04
% 6.10/2.18  MUC search           : 0.00
% 6.10/2.18  Cooper               : 0.00
% 6.10/2.18  Total                : 1.43
% 6.10/2.18  Index Insertion      : 0.00
% 6.10/2.18  Index Deletion       : 0.00
% 6.10/2.18  Index Matching       : 0.00
% 6.10/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
