%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:57 EST 2020

% Result     : Theorem 6.68s
% Output     : CNFRefutation 6.68s
% Verified   : 
% Statistics : Number of formulae       :  149 (3076 expanded)
%              Number of leaves         :   32 (1037 expanded)
%              Depth                    :   29
%              Number of atoms          :  395 (9210 expanded)
%              Number of equality atoms :   20 ( 900 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k9_setfam_1 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_150,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                & v1_tdlat_3(A) )
             => v1_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tex_2)).

tff(f_112,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_132,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_tdlat_3(A)
       => v2_pre_topc(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
       => v2_pre_topc(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_pre_topc)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_126,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
             => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> r1_tarski(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

tff(f_138,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_tdlat_3(A)
      <=> u1_pre_topc(A) = k9_setfam_1(u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tdlat_3)).

tff(f_99,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_2)).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_32,plain,(
    ! [A_40] :
      ( m1_pre_topc(A_40,A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_46,plain,(
    v1_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_38,plain,(
    ! [A_48] :
      ( v2_pre_topc(A_48)
      | ~ v1_tdlat_3(A_48)
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_117,plain,(
    ! [A_63] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_63),u1_pre_topc(A_63)))
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_48,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_88,plain,(
    ! [A_61] :
      ( v2_pre_topc(A_61)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(A_61),u1_pre_topc(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_91,plain,
    ( v2_pre_topc('#skF_2')
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_88])).

tff(c_96,plain,
    ( v2_pre_topc('#skF_2')
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_91])).

tff(c_98,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_120,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_117,c_98])).

tff(c_129,plain,(
    ~ v2_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_120])).

tff(c_136,plain,
    ( ~ v1_tdlat_3('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_129])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_136])).

tff(c_142,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_16,plain,(
    ! [A_8] :
      ( v2_pre_topc(A_8)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(A_8),u1_pre_topc(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_145,plain,
    ( v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_142,c_16])).

tff(c_148,plain,(
    v2_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_145])).

tff(c_183,plain,(
    ! [A_69,B_70] :
      ( m1_pre_topc(A_69,g1_pre_topc(u1_struct_0(B_70),u1_pre_topc(B_70)))
      | ~ m1_pre_topc(A_69,B_70)
      | ~ l1_pre_topc(B_70)
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_196,plain,(
    ! [A_69] :
      ( m1_pre_topc(A_69,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_pre_topc(A_69,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_183])).

tff(c_219,plain,(
    ! [A_75] :
      ( m1_pre_topc(A_75,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_pre_topc(A_75,'#skF_2')
      | ~ l1_pre_topc(A_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_196])).

tff(c_18,plain,(
    ! [B_11,A_9] :
      ( m1_pre_topc(B_11,A_9)
      | ~ m1_pre_topc(B_11,g1_pre_topc(u1_struct_0(A_9),u1_pre_topc(A_9)))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_225,plain,(
    ! [A_75] :
      ( m1_pre_topc(A_75,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_pre_topc(A_75,'#skF_2')
      | ~ l1_pre_topc(A_75) ) ),
    inference(resolution,[status(thm)],[c_219,c_18])).

tff(c_234,plain,(
    ! [A_76] :
      ( m1_pre_topc(A_76,'#skF_1')
      | ~ m1_pre_topc(A_76,'#skF_2')
      | ~ l1_pre_topc(A_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_225])).

tff(c_241,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_234])).

tff(c_245,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_241])).

tff(c_165,plain,(
    ! [B_66,A_67] :
      ( m1_pre_topc(B_66,A_67)
      | ~ m1_pre_topc(B_66,g1_pre_topc(u1_struct_0(A_67),u1_pre_topc(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_168,plain,(
    ! [B_66] :
      ( m1_pre_topc(B_66,'#skF_2')
      | ~ m1_pre_topc(B_66,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_165])).

tff(c_174,plain,(
    ! [B_66] :
      ( m1_pre_topc(B_66,'#skF_2')
      | ~ m1_pre_topc(B_66,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_168])).

tff(c_187,plain,(
    ! [A_69] :
      ( m1_pre_topc(A_69,'#skF_2')
      | ~ m1_pre_topc(A_69,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ l1_pre_topc(A_69) ) ),
    inference(resolution,[status(thm)],[c_183,c_174])).

tff(c_199,plain,(
    ! [A_69] :
      ( m1_pre_topc(A_69,'#skF_2')
      | ~ m1_pre_topc(A_69,'#skF_1')
      | ~ l1_pre_topc(A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_187])).

tff(c_358,plain,(
    ! [B_93,C_94,A_95] :
      ( r1_tarski(u1_struct_0(B_93),u1_struct_0(C_94))
      | ~ m1_pre_topc(B_93,C_94)
      | ~ m1_pre_topc(C_94,A_95)
      | ~ m1_pre_topc(B_93,A_95)
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_387,plain,(
    ! [B_93,A_40] :
      ( r1_tarski(u1_struct_0(B_93),u1_struct_0(A_40))
      | ~ m1_pre_topc(B_93,A_40)
      | ~ v2_pre_topc(A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(resolution,[status(thm)],[c_32,c_358])).

tff(c_141,plain,(
    v2_pre_topc('#skF_2') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_307,plain,(
    ! [B_86,C_87,A_88] :
      ( m1_pre_topc(B_86,C_87)
      | ~ r1_tarski(u1_struct_0(B_86),u1_struct_0(C_87))
      | ~ m1_pre_topc(C_87,A_88)
      | ~ m1_pre_topc(B_86,A_88)
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_312,plain,(
    ! [B_89,A_90] :
      ( m1_pre_topc(B_89,B_89)
      | ~ m1_pre_topc(B_89,A_90)
      | ~ l1_pre_topc(A_90)
      | ~ v2_pre_topc(A_90) ) ),
    inference(resolution,[status(thm)],[c_6,c_307])).

tff(c_316,plain,
    ( m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_245,c_312])).

tff(c_328,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_52,c_316])).

tff(c_360,plain,(
    ! [B_93] :
      ( r1_tarski(u1_struct_0(B_93),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_93,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_328,c_358])).

tff(c_388,plain,(
    ! [B_96] :
      ( r1_tarski(u1_struct_0(B_96),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_96,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_50,c_360])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_402,plain,(
    ! [B_99] :
      ( u1_struct_0(B_99) = u1_struct_0('#skF_2')
      | ~ r1_tarski(u1_struct_0('#skF_2'),u1_struct_0(B_99))
      | ~ m1_pre_topc(B_99,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_388,c_2])).

tff(c_424,plain,(
    ! [A_100] :
      ( u1_struct_0(A_100) = u1_struct_0('#skF_2')
      | ~ m1_pre_topc(A_100,'#skF_2')
      | ~ m1_pre_topc('#skF_2',A_100)
      | ~ v2_pre_topc(A_100)
      | ~ l1_pre_topc(A_100) ) ),
    inference(resolution,[status(thm)],[c_387,c_402])).

tff(c_454,plain,(
    ! [A_104] :
      ( u1_struct_0(A_104) = u1_struct_0('#skF_2')
      | ~ m1_pre_topc('#skF_2',A_104)
      | ~ v2_pre_topc(A_104)
      | ~ m1_pre_topc(A_104,'#skF_1')
      | ~ l1_pre_topc(A_104) ) ),
    inference(resolution,[status(thm)],[c_199,c_424])).

tff(c_458,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_245,c_454])).

tff(c_477,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_148,c_458])).

tff(c_492,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_477])).

tff(c_495,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_492])).

tff(c_499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_495])).

tff(c_501,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_477])).

tff(c_10,plain,(
    ! [A_6] :
      ( m1_subset_1(u1_pre_topc(A_6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_6))))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_291,plain,(
    ! [C_81,A_82,B_83] :
      ( m1_subset_1(C_81,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_82))))
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_83))))
      | ~ m1_pre_topc(B_83,A_82)
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_295,plain,(
    ! [A_84,A_85] :
      ( m1_subset_1(u1_pre_topc(A_84),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_85))))
      | ~ m1_pre_topc(A_84,A_85)
      | ~ l1_pre_topc(A_85)
      | ~ l1_pre_topc(A_84) ) ),
    inference(resolution,[status(thm)],[c_10,c_291])).

tff(c_30,plain,(
    ! [B_39,A_37] :
      ( r1_tarski(B_39,u1_pre_topc(A_37))
      | ~ v1_tops_2(B_39,A_37)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37))))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_305,plain,(
    ! [A_84,A_85] :
      ( r1_tarski(u1_pre_topc(A_84),u1_pre_topc(A_85))
      | ~ v1_tops_2(u1_pre_topc(A_84),A_85)
      | ~ m1_pre_topc(A_84,A_85)
      | ~ l1_pre_topc(A_85)
      | ~ l1_pre_topc(A_84) ) ),
    inference(resolution,[status(thm)],[c_295,c_30])).

tff(c_42,plain,(
    ! [A_49] :
      ( k9_setfam_1(u1_struct_0(A_49)) = u1_pre_topc(A_49)
      | ~ v1_tdlat_3(A_49)
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_44,plain,(
    ~ v1_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_500,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_477])).

tff(c_40,plain,(
    ! [A_49] :
      ( v1_tdlat_3(A_49)
      | k9_setfam_1(u1_struct_0(A_49)) != u1_pre_topc(A_49)
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_596,plain,
    ( v1_tdlat_3('#skF_2')
    | k9_setfam_1(u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_500,c_40])).

tff(c_630,plain,
    ( v1_tdlat_3('#skF_2')
    | k9_setfam_1(u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_596])).

tff(c_631,plain,(
    k9_setfam_1(u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_630])).

tff(c_635,plain,
    ( u1_pre_topc('#skF_2') != u1_pre_topc('#skF_1')
    | ~ v1_tdlat_3('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_631])).

tff(c_637,plain,(
    u1_pre_topc('#skF_2') != u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_635])).

tff(c_593,plain,
    ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_500,c_10])).

tff(c_628,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_593])).

tff(c_28,plain,(
    ! [B_39,A_37] :
      ( v1_tops_2(B_39,A_37)
      | ~ r1_tarski(B_39,u1_pre_topc(A_37))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37))))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_572,plain,(
    ! [B_39] :
      ( v1_tops_2(B_39,'#skF_2')
      | ~ r1_tarski(B_39,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_500,c_28])).

tff(c_1329,plain,(
    ! [B_138] :
      ( v1_tops_2(B_138,'#skF_2')
      | ~ r1_tarski(B_138,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_138,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_572])).

tff(c_1349,plain,
    ( v1_tops_2(u1_pre_topc('#skF_2'),'#skF_2')
    | ~ r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_628,c_1329])).

tff(c_1372,plain,(
    v1_tops_2(u1_pre_topc('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1349])).

tff(c_24,plain,(
    ! [C_21,A_15,B_19] :
      ( m1_subset_1(C_21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_15))))
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_19))))
      | ~ m1_pre_topc(B_19,A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1069,plain,(
    ! [A_125,A_126,A_127] :
      ( m1_subset_1(u1_pre_topc(A_125),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_126))))
      | ~ m1_pre_topc(A_127,A_126)
      | ~ l1_pre_topc(A_126)
      | ~ m1_pre_topc(A_125,A_127)
      | ~ l1_pre_topc(A_127)
      | ~ l1_pre_topc(A_125) ) ),
    inference(resolution,[status(thm)],[c_295,c_24])).

tff(c_1073,plain,(
    ! [A_125] :
      ( m1_subset_1(u1_pre_topc(A_125),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_pre_topc(A_125,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ l1_pre_topc(A_125) ) ),
    inference(resolution,[status(thm)],[c_501,c_1069])).

tff(c_1093,plain,(
    ! [A_125] :
      ( m1_subset_1(u1_pre_topc(A_125),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_pre_topc(A_125,'#skF_1')
      | ~ l1_pre_topc(A_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1073])).

tff(c_294,plain,(
    ! [A_6,A_82] :
      ( m1_subset_1(u1_pre_topc(A_6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_82))))
      | ~ m1_pre_topc(A_6,A_82)
      | ~ l1_pre_topc(A_82)
      | ~ l1_pre_topc(A_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_291])).

tff(c_447,plain,(
    ! [D_101,C_102,A_103] :
      ( v1_tops_2(D_101,C_102)
      | ~ m1_subset_1(D_101,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_102))))
      | ~ v1_tops_2(D_101,A_103)
      | ~ m1_pre_topc(C_102,A_103)
      | ~ m1_subset_1(D_101,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_103))))
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1249,plain,(
    ! [A_133,A_134,A_135] :
      ( v1_tops_2(u1_pre_topc(A_133),A_134)
      | ~ v1_tops_2(u1_pre_topc(A_133),A_135)
      | ~ m1_pre_topc(A_134,A_135)
      | ~ m1_subset_1(u1_pre_topc(A_133),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_135))))
      | ~ l1_pre_topc(A_135)
      | ~ m1_pre_topc(A_133,A_134)
      | ~ l1_pre_topc(A_134)
      | ~ l1_pre_topc(A_133) ) ),
    inference(resolution,[status(thm)],[c_294,c_447])).

tff(c_1263,plain,(
    ! [A_133,A_69] :
      ( v1_tops_2(u1_pre_topc(A_133),A_69)
      | ~ v1_tops_2(u1_pre_topc(A_133),'#skF_2')
      | ~ m1_subset_1(u1_pre_topc(A_133),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ l1_pre_topc('#skF_2')
      | ~ m1_pre_topc(A_133,A_69)
      | ~ l1_pre_topc(A_133)
      | ~ m1_pre_topc(A_69,'#skF_1')
      | ~ l1_pre_topc(A_69) ) ),
    inference(resolution,[status(thm)],[c_199,c_1249])).

tff(c_1288,plain,(
    ! [A_136,A_137] :
      ( v1_tops_2(u1_pre_topc(A_136),A_137)
      | ~ v1_tops_2(u1_pre_topc(A_136),'#skF_2')
      | ~ m1_subset_1(u1_pre_topc(A_136),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_pre_topc(A_136,A_137)
      | ~ l1_pre_topc(A_136)
      | ~ m1_pre_topc(A_137,'#skF_1')
      | ~ l1_pre_topc(A_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_500,c_1263])).

tff(c_1779,plain,(
    ! [A_159,A_160] :
      ( v1_tops_2(u1_pre_topc(A_159),A_160)
      | ~ v1_tops_2(u1_pre_topc(A_159),'#skF_2')
      | ~ m1_pre_topc(A_159,A_160)
      | ~ m1_pre_topc(A_160,'#skF_1')
      | ~ l1_pre_topc(A_160)
      | ~ m1_pre_topc(A_159,'#skF_1')
      | ~ l1_pre_topc(A_159) ) ),
    inference(resolution,[status(thm)],[c_1093,c_1288])).

tff(c_1781,plain,(
    ! [A_160] :
      ( v1_tops_2(u1_pre_topc('#skF_2'),A_160)
      | ~ m1_pre_topc('#skF_2',A_160)
      | ~ m1_pre_topc(A_160,'#skF_1')
      | ~ l1_pre_topc(A_160)
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1372,c_1779])).

tff(c_1791,plain,(
    ! [A_161] :
      ( v1_tops_2(u1_pre_topc('#skF_2'),A_161)
      | ~ m1_pre_topc('#skF_2',A_161)
      | ~ m1_pre_topc(A_161,'#skF_1')
      | ~ l1_pre_topc(A_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_245,c_1781])).

tff(c_668,plain,
    ( v1_tops_2(u1_pre_topc('#skF_2'),'#skF_1')
    | ~ r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_628,c_28])).

tff(c_676,plain,
    ( v1_tops_2(u1_pre_topc('#skF_2'),'#skF_1')
    | ~ r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_668])).

tff(c_709,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_676])).

tff(c_712,plain,
    ( ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_305,c_709])).

tff(c_715,plain,(
    ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_245,c_712])).

tff(c_1797,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1791,c_715])).

tff(c_1804,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_501,c_245,c_1797])).

tff(c_1806,plain,(
    r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_676])).

tff(c_1808,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_1')
    | ~ r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1806,c_2])).

tff(c_1811,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_637,c_1808])).

tff(c_1814,plain,
    ( ~ v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2')
    | ~ m1_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_305,c_1811])).

tff(c_1817,plain,
    ( ~ v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2')
    | ~ m1_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1814])).

tff(c_1818,plain,(
    ~ m1_pre_topc('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1817])).

tff(c_1853,plain,
    ( ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_199,c_1818])).

tff(c_1857,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_501,c_1853])).

tff(c_1858,plain,(
    ~ v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1817])).

tff(c_1859,plain,(
    m1_pre_topc('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1817])).

tff(c_2430,plain,(
    ! [A_185,A_186,A_187] :
      ( m1_subset_1(u1_pre_topc(A_185),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_186))))
      | ~ m1_pre_topc(A_187,A_186)
      | ~ l1_pre_topc(A_186)
      | ~ m1_pre_topc(A_185,A_187)
      | ~ l1_pre_topc(A_187)
      | ~ l1_pre_topc(A_185) ) ),
    inference(resolution,[status(thm)],[c_295,c_24])).

tff(c_2444,plain,(
    ! [A_185,A_69] :
      ( m1_subset_1(u1_pre_topc(A_185),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ l1_pre_topc('#skF_2')
      | ~ m1_pre_topc(A_185,A_69)
      | ~ l1_pre_topc(A_185)
      | ~ m1_pre_topc(A_69,'#skF_1')
      | ~ l1_pre_topc(A_69) ) ),
    inference(resolution,[status(thm)],[c_199,c_2430])).

tff(c_2495,plain,(
    ! [A_189,A_190] :
      ( m1_subset_1(u1_pre_topc(A_189),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_pre_topc(A_189,A_190)
      | ~ l1_pre_topc(A_189)
      | ~ m1_pre_topc(A_190,'#skF_1')
      | ~ l1_pre_topc(A_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_500,c_2444])).

tff(c_2499,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_501,c_2495])).

tff(c_2519,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_501,c_2499])).

tff(c_2548,plain,
    ( v1_tops_2(u1_pre_topc('#skF_1'),'#skF_1')
    | ~ r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2519,c_28])).

tff(c_2560,plain,(
    v1_tops_2(u1_pre_topc('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_6,c_2548])).

tff(c_3290,plain,(
    ! [C_226,A_227] :
      ( m1_subset_1(C_226,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_227))))
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_pre_topc('#skF_2',A_227)
      | ~ l1_pre_topc(A_227) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_500,c_24])).

tff(c_3317,plain,(
    ! [A_227] :
      ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_227))))
      | ~ m1_pre_topc('#skF_2',A_227)
      | ~ l1_pre_topc(A_227) ) ),
    inference(resolution,[status(thm)],[c_2519,c_3290])).

tff(c_2619,plain,(
    ! [A_193,A_194,A_195] :
      ( v1_tops_2(u1_pre_topc(A_193),A_194)
      | ~ v1_tops_2(u1_pre_topc(A_193),A_195)
      | ~ m1_pre_topc(A_194,A_195)
      | ~ m1_subset_1(u1_pre_topc(A_193),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_195))))
      | ~ l1_pre_topc(A_195)
      | ~ m1_pre_topc(A_193,A_194)
      | ~ l1_pre_topc(A_194)
      | ~ l1_pre_topc(A_193) ) ),
    inference(resolution,[status(thm)],[c_294,c_447])).

tff(c_2629,plain,(
    ! [A_193] :
      ( v1_tops_2(u1_pre_topc(A_193),'#skF_2')
      | ~ v1_tops_2(u1_pre_topc(A_193),'#skF_1')
      | ~ m1_subset_1(u1_pre_topc(A_193),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_pre_topc(A_193,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_193) ) ),
    inference(resolution,[status(thm)],[c_245,c_2619])).

tff(c_6502,plain,(
    ! [A_325] :
      ( v1_tops_2(u1_pre_topc(A_325),'#skF_2')
      | ~ v1_tops_2(u1_pre_topc(A_325),'#skF_1')
      | ~ m1_subset_1(u1_pre_topc(A_325),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_pre_topc(A_325,'#skF_2')
      | ~ l1_pre_topc(A_325) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_2629])).

tff(c_6533,plain,
    ( v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2')
    | ~ v1_tops_2(u1_pre_topc('#skF_1'),'#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_3317,c_6502])).

tff(c_6586,plain,(
    v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_245,c_1859,c_2560,c_6533])).

tff(c_6588,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1858,c_6586])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:06:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.68/2.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.68/2.44  
% 6.68/2.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.68/2.44  %$ v1_tops_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k9_setfam_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 6.68/2.44  
% 6.68/2.44  %Foreground sorts:
% 6.68/2.44  
% 6.68/2.44  
% 6.68/2.44  %Background operators:
% 6.68/2.44  
% 6.68/2.44  
% 6.68/2.44  %Foreground operators:
% 6.68/2.44  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 6.68/2.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.68/2.44  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 6.68/2.44  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 6.68/2.44  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.68/2.44  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 6.68/2.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.68/2.44  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 6.68/2.44  tff('#skF_2', type, '#skF_2': $i).
% 6.68/2.44  tff('#skF_1', type, '#skF_1': $i).
% 6.68/2.44  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 6.68/2.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.68/2.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.68/2.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.68/2.44  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.68/2.44  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.68/2.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.68/2.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.68/2.44  
% 6.68/2.46  tff(f_150, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & v1_tdlat_3(A)) => v1_tdlat_3(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_tex_2)).
% 6.68/2.46  tff(f_112, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 6.68/2.46  tff(f_132, axiom, (![A]: (l1_pre_topc(A) => (v1_tdlat_3(A) => v2_pre_topc(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_tdlat_3)).
% 6.68/2.46  tff(f_50, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_pre_topc)).
% 6.68/2.46  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => v2_pre_topc(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_pre_topc)).
% 6.68/2.46  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 6.68/2.46  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 6.68/2.46  tff(f_126, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 6.68/2.46  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.68/2.46  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 6.68/2.46  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_2)).
% 6.68/2.46  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> r1_tarski(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_tops_2)).
% 6.68/2.46  tff(f_138, axiom, (![A]: (l1_pre_topc(A) => (v1_tdlat_3(A) <=> (u1_pre_topc(A) = k9_setfam_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tdlat_3)).
% 6.68/2.46  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_pre_topc(C, A) => (v1_tops_2(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C)))) => ((D = B) => v1_tops_2(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tops_2)).
% 6.68/2.46  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 6.68/2.46  tff(c_32, plain, (![A_40]: (m1_pre_topc(A_40, A_40) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.68/2.46  tff(c_46, plain, (v1_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 6.68/2.46  tff(c_38, plain, (![A_48]: (v2_pre_topc(A_48) | ~v1_tdlat_3(A_48) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_132])).
% 6.68/2.46  tff(c_117, plain, (![A_63]: (v2_pre_topc(g1_pre_topc(u1_struct_0(A_63), u1_pre_topc(A_63))) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.68/2.46  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 6.68/2.46  tff(c_48, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 6.68/2.46  tff(c_88, plain, (![A_61]: (v2_pre_topc(A_61) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(A_61), u1_pre_topc(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.68/2.46  tff(c_91, plain, (v2_pre_topc('#skF_2') | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_48, c_88])).
% 6.68/2.46  tff(c_96, plain, (v2_pre_topc('#skF_2') | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_91])).
% 6.68/2.46  tff(c_98, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_96])).
% 6.68/2.46  tff(c_120, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_117, c_98])).
% 6.68/2.46  tff(c_129, plain, (~v2_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_120])).
% 6.68/2.46  tff(c_136, plain, (~v1_tdlat_3('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_129])).
% 6.68/2.46  tff(c_140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_136])).
% 6.68/2.46  tff(c_142, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_96])).
% 6.68/2.46  tff(c_16, plain, (![A_8]: (v2_pre_topc(A_8) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(A_8), u1_pre_topc(A_8))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.68/2.46  tff(c_145, plain, (v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_142, c_16])).
% 6.68/2.46  tff(c_148, plain, (v2_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_145])).
% 6.68/2.46  tff(c_183, plain, (![A_69, B_70]: (m1_pre_topc(A_69, g1_pre_topc(u1_struct_0(B_70), u1_pre_topc(B_70))) | ~m1_pre_topc(A_69, B_70) | ~l1_pre_topc(B_70) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.68/2.46  tff(c_196, plain, (![A_69]: (m1_pre_topc(A_69, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_pre_topc(A_69, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_69))), inference(superposition, [status(thm), theory('equality')], [c_48, c_183])).
% 6.68/2.46  tff(c_219, plain, (![A_75]: (m1_pre_topc(A_75, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_pre_topc(A_75, '#skF_2') | ~l1_pre_topc(A_75))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_196])).
% 6.68/2.46  tff(c_18, plain, (![B_11, A_9]: (m1_pre_topc(B_11, A_9) | ~m1_pre_topc(B_11, g1_pre_topc(u1_struct_0(A_9), u1_pre_topc(A_9))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.68/2.46  tff(c_225, plain, (![A_75]: (m1_pre_topc(A_75, '#skF_1') | ~l1_pre_topc('#skF_1') | ~m1_pre_topc(A_75, '#skF_2') | ~l1_pre_topc(A_75))), inference(resolution, [status(thm)], [c_219, c_18])).
% 6.68/2.46  tff(c_234, plain, (![A_76]: (m1_pre_topc(A_76, '#skF_1') | ~m1_pre_topc(A_76, '#skF_2') | ~l1_pre_topc(A_76))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_225])).
% 6.68/2.46  tff(c_241, plain, (m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_234])).
% 6.68/2.46  tff(c_245, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_241])).
% 6.68/2.46  tff(c_165, plain, (![B_66, A_67]: (m1_pre_topc(B_66, A_67) | ~m1_pre_topc(B_66, g1_pre_topc(u1_struct_0(A_67), u1_pre_topc(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.68/2.46  tff(c_168, plain, (![B_66]: (m1_pre_topc(B_66, '#skF_2') | ~m1_pre_topc(B_66, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_165])).
% 6.68/2.46  tff(c_174, plain, (![B_66]: (m1_pre_topc(B_66, '#skF_2') | ~m1_pre_topc(B_66, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_168])).
% 6.68/2.46  tff(c_187, plain, (![A_69]: (m1_pre_topc(A_69, '#skF_2') | ~m1_pre_topc(A_69, '#skF_1') | ~l1_pre_topc('#skF_1') | ~l1_pre_topc(A_69))), inference(resolution, [status(thm)], [c_183, c_174])).
% 6.68/2.46  tff(c_199, plain, (![A_69]: (m1_pre_topc(A_69, '#skF_2') | ~m1_pre_topc(A_69, '#skF_1') | ~l1_pre_topc(A_69))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_187])).
% 6.68/2.46  tff(c_358, plain, (![B_93, C_94, A_95]: (r1_tarski(u1_struct_0(B_93), u1_struct_0(C_94)) | ~m1_pre_topc(B_93, C_94) | ~m1_pre_topc(C_94, A_95) | ~m1_pre_topc(B_93, A_95) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.68/2.46  tff(c_387, plain, (![B_93, A_40]: (r1_tarski(u1_struct_0(B_93), u1_struct_0(A_40)) | ~m1_pre_topc(B_93, A_40) | ~v2_pre_topc(A_40) | ~l1_pre_topc(A_40))), inference(resolution, [status(thm)], [c_32, c_358])).
% 6.68/2.46  tff(c_141, plain, (v2_pre_topc('#skF_2')), inference(splitRight, [status(thm)], [c_96])).
% 6.68/2.46  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.68/2.46  tff(c_307, plain, (![B_86, C_87, A_88]: (m1_pre_topc(B_86, C_87) | ~r1_tarski(u1_struct_0(B_86), u1_struct_0(C_87)) | ~m1_pre_topc(C_87, A_88) | ~m1_pre_topc(B_86, A_88) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.68/2.46  tff(c_312, plain, (![B_89, A_90]: (m1_pre_topc(B_89, B_89) | ~m1_pre_topc(B_89, A_90) | ~l1_pre_topc(A_90) | ~v2_pre_topc(A_90))), inference(resolution, [status(thm)], [c_6, c_307])).
% 6.68/2.46  tff(c_316, plain, (m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_245, c_312])).
% 6.68/2.46  tff(c_328, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_52, c_316])).
% 6.68/2.46  tff(c_360, plain, (![B_93]: (r1_tarski(u1_struct_0(B_93), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_93, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_328, c_358])).
% 6.68/2.46  tff(c_388, plain, (![B_96]: (r1_tarski(u1_struct_0(B_96), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_96, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_50, c_360])).
% 6.68/2.46  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.68/2.46  tff(c_402, plain, (![B_99]: (u1_struct_0(B_99)=u1_struct_0('#skF_2') | ~r1_tarski(u1_struct_0('#skF_2'), u1_struct_0(B_99)) | ~m1_pre_topc(B_99, '#skF_2'))), inference(resolution, [status(thm)], [c_388, c_2])).
% 6.68/2.46  tff(c_424, plain, (![A_100]: (u1_struct_0(A_100)=u1_struct_0('#skF_2') | ~m1_pre_topc(A_100, '#skF_2') | ~m1_pre_topc('#skF_2', A_100) | ~v2_pre_topc(A_100) | ~l1_pre_topc(A_100))), inference(resolution, [status(thm)], [c_387, c_402])).
% 6.68/2.46  tff(c_454, plain, (![A_104]: (u1_struct_0(A_104)=u1_struct_0('#skF_2') | ~m1_pre_topc('#skF_2', A_104) | ~v2_pre_topc(A_104) | ~m1_pre_topc(A_104, '#skF_1') | ~l1_pre_topc(A_104))), inference(resolution, [status(thm)], [c_199, c_424])).
% 6.68/2.46  tff(c_458, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_245, c_454])).
% 6.68/2.46  tff(c_477, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_148, c_458])).
% 6.68/2.46  tff(c_492, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_477])).
% 6.68/2.46  tff(c_495, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_492])).
% 6.68/2.46  tff(c_499, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_495])).
% 6.68/2.46  tff(c_501, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_477])).
% 6.68/2.46  tff(c_10, plain, (![A_6]: (m1_subset_1(u1_pre_topc(A_6), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_6)))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.68/2.46  tff(c_291, plain, (![C_81, A_82, B_83]: (m1_subset_1(C_81, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_82)))) | ~m1_subset_1(C_81, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_83)))) | ~m1_pre_topc(B_83, A_82) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.68/2.46  tff(c_295, plain, (![A_84, A_85]: (m1_subset_1(u1_pre_topc(A_84), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_85)))) | ~m1_pre_topc(A_84, A_85) | ~l1_pre_topc(A_85) | ~l1_pre_topc(A_84))), inference(resolution, [status(thm)], [c_10, c_291])).
% 6.68/2.46  tff(c_30, plain, (![B_39, A_37]: (r1_tarski(B_39, u1_pre_topc(A_37)) | ~v1_tops_2(B_39, A_37) | ~m1_subset_1(B_39, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37)))) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.68/2.46  tff(c_305, plain, (![A_84, A_85]: (r1_tarski(u1_pre_topc(A_84), u1_pre_topc(A_85)) | ~v1_tops_2(u1_pre_topc(A_84), A_85) | ~m1_pre_topc(A_84, A_85) | ~l1_pre_topc(A_85) | ~l1_pre_topc(A_84))), inference(resolution, [status(thm)], [c_295, c_30])).
% 6.68/2.46  tff(c_42, plain, (![A_49]: (k9_setfam_1(u1_struct_0(A_49))=u1_pre_topc(A_49) | ~v1_tdlat_3(A_49) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.68/2.46  tff(c_44, plain, (~v1_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 6.68/2.46  tff(c_500, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_477])).
% 6.68/2.46  tff(c_40, plain, (![A_49]: (v1_tdlat_3(A_49) | k9_setfam_1(u1_struct_0(A_49))!=u1_pre_topc(A_49) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.68/2.46  tff(c_596, plain, (v1_tdlat_3('#skF_2') | k9_setfam_1(u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_500, c_40])).
% 6.68/2.46  tff(c_630, plain, (v1_tdlat_3('#skF_2') | k9_setfam_1(u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_596])).
% 6.68/2.46  tff(c_631, plain, (k9_setfam_1(u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_44, c_630])).
% 6.68/2.46  tff(c_635, plain, (u1_pre_topc('#skF_2')!=u1_pre_topc('#skF_1') | ~v1_tdlat_3('#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_42, c_631])).
% 6.68/2.46  tff(c_637, plain, (u1_pre_topc('#skF_2')!=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_635])).
% 6.68/2.46  tff(c_593, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_500, c_10])).
% 6.68/2.46  tff(c_628, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_593])).
% 6.68/2.46  tff(c_28, plain, (![B_39, A_37]: (v1_tops_2(B_39, A_37) | ~r1_tarski(B_39, u1_pre_topc(A_37)) | ~m1_subset_1(B_39, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37)))) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.68/2.46  tff(c_572, plain, (![B_39]: (v1_tops_2(B_39, '#skF_2') | ~r1_tarski(B_39, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_39, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_500, c_28])).
% 6.68/2.46  tff(c_1329, plain, (![B_138]: (v1_tops_2(B_138, '#skF_2') | ~r1_tarski(B_138, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_138, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_572])).
% 6.68/2.46  tff(c_1349, plain, (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_2') | ~r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_628, c_1329])).
% 6.68/2.46  tff(c_1372, plain, (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1349])).
% 6.68/2.46  tff(c_24, plain, (![C_21, A_15, B_19]: (m1_subset_1(C_21, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_15)))) | ~m1_subset_1(C_21, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_19)))) | ~m1_pre_topc(B_19, A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.68/2.46  tff(c_1069, plain, (![A_125, A_126, A_127]: (m1_subset_1(u1_pre_topc(A_125), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_126)))) | ~m1_pre_topc(A_127, A_126) | ~l1_pre_topc(A_126) | ~m1_pre_topc(A_125, A_127) | ~l1_pre_topc(A_127) | ~l1_pre_topc(A_125))), inference(resolution, [status(thm)], [c_295, c_24])).
% 6.68/2.46  tff(c_1073, plain, (![A_125]: (m1_subset_1(u1_pre_topc(A_125), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc(A_125, '#skF_1') | ~l1_pre_topc('#skF_1') | ~l1_pre_topc(A_125))), inference(resolution, [status(thm)], [c_501, c_1069])).
% 6.68/2.46  tff(c_1093, plain, (![A_125]: (m1_subset_1(u1_pre_topc(A_125), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc(A_125, '#skF_1') | ~l1_pre_topc(A_125))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1073])).
% 6.68/2.46  tff(c_294, plain, (![A_6, A_82]: (m1_subset_1(u1_pre_topc(A_6), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_82)))) | ~m1_pre_topc(A_6, A_82) | ~l1_pre_topc(A_82) | ~l1_pre_topc(A_6))), inference(resolution, [status(thm)], [c_10, c_291])).
% 6.68/2.46  tff(c_447, plain, (![D_101, C_102, A_103]: (v1_tops_2(D_101, C_102) | ~m1_subset_1(D_101, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_102)))) | ~v1_tops_2(D_101, A_103) | ~m1_pre_topc(C_102, A_103) | ~m1_subset_1(D_101, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_103)))) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.68/2.46  tff(c_1249, plain, (![A_133, A_134, A_135]: (v1_tops_2(u1_pre_topc(A_133), A_134) | ~v1_tops_2(u1_pre_topc(A_133), A_135) | ~m1_pre_topc(A_134, A_135) | ~m1_subset_1(u1_pre_topc(A_133), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_135)))) | ~l1_pre_topc(A_135) | ~m1_pre_topc(A_133, A_134) | ~l1_pre_topc(A_134) | ~l1_pre_topc(A_133))), inference(resolution, [status(thm)], [c_294, c_447])).
% 6.68/2.46  tff(c_1263, plain, (![A_133, A_69]: (v1_tops_2(u1_pre_topc(A_133), A_69) | ~v1_tops_2(u1_pre_topc(A_133), '#skF_2') | ~m1_subset_1(u1_pre_topc(A_133), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2') | ~m1_pre_topc(A_133, A_69) | ~l1_pre_topc(A_133) | ~m1_pre_topc(A_69, '#skF_1') | ~l1_pre_topc(A_69))), inference(resolution, [status(thm)], [c_199, c_1249])).
% 6.68/2.46  tff(c_1288, plain, (![A_136, A_137]: (v1_tops_2(u1_pre_topc(A_136), A_137) | ~v1_tops_2(u1_pre_topc(A_136), '#skF_2') | ~m1_subset_1(u1_pre_topc(A_136), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc(A_136, A_137) | ~l1_pre_topc(A_136) | ~m1_pre_topc(A_137, '#skF_1') | ~l1_pre_topc(A_137))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_500, c_1263])).
% 6.68/2.46  tff(c_1779, plain, (![A_159, A_160]: (v1_tops_2(u1_pre_topc(A_159), A_160) | ~v1_tops_2(u1_pre_topc(A_159), '#skF_2') | ~m1_pre_topc(A_159, A_160) | ~m1_pre_topc(A_160, '#skF_1') | ~l1_pre_topc(A_160) | ~m1_pre_topc(A_159, '#skF_1') | ~l1_pre_topc(A_159))), inference(resolution, [status(thm)], [c_1093, c_1288])).
% 6.68/2.46  tff(c_1781, plain, (![A_160]: (v1_tops_2(u1_pre_topc('#skF_2'), A_160) | ~m1_pre_topc('#skF_2', A_160) | ~m1_pre_topc(A_160, '#skF_1') | ~l1_pre_topc(A_160) | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_1372, c_1779])).
% 6.68/2.46  tff(c_1791, plain, (![A_161]: (v1_tops_2(u1_pre_topc('#skF_2'), A_161) | ~m1_pre_topc('#skF_2', A_161) | ~m1_pre_topc(A_161, '#skF_1') | ~l1_pre_topc(A_161))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_245, c_1781])).
% 6.68/2.46  tff(c_668, plain, (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_1') | ~r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_628, c_28])).
% 6.68/2.46  tff(c_676, plain, (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_1') | ~r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_668])).
% 6.68/2.46  tff(c_709, plain, (~r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_1'))), inference(splitLeft, [status(thm)], [c_676])).
% 6.68/2.46  tff(c_712, plain, (~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_305, c_709])).
% 6.68/2.46  tff(c_715, plain, (~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_245, c_712])).
% 6.68/2.46  tff(c_1797, plain, (~m1_pre_topc('#skF_2', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1791, c_715])).
% 6.68/2.46  tff(c_1804, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_501, c_245, c_1797])).
% 6.68/2.46  tff(c_1806, plain, (r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_1'))), inference(splitRight, [status(thm)], [c_676])).
% 6.68/2.46  tff(c_1808, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_1') | ~r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_1806, c_2])).
% 6.68/2.46  tff(c_1811, plain, (~r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_637, c_1808])).
% 6.68/2.46  tff(c_1814, plain, (~v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2') | ~m1_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_305, c_1811])).
% 6.68/2.46  tff(c_1817, plain, (~v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2') | ~m1_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1814])).
% 6.68/2.46  tff(c_1818, plain, (~m1_pre_topc('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_1817])).
% 6.68/2.46  tff(c_1853, plain, (~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_199, c_1818])).
% 6.68/2.46  tff(c_1857, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_501, c_1853])).
% 6.68/2.46  tff(c_1858, plain, (~v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_1817])).
% 6.68/2.46  tff(c_1859, plain, (m1_pre_topc('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_1817])).
% 6.68/2.46  tff(c_2430, plain, (![A_185, A_186, A_187]: (m1_subset_1(u1_pre_topc(A_185), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_186)))) | ~m1_pre_topc(A_187, A_186) | ~l1_pre_topc(A_186) | ~m1_pre_topc(A_185, A_187) | ~l1_pre_topc(A_187) | ~l1_pre_topc(A_185))), inference(resolution, [status(thm)], [c_295, c_24])).
% 6.68/2.46  tff(c_2444, plain, (![A_185, A_69]: (m1_subset_1(u1_pre_topc(A_185), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2') | ~m1_pre_topc(A_185, A_69) | ~l1_pre_topc(A_185) | ~m1_pre_topc(A_69, '#skF_1') | ~l1_pre_topc(A_69))), inference(resolution, [status(thm)], [c_199, c_2430])).
% 6.68/2.46  tff(c_2495, plain, (![A_189, A_190]: (m1_subset_1(u1_pre_topc(A_189), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc(A_189, A_190) | ~l1_pre_topc(A_189) | ~m1_pre_topc(A_190, '#skF_1') | ~l1_pre_topc(A_190))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_500, c_2444])).
% 6.68/2.46  tff(c_2499, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_501, c_2495])).
% 6.68/2.46  tff(c_2519, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_501, c_2499])).
% 6.68/2.46  tff(c_2548, plain, (v1_tops_2(u1_pre_topc('#skF_1'), '#skF_1') | ~r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2519, c_28])).
% 6.68/2.46  tff(c_2560, plain, (v1_tops_2(u1_pre_topc('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_6, c_2548])).
% 6.68/2.46  tff(c_3290, plain, (![C_226, A_227]: (m1_subset_1(C_226, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_227)))) | ~m1_subset_1(C_226, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc('#skF_2', A_227) | ~l1_pre_topc(A_227))), inference(superposition, [status(thm), theory('equality')], [c_500, c_24])).
% 6.68/2.46  tff(c_3317, plain, (![A_227]: (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_227)))) | ~m1_pre_topc('#skF_2', A_227) | ~l1_pre_topc(A_227))), inference(resolution, [status(thm)], [c_2519, c_3290])).
% 6.68/2.46  tff(c_2619, plain, (![A_193, A_194, A_195]: (v1_tops_2(u1_pre_topc(A_193), A_194) | ~v1_tops_2(u1_pre_topc(A_193), A_195) | ~m1_pre_topc(A_194, A_195) | ~m1_subset_1(u1_pre_topc(A_193), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_195)))) | ~l1_pre_topc(A_195) | ~m1_pre_topc(A_193, A_194) | ~l1_pre_topc(A_194) | ~l1_pre_topc(A_193))), inference(resolution, [status(thm)], [c_294, c_447])).
% 6.68/2.46  tff(c_2629, plain, (![A_193]: (v1_tops_2(u1_pre_topc(A_193), '#skF_2') | ~v1_tops_2(u1_pre_topc(A_193), '#skF_1') | ~m1_subset_1(u1_pre_topc(A_193), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1') | ~m1_pre_topc(A_193, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_193))), inference(resolution, [status(thm)], [c_245, c_2619])).
% 6.68/2.46  tff(c_6502, plain, (![A_325]: (v1_tops_2(u1_pre_topc(A_325), '#skF_2') | ~v1_tops_2(u1_pre_topc(A_325), '#skF_1') | ~m1_subset_1(u1_pre_topc(A_325), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc(A_325, '#skF_2') | ~l1_pre_topc(A_325))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_2629])).
% 6.68/2.46  tff(c_6533, plain, (v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2') | ~v1_tops_2(u1_pre_topc('#skF_1'), '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_3317, c_6502])).
% 6.68/2.46  tff(c_6586, plain, (v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_245, c_1859, c_2560, c_6533])).
% 6.68/2.46  tff(c_6588, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1858, c_6586])).
% 6.68/2.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.68/2.46  
% 6.68/2.46  Inference rules
% 6.68/2.46  ----------------------
% 6.68/2.46  #Ref     : 0
% 6.68/2.46  #Sup     : 1216
% 6.68/2.46  #Fact    : 0
% 6.68/2.46  #Define  : 0
% 6.68/2.46  #Split   : 10
% 6.68/2.46  #Chain   : 0
% 6.68/2.46  #Close   : 0
% 6.68/2.46  
% 6.68/2.46  Ordering : KBO
% 6.68/2.47  
% 6.68/2.47  Simplification rules
% 6.68/2.47  ----------------------
% 6.68/2.47  #Subsume      : 336
% 6.68/2.47  #Demod        : 2113
% 6.68/2.47  #Tautology    : 464
% 6.68/2.47  #SimpNegUnit  : 48
% 6.68/2.47  #BackRed      : 7
% 6.68/2.47  
% 6.68/2.47  #Partial instantiations: 0
% 6.68/2.47  #Strategies tried      : 1
% 6.68/2.47  
% 6.68/2.47  Timing (in seconds)
% 6.68/2.47  ----------------------
% 6.68/2.47  Preprocessing        : 0.36
% 6.68/2.47  Parsing              : 0.19
% 6.68/2.47  CNF conversion       : 0.03
% 6.68/2.47  Main loop            : 1.26
% 6.68/2.47  Inferencing          : 0.40
% 6.68/2.48  Reduction            : 0.44
% 6.68/2.48  Demodulation         : 0.32
% 6.68/2.48  BG Simplification    : 0.04
% 6.68/2.48  Subsumption          : 0.31
% 6.68/2.48  Abstraction          : 0.06
% 6.68/2.48  MUC search           : 0.00
% 6.68/2.48  Cooper               : 0.00
% 6.68/2.48  Total                : 1.68
% 6.68/2.48  Index Insertion      : 0.00
% 6.68/2.48  Index Deletion       : 0.00
% 6.68/2.48  Index Matching       : 0.00
% 6.68/2.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
