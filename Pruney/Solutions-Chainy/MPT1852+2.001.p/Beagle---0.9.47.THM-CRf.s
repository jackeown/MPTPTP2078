%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:58 EST 2020

% Result     : Theorem 12.04s
% Output     : CNFRefutation 12.04s
% Verified   : 
% Statistics : Number of formulae       :  201 (2597 expanded)
%              Number of leaves         :   35 ( 886 expanded)
%              Depth                    :   25
%              Number of atoms          :  562 (7841 expanded)
%              Number of equality atoms :   10 ( 848 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > l1_pre_topc > k6_subset_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_162,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                & v3_tdlat_3(A) )
             => v3_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tex_2)).

tff(f_128,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => v1_tops_2(u1_pre_topc(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_compts_1)).

tff(f_132,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_139,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).

tff(f_150,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( r2_hidden(B,u1_pre_topc(A))
             => r2_hidden(k6_subset_1(u1_struct_0(A),B),u1_pre_topc(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tdlat_3)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
             => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).

tff(f_124,axiom,(
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

tff(c_60,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_38,plain,(
    ! [A_58] :
      ( v1_tops_2(u1_pre_topc(A_58),A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_58,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_40,plain,(
    ! [A_59] :
      ( m1_pre_topc(A_59,A_59)
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_123,plain,(
    ! [A_94,B_95] :
      ( m1_pre_topc(A_94,g1_pre_topc(u1_struct_0(B_95),u1_pre_topc(B_95)))
      | ~ m1_pre_topc(A_94,B_95)
      | ~ l1_pre_topc(B_95)
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_56,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_100,plain,(
    ! [B_86,A_87] :
      ( m1_pre_topc(B_86,A_87)
      | ~ m1_pre_topc(B_86,g1_pre_topc(u1_struct_0(A_87),u1_pre_topc(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_103,plain,(
    ! [B_86] :
      ( m1_pre_topc(B_86,'#skF_3')
      | ~ m1_pre_topc(B_86,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_100])).

tff(c_109,plain,(
    ! [B_86] :
      ( m1_pre_topc(B_86,'#skF_3')
      | ~ m1_pre_topc(B_86,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_103])).

tff(c_127,plain,(
    ! [A_94] :
      ( m1_pre_topc(A_94,'#skF_3')
      | ~ m1_pre_topc(A_94,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_94) ) ),
    inference(resolution,[status(thm)],[c_123,c_109])).

tff(c_139,plain,(
    ! [A_94] :
      ( m1_pre_topc(A_94,'#skF_3')
      | ~ m1_pre_topc(A_94,'#skF_4')
      | ~ l1_pre_topc(A_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_127])).

tff(c_136,plain,(
    ! [A_94] :
      ( m1_pre_topc(A_94,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_pre_topc(A_94,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_123])).

tff(c_160,plain,(
    ! [A_99] :
      ( m1_pre_topc(A_99,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_pre_topc(A_99,'#skF_3')
      | ~ l1_pre_topc(A_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_136])).

tff(c_20,plain,(
    ! [B_22,A_20] :
      ( m1_pre_topc(B_22,A_20)
      | ~ m1_pre_topc(B_22,g1_pre_topc(u1_struct_0(A_20),u1_pre_topc(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_166,plain,(
    ! [A_99] :
      ( m1_pre_topc(A_99,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ m1_pre_topc(A_99,'#skF_3')
      | ~ l1_pre_topc(A_99) ) ),
    inference(resolution,[status(thm)],[c_160,c_20])).

tff(c_175,plain,(
    ! [A_100] :
      ( m1_pre_topc(A_100,'#skF_4')
      | ~ m1_pre_topc(A_100,'#skF_3')
      | ~ l1_pre_topc(A_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_166])).

tff(c_182,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_175])).

tff(c_186,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_182])).

tff(c_42,plain,(
    ! [B_62,A_60] :
      ( r1_tarski(u1_struct_0(B_62),u1_struct_0(A_60))
      | ~ m1_pre_topc(B_62,A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_84,plain,(
    ! [B_78,A_79] :
      ( r1_tarski(u1_struct_0(B_78),u1_struct_0(A_79))
      | ~ m1_pre_topc(B_78,A_79)
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_208,plain,(
    ! [B_106,A_107] :
      ( u1_struct_0(B_106) = u1_struct_0(A_107)
      | ~ r1_tarski(u1_struct_0(A_107),u1_struct_0(B_106))
      | ~ m1_pre_topc(B_106,A_107)
      | ~ l1_pre_topc(A_107) ) ),
    inference(resolution,[status(thm)],[c_84,c_2])).

tff(c_219,plain,(
    ! [B_108,A_109] :
      ( u1_struct_0(B_108) = u1_struct_0(A_109)
      | ~ m1_pre_topc(A_109,B_108)
      | ~ l1_pre_topc(B_108)
      | ~ m1_pre_topc(B_108,A_109)
      | ~ l1_pre_topc(A_109) ) ),
    inference(resolution,[status(thm)],[c_42,c_208])).

tff(c_221,plain,
    ( u1_struct_0('#skF_3') = u1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_186,c_219])).

tff(c_232,plain,
    ( u1_struct_0('#skF_3') = u1_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_221])).

tff(c_247,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_232])).

tff(c_250,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_139,c_247])).

tff(c_253,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_250])).

tff(c_256,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_253])).

tff(c_260,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_256])).

tff(c_261,plain,(
    u1_struct_0('#skF_3') = u1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_232])).

tff(c_16,plain,(
    ! [A_12] :
      ( m1_subset_1(u1_pre_topc(A_12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_12))))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_361,plain,
    ( m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_16])).

tff(c_382,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_361])).

tff(c_262,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_232])).

tff(c_387,plain,(
    ! [A_114,B_115] :
      ( r2_hidden('#skF_1'(A_114,B_115),B_115)
      | v1_tops_2(B_115,A_114)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_114))))
      | ~ l1_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_389,plain,(
    ! [B_115] :
      ( r2_hidden('#skF_1'('#skF_3',B_115),B_115)
      | v1_tops_2(B_115,'#skF_3')
      | ~ m1_subset_1(B_115,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_387])).

tff(c_20985,plain,(
    ! [B_1243] :
      ( r2_hidden('#skF_1'('#skF_3',B_1243),B_1243)
      | v1_tops_2(B_1243,'#skF_3')
      | ~ m1_subset_1(B_1243,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_389])).

tff(c_21006,plain,
    ( r2_hidden('#skF_1'('#skF_3',u1_pre_topc('#skF_3')),u1_pre_topc('#skF_3'))
    | v1_tops_2(u1_pre_topc('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_382,c_20985])).

tff(c_21010,plain,(
    v1_tops_2(u1_pre_topc('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_21006])).

tff(c_52,plain,(
    ~ v3_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_48,plain,(
    ! [A_63] :
      ( r2_hidden('#skF_2'(A_63),u1_pre_topc(A_63))
      | v3_tdlat_3(A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_88,plain,(
    ! [A_80,C_81,B_82] :
      ( m1_subset_1(A_80,C_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(C_81))
      | ~ r2_hidden(A_80,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_94,plain,(
    ! [A_80,A_12] :
      ( m1_subset_1(A_80,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ r2_hidden(A_80,u1_pre_topc(A_12))
      | ~ l1_pre_topc(A_12) ) ),
    inference(resolution,[status(thm)],[c_16,c_88])).

tff(c_193,plain,(
    ! [B_101,A_102] :
      ( v3_pre_topc(B_101,A_102)
      | ~ r2_hidden(B_101,u1_pre_topc(A_102))
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_202,plain,(
    ! [A_103,A_104] :
      ( v3_pre_topc(A_103,A_104)
      | ~ r2_hidden(A_103,u1_pre_topc(A_104))
      | ~ l1_pre_topc(A_104) ) ),
    inference(resolution,[status(thm)],[c_94,c_193])).

tff(c_206,plain,(
    ! [A_63] :
      ( v3_pre_topc('#skF_2'(A_63),A_63)
      | v3_tdlat_3(A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(resolution,[status(thm)],[c_48,c_202])).

tff(c_50,plain,(
    ! [A_63] :
      ( m1_subset_1('#skF_2'(A_63),k1_zfmisc_1(u1_struct_0(A_63)))
      | v3_tdlat_3(A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_12,plain,(
    ! [B_8,A_6] :
      ( r2_hidden(B_8,u1_pre_topc(A_6))
      | ~ v3_pre_topc(B_8,A_6)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_337,plain,(
    ! [B_8] :
      ( r2_hidden(B_8,u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc(B_8,'#skF_3')
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_12])).

tff(c_500,plain,(
    ! [B_126] :
      ( r2_hidden(B_126,u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc(B_126,'#skF_3')
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_337])).

tff(c_511,plain,
    ( r2_hidden('#skF_2'('#skF_4'),u1_pre_topc('#skF_3'))
    | ~ v3_pre_topc('#skF_2'('#skF_4'),'#skF_3')
    | v3_tdlat_3('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_500])).

tff(c_518,plain,
    ( r2_hidden('#skF_2'('#skF_4'),u1_pre_topc('#skF_3'))
    | ~ v3_pre_topc('#skF_2'('#skF_4'),'#skF_3')
    | v3_tdlat_3('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_511])).

tff(c_519,plain,
    ( r2_hidden('#skF_2'('#skF_4'),u1_pre_topc('#skF_3'))
    | ~ v3_pre_topc('#skF_2'('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_518])).

tff(c_520,plain,(
    ~ v3_pre_topc('#skF_2'('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_519])).

tff(c_753,plain,(
    ! [B_142] :
      ( r2_hidden('#skF_1'('#skF_3',B_142),B_142)
      | v1_tops_2(B_142,'#skF_3')
      | ~ m1_subset_1(B_142,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_389])).

tff(c_766,plain,
    ( r2_hidden('#skF_1'('#skF_3',u1_pre_topc('#skF_4')),u1_pre_topc('#skF_4'))
    | v1_tops_2(u1_pre_topc('#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_753])).

tff(c_777,plain,
    ( r2_hidden('#skF_1'('#skF_3',u1_pre_topc('#skF_4')),u1_pre_topc('#skF_4'))
    | v1_tops_2(u1_pre_topc('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_766])).

tff(c_785,plain,(
    v1_tops_2(u1_pre_topc('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_777])).

tff(c_18,plain,(
    ! [C_19,A_13,B_17] :
      ( m1_subset_1(C_19,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ m1_subset_1(C_19,k1_zfmisc_1(u1_struct_0(B_17)))
      | ~ m1_pre_topc(B_17,A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_961,plain,(
    ! [C_158,A_159] :
      ( m1_subset_1(C_158,k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ m1_subset_1(C_158,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_3',A_159)
      | ~ l1_pre_topc(A_159) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_18])).

tff(c_980,plain,(
    ! [A_159] :
      ( m1_subset_1('#skF_2'('#skF_4'),k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ m1_pre_topc('#skF_3',A_159)
      | ~ l1_pre_topc(A_159)
      | v3_tdlat_3('#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_961])).

tff(c_997,plain,(
    ! [A_159] :
      ( m1_subset_1('#skF_2'('#skF_4'),k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ m1_pre_topc('#skF_3',A_159)
      | ~ l1_pre_topc(A_159)
      | v3_tdlat_3('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_980])).

tff(c_999,plain,(
    ! [A_160] :
      ( m1_subset_1('#skF_2'('#skF_4'),k1_zfmisc_1(u1_struct_0(A_160)))
      | ~ m1_pre_topc('#skF_3',A_160)
      | ~ l1_pre_topc(A_160) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_997])).

tff(c_1016,plain,
    ( m1_subset_1('#skF_2'('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_999])).

tff(c_1027,plain,
    ( m1_subset_1('#skF_2'('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1016])).

tff(c_1028,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1027])).

tff(c_1032,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_139,c_1028])).

tff(c_1039,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_186,c_1032])).

tff(c_1040,plain,(
    m1_subset_1('#skF_2'('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1027])).

tff(c_576,plain,(
    ! [C_129,A_130,B_131] :
      ( m1_subset_1(C_129,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_130))))
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_131))))
      | ~ m1_pre_topc(B_131,A_130)
      | ~ l1_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_670,plain,(
    ! [A_136,A_137] :
      ( m1_subset_1(u1_pre_topc(A_136),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_137))))
      | ~ m1_pre_topc(A_136,A_137)
      | ~ l1_pre_topc(A_137)
      | ~ l1_pre_topc(A_136) ) ),
    inference(resolution,[status(thm)],[c_16,c_576])).

tff(c_679,plain,(
    ! [A_136] :
      ( m1_subset_1(u1_pre_topc(A_136),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ m1_pre_topc(A_136,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_136) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_670])).

tff(c_684,plain,(
    ! [A_136] :
      ( m1_subset_1(u1_pre_topc(A_136),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ m1_pre_topc(A_136,'#skF_3')
      | ~ l1_pre_topc(A_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_679])).

tff(c_708,plain,(
    ! [A_140] :
      ( m1_subset_1(u1_pre_topc(A_140),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ m1_pre_topc(A_140,'#skF_3')
      | ~ l1_pre_topc(A_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_679])).

tff(c_30,plain,(
    ! [A_26,B_32] :
      ( r2_hidden('#skF_1'(A_26,B_32),B_32)
      | v1_tops_2(B_32,A_26)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_26))))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_712,plain,(
    ! [A_140] :
      ( r2_hidden('#skF_1'('#skF_4',u1_pre_topc(A_140)),u1_pre_topc(A_140))
      | v1_tops_2(u1_pre_topc(A_140),'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ m1_pre_topc(A_140,'#skF_3')
      | ~ l1_pre_topc(A_140) ) ),
    inference(resolution,[status(thm)],[c_708,c_30])).

tff(c_1541,plain,(
    ! [A_206] :
      ( r2_hidden('#skF_1'('#skF_4',u1_pre_topc(A_206)),u1_pre_topc(A_206))
      | v1_tops_2(u1_pre_topc(A_206),'#skF_4')
      | ~ m1_pre_topc(A_206,'#skF_3')
      | ~ l1_pre_topc(A_206) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_712])).

tff(c_200,plain,(
    ! [A_80,A_12] :
      ( v3_pre_topc(A_80,A_12)
      | ~ r2_hidden(A_80,u1_pre_topc(A_12))
      | ~ l1_pre_topc(A_12) ) ),
    inference(resolution,[status(thm)],[c_94,c_193])).

tff(c_1577,plain,(
    ! [A_208] :
      ( v3_pre_topc('#skF_1'('#skF_4',u1_pre_topc(A_208)),A_208)
      | v1_tops_2(u1_pre_topc(A_208),'#skF_4')
      | ~ m1_pre_topc(A_208,'#skF_3')
      | ~ l1_pre_topc(A_208) ) ),
    inference(resolution,[status(thm)],[c_1541,c_200])).

tff(c_28,plain,(
    ! [A_26,B_32] :
      ( ~ v3_pre_topc('#skF_1'(A_26,B_32),A_26)
      | v1_tops_2(B_32,A_26)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_26))))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1580,plain,
    ( ~ m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | v1_tops_2(u1_pre_topc('#skF_4'),'#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1577,c_28])).

tff(c_1583,plain,
    ( ~ m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | v1_tops_2(u1_pre_topc('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_262,c_1580])).

tff(c_1584,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitLeft,[status(thm)],[c_1583])).

tff(c_1587,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_684,c_1584])).

tff(c_1597,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_262,c_1587])).

tff(c_1599,plain,(
    m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_1583])).

tff(c_34,plain,(
    ! [C_42,A_36,B_40] :
      ( m1_subset_1(C_42,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_36))))
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_40))))
      | ~ m1_pre_topc(B_40,A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1658,plain,(
    ! [A_211] :
      ( m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_211))))
      | ~ m1_pre_topc('#skF_4',A_211)
      | ~ l1_pre_topc(A_211) ) ),
    inference(resolution,[status(thm)],[c_1599,c_34])).

tff(c_951,plain,(
    ! [C_155,A_156,B_157] :
      ( v3_pre_topc(C_155,A_156)
      | ~ r2_hidden(C_155,B_157)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ v1_tops_2(B_157,A_156)
      | ~ m1_subset_1(B_157,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_156))))
      | ~ l1_pre_topc(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_960,plain,(
    ! [A_63,A_156] :
      ( v3_pre_topc('#skF_2'(A_63),A_156)
      | ~ m1_subset_1('#skF_2'(A_63),k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ v1_tops_2(u1_pre_topc(A_63),A_156)
      | ~ m1_subset_1(u1_pre_topc(A_63),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_156))))
      | ~ l1_pre_topc(A_156)
      | v3_tdlat_3(A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(resolution,[status(thm)],[c_48,c_951])).

tff(c_1661,plain,(
    ! [A_211] :
      ( v3_pre_topc('#skF_2'('#skF_4'),A_211)
      | ~ m1_subset_1('#skF_2'('#skF_4'),k1_zfmisc_1(u1_struct_0(A_211)))
      | ~ v1_tops_2(u1_pre_topc('#skF_4'),A_211)
      | v3_tdlat_3('#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ m1_pre_topc('#skF_4',A_211)
      | ~ l1_pre_topc(A_211) ) ),
    inference(resolution,[status(thm)],[c_1658,c_960])).

tff(c_1678,plain,(
    ! [A_211] :
      ( v3_pre_topc('#skF_2'('#skF_4'),A_211)
      | ~ m1_subset_1('#skF_2'('#skF_4'),k1_zfmisc_1(u1_struct_0(A_211)))
      | ~ v1_tops_2(u1_pre_topc('#skF_4'),A_211)
      | v3_tdlat_3('#skF_4')
      | ~ m1_pre_topc('#skF_4',A_211)
      | ~ l1_pre_topc(A_211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1661])).

tff(c_1719,plain,(
    ! [A_213] :
      ( v3_pre_topc('#skF_2'('#skF_4'),A_213)
      | ~ m1_subset_1('#skF_2'('#skF_4'),k1_zfmisc_1(u1_struct_0(A_213)))
      | ~ v1_tops_2(u1_pre_topc('#skF_4'),A_213)
      | ~ m1_pre_topc('#skF_4',A_213)
      | ~ l1_pre_topc(A_213) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1678])).

tff(c_1763,plain,
    ( v3_pre_topc('#skF_2'('#skF_4'),'#skF_3')
    | ~ m1_subset_1('#skF_2'('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ v1_tops_2(u1_pre_topc('#skF_4'),'#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_1719])).

tff(c_1800,plain,(
    v3_pre_topc('#skF_2'('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_262,c_785,c_1040,c_1763])).

tff(c_1802,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_520,c_1800])).

tff(c_1804,plain,(
    ~ v1_tops_2(u1_pre_topc('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_777])).

tff(c_2910,plain,(
    ! [A_297] :
      ( r2_hidden('#skF_1'('#skF_4',u1_pre_topc(A_297)),u1_pre_topc(A_297))
      | v1_tops_2(u1_pre_topc(A_297),'#skF_4')
      | ~ m1_pre_topc(A_297,'#skF_3')
      | ~ l1_pre_topc(A_297) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_712])).

tff(c_2940,plain,(
    ! [A_298] :
      ( v3_pre_topc('#skF_1'('#skF_4',u1_pre_topc(A_298)),A_298)
      | v1_tops_2(u1_pre_topc(A_298),'#skF_4')
      | ~ m1_pre_topc(A_298,'#skF_3')
      | ~ l1_pre_topc(A_298) ) ),
    inference(resolution,[status(thm)],[c_2910,c_200])).

tff(c_2943,plain,
    ( ~ m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | v1_tops_2(u1_pre_topc('#skF_4'),'#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_2940,c_28])).

tff(c_2946,plain,
    ( ~ m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | v1_tops_2(u1_pre_topc('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_262,c_2943])).

tff(c_2997,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitLeft,[status(thm)],[c_2946])).

tff(c_3000,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_684,c_2997])).

tff(c_3010,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_262,c_3000])).

tff(c_3011,plain,(
    v1_tops_2(u1_pre_topc('#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_2946])).

tff(c_3949,plain,(
    ! [C_344,A_345] :
      ( m1_subset_1(C_344,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_345))))
      | ~ m1_subset_1(C_344,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ m1_pre_topc('#skF_3',A_345)
      | ~ l1_pre_topc(A_345) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_576])).

tff(c_3967,plain,(
    ! [A_345] :
      ( m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_345))))
      | ~ m1_pre_topc('#skF_3',A_345)
      | ~ l1_pre_topc(A_345)
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_3949])).

tff(c_3982,plain,(
    ! [A_345] :
      ( m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_345))))
      | ~ m1_pre_topc('#skF_3',A_345)
      | ~ l1_pre_topc(A_345) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_3967])).

tff(c_584,plain,(
    ! [A_12,A_130] :
      ( m1_subset_1(u1_pre_topc(A_12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_130))))
      | ~ m1_pre_topc(A_12,A_130)
      | ~ l1_pre_topc(A_130)
      | ~ l1_pre_topc(A_12) ) ),
    inference(resolution,[status(thm)],[c_16,c_576])).

tff(c_2078,plain,(
    ! [D_229,C_230,A_231] :
      ( v1_tops_2(D_229,C_230)
      | ~ m1_subset_1(D_229,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_230))))
      | ~ v1_tops_2(D_229,A_231)
      | ~ m1_pre_topc(C_230,A_231)
      | ~ m1_subset_1(D_229,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_231))))
      | ~ l1_pre_topc(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_5225,plain,(
    ! [A_406,A_407,A_408] :
      ( v1_tops_2(u1_pre_topc(A_406),A_407)
      | ~ v1_tops_2(u1_pre_topc(A_406),A_408)
      | ~ m1_pre_topc(A_407,A_408)
      | ~ m1_subset_1(u1_pre_topc(A_406),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_408))))
      | ~ l1_pre_topc(A_408)
      | ~ m1_pre_topc(A_406,A_407)
      | ~ l1_pre_topc(A_407)
      | ~ l1_pre_topc(A_406) ) ),
    inference(resolution,[status(thm)],[c_584,c_2078])).

tff(c_5235,plain,(
    ! [A_406] :
      ( v1_tops_2(u1_pre_topc(A_406),'#skF_3')
      | ~ v1_tops_2(u1_pre_topc(A_406),'#skF_4')
      | ~ m1_subset_1(u1_pre_topc(A_406),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ l1_pre_topc('#skF_4')
      | ~ m1_pre_topc(A_406,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_406) ) ),
    inference(resolution,[status(thm)],[c_186,c_5225])).

tff(c_6884,plain,(
    ! [A_509] :
      ( v1_tops_2(u1_pre_topc(A_509),'#skF_3')
      | ~ v1_tops_2(u1_pre_topc(A_509),'#skF_4')
      | ~ m1_subset_1(u1_pre_topc(A_509),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ m1_pre_topc(A_509,'#skF_3')
      | ~ l1_pre_topc(A_509) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_5235])).

tff(c_6908,plain,
    ( v1_tops_2(u1_pre_topc('#skF_4'),'#skF_3')
    | ~ v1_tops_2(u1_pre_topc('#skF_4'),'#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_3982,c_6884])).

tff(c_6958,plain,(
    v1_tops_2(u1_pre_topc('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_186,c_262,c_3011,c_6908])).

tff(c_6960,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1804,c_6958])).

tff(c_6961,plain,(
    r2_hidden('#skF_2'('#skF_4'),u1_pre_topc('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_519])).

tff(c_346,plain,(
    ! [A_80] :
      ( m1_subset_1(A_80,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(A_80,u1_pre_topc('#skF_3'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_94])).

tff(c_415,plain,(
    ! [A_117] :
      ( m1_subset_1(A_117,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(A_117,u1_pre_topc('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_346])).

tff(c_420,plain,(
    ! [A_117] :
      ( r2_hidden(A_117,u1_pre_topc('#skF_4'))
      | ~ v3_pre_topc(A_117,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ r2_hidden(A_117,u1_pre_topc('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_415,c_12])).

tff(c_426,plain,(
    ! [A_117] :
      ( r2_hidden(A_117,u1_pre_topc('#skF_4'))
      | ~ v3_pre_topc(A_117,'#skF_4')
      | ~ r2_hidden(A_117,u1_pre_topc('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_420])).

tff(c_6982,plain,
    ( r2_hidden('#skF_2'('#skF_4'),u1_pre_topc('#skF_4'))
    | ~ v3_pre_topc('#skF_2'('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_6961,c_426])).

tff(c_6988,plain,(
    ~ v3_pre_topc('#skF_2'('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_6982])).

tff(c_6991,plain,
    ( v3_tdlat_3('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_206,c_6988])).

tff(c_6994,plain,(
    v3_tdlat_3('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_6991])).

tff(c_6996,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_6994])).

tff(c_6997,plain,(
    r2_hidden('#skF_2'('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_6982])).

tff(c_6963,plain,(
    ! [C_510,A_511,B_512] :
      ( m1_subset_1(C_510,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_511))))
      | ~ m1_subset_1(C_510,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_512))))
      | ~ m1_pre_topc(B_512,A_511)
      | ~ l1_pre_topc(A_511) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_7230,plain,(
    ! [A_525,A_526] :
      ( m1_subset_1(u1_pre_topc(A_525),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_526))))
      | ~ m1_pre_topc(A_525,A_526)
      | ~ l1_pre_topc(A_526)
      | ~ l1_pre_topc(A_525) ) ),
    inference(resolution,[status(thm)],[c_16,c_6963])).

tff(c_7239,plain,(
    ! [A_525] :
      ( m1_subset_1(u1_pre_topc(A_525),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ m1_pre_topc(A_525,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_525) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_7230])).

tff(c_7245,plain,(
    ! [A_527] :
      ( m1_subset_1(u1_pre_topc(A_527),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ m1_pre_topc(A_527,'#skF_3')
      | ~ l1_pre_topc(A_527) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_7239])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( m1_subset_1(A_3,C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_7371,plain,(
    ! [A_534,A_535] :
      ( m1_subset_1(A_534,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(A_534,u1_pre_topc(A_535))
      | ~ m1_pre_topc(A_535,'#skF_3')
      | ~ l1_pre_topc(A_535) ) ),
    inference(resolution,[status(thm)],[c_7245,c_8])).

tff(c_7377,plain,
    ( m1_subset_1('#skF_2'('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6997,c_7371])).

tff(c_7388,plain,(
    m1_subset_1('#skF_2'('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_262,c_7377])).

tff(c_54,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_396,plain,
    ( r2_hidden('#skF_1'('#skF_4',u1_pre_topc('#skF_3')),u1_pre_topc('#skF_3'))
    | v1_tops_2(u1_pre_topc('#skF_3'),'#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_382,c_30])).

tff(c_401,plain,
    ( r2_hidden('#skF_1'('#skF_4',u1_pre_topc('#skF_3')),u1_pre_topc('#skF_3'))
    | v1_tops_2(u1_pre_topc('#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_396])).

tff(c_448,plain,(
    v1_tops_2(u1_pre_topc('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_401])).

tff(c_44,plain,(
    ! [A_63,B_66] :
      ( r2_hidden(k6_subset_1(u1_struct_0(A_63),B_66),u1_pre_topc(A_63))
      | ~ r2_hidden(B_66,u1_pre_topc(A_63))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ v3_tdlat_3(A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_8055,plain,(
    ! [A_581,A_582,A_583] :
      ( m1_subset_1(A_581,k1_zfmisc_1(u1_struct_0(A_582)))
      | ~ r2_hidden(A_581,u1_pre_topc(A_583))
      | ~ m1_pre_topc(A_583,A_582)
      | ~ l1_pre_topc(A_582)
      | ~ l1_pre_topc(A_583) ) ),
    inference(resolution,[status(thm)],[c_7230,c_8])).

tff(c_12665,plain,(
    ! [A_830,B_831,A_832] :
      ( m1_subset_1(k6_subset_1(u1_struct_0(A_830),B_831),k1_zfmisc_1(u1_struct_0(A_832)))
      | ~ m1_pre_topc(A_830,A_832)
      | ~ l1_pre_topc(A_832)
      | ~ r2_hidden(B_831,u1_pre_topc(A_830))
      | ~ m1_subset_1(B_831,k1_zfmisc_1(u1_struct_0(A_830)))
      | ~ v3_tdlat_3(A_830)
      | ~ l1_pre_topc(A_830) ) ),
    inference(resolution,[status(thm)],[c_44,c_8055])).

tff(c_7257,plain,(
    ! [C_528,A_529,B_530] :
      ( v3_pre_topc(C_528,A_529)
      | ~ r2_hidden(C_528,B_530)
      | ~ m1_subset_1(C_528,k1_zfmisc_1(u1_struct_0(A_529)))
      | ~ v1_tops_2(B_530,A_529)
      | ~ m1_subset_1(B_530,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_529))))
      | ~ l1_pre_topc(A_529) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_7268,plain,(
    ! [A_63,B_66,A_529] :
      ( v3_pre_topc(k6_subset_1(u1_struct_0(A_63),B_66),A_529)
      | ~ m1_subset_1(k6_subset_1(u1_struct_0(A_63),B_66),k1_zfmisc_1(u1_struct_0(A_529)))
      | ~ v1_tops_2(u1_pre_topc(A_63),A_529)
      | ~ m1_subset_1(u1_pre_topc(A_63),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_529))))
      | ~ l1_pre_topc(A_529)
      | ~ r2_hidden(B_66,u1_pre_topc(A_63))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ v3_tdlat_3(A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(resolution,[status(thm)],[c_44,c_7257])).

tff(c_20567,plain,(
    ! [A_1216,B_1217,A_1218] :
      ( v3_pre_topc(k6_subset_1(u1_struct_0(A_1216),B_1217),A_1218)
      | ~ v1_tops_2(u1_pre_topc(A_1216),A_1218)
      | ~ m1_subset_1(u1_pre_topc(A_1216),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1218))))
      | ~ m1_pre_topc(A_1216,A_1218)
      | ~ l1_pre_topc(A_1218)
      | ~ r2_hidden(B_1217,u1_pre_topc(A_1216))
      | ~ m1_subset_1(B_1217,k1_zfmisc_1(u1_struct_0(A_1216)))
      | ~ v3_tdlat_3(A_1216)
      | ~ l1_pre_topc(A_1216) ) ),
    inference(resolution,[status(thm)],[c_12665,c_7268])).

tff(c_20615,plain,(
    ! [B_1217] :
      ( v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'),B_1217),'#skF_4')
      | ~ v1_tops_2(u1_pre_topc('#skF_3'),'#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ r2_hidden(B_1217,u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(B_1217,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v3_tdlat_3('#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_382,c_20567])).

tff(c_20675,plain,(
    ! [B_1219] :
      ( v3_pre_topc(k6_subset_1(u1_struct_0('#skF_4'),B_1219),'#skF_4')
      | ~ r2_hidden(B_1219,u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(B_1219,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_54,c_261,c_58,c_186,c_448,c_261,c_20615])).

tff(c_7110,plain,(
    ! [A_518,B_519] :
      ( r2_hidden(k6_subset_1(u1_struct_0(A_518),B_519),u1_pre_topc(A_518))
      | ~ r2_hidden(B_519,u1_pre_topc(A_518))
      | ~ m1_subset_1(B_519,k1_zfmisc_1(u1_struct_0(A_518)))
      | ~ v3_tdlat_3(A_518)
      | ~ l1_pre_topc(A_518) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_7114,plain,(
    ! [B_519] :
      ( r2_hidden(k6_subset_1(u1_struct_0('#skF_3'),B_519),u1_pre_topc('#skF_4'))
      | ~ v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'),B_519),'#skF_4')
      | ~ r2_hidden(B_519,u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(B_519,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v3_tdlat_3('#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_7110,c_426])).

tff(c_15661,plain,(
    ! [B_954] :
      ( r2_hidden(k6_subset_1(u1_struct_0('#skF_4'),B_954),u1_pre_topc('#skF_4'))
      | ~ v3_pre_topc(k6_subset_1(u1_struct_0('#skF_4'),B_954),'#skF_4')
      | ~ r2_hidden(B_954,u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(B_954,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_54,c_261,c_261,c_261,c_7114])).

tff(c_46,plain,(
    ! [A_63] :
      ( ~ r2_hidden(k6_subset_1(u1_struct_0(A_63),'#skF_2'(A_63)),u1_pre_topc(A_63))
      | v3_tdlat_3(A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_15702,plain,
    ( v3_tdlat_3('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v3_pre_topc(k6_subset_1(u1_struct_0('#skF_4'),'#skF_2'('#skF_4')),'#skF_4')
    | ~ r2_hidden('#skF_2'('#skF_4'),u1_pre_topc('#skF_3'))
    | ~ m1_subset_1('#skF_2'('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_15661,c_46])).

tff(c_15739,plain,
    ( v3_tdlat_3('#skF_4')
    | ~ v3_pre_topc(k6_subset_1(u1_struct_0('#skF_4'),'#skF_2'('#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7388,c_6961,c_58,c_15702])).

tff(c_15740,plain,(
    ~ v3_pre_topc(k6_subset_1(u1_struct_0('#skF_4'),'#skF_2'('#skF_4')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_15739])).

tff(c_20678,plain,
    ( ~ r2_hidden('#skF_2'('#skF_4'),u1_pre_topc('#skF_3'))
    | ~ m1_subset_1('#skF_2'('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_20675,c_15740])).

tff(c_20682,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7388,c_6961,c_20678])).

tff(c_20684,plain,(
    ~ v1_tops_2(u1_pre_topc('#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_401])).

tff(c_22447,plain,(
    ! [D_1338,C_1339,A_1340] :
      ( v1_tops_2(D_1338,C_1339)
      | ~ m1_subset_1(D_1338,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_1339))))
      | ~ v1_tops_2(D_1338,A_1340)
      | ~ m1_pre_topc(C_1339,A_1340)
      | ~ m1_subset_1(D_1338,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1340))))
      | ~ l1_pre_topc(A_1340) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_22455,plain,(
    ! [A_1340] :
      ( v1_tops_2(u1_pre_topc('#skF_3'),'#skF_4')
      | ~ v1_tops_2(u1_pre_topc('#skF_3'),A_1340)
      | ~ m1_pre_topc('#skF_4',A_1340)
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1340))))
      | ~ l1_pre_topc(A_1340) ) ),
    inference(resolution,[status(thm)],[c_382,c_22447])).

tff(c_23273,plain,(
    ! [A_1405] :
      ( ~ v1_tops_2(u1_pre_topc('#skF_3'),A_1405)
      | ~ m1_pre_topc('#skF_4',A_1405)
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1405))))
      | ~ l1_pre_topc(A_1405) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20684,c_22455])).

tff(c_23290,plain,
    ( ~ v1_tops_2(u1_pre_topc('#skF_3'),'#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_23273])).

tff(c_23307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_382,c_262,c_21010,c_23290])).

tff(c_23309,plain,(
    ~ v1_tops_2(u1_pre_topc('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_21006])).

tff(c_23312,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_23309])).

tff(c_23316,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_23312])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:41:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.04/5.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.04/5.28  
% 12.04/5.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.04/5.28  %$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > l1_pre_topc > k6_subset_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 12.04/5.28  
% 12.04/5.28  %Foreground sorts:
% 12.04/5.28  
% 12.04/5.28  
% 12.04/5.28  %Background operators:
% 12.04/5.28  
% 12.04/5.28  
% 12.04/5.28  %Foreground operators:
% 12.04/5.28  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 12.04/5.28  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 12.04/5.28  tff('#skF_2', type, '#skF_2': $i > $i).
% 12.04/5.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.04/5.28  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 12.04/5.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.04/5.28  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 12.04/5.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 12.04/5.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.04/5.28  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 12.04/5.28  tff('#skF_3', type, '#skF_3': $i).
% 12.04/5.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.04/5.28  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 12.04/5.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.04/5.28  tff('#skF_4', type, '#skF_4': $i).
% 12.04/5.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.04/5.28  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 12.04/5.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.04/5.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.04/5.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.04/5.28  
% 12.04/5.31  tff(f_162, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & v3_tdlat_3(A)) => v3_tdlat_3(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tex_2)).
% 12.04/5.31  tff(f_128, axiom, (![A]: (l1_pre_topc(A) => v1_tops_2(u1_pre_topc(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_compts_1)).
% 12.04/5.31  tff(f_132, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 12.04/5.31  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 12.04/5.31  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 12.04/5.31  tff(f_139, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_borsuk_1)).
% 12.04/5.31  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.04/5.31  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 12.04/5.31  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_2)).
% 12.04/5.31  tff(f_150, axiom, (![A]: (l1_pre_topc(A) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) => r2_hidden(k6_subset_1(u1_struct_0(A), B), u1_pre_topc(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tdlat_3)).
% 12.04/5.31  tff(f_37, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 12.04/5.31  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 12.04/5.31  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 12.04/5.31  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_2)).
% 12.04/5.31  tff(f_124, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_pre_topc(C, A) => (v1_tops_2(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C)))) => ((D = B) => v1_tops_2(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tops_2)).
% 12.04/5.31  tff(c_60, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_162])).
% 12.04/5.31  tff(c_38, plain, (![A_58]: (v1_tops_2(u1_pre_topc(A_58), A_58) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_128])).
% 12.04/5.31  tff(c_58, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 12.04/5.31  tff(c_40, plain, (![A_59]: (m1_pre_topc(A_59, A_59) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_132])).
% 12.04/5.31  tff(c_123, plain, (![A_94, B_95]: (m1_pre_topc(A_94, g1_pre_topc(u1_struct_0(B_95), u1_pre_topc(B_95))) | ~m1_pre_topc(A_94, B_95) | ~l1_pre_topc(B_95) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_83])).
% 12.04/5.31  tff(c_56, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_162])).
% 12.04/5.31  tff(c_100, plain, (![B_86, A_87]: (m1_pre_topc(B_86, A_87) | ~m1_pre_topc(B_86, g1_pre_topc(u1_struct_0(A_87), u1_pre_topc(A_87))) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_74])).
% 12.04/5.31  tff(c_103, plain, (![B_86]: (m1_pre_topc(B_86, '#skF_3') | ~m1_pre_topc(B_86, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_100])).
% 12.04/5.31  tff(c_109, plain, (![B_86]: (m1_pre_topc(B_86, '#skF_3') | ~m1_pre_topc(B_86, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_103])).
% 12.04/5.31  tff(c_127, plain, (![A_94]: (m1_pre_topc(A_94, '#skF_3') | ~m1_pre_topc(A_94, '#skF_4') | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_94))), inference(resolution, [status(thm)], [c_123, c_109])).
% 12.04/5.31  tff(c_139, plain, (![A_94]: (m1_pre_topc(A_94, '#skF_3') | ~m1_pre_topc(A_94, '#skF_4') | ~l1_pre_topc(A_94))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_127])).
% 12.04/5.31  tff(c_136, plain, (![A_94]: (m1_pre_topc(A_94, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_pre_topc(A_94, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_94))), inference(superposition, [status(thm), theory('equality')], [c_56, c_123])).
% 12.04/5.31  tff(c_160, plain, (![A_99]: (m1_pre_topc(A_99, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_pre_topc(A_99, '#skF_3') | ~l1_pre_topc(A_99))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_136])).
% 12.04/5.31  tff(c_20, plain, (![B_22, A_20]: (m1_pre_topc(B_22, A_20) | ~m1_pre_topc(B_22, g1_pre_topc(u1_struct_0(A_20), u1_pre_topc(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_74])).
% 12.04/5.31  tff(c_166, plain, (![A_99]: (m1_pre_topc(A_99, '#skF_4') | ~l1_pre_topc('#skF_4') | ~m1_pre_topc(A_99, '#skF_3') | ~l1_pre_topc(A_99))), inference(resolution, [status(thm)], [c_160, c_20])).
% 12.04/5.31  tff(c_175, plain, (![A_100]: (m1_pre_topc(A_100, '#skF_4') | ~m1_pre_topc(A_100, '#skF_3') | ~l1_pre_topc(A_100))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_166])).
% 12.04/5.31  tff(c_182, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_175])).
% 12.04/5.31  tff(c_186, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_182])).
% 12.04/5.31  tff(c_42, plain, (![B_62, A_60]: (r1_tarski(u1_struct_0(B_62), u1_struct_0(A_60)) | ~m1_pre_topc(B_62, A_60) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_139])).
% 12.04/5.31  tff(c_84, plain, (![B_78, A_79]: (r1_tarski(u1_struct_0(B_78), u1_struct_0(A_79)) | ~m1_pre_topc(B_78, A_79) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_139])).
% 12.04/5.31  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.04/5.31  tff(c_208, plain, (![B_106, A_107]: (u1_struct_0(B_106)=u1_struct_0(A_107) | ~r1_tarski(u1_struct_0(A_107), u1_struct_0(B_106)) | ~m1_pre_topc(B_106, A_107) | ~l1_pre_topc(A_107))), inference(resolution, [status(thm)], [c_84, c_2])).
% 12.04/5.31  tff(c_219, plain, (![B_108, A_109]: (u1_struct_0(B_108)=u1_struct_0(A_109) | ~m1_pre_topc(A_109, B_108) | ~l1_pre_topc(B_108) | ~m1_pre_topc(B_108, A_109) | ~l1_pre_topc(A_109))), inference(resolution, [status(thm)], [c_42, c_208])).
% 12.04/5.31  tff(c_221, plain, (u1_struct_0('#skF_3')=u1_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_186, c_219])).
% 12.04/5.31  tff(c_232, plain, (u1_struct_0('#skF_3')=u1_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_221])).
% 12.04/5.31  tff(c_247, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_232])).
% 12.04/5.31  tff(c_250, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_139, c_247])).
% 12.04/5.31  tff(c_253, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_250])).
% 12.04/5.31  tff(c_256, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_40, c_253])).
% 12.04/5.31  tff(c_260, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_256])).
% 12.04/5.31  tff(c_261, plain, (u1_struct_0('#skF_3')=u1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_232])).
% 12.04/5.31  tff(c_16, plain, (![A_12]: (m1_subset_1(u1_pre_topc(A_12), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_12)))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.04/5.31  tff(c_361, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_261, c_16])).
% 12.04/5.31  tff(c_382, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_361])).
% 12.04/5.31  tff(c_262, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_232])).
% 12.04/5.31  tff(c_387, plain, (![A_114, B_115]: (r2_hidden('#skF_1'(A_114, B_115), B_115) | v1_tops_2(B_115, A_114) | ~m1_subset_1(B_115, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_114)))) | ~l1_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.04/5.31  tff(c_389, plain, (![B_115]: (r2_hidden('#skF_1'('#skF_3', B_115), B_115) | v1_tops_2(B_115, '#skF_3') | ~m1_subset_1(B_115, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_261, c_387])).
% 12.04/5.31  tff(c_20985, plain, (![B_1243]: (r2_hidden('#skF_1'('#skF_3', B_1243), B_1243) | v1_tops_2(B_1243, '#skF_3') | ~m1_subset_1(B_1243, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_389])).
% 12.04/5.31  tff(c_21006, plain, (r2_hidden('#skF_1'('#skF_3', u1_pre_topc('#skF_3')), u1_pre_topc('#skF_3')) | v1_tops_2(u1_pre_topc('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_382, c_20985])).
% 12.04/5.31  tff(c_21010, plain, (v1_tops_2(u1_pre_topc('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_21006])).
% 12.04/5.31  tff(c_52, plain, (~v3_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 12.04/5.31  tff(c_48, plain, (![A_63]: (r2_hidden('#skF_2'(A_63), u1_pre_topc(A_63)) | v3_tdlat_3(A_63) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_150])).
% 12.04/5.31  tff(c_88, plain, (![A_80, C_81, B_82]: (m1_subset_1(A_80, C_81) | ~m1_subset_1(B_82, k1_zfmisc_1(C_81)) | ~r2_hidden(A_80, B_82))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.04/5.31  tff(c_94, plain, (![A_80, A_12]: (m1_subset_1(A_80, k1_zfmisc_1(u1_struct_0(A_12))) | ~r2_hidden(A_80, u1_pre_topc(A_12)) | ~l1_pre_topc(A_12))), inference(resolution, [status(thm)], [c_16, c_88])).
% 12.04/5.31  tff(c_193, plain, (![B_101, A_102]: (v3_pre_topc(B_101, A_102) | ~r2_hidden(B_101, u1_pre_topc(A_102)) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.04/5.31  tff(c_202, plain, (![A_103, A_104]: (v3_pre_topc(A_103, A_104) | ~r2_hidden(A_103, u1_pre_topc(A_104)) | ~l1_pre_topc(A_104))), inference(resolution, [status(thm)], [c_94, c_193])).
% 12.04/5.31  tff(c_206, plain, (![A_63]: (v3_pre_topc('#skF_2'(A_63), A_63) | v3_tdlat_3(A_63) | ~l1_pre_topc(A_63))), inference(resolution, [status(thm)], [c_48, c_202])).
% 12.04/5.31  tff(c_50, plain, (![A_63]: (m1_subset_1('#skF_2'(A_63), k1_zfmisc_1(u1_struct_0(A_63))) | v3_tdlat_3(A_63) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_150])).
% 12.04/5.31  tff(c_12, plain, (![B_8, A_6]: (r2_hidden(B_8, u1_pre_topc(A_6)) | ~v3_pre_topc(B_8, A_6) | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.04/5.31  tff(c_337, plain, (![B_8]: (r2_hidden(B_8, u1_pre_topc('#skF_3')) | ~v3_pre_topc(B_8, '#skF_3') | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_261, c_12])).
% 12.04/5.31  tff(c_500, plain, (![B_126]: (r2_hidden(B_126, u1_pre_topc('#skF_3')) | ~v3_pre_topc(B_126, '#skF_3') | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_337])).
% 12.04/5.31  tff(c_511, plain, (r2_hidden('#skF_2'('#skF_4'), u1_pre_topc('#skF_3')) | ~v3_pre_topc('#skF_2'('#skF_4'), '#skF_3') | v3_tdlat_3('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_50, c_500])).
% 12.04/5.31  tff(c_518, plain, (r2_hidden('#skF_2'('#skF_4'), u1_pre_topc('#skF_3')) | ~v3_pre_topc('#skF_2'('#skF_4'), '#skF_3') | v3_tdlat_3('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_511])).
% 12.04/5.31  tff(c_519, plain, (r2_hidden('#skF_2'('#skF_4'), u1_pre_topc('#skF_3')) | ~v3_pre_topc('#skF_2'('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_52, c_518])).
% 12.04/5.31  tff(c_520, plain, (~v3_pre_topc('#skF_2'('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_519])).
% 12.04/5.31  tff(c_753, plain, (![B_142]: (r2_hidden('#skF_1'('#skF_3', B_142), B_142) | v1_tops_2(B_142, '#skF_3') | ~m1_subset_1(B_142, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_389])).
% 12.04/5.31  tff(c_766, plain, (r2_hidden('#skF_1'('#skF_3', u1_pre_topc('#skF_4')), u1_pre_topc('#skF_4')) | v1_tops_2(u1_pre_topc('#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_16, c_753])).
% 12.04/5.31  tff(c_777, plain, (r2_hidden('#skF_1'('#skF_3', u1_pre_topc('#skF_4')), u1_pre_topc('#skF_4')) | v1_tops_2(u1_pre_topc('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_766])).
% 12.04/5.31  tff(c_785, plain, (v1_tops_2(u1_pre_topc('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_777])).
% 12.04/5.31  tff(c_18, plain, (![C_19, A_13, B_17]: (m1_subset_1(C_19, k1_zfmisc_1(u1_struct_0(A_13))) | ~m1_subset_1(C_19, k1_zfmisc_1(u1_struct_0(B_17))) | ~m1_pre_topc(B_17, A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_67])).
% 12.04/5.31  tff(c_961, plain, (![C_158, A_159]: (m1_subset_1(C_158, k1_zfmisc_1(u1_struct_0(A_159))) | ~m1_subset_1(C_158, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', A_159) | ~l1_pre_topc(A_159))), inference(superposition, [status(thm), theory('equality')], [c_261, c_18])).
% 12.04/5.31  tff(c_980, plain, (![A_159]: (m1_subset_1('#skF_2'('#skF_4'), k1_zfmisc_1(u1_struct_0(A_159))) | ~m1_pre_topc('#skF_3', A_159) | ~l1_pre_topc(A_159) | v3_tdlat_3('#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_961])).
% 12.04/5.31  tff(c_997, plain, (![A_159]: (m1_subset_1('#skF_2'('#skF_4'), k1_zfmisc_1(u1_struct_0(A_159))) | ~m1_pre_topc('#skF_3', A_159) | ~l1_pre_topc(A_159) | v3_tdlat_3('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_980])).
% 12.04/5.31  tff(c_999, plain, (![A_160]: (m1_subset_1('#skF_2'('#skF_4'), k1_zfmisc_1(u1_struct_0(A_160))) | ~m1_pre_topc('#skF_3', A_160) | ~l1_pre_topc(A_160))), inference(negUnitSimplification, [status(thm)], [c_52, c_997])).
% 12.04/5.31  tff(c_1016, plain, (m1_subset_1('#skF_2'('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_261, c_999])).
% 12.04/5.31  tff(c_1027, plain, (m1_subset_1('#skF_2'('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1016])).
% 12.04/5.31  tff(c_1028, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_1027])).
% 12.04/5.31  tff(c_1032, plain, (~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_139, c_1028])).
% 12.04/5.31  tff(c_1039, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_186, c_1032])).
% 12.04/5.31  tff(c_1040, plain, (m1_subset_1('#skF_2'('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_1027])).
% 12.04/5.31  tff(c_576, plain, (![C_129, A_130, B_131]: (m1_subset_1(C_129, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_130)))) | ~m1_subset_1(C_129, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_131)))) | ~m1_pre_topc(B_131, A_130) | ~l1_pre_topc(A_130))), inference(cnfTransformation, [status(thm)], [f_107])).
% 12.04/5.31  tff(c_670, plain, (![A_136, A_137]: (m1_subset_1(u1_pre_topc(A_136), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_137)))) | ~m1_pre_topc(A_136, A_137) | ~l1_pre_topc(A_137) | ~l1_pre_topc(A_136))), inference(resolution, [status(thm)], [c_16, c_576])).
% 12.04/5.31  tff(c_679, plain, (![A_136]: (m1_subset_1(u1_pre_topc(A_136), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~m1_pre_topc(A_136, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_136))), inference(superposition, [status(thm), theory('equality')], [c_261, c_670])).
% 12.04/5.31  tff(c_684, plain, (![A_136]: (m1_subset_1(u1_pre_topc(A_136), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~m1_pre_topc(A_136, '#skF_3') | ~l1_pre_topc(A_136))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_679])).
% 12.04/5.31  tff(c_708, plain, (![A_140]: (m1_subset_1(u1_pre_topc(A_140), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~m1_pre_topc(A_140, '#skF_3') | ~l1_pre_topc(A_140))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_679])).
% 12.04/5.31  tff(c_30, plain, (![A_26, B_32]: (r2_hidden('#skF_1'(A_26, B_32), B_32) | v1_tops_2(B_32, A_26) | ~m1_subset_1(B_32, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_26)))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.04/5.31  tff(c_712, plain, (![A_140]: (r2_hidden('#skF_1'('#skF_4', u1_pre_topc(A_140)), u1_pre_topc(A_140)) | v1_tops_2(u1_pre_topc(A_140), '#skF_4') | ~l1_pre_topc('#skF_4') | ~m1_pre_topc(A_140, '#skF_3') | ~l1_pre_topc(A_140))), inference(resolution, [status(thm)], [c_708, c_30])).
% 12.04/5.31  tff(c_1541, plain, (![A_206]: (r2_hidden('#skF_1'('#skF_4', u1_pre_topc(A_206)), u1_pre_topc(A_206)) | v1_tops_2(u1_pre_topc(A_206), '#skF_4') | ~m1_pre_topc(A_206, '#skF_3') | ~l1_pre_topc(A_206))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_712])).
% 12.04/5.31  tff(c_200, plain, (![A_80, A_12]: (v3_pre_topc(A_80, A_12) | ~r2_hidden(A_80, u1_pre_topc(A_12)) | ~l1_pre_topc(A_12))), inference(resolution, [status(thm)], [c_94, c_193])).
% 12.04/5.31  tff(c_1577, plain, (![A_208]: (v3_pre_topc('#skF_1'('#skF_4', u1_pre_topc(A_208)), A_208) | v1_tops_2(u1_pre_topc(A_208), '#skF_4') | ~m1_pre_topc(A_208, '#skF_3') | ~l1_pre_topc(A_208))), inference(resolution, [status(thm)], [c_1541, c_200])).
% 12.04/5.31  tff(c_28, plain, (![A_26, B_32]: (~v3_pre_topc('#skF_1'(A_26, B_32), A_26) | v1_tops_2(B_32, A_26) | ~m1_subset_1(B_32, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_26)))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.04/5.31  tff(c_1580, plain, (~m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | v1_tops_2(u1_pre_topc('#skF_4'), '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_1577, c_28])).
% 12.04/5.31  tff(c_1583, plain, (~m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | v1_tops_2(u1_pre_topc('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_262, c_1580])).
% 12.04/5.31  tff(c_1584, plain, (~m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(splitLeft, [status(thm)], [c_1583])).
% 12.04/5.31  tff(c_1587, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_684, c_1584])).
% 12.04/5.31  tff(c_1597, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_262, c_1587])).
% 12.04/5.31  tff(c_1599, plain, (m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_1583])).
% 12.04/5.31  tff(c_34, plain, (![C_42, A_36, B_40]: (m1_subset_1(C_42, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_36)))) | ~m1_subset_1(C_42, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_40)))) | ~m1_pre_topc(B_40, A_36) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_107])).
% 12.04/5.31  tff(c_1658, plain, (![A_211]: (m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_211)))) | ~m1_pre_topc('#skF_4', A_211) | ~l1_pre_topc(A_211))), inference(resolution, [status(thm)], [c_1599, c_34])).
% 12.04/5.31  tff(c_951, plain, (![C_155, A_156, B_157]: (v3_pre_topc(C_155, A_156) | ~r2_hidden(C_155, B_157) | ~m1_subset_1(C_155, k1_zfmisc_1(u1_struct_0(A_156))) | ~v1_tops_2(B_157, A_156) | ~m1_subset_1(B_157, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_156)))) | ~l1_pre_topc(A_156))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.04/5.31  tff(c_960, plain, (![A_63, A_156]: (v3_pre_topc('#skF_2'(A_63), A_156) | ~m1_subset_1('#skF_2'(A_63), k1_zfmisc_1(u1_struct_0(A_156))) | ~v1_tops_2(u1_pre_topc(A_63), A_156) | ~m1_subset_1(u1_pre_topc(A_63), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_156)))) | ~l1_pre_topc(A_156) | v3_tdlat_3(A_63) | ~l1_pre_topc(A_63))), inference(resolution, [status(thm)], [c_48, c_951])).
% 12.04/5.31  tff(c_1661, plain, (![A_211]: (v3_pre_topc('#skF_2'('#skF_4'), A_211) | ~m1_subset_1('#skF_2'('#skF_4'), k1_zfmisc_1(u1_struct_0(A_211))) | ~v1_tops_2(u1_pre_topc('#skF_4'), A_211) | v3_tdlat_3('#skF_4') | ~l1_pre_topc('#skF_4') | ~m1_pre_topc('#skF_4', A_211) | ~l1_pre_topc(A_211))), inference(resolution, [status(thm)], [c_1658, c_960])).
% 12.04/5.31  tff(c_1678, plain, (![A_211]: (v3_pre_topc('#skF_2'('#skF_4'), A_211) | ~m1_subset_1('#skF_2'('#skF_4'), k1_zfmisc_1(u1_struct_0(A_211))) | ~v1_tops_2(u1_pre_topc('#skF_4'), A_211) | v3_tdlat_3('#skF_4') | ~m1_pre_topc('#skF_4', A_211) | ~l1_pre_topc(A_211))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1661])).
% 12.04/5.31  tff(c_1719, plain, (![A_213]: (v3_pre_topc('#skF_2'('#skF_4'), A_213) | ~m1_subset_1('#skF_2'('#skF_4'), k1_zfmisc_1(u1_struct_0(A_213))) | ~v1_tops_2(u1_pre_topc('#skF_4'), A_213) | ~m1_pre_topc('#skF_4', A_213) | ~l1_pre_topc(A_213))), inference(negUnitSimplification, [status(thm)], [c_52, c_1678])).
% 12.04/5.31  tff(c_1763, plain, (v3_pre_topc('#skF_2'('#skF_4'), '#skF_3') | ~m1_subset_1('#skF_2'('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v1_tops_2(u1_pre_topc('#skF_4'), '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_261, c_1719])).
% 12.04/5.31  tff(c_1800, plain, (v3_pre_topc('#skF_2'('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_262, c_785, c_1040, c_1763])).
% 12.04/5.31  tff(c_1802, plain, $false, inference(negUnitSimplification, [status(thm)], [c_520, c_1800])).
% 12.04/5.31  tff(c_1804, plain, (~v1_tops_2(u1_pre_topc('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_777])).
% 12.04/5.31  tff(c_2910, plain, (![A_297]: (r2_hidden('#skF_1'('#skF_4', u1_pre_topc(A_297)), u1_pre_topc(A_297)) | v1_tops_2(u1_pre_topc(A_297), '#skF_4') | ~m1_pre_topc(A_297, '#skF_3') | ~l1_pre_topc(A_297))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_712])).
% 12.04/5.31  tff(c_2940, plain, (![A_298]: (v3_pre_topc('#skF_1'('#skF_4', u1_pre_topc(A_298)), A_298) | v1_tops_2(u1_pre_topc(A_298), '#skF_4') | ~m1_pre_topc(A_298, '#skF_3') | ~l1_pre_topc(A_298))), inference(resolution, [status(thm)], [c_2910, c_200])).
% 12.04/5.31  tff(c_2943, plain, (~m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | v1_tops_2(u1_pre_topc('#skF_4'), '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_2940, c_28])).
% 12.04/5.31  tff(c_2946, plain, (~m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | v1_tops_2(u1_pre_topc('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_262, c_2943])).
% 12.04/5.31  tff(c_2997, plain, (~m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(splitLeft, [status(thm)], [c_2946])).
% 12.04/5.31  tff(c_3000, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_684, c_2997])).
% 12.04/5.31  tff(c_3010, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_262, c_3000])).
% 12.04/5.31  tff(c_3011, plain, (v1_tops_2(u1_pre_topc('#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_2946])).
% 12.04/5.31  tff(c_3949, plain, (![C_344, A_345]: (m1_subset_1(C_344, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_345)))) | ~m1_subset_1(C_344, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~m1_pre_topc('#skF_3', A_345) | ~l1_pre_topc(A_345))), inference(superposition, [status(thm), theory('equality')], [c_261, c_576])).
% 12.04/5.31  tff(c_3967, plain, (![A_345]: (m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_345)))) | ~m1_pre_topc('#skF_3', A_345) | ~l1_pre_topc(A_345) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_16, c_3949])).
% 12.04/5.31  tff(c_3982, plain, (![A_345]: (m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_345)))) | ~m1_pre_topc('#skF_3', A_345) | ~l1_pre_topc(A_345))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_3967])).
% 12.04/5.31  tff(c_584, plain, (![A_12, A_130]: (m1_subset_1(u1_pre_topc(A_12), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_130)))) | ~m1_pre_topc(A_12, A_130) | ~l1_pre_topc(A_130) | ~l1_pre_topc(A_12))), inference(resolution, [status(thm)], [c_16, c_576])).
% 12.04/5.31  tff(c_2078, plain, (![D_229, C_230, A_231]: (v1_tops_2(D_229, C_230) | ~m1_subset_1(D_229, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_230)))) | ~v1_tops_2(D_229, A_231) | ~m1_pre_topc(C_230, A_231) | ~m1_subset_1(D_229, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_231)))) | ~l1_pre_topc(A_231))), inference(cnfTransformation, [status(thm)], [f_124])).
% 12.04/5.31  tff(c_5225, plain, (![A_406, A_407, A_408]: (v1_tops_2(u1_pre_topc(A_406), A_407) | ~v1_tops_2(u1_pre_topc(A_406), A_408) | ~m1_pre_topc(A_407, A_408) | ~m1_subset_1(u1_pre_topc(A_406), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_408)))) | ~l1_pre_topc(A_408) | ~m1_pre_topc(A_406, A_407) | ~l1_pre_topc(A_407) | ~l1_pre_topc(A_406))), inference(resolution, [status(thm)], [c_584, c_2078])).
% 12.04/5.31  tff(c_5235, plain, (![A_406]: (v1_tops_2(u1_pre_topc(A_406), '#skF_3') | ~v1_tops_2(u1_pre_topc(A_406), '#skF_4') | ~m1_subset_1(u1_pre_topc(A_406), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~l1_pre_topc('#skF_4') | ~m1_pre_topc(A_406, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_406))), inference(resolution, [status(thm)], [c_186, c_5225])).
% 12.04/5.31  tff(c_6884, plain, (![A_509]: (v1_tops_2(u1_pre_topc(A_509), '#skF_3') | ~v1_tops_2(u1_pre_topc(A_509), '#skF_4') | ~m1_subset_1(u1_pre_topc(A_509), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~m1_pre_topc(A_509, '#skF_3') | ~l1_pre_topc(A_509))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_5235])).
% 12.04/5.31  tff(c_6908, plain, (v1_tops_2(u1_pre_topc('#skF_4'), '#skF_3') | ~v1_tops_2(u1_pre_topc('#skF_4'), '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_3982, c_6884])).
% 12.04/5.31  tff(c_6958, plain, (v1_tops_2(u1_pre_topc('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_186, c_262, c_3011, c_6908])).
% 12.04/5.31  tff(c_6960, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1804, c_6958])).
% 12.04/5.31  tff(c_6961, plain, (r2_hidden('#skF_2'('#skF_4'), u1_pre_topc('#skF_3'))), inference(splitRight, [status(thm)], [c_519])).
% 12.04/5.31  tff(c_346, plain, (![A_80]: (m1_subset_1(A_80, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r2_hidden(A_80, u1_pre_topc('#skF_3')) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_261, c_94])).
% 12.04/5.31  tff(c_415, plain, (![A_117]: (m1_subset_1(A_117, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r2_hidden(A_117, u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_346])).
% 12.04/5.31  tff(c_420, plain, (![A_117]: (r2_hidden(A_117, u1_pre_topc('#skF_4')) | ~v3_pre_topc(A_117, '#skF_4') | ~l1_pre_topc('#skF_4') | ~r2_hidden(A_117, u1_pre_topc('#skF_3')))), inference(resolution, [status(thm)], [c_415, c_12])).
% 12.04/5.31  tff(c_426, plain, (![A_117]: (r2_hidden(A_117, u1_pre_topc('#skF_4')) | ~v3_pre_topc(A_117, '#skF_4') | ~r2_hidden(A_117, u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_420])).
% 12.04/5.31  tff(c_6982, plain, (r2_hidden('#skF_2'('#skF_4'), u1_pre_topc('#skF_4')) | ~v3_pre_topc('#skF_2'('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_6961, c_426])).
% 12.04/5.31  tff(c_6988, plain, (~v3_pre_topc('#skF_2'('#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_6982])).
% 12.04/5.31  tff(c_6991, plain, (v3_tdlat_3('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_206, c_6988])).
% 12.04/5.31  tff(c_6994, plain, (v3_tdlat_3('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_6991])).
% 12.04/5.31  tff(c_6996, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_6994])).
% 12.04/5.31  tff(c_6997, plain, (r2_hidden('#skF_2'('#skF_4'), u1_pre_topc('#skF_4'))), inference(splitRight, [status(thm)], [c_6982])).
% 12.04/5.31  tff(c_6963, plain, (![C_510, A_511, B_512]: (m1_subset_1(C_510, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_511)))) | ~m1_subset_1(C_510, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_512)))) | ~m1_pre_topc(B_512, A_511) | ~l1_pre_topc(A_511))), inference(cnfTransformation, [status(thm)], [f_107])).
% 12.04/5.31  tff(c_7230, plain, (![A_525, A_526]: (m1_subset_1(u1_pre_topc(A_525), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_526)))) | ~m1_pre_topc(A_525, A_526) | ~l1_pre_topc(A_526) | ~l1_pre_topc(A_525))), inference(resolution, [status(thm)], [c_16, c_6963])).
% 12.04/5.31  tff(c_7239, plain, (![A_525]: (m1_subset_1(u1_pre_topc(A_525), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~m1_pre_topc(A_525, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_525))), inference(superposition, [status(thm), theory('equality')], [c_261, c_7230])).
% 12.04/5.31  tff(c_7245, plain, (![A_527]: (m1_subset_1(u1_pre_topc(A_527), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~m1_pre_topc(A_527, '#skF_3') | ~l1_pre_topc(A_527))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_7239])).
% 12.04/5.31  tff(c_8, plain, (![A_3, C_5, B_4]: (m1_subset_1(A_3, C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.04/5.31  tff(c_7371, plain, (![A_534, A_535]: (m1_subset_1(A_534, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r2_hidden(A_534, u1_pre_topc(A_535)) | ~m1_pre_topc(A_535, '#skF_3') | ~l1_pre_topc(A_535))), inference(resolution, [status(thm)], [c_7245, c_8])).
% 12.04/5.31  tff(c_7377, plain, (m1_subset_1('#skF_2'('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6997, c_7371])).
% 12.04/5.31  tff(c_7388, plain, (m1_subset_1('#skF_2'('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_262, c_7377])).
% 12.04/5.31  tff(c_54, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_162])).
% 12.04/5.31  tff(c_396, plain, (r2_hidden('#skF_1'('#skF_4', u1_pre_topc('#skF_3')), u1_pre_topc('#skF_3')) | v1_tops_2(u1_pre_topc('#skF_3'), '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_382, c_30])).
% 12.04/5.31  tff(c_401, plain, (r2_hidden('#skF_1'('#skF_4', u1_pre_topc('#skF_3')), u1_pre_topc('#skF_3')) | v1_tops_2(u1_pre_topc('#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_396])).
% 12.04/5.31  tff(c_448, plain, (v1_tops_2(u1_pre_topc('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_401])).
% 12.04/5.31  tff(c_44, plain, (![A_63, B_66]: (r2_hidden(k6_subset_1(u1_struct_0(A_63), B_66), u1_pre_topc(A_63)) | ~r2_hidden(B_66, u1_pre_topc(A_63)) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_63))) | ~v3_tdlat_3(A_63) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_150])).
% 12.04/5.31  tff(c_8055, plain, (![A_581, A_582, A_583]: (m1_subset_1(A_581, k1_zfmisc_1(u1_struct_0(A_582))) | ~r2_hidden(A_581, u1_pre_topc(A_583)) | ~m1_pre_topc(A_583, A_582) | ~l1_pre_topc(A_582) | ~l1_pre_topc(A_583))), inference(resolution, [status(thm)], [c_7230, c_8])).
% 12.04/5.31  tff(c_12665, plain, (![A_830, B_831, A_832]: (m1_subset_1(k6_subset_1(u1_struct_0(A_830), B_831), k1_zfmisc_1(u1_struct_0(A_832))) | ~m1_pre_topc(A_830, A_832) | ~l1_pre_topc(A_832) | ~r2_hidden(B_831, u1_pre_topc(A_830)) | ~m1_subset_1(B_831, k1_zfmisc_1(u1_struct_0(A_830))) | ~v3_tdlat_3(A_830) | ~l1_pre_topc(A_830))), inference(resolution, [status(thm)], [c_44, c_8055])).
% 12.04/5.31  tff(c_7257, plain, (![C_528, A_529, B_530]: (v3_pre_topc(C_528, A_529) | ~r2_hidden(C_528, B_530) | ~m1_subset_1(C_528, k1_zfmisc_1(u1_struct_0(A_529))) | ~v1_tops_2(B_530, A_529) | ~m1_subset_1(B_530, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_529)))) | ~l1_pre_topc(A_529))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.04/5.31  tff(c_7268, plain, (![A_63, B_66, A_529]: (v3_pre_topc(k6_subset_1(u1_struct_0(A_63), B_66), A_529) | ~m1_subset_1(k6_subset_1(u1_struct_0(A_63), B_66), k1_zfmisc_1(u1_struct_0(A_529))) | ~v1_tops_2(u1_pre_topc(A_63), A_529) | ~m1_subset_1(u1_pre_topc(A_63), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_529)))) | ~l1_pre_topc(A_529) | ~r2_hidden(B_66, u1_pre_topc(A_63)) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_63))) | ~v3_tdlat_3(A_63) | ~l1_pre_topc(A_63))), inference(resolution, [status(thm)], [c_44, c_7257])).
% 12.04/5.31  tff(c_20567, plain, (![A_1216, B_1217, A_1218]: (v3_pre_topc(k6_subset_1(u1_struct_0(A_1216), B_1217), A_1218) | ~v1_tops_2(u1_pre_topc(A_1216), A_1218) | ~m1_subset_1(u1_pre_topc(A_1216), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1218)))) | ~m1_pre_topc(A_1216, A_1218) | ~l1_pre_topc(A_1218) | ~r2_hidden(B_1217, u1_pre_topc(A_1216)) | ~m1_subset_1(B_1217, k1_zfmisc_1(u1_struct_0(A_1216))) | ~v3_tdlat_3(A_1216) | ~l1_pre_topc(A_1216))), inference(resolution, [status(thm)], [c_12665, c_7268])).
% 12.04/5.31  tff(c_20615, plain, (![B_1217]: (v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'), B_1217), '#skF_4') | ~v1_tops_2(u1_pre_topc('#skF_3'), '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~r2_hidden(B_1217, u1_pre_topc('#skF_3')) | ~m1_subset_1(B_1217, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_382, c_20567])).
% 12.04/5.31  tff(c_20675, plain, (![B_1219]: (v3_pre_topc(k6_subset_1(u1_struct_0('#skF_4'), B_1219), '#skF_4') | ~r2_hidden(B_1219, u1_pre_topc('#skF_3')) | ~m1_subset_1(B_1219, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_54, c_261, c_58, c_186, c_448, c_261, c_20615])).
% 12.04/5.31  tff(c_7110, plain, (![A_518, B_519]: (r2_hidden(k6_subset_1(u1_struct_0(A_518), B_519), u1_pre_topc(A_518)) | ~r2_hidden(B_519, u1_pre_topc(A_518)) | ~m1_subset_1(B_519, k1_zfmisc_1(u1_struct_0(A_518))) | ~v3_tdlat_3(A_518) | ~l1_pre_topc(A_518))), inference(cnfTransformation, [status(thm)], [f_150])).
% 12.04/5.31  tff(c_7114, plain, (![B_519]: (r2_hidden(k6_subset_1(u1_struct_0('#skF_3'), B_519), u1_pre_topc('#skF_4')) | ~v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'), B_519), '#skF_4') | ~r2_hidden(B_519, u1_pre_topc('#skF_3')) | ~m1_subset_1(B_519, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_7110, c_426])).
% 12.04/5.31  tff(c_15661, plain, (![B_954]: (r2_hidden(k6_subset_1(u1_struct_0('#skF_4'), B_954), u1_pre_topc('#skF_4')) | ~v3_pre_topc(k6_subset_1(u1_struct_0('#skF_4'), B_954), '#skF_4') | ~r2_hidden(B_954, u1_pre_topc('#skF_3')) | ~m1_subset_1(B_954, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_54, c_261, c_261, c_261, c_7114])).
% 12.04/5.31  tff(c_46, plain, (![A_63]: (~r2_hidden(k6_subset_1(u1_struct_0(A_63), '#skF_2'(A_63)), u1_pre_topc(A_63)) | v3_tdlat_3(A_63) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_150])).
% 12.04/5.31  tff(c_15702, plain, (v3_tdlat_3('#skF_4') | ~l1_pre_topc('#skF_4') | ~v3_pre_topc(k6_subset_1(u1_struct_0('#skF_4'), '#skF_2'('#skF_4')), '#skF_4') | ~r2_hidden('#skF_2'('#skF_4'), u1_pre_topc('#skF_3')) | ~m1_subset_1('#skF_2'('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_15661, c_46])).
% 12.04/5.31  tff(c_15739, plain, (v3_tdlat_3('#skF_4') | ~v3_pre_topc(k6_subset_1(u1_struct_0('#skF_4'), '#skF_2'('#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7388, c_6961, c_58, c_15702])).
% 12.04/5.31  tff(c_15740, plain, (~v3_pre_topc(k6_subset_1(u1_struct_0('#skF_4'), '#skF_2'('#skF_4')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_52, c_15739])).
% 12.04/5.31  tff(c_20678, plain, (~r2_hidden('#skF_2'('#skF_4'), u1_pre_topc('#skF_3')) | ~m1_subset_1('#skF_2'('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_20675, c_15740])).
% 12.04/5.31  tff(c_20682, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7388, c_6961, c_20678])).
% 12.04/5.31  tff(c_20684, plain, (~v1_tops_2(u1_pre_topc('#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_401])).
% 12.04/5.31  tff(c_22447, plain, (![D_1338, C_1339, A_1340]: (v1_tops_2(D_1338, C_1339) | ~m1_subset_1(D_1338, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_1339)))) | ~v1_tops_2(D_1338, A_1340) | ~m1_pre_topc(C_1339, A_1340) | ~m1_subset_1(D_1338, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1340)))) | ~l1_pre_topc(A_1340))), inference(cnfTransformation, [status(thm)], [f_124])).
% 12.04/5.31  tff(c_22455, plain, (![A_1340]: (v1_tops_2(u1_pre_topc('#skF_3'), '#skF_4') | ~v1_tops_2(u1_pre_topc('#skF_3'), A_1340) | ~m1_pre_topc('#skF_4', A_1340) | ~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1340)))) | ~l1_pre_topc(A_1340))), inference(resolution, [status(thm)], [c_382, c_22447])).
% 12.04/5.31  tff(c_23273, plain, (![A_1405]: (~v1_tops_2(u1_pre_topc('#skF_3'), A_1405) | ~m1_pre_topc('#skF_4', A_1405) | ~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1405)))) | ~l1_pre_topc(A_1405))), inference(negUnitSimplification, [status(thm)], [c_20684, c_22455])).
% 12.04/5.31  tff(c_23290, plain, (~v1_tops_2(u1_pre_topc('#skF_3'), '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_261, c_23273])).
% 12.04/5.31  tff(c_23307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_382, c_262, c_21010, c_23290])).
% 12.04/5.31  tff(c_23309, plain, (~v1_tops_2(u1_pre_topc('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_21006])).
% 12.04/5.31  tff(c_23312, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_23309])).
% 12.04/5.31  tff(c_23316, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_23312])).
% 12.04/5.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.04/5.31  
% 12.04/5.31  Inference rules
% 12.04/5.31  ----------------------
% 12.04/5.31  #Ref     : 0
% 12.04/5.31  #Sup     : 5024
% 12.04/5.31  #Fact    : 0
% 12.04/5.31  #Define  : 0
% 12.04/5.31  #Split   : 57
% 12.04/5.31  #Chain   : 0
% 12.04/5.31  #Close   : 0
% 12.04/5.31  
% 12.04/5.31  Ordering : KBO
% 12.04/5.31  
% 12.04/5.31  Simplification rules
% 12.04/5.31  ----------------------
% 12.04/5.31  #Subsume      : 1759
% 12.04/5.31  #Demod        : 6022
% 12.04/5.31  #Tautology    : 762
% 12.04/5.31  #SimpNegUnit  : 170
% 12.04/5.31  #BackRed      : 2
% 12.04/5.31  
% 12.04/5.31  #Partial instantiations: 0
% 12.04/5.31  #Strategies tried      : 1
% 12.04/5.31  
% 12.04/5.31  Timing (in seconds)
% 12.04/5.31  ----------------------
% 12.04/5.31  Preprocessing        : 0.34
% 12.04/5.31  Parsing              : 0.19
% 12.04/5.31  CNF conversion       : 0.03
% 12.04/5.31  Main loop            : 4.18
% 12.04/5.31  Inferencing          : 1.18
% 12.04/5.31  Reduction            : 1.18
% 12.04/5.31  Demodulation         : 0.80
% 12.04/5.31  BG Simplification    : 0.08
% 12.04/5.31  Subsumption          : 1.48
% 12.04/5.31  Abstraction          : 0.14
% 12.35/5.31  MUC search           : 0.00
% 12.35/5.31  Cooper               : 0.00
% 12.35/5.31  Total                : 4.58
% 12.35/5.31  Index Insertion      : 0.00
% 12.35/5.31  Index Deletion       : 0.00
% 12.35/5.31  Index Matching       : 0.00
% 12.35/5.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
