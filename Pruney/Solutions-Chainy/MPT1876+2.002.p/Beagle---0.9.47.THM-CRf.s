%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:50 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 491 expanded)
%              Number of leaves         :   34 ( 178 expanded)
%              Depth                    :   14
%              Number of atoms          :  277 (1591 expanded)
%              Number of equality atoms :    8 (  66 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_182,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v2_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v2_tex_2(B,A)
            <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v2_struct_0(A)
        & l1_struct_0(A) )
     => v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_67,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ( ~ v2_struct_0(A)
          & v7_struct_0(A)
          & v2_pre_topc(A) )
       => ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & v2_tdlat_3(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tex_1)).

tff(f_162,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v2_tex_2(C,A)
                <=> v1_tdlat_3(B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

tff(f_128,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & v2_tdlat_3(A) )
       => ( ~ v2_struct_0(A)
          & v7_struct_0(A)
          & v2_pre_topc(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_142,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_tdlat_3(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_tdlat_3)).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_359,plain,(
    ! [A_78,B_79] :
      ( m1_pre_topc(k1_pre_topc(A_78,B_79),A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_363,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_359])).

tff(c_366,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_363])).

tff(c_10,plain,(
    ! [B_9,A_7] :
      ( l1_pre_topc(B_9)
      | ~ m1_pre_topc(B_9,A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_372,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_366,c_10])).

tff(c_378,plain,(
    l1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_372])).

tff(c_8,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_93,plain,(
    ! [A_45,B_46] :
      ( m1_pre_topc(k1_pre_topc(A_45,B_46),A_45)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_95,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_93])).

tff(c_98,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_95])).

tff(c_104,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_98,c_10])).

tff(c_110,plain,(
    l1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_104])).

tff(c_62,plain,
    ( v2_tex_2('#skF_2','#skF_1')
    | v1_zfmisc_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_64,plain,(
    v1_zfmisc_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_56,plain,
    ( ~ v1_zfmisc_1('#skF_2')
    | ~ v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_66,plain,(
    ~ v2_tex_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_56])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_120,plain,(
    ! [A_48,B_49] :
      ( u1_struct_0(k1_pre_topc(A_48,B_49)) = B_49
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_123,plain,
    ( u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2'
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_120])).

tff(c_126,plain,(
    u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_123])).

tff(c_12,plain,(
    ! [A_10] :
      ( v1_xboole_0(u1_struct_0(A_10))
      | ~ l1_struct_0(A_10)
      | ~ v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_141,plain,
    ( v1_xboole_0('#skF_2')
    | ~ l1_struct_0(k1_pre_topc('#skF_1','#skF_2'))
    | ~ v2_struct_0(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_12])).

tff(c_154,plain,
    ( ~ l1_struct_0(k1_pre_topc('#skF_1','#skF_2'))
    | ~ v2_struct_0(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_141])).

tff(c_158,plain,(
    ~ v2_struct_0(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_52,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v2_pre_topc(B_3)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_101,plain,
    ( v2_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_98,c_2])).

tff(c_107,plain,(
    v2_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_101])).

tff(c_14,plain,(
    ! [A_11] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_11))
      | ~ l1_struct_0(A_11)
      | v7_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_144,plain,
    ( ~ v1_zfmisc_1('#skF_2')
    | ~ l1_struct_0(k1_pre_topc('#skF_1','#skF_2'))
    | v7_struct_0(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_14])).

tff(c_156,plain,
    ( ~ l1_struct_0(k1_pre_topc('#skF_1','#skF_2'))
    | v7_struct_0(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_144])).

tff(c_159,plain,(
    ~ l1_struct_0(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_162,plain,(
    ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_8,c_159])).

tff(c_166,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_162])).

tff(c_167,plain,(
    v7_struct_0(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_24,plain,(
    ! [A_17] :
      ( v1_tdlat_3(A_17)
      | ~ v2_pre_topc(A_17)
      | ~ v7_struct_0(A_17)
      | v2_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_174,plain,
    ( v1_tdlat_3(k1_pre_topc('#skF_1','#skF_2'))
    | ~ v2_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
    | v2_struct_0(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_167,c_24])).

tff(c_181,plain,
    ( v1_tdlat_3(k1_pre_topc('#skF_1','#skF_2'))
    | v2_struct_0(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_107,c_174])).

tff(c_182,plain,(
    v1_tdlat_3(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_158,c_181])).

tff(c_257,plain,(
    ! [B_60,A_61] :
      ( v2_tex_2(u1_struct_0(B_60),A_61)
      | ~ v1_tdlat_3(B_60)
      | ~ m1_subset_1(u1_struct_0(B_60),k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ m1_pre_topc(B_60,A_61)
      | v2_struct_0(B_60)
      | ~ l1_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_266,plain,(
    ! [A_61] :
      ( v2_tex_2(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),A_61)
      | ~ v1_tdlat_3(k1_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_61)
      | v2_struct_0(k1_pre_topc('#skF_1','#skF_2'))
      | ~ l1_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_257])).

tff(c_271,plain,(
    ! [A_61] :
      ( v2_tex_2('#skF_2',A_61)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_61)
      | v2_struct_0(k1_pre_topc('#skF_1','#skF_2'))
      | ~ l1_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_126,c_266])).

tff(c_276,plain,(
    ! [A_62] :
      ( v2_tex_2('#skF_2',A_62)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_62)
      | ~ l1_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(negUnitSimplification,[status(thm)],[c_158,c_271])).

tff(c_285,plain,
    ( v2_tex_2('#skF_2','#skF_1')
    | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_276])).

tff(c_291,plain,
    ( v2_tex_2('#skF_2','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_98,c_285])).

tff(c_293,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_66,c_291])).

tff(c_294,plain,(
    ~ l1_struct_0(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_298,plain,(
    ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_8,c_294])).

tff(c_302,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_298])).

tff(c_303,plain,(
    v2_tex_2('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_331,plain,(
    ! [A_76,B_77] :
      ( u1_struct_0(k1_pre_topc(A_76,B_77)) = B_77
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_334,plain,
    ( u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2'
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_331])).

tff(c_337,plain,(
    u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_334])).

tff(c_350,plain,
    ( v1_xboole_0('#skF_2')
    | ~ l1_struct_0(k1_pre_topc('#skF_1','#skF_2'))
    | ~ v2_struct_0(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_12])).

tff(c_357,plain,
    ( ~ l1_struct_0(k1_pre_topc('#skF_1','#skF_2'))
    | ~ v2_struct_0(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_350])).

tff(c_379,plain,(
    ~ v2_struct_0(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_357])).

tff(c_369,plain,
    ( v2_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_366,c_2])).

tff(c_375,plain,(
    v2_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_369])).

tff(c_381,plain,(
    ! [A_80] :
      ( v7_struct_0(A_80)
      | ~ v2_tdlat_3(A_80)
      | ~ v1_tdlat_3(A_80)
      | ~ v2_pre_topc(A_80)
      | v2_struct_0(A_80)
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_304,plain,(
    ~ v1_zfmisc_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_16,plain,(
    ! [A_12] :
      ( v1_zfmisc_1(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12)
      | ~ v7_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_347,plain,
    ( v1_zfmisc_1('#skF_2')
    | ~ l1_struct_0(k1_pre_topc('#skF_1','#skF_2'))
    | ~ v7_struct_0(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_16])).

tff(c_356,plain,
    ( ~ l1_struct_0(k1_pre_topc('#skF_1','#skF_2'))
    | ~ v7_struct_0(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_304,c_347])).

tff(c_380,plain,(
    ~ v7_struct_0(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_356])).

tff(c_384,plain,
    ( ~ v2_tdlat_3(k1_pre_topc('#skF_1','#skF_2'))
    | ~ v1_tdlat_3(k1_pre_topc('#skF_1','#skF_2'))
    | ~ v2_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
    | v2_struct_0(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_381,c_380])).

tff(c_393,plain,
    ( ~ v2_tdlat_3(k1_pre_topc('#skF_1','#skF_2'))
    | ~ v1_tdlat_3(k1_pre_topc('#skF_1','#skF_2'))
    | v2_struct_0(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_375,c_384])).

tff(c_394,plain,
    ( ~ v2_tdlat_3(k1_pre_topc('#skF_1','#skF_2'))
    | ~ v1_tdlat_3(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_379,c_393])).

tff(c_397,plain,(
    ~ v1_tdlat_3(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_394])).

tff(c_522,plain,(
    ! [B_96,A_97] :
      ( v1_tdlat_3(B_96)
      | ~ v2_tex_2(u1_struct_0(B_96),A_97)
      | ~ m1_subset_1(u1_struct_0(B_96),k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ m1_pre_topc(B_96,A_97)
      | v2_struct_0(B_96)
      | ~ l1_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_531,plain,(
    ! [A_97] :
      ( v1_tdlat_3(k1_pre_topc('#skF_1','#skF_2'))
      | ~ v2_tex_2(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),A_97)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_97)
      | v2_struct_0(k1_pre_topc('#skF_1','#skF_2'))
      | ~ l1_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_522])).

tff(c_535,plain,(
    ! [A_97] :
      ( v1_tdlat_3(k1_pre_topc('#skF_1','#skF_2'))
      | ~ v2_tex_2('#skF_2',A_97)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_97)
      | v2_struct_0(k1_pre_topc('#skF_1','#skF_2'))
      | ~ l1_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_531])).

tff(c_540,plain,(
    ! [A_98] :
      ( ~ v2_tex_2('#skF_2',A_98)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_98)
      | ~ l1_pre_topc(A_98)
      | v2_struct_0(A_98) ) ),
    inference(negUnitSimplification,[status(thm)],[c_379,c_397,c_535])).

tff(c_549,plain,
    ( ~ v2_tex_2('#skF_2','#skF_1')
    | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_540])).

tff(c_555,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_366,c_303,c_549])).

tff(c_557,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_555])).

tff(c_558,plain,(
    ~ v2_tdlat_3(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_394])).

tff(c_50,plain,(
    v2_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_560,plain,(
    ! [B_99,A_100] :
      ( v2_tdlat_3(B_99)
      | ~ m1_pre_topc(B_99,A_100)
      | ~ l1_pre_topc(A_100)
      | ~ v2_tdlat_3(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_563,plain,
    ( v2_tdlat_3(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_tdlat_3('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_366,c_560])).

tff(c_566,plain,
    ( v2_tdlat_3(k1_pre_topc('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_563])).

tff(c_568,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_558,c_566])).

tff(c_569,plain,(
    ~ l1_struct_0(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_356])).

tff(c_582,plain,(
    ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_8,c_569])).

tff(c_586,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_582])).

tff(c_587,plain,(
    ~ l1_struct_0(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_357])).

tff(c_591,plain,(
    ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_8,c_587])).

tff(c_595,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_591])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:00:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.39  
% 2.65/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.40  %$ v2_tex_2 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.65/1.40  
% 2.65/1.40  %Foreground sorts:
% 2.65/1.40  
% 2.65/1.40  
% 2.65/1.40  %Background operators:
% 2.65/1.40  
% 2.65/1.40  
% 2.65/1.40  %Foreground operators:
% 2.65/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.65/1.40  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 2.65/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.40  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.65/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.65/1.40  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.65/1.40  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.65/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.65/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.65/1.40  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.65/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.65/1.40  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.65/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.40  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.65/1.40  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.65/1.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.65/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.65/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.65/1.40  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 2.65/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.65/1.40  
% 2.96/1.42  tff(f_182, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 2.96/1.42  tff(f_42, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 2.96/1.42  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.96/1.42  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.96/1.42  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_pre_topc)).
% 2.96/1.42  tff(f_59, axiom, (![A]: ((v2_struct_0(A) & l1_struct_0(A)) => v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_struct_0)).
% 2.96/1.42  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 2.96/1.42  tff(f_67, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_struct_0)).
% 2.96/1.42  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (((~v2_struct_0(A) & v7_struct_0(A)) & v2_pre_topc(A)) => (((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & v2_tdlat_3(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tex_1)).
% 2.96/1.42  tff(f_162, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_tex_2)).
% 2.96/1.42  tff(f_128, axiom, (![A]: (l1_pre_topc(A) => ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & v2_tdlat_3(A)) => ((~v2_struct_0(A) & v7_struct_0(A)) & v2_pre_topc(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_1)).
% 2.96/1.42  tff(f_73, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 2.96/1.42  tff(f_142, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_tdlat_3(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_tdlat_3)).
% 2.96/1.42  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.96/1.42  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.96/1.42  tff(c_359, plain, (![A_78, B_79]: (m1_pre_topc(k1_pre_topc(A_78, B_79), A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.96/1.42  tff(c_363, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_359])).
% 2.96/1.42  tff(c_366, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_363])).
% 2.96/1.42  tff(c_10, plain, (![B_9, A_7]: (l1_pre_topc(B_9) | ~m1_pre_topc(B_9, A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.96/1.42  tff(c_372, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_366, c_10])).
% 2.96/1.42  tff(c_378, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_372])).
% 2.96/1.42  tff(c_8, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.96/1.42  tff(c_54, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.96/1.42  tff(c_93, plain, (![A_45, B_46]: (m1_pre_topc(k1_pre_topc(A_45, B_46), A_45) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.96/1.42  tff(c_95, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_93])).
% 2.96/1.42  tff(c_98, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_95])).
% 2.96/1.42  tff(c_104, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_98, c_10])).
% 2.96/1.42  tff(c_110, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_104])).
% 2.96/1.42  tff(c_62, plain, (v2_tex_2('#skF_2', '#skF_1') | v1_zfmisc_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.96/1.42  tff(c_64, plain, (v1_zfmisc_1('#skF_2')), inference(splitLeft, [status(thm)], [c_62])).
% 2.96/1.42  tff(c_56, plain, (~v1_zfmisc_1('#skF_2') | ~v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.96/1.42  tff(c_66, plain, (~v2_tex_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_56])).
% 2.96/1.42  tff(c_46, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.96/1.42  tff(c_120, plain, (![A_48, B_49]: (u1_struct_0(k1_pre_topc(A_48, B_49))=B_49 | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.96/1.42  tff(c_123, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2' | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_120])).
% 2.96/1.42  tff(c_126, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_123])).
% 2.96/1.42  tff(c_12, plain, (![A_10]: (v1_xboole_0(u1_struct_0(A_10)) | ~l1_struct_0(A_10) | ~v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.96/1.42  tff(c_141, plain, (v1_xboole_0('#skF_2') | ~l1_struct_0(k1_pre_topc('#skF_1', '#skF_2')) | ~v2_struct_0(k1_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_126, c_12])).
% 2.96/1.42  tff(c_154, plain, (~l1_struct_0(k1_pre_topc('#skF_1', '#skF_2')) | ~v2_struct_0(k1_pre_topc('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_46, c_141])).
% 2.96/1.42  tff(c_158, plain, (~v2_struct_0(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_154])).
% 2.96/1.42  tff(c_52, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.96/1.42  tff(c_2, plain, (![B_3, A_1]: (v2_pre_topc(B_3) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.96/1.42  tff(c_101, plain, (v2_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_98, c_2])).
% 2.96/1.42  tff(c_107, plain, (v2_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_101])).
% 2.96/1.42  tff(c_14, plain, (![A_11]: (~v1_zfmisc_1(u1_struct_0(A_11)) | ~l1_struct_0(A_11) | v7_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.96/1.42  tff(c_144, plain, (~v1_zfmisc_1('#skF_2') | ~l1_struct_0(k1_pre_topc('#skF_1', '#skF_2')) | v7_struct_0(k1_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_126, c_14])).
% 2.96/1.42  tff(c_156, plain, (~l1_struct_0(k1_pre_topc('#skF_1', '#skF_2')) | v7_struct_0(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_144])).
% 2.96/1.42  tff(c_159, plain, (~l1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_156])).
% 2.96/1.42  tff(c_162, plain, (~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_8, c_159])).
% 2.96/1.42  tff(c_166, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_162])).
% 2.96/1.42  tff(c_167, plain, (v7_struct_0(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_156])).
% 2.96/1.42  tff(c_24, plain, (![A_17]: (v1_tdlat_3(A_17) | ~v2_pre_topc(A_17) | ~v7_struct_0(A_17) | v2_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.96/1.42  tff(c_174, plain, (v1_tdlat_3(k1_pre_topc('#skF_1', '#skF_2')) | ~v2_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | v2_struct_0(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_167, c_24])).
% 2.96/1.42  tff(c_181, plain, (v1_tdlat_3(k1_pre_topc('#skF_1', '#skF_2')) | v2_struct_0(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_107, c_174])).
% 2.96/1.42  tff(c_182, plain, (v1_tdlat_3(k1_pre_topc('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_158, c_181])).
% 2.96/1.42  tff(c_257, plain, (![B_60, A_61]: (v2_tex_2(u1_struct_0(B_60), A_61) | ~v1_tdlat_3(B_60) | ~m1_subset_1(u1_struct_0(B_60), k1_zfmisc_1(u1_struct_0(A_61))) | ~m1_pre_topc(B_60, A_61) | v2_struct_0(B_60) | ~l1_pre_topc(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_162])).
% 2.96/1.42  tff(c_266, plain, (![A_61]: (v2_tex_2(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), A_61) | ~v1_tdlat_3(k1_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_61))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_61) | v2_struct_0(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc(A_61) | v2_struct_0(A_61))), inference(superposition, [status(thm), theory('equality')], [c_126, c_257])).
% 2.96/1.42  tff(c_271, plain, (![A_61]: (v2_tex_2('#skF_2', A_61) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_61))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_61) | v2_struct_0(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc(A_61) | v2_struct_0(A_61))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_126, c_266])).
% 2.96/1.42  tff(c_276, plain, (![A_62]: (v2_tex_2('#skF_2', A_62) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_62))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_62) | ~l1_pre_topc(A_62) | v2_struct_0(A_62))), inference(negUnitSimplification, [status(thm)], [c_158, c_271])).
% 2.96/1.42  tff(c_285, plain, (v2_tex_2('#skF_2', '#skF_1') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_276])).
% 2.96/1.42  tff(c_291, plain, (v2_tex_2('#skF_2', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_98, c_285])).
% 2.96/1.42  tff(c_293, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_66, c_291])).
% 2.96/1.42  tff(c_294, plain, (~l1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_154])).
% 2.96/1.42  tff(c_298, plain, (~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_8, c_294])).
% 2.96/1.42  tff(c_302, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_298])).
% 2.96/1.42  tff(c_303, plain, (v2_tex_2('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_62])).
% 2.96/1.42  tff(c_331, plain, (![A_76, B_77]: (u1_struct_0(k1_pre_topc(A_76, B_77))=B_77 | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.96/1.42  tff(c_334, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2' | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_331])).
% 2.96/1.42  tff(c_337, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_334])).
% 2.96/1.42  tff(c_350, plain, (v1_xboole_0('#skF_2') | ~l1_struct_0(k1_pre_topc('#skF_1', '#skF_2')) | ~v2_struct_0(k1_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_337, c_12])).
% 2.96/1.42  tff(c_357, plain, (~l1_struct_0(k1_pre_topc('#skF_1', '#skF_2')) | ~v2_struct_0(k1_pre_topc('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_46, c_350])).
% 2.96/1.42  tff(c_379, plain, (~v2_struct_0(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_357])).
% 2.96/1.42  tff(c_369, plain, (v2_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_366, c_2])).
% 2.96/1.42  tff(c_375, plain, (v2_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_369])).
% 2.96/1.42  tff(c_381, plain, (![A_80]: (v7_struct_0(A_80) | ~v2_tdlat_3(A_80) | ~v1_tdlat_3(A_80) | ~v2_pre_topc(A_80) | v2_struct_0(A_80) | ~l1_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.96/1.42  tff(c_304, plain, (~v1_zfmisc_1('#skF_2')), inference(splitRight, [status(thm)], [c_62])).
% 2.96/1.42  tff(c_16, plain, (![A_12]: (v1_zfmisc_1(u1_struct_0(A_12)) | ~l1_struct_0(A_12) | ~v7_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.96/1.42  tff(c_347, plain, (v1_zfmisc_1('#skF_2') | ~l1_struct_0(k1_pre_topc('#skF_1', '#skF_2')) | ~v7_struct_0(k1_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_337, c_16])).
% 2.96/1.42  tff(c_356, plain, (~l1_struct_0(k1_pre_topc('#skF_1', '#skF_2')) | ~v7_struct_0(k1_pre_topc('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_304, c_347])).
% 2.96/1.42  tff(c_380, plain, (~v7_struct_0(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_356])).
% 2.96/1.42  tff(c_384, plain, (~v2_tdlat_3(k1_pre_topc('#skF_1', '#skF_2')) | ~v1_tdlat_3(k1_pre_topc('#skF_1', '#skF_2')) | ~v2_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | v2_struct_0(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_381, c_380])).
% 2.96/1.42  tff(c_393, plain, (~v2_tdlat_3(k1_pre_topc('#skF_1', '#skF_2')) | ~v1_tdlat_3(k1_pre_topc('#skF_1', '#skF_2')) | v2_struct_0(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_378, c_375, c_384])).
% 2.96/1.42  tff(c_394, plain, (~v2_tdlat_3(k1_pre_topc('#skF_1', '#skF_2')) | ~v1_tdlat_3(k1_pre_topc('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_379, c_393])).
% 2.96/1.42  tff(c_397, plain, (~v1_tdlat_3(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_394])).
% 2.96/1.42  tff(c_522, plain, (![B_96, A_97]: (v1_tdlat_3(B_96) | ~v2_tex_2(u1_struct_0(B_96), A_97) | ~m1_subset_1(u1_struct_0(B_96), k1_zfmisc_1(u1_struct_0(A_97))) | ~m1_pre_topc(B_96, A_97) | v2_struct_0(B_96) | ~l1_pre_topc(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_162])).
% 2.96/1.42  tff(c_531, plain, (![A_97]: (v1_tdlat_3(k1_pre_topc('#skF_1', '#skF_2')) | ~v2_tex_2(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), A_97) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_97))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_97) | v2_struct_0(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc(A_97) | v2_struct_0(A_97))), inference(superposition, [status(thm), theory('equality')], [c_337, c_522])).
% 2.96/1.42  tff(c_535, plain, (![A_97]: (v1_tdlat_3(k1_pre_topc('#skF_1', '#skF_2')) | ~v2_tex_2('#skF_2', A_97) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_97))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_97) | v2_struct_0(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc(A_97) | v2_struct_0(A_97))), inference(demodulation, [status(thm), theory('equality')], [c_337, c_531])).
% 2.96/1.42  tff(c_540, plain, (![A_98]: (~v2_tex_2('#skF_2', A_98) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_98))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_98) | ~l1_pre_topc(A_98) | v2_struct_0(A_98))), inference(negUnitSimplification, [status(thm)], [c_379, c_397, c_535])).
% 2.96/1.42  tff(c_549, plain, (~v2_tex_2('#skF_2', '#skF_1') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_540])).
% 2.96/1.42  tff(c_555, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_366, c_303, c_549])).
% 2.96/1.42  tff(c_557, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_555])).
% 2.96/1.42  tff(c_558, plain, (~v2_tdlat_3(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_394])).
% 2.96/1.42  tff(c_50, plain, (v2_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.96/1.42  tff(c_560, plain, (![B_99, A_100]: (v2_tdlat_3(B_99) | ~m1_pre_topc(B_99, A_100) | ~l1_pre_topc(A_100) | ~v2_tdlat_3(A_100) | ~v2_pre_topc(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.96/1.42  tff(c_563, plain, (v2_tdlat_3(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_tdlat_3('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_366, c_560])).
% 2.96/1.42  tff(c_566, plain, (v2_tdlat_3(k1_pre_topc('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_563])).
% 2.96/1.42  tff(c_568, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_558, c_566])).
% 2.96/1.42  tff(c_569, plain, (~l1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_356])).
% 2.96/1.42  tff(c_582, plain, (~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_8, c_569])).
% 2.96/1.42  tff(c_586, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_378, c_582])).
% 2.96/1.42  tff(c_587, plain, (~l1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_357])).
% 2.96/1.42  tff(c_591, plain, (~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_8, c_587])).
% 2.96/1.42  tff(c_595, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_378, c_591])).
% 2.96/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.42  
% 2.96/1.42  Inference rules
% 2.96/1.42  ----------------------
% 2.96/1.42  #Ref     : 0
% 2.96/1.42  #Sup     : 98
% 2.96/1.42  #Fact    : 0
% 2.96/1.42  #Define  : 0
% 2.96/1.42  #Split   : 6
% 2.96/1.42  #Chain   : 0
% 2.96/1.42  #Close   : 0
% 2.96/1.42  
% 2.96/1.42  Ordering : KBO
% 2.96/1.42  
% 2.96/1.42  Simplification rules
% 2.96/1.42  ----------------------
% 2.96/1.42  #Subsume      : 7
% 2.96/1.42  #Demod        : 76
% 2.96/1.42  #Tautology    : 29
% 2.96/1.42  #SimpNegUnit  : 22
% 2.96/1.42  #BackRed      : 0
% 2.96/1.42  
% 2.96/1.42  #Partial instantiations: 0
% 2.96/1.42  #Strategies tried      : 1
% 2.96/1.42  
% 2.96/1.42  Timing (in seconds)
% 2.96/1.42  ----------------------
% 2.96/1.42  Preprocessing        : 0.33
% 2.96/1.42  Parsing              : 0.19
% 2.96/1.42  CNF conversion       : 0.02
% 2.96/1.42  Main loop            : 0.32
% 2.96/1.42  Inferencing          : 0.12
% 2.96/1.42  Reduction            : 0.09
% 2.96/1.42  Demodulation         : 0.06
% 2.96/1.42  BG Simplification    : 0.02
% 2.96/1.42  Subsumption          : 0.06
% 2.96/1.42  Abstraction          : 0.01
% 2.96/1.42  MUC search           : 0.00
% 2.96/1.42  Cooper               : 0.00
% 2.96/1.42  Total                : 0.69
% 2.96/1.42  Index Insertion      : 0.00
% 2.96/1.42  Index Deletion       : 0.00
% 2.96/1.42  Index Matching       : 0.00
% 2.96/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
