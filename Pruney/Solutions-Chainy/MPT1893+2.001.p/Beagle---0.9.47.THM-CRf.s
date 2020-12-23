%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:25 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 321 expanded)
%              Number of leaves         :   35 ( 123 expanded)
%              Depth                    :   11
%              Number of atoms          :  217 (1091 expanded)
%              Number of equality atoms :    5 (  39 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v3_tex_2 > v3_pre_topc > v2_tops_1 > v1_tops_1 > v1_subset_1 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k3_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_157,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ~ ( ( v3_pre_topc(B,A)
                  | v4_pre_topc(B,A) )
                & v3_tex_2(B,A)
                & v1_subset_1(B,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tex_2)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ~ v1_subset_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_subset_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_subset_1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(A)) )
     => ~ v1_xboole_0(k3_subset_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tex_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_119,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v2_tops_1(B,A)
              & v4_pre_topc(B,A) )
           => v3_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_tops_1)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

tff(f_135,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v3_pre_topc(B,A)
              & v3_tex_2(B,A) )
           => v1_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v3_pre_topc(B,A)
              & v3_tops_1(B,A) )
           => v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_tops_1)).

tff(f_106,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tdlat_3)).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_40,plain,(
    v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_56,plain,(
    ! [B_34,A_35] :
      ( ~ v1_subset_1(B_34,A_35)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_35))
      | ~ v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_59,plain,
    ( ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_56])).

tff(c_62,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_59])).

tff(c_109,plain,(
    ! [A_48,B_49] :
      ( ~ v1_xboole_0(k3_subset_1(A_48,B_49))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_48))
      | ~ v1_subset_1(B_49,A_48)
      | v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_121,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'))
    | ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_109])).

tff(c_127,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_121])).

tff(c_128,plain,(
    ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_127])).

tff(c_52,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_50,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k3_subset_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_44,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | v3_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_55,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_64,plain,(
    ! [A_37,B_38] :
      ( k3_subset_1(A_37,k3_subset_1(A_37,B_38)) = B_38
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_67,plain,(
    k3_subset_1(u1_struct_0('#skF_3'),k3_subset_1(u1_struct_0('#skF_3'),'#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_64])).

tff(c_227,plain,(
    ! [B_62,A_63] :
      ( v4_pre_topc(B_62,A_63)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_63),B_62),A_63)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_237,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_227])).

tff(c_240,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_55,c_237])).

tff(c_241,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_240])).

tff(c_244,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_2,c_241])).

tff(c_248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_244])).

tff(c_249,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_240])).

tff(c_250,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_240])).

tff(c_30,plain,(
    ! [B_29,A_26] :
      ( v3_pre_topc(B_29,A_26)
      | ~ v4_pre_topc(B_29,A_26)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ v3_tdlat_3(A_26)
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_273,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_250,c_30])).

tff(c_287,plain,(
    v3_pre_topc(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_50,c_249,c_273])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_18,plain,(
    ! [B_19,A_17] :
      ( v3_tops_1(B_19,A_17)
      | ~ v4_pre_topc(B_19,A_17)
      | ~ v2_tops_1(B_19,A_17)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_276,plain,
    ( v3_tops_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | ~ v2_tops_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_250,c_18])).

tff(c_290,plain,
    ( v3_tops_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | ~ v2_tops_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_249,c_276])).

tff(c_304,plain,(
    ~ v2_tops_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_290])).

tff(c_213,plain,(
    ! [B_60,A_61] :
      ( v2_tops_1(B_60,A_61)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(A_61),B_60),A_61)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_223,plain,
    ( v2_tops_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_213])).

tff(c_226,plain,
    ( v2_tops_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_223])).

tff(c_464,plain,
    ( v2_tops_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_226])).

tff(c_465,plain,(
    ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_304,c_464])).

tff(c_42,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_466,plain,(
    ! [B_75,A_76] :
      ( v1_tops_1(B_75,A_76)
      | ~ v3_tex_2(B_75,A_76)
      | ~ v3_pre_topc(B_75,A_76)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_482,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_466])).

tff(c_492,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_55,c_42,c_482])).

tff(c_494,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_465,c_492])).

tff(c_495,plain,(
    v3_tops_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_290])).

tff(c_569,plain,(
    ! [B_79,A_80] :
      ( v1_xboole_0(B_79)
      | ~ v3_tops_1(B_79,A_80)
      | ~ v3_pre_topc(B_79,A_80)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_572,plain,
    ( v1_xboole_0(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'))
    | ~ v3_tops_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_250,c_569])).

tff(c_588,plain,(
    v1_xboole_0(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_287,c_495,c_572])).

tff(c_590,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_588])).

tff(c_591,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_16,plain,(
    ! [A_14,B_16] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_14),B_16),A_14)
      | ~ v4_pre_topc(B_16,A_14)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_592,plain,(
    ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_601,plain,(
    ! [A_84,B_85] :
      ( k3_subset_1(A_84,k3_subset_1(A_84,B_85)) = B_85
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_604,plain,(
    k3_subset_1(u1_struct_0('#skF_3'),k3_subset_1(u1_struct_0('#skF_3'),'#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_601])).

tff(c_740,plain,(
    ! [A_105,B_106] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_105),B_106),A_105)
      | ~ v4_pre_topc(B_106,A_105)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_750,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_604,c_740])).

tff(c_753,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_750])).

tff(c_754,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_592,c_753])).

tff(c_755,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_754])).

tff(c_758,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_2,c_755])).

tff(c_762,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_758])).

tff(c_763,plain,(
    ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_754])).

tff(c_764,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_754])).

tff(c_882,plain,(
    ! [B_113,A_114] :
      ( v4_pre_topc(B_113,A_114)
      | ~ v3_pre_topc(B_113,A_114)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ v3_tdlat_3(A_114)
      | ~ l1_pre_topc(A_114)
      | ~ v2_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_885,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_764,c_882])).

tff(c_901,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_50,c_885])).

tff(c_902,plain,(
    ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_763,c_901])).

tff(c_911,plain,
    ( ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_902])).

tff(c_915,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_591,c_911])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:12:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.47  
% 3.14/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.47  %$ v4_pre_topc > v3_tops_1 > v3_tex_2 > v3_pre_topc > v2_tops_1 > v1_tops_1 > v1_subset_1 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k3_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 3.14/1.47  
% 3.14/1.47  %Foreground sorts:
% 3.14/1.47  
% 3.14/1.47  
% 3.14/1.47  %Background operators:
% 3.14/1.47  
% 3.14/1.47  
% 3.14/1.47  %Foreground operators:
% 3.14/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.14/1.47  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.14/1.47  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.14/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.47  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.14/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.14/1.47  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.14/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.14/1.47  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 3.14/1.47  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.14/1.47  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.14/1.47  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.14/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.14/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.14/1.47  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.14/1.47  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.14/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.14/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.14/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.14/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.14/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.14/1.47  
% 3.14/1.49  tff(f_157, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(((v3_pre_topc(B, A) | v4_pre_topc(B, A)) & v3_tex_2(B, A)) & v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_tex_2)).
% 3.14/1.49  tff(f_41, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~v1_subset_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_subset_1)).
% 3.14/1.49  tff(f_93, axiom, (![A, B]: (((~v1_xboole_0(A) & v1_subset_1(B, A)) & m1_subset_1(B, k1_zfmisc_1(A))) => ~v1_xboole_0(k3_subset_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tex_2)).
% 3.14/1.49  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.14/1.49  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.14/1.49  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 3.14/1.49  tff(f_119, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tdlat_3)).
% 3.14/1.49  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tops_1(B, A) & v4_pre_topc(B, A)) => v3_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_tops_1)).
% 3.14/1.49  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_1)).
% 3.14/1.49  tff(f_135, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_tex_2)).
% 3.14/1.49  tff(f_54, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tops_1(B, A)) => v1_xboole_0(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_tops_1)).
% 3.14/1.49  tff(f_106, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tdlat_3)).
% 3.14/1.49  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.14/1.49  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.14/1.49  tff(c_40, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.14/1.49  tff(c_56, plain, (![B_34, A_35]: (~v1_subset_1(B_34, A_35) | ~m1_subset_1(B_34, k1_zfmisc_1(A_35)) | ~v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.14/1.49  tff(c_59, plain, (~v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_56])).
% 3.14/1.49  tff(c_62, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_59])).
% 3.14/1.49  tff(c_109, plain, (![A_48, B_49]: (~v1_xboole_0(k3_subset_1(A_48, B_49)) | ~m1_subset_1(B_49, k1_zfmisc_1(A_48)) | ~v1_subset_1(B_49, A_48) | v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.14/1.49  tff(c_121, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4')) | ~v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_109])).
% 3.14/1.49  tff(c_127, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_121])).
% 3.14/1.49  tff(c_128, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_62, c_127])).
% 3.14/1.49  tff(c_52, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.14/1.49  tff(c_50, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.14/1.49  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.14/1.49  tff(c_44, plain, (v4_pre_topc('#skF_4', '#skF_3') | v3_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.14/1.49  tff(c_55, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 3.14/1.49  tff(c_64, plain, (![A_37, B_38]: (k3_subset_1(A_37, k3_subset_1(A_37, B_38))=B_38 | ~m1_subset_1(B_38, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.14/1.49  tff(c_67, plain, (k3_subset_1(u1_struct_0('#skF_3'), k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_46, c_64])).
% 3.14/1.49  tff(c_227, plain, (![B_62, A_63]: (v4_pre_topc(B_62, A_63) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_63), B_62), A_63) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.14/1.49  tff(c_237, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_67, c_227])).
% 3.14/1.49  tff(c_240, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_55, c_237])).
% 3.14/1.49  tff(c_241, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_240])).
% 3.14/1.49  tff(c_244, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_2, c_241])).
% 3.14/1.49  tff(c_248, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_244])).
% 3.14/1.49  tff(c_249, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_240])).
% 3.14/1.49  tff(c_250, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_240])).
% 3.14/1.49  tff(c_30, plain, (![B_29, A_26]: (v3_pre_topc(B_29, A_26) | ~v4_pre_topc(B_29, A_26) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_26))) | ~v3_tdlat_3(A_26) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.14/1.49  tff(c_273, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_250, c_30])).
% 3.14/1.49  tff(c_287, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_50, c_249, c_273])).
% 3.14/1.49  tff(c_54, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.14/1.49  tff(c_18, plain, (![B_19, A_17]: (v3_tops_1(B_19, A_17) | ~v4_pre_topc(B_19, A_17) | ~v2_tops_1(B_19, A_17) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.14/1.49  tff(c_276, plain, (v3_tops_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~v2_tops_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_250, c_18])).
% 3.14/1.49  tff(c_290, plain, (v3_tops_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~v2_tops_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_249, c_276])).
% 3.14/1.49  tff(c_304, plain, (~v2_tops_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_290])).
% 3.14/1.49  tff(c_213, plain, (![B_60, A_61]: (v2_tops_1(B_60, A_61) | ~v1_tops_1(k3_subset_1(u1_struct_0(A_61), B_60), A_61) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.14/1.49  tff(c_223, plain, (v2_tops_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~v1_tops_1('#skF_4', '#skF_3') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_67, c_213])).
% 3.14/1.49  tff(c_226, plain, (v2_tops_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~v1_tops_1('#skF_4', '#skF_3') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_223])).
% 3.14/1.49  tff(c_464, plain, (v2_tops_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_250, c_226])).
% 3.14/1.49  tff(c_465, plain, (~v1_tops_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_304, c_464])).
% 3.14/1.49  tff(c_42, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.14/1.49  tff(c_466, plain, (![B_75, A_76]: (v1_tops_1(B_75, A_76) | ~v3_tex_2(B_75, A_76) | ~v3_pre_topc(B_75, A_76) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76) | ~v2_pre_topc(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.14/1.49  tff(c_482, plain, (v1_tops_1('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_46, c_466])).
% 3.14/1.49  tff(c_492, plain, (v1_tops_1('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_55, c_42, c_482])).
% 3.14/1.49  tff(c_494, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_465, c_492])).
% 3.14/1.49  tff(c_495, plain, (v3_tops_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_290])).
% 3.14/1.49  tff(c_569, plain, (![B_79, A_80]: (v1_xboole_0(B_79) | ~v3_tops_1(B_79, A_80) | ~v3_pre_topc(B_79, A_80) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80) | ~v2_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.14/1.49  tff(c_572, plain, (v1_xboole_0(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4')) | ~v3_tops_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_250, c_569])).
% 3.14/1.49  tff(c_588, plain, (v1_xboole_0(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_287, c_495, c_572])).
% 3.14/1.49  tff(c_590, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_588])).
% 3.14/1.49  tff(c_591, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 3.14/1.49  tff(c_16, plain, (![A_14, B_16]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_14), B_16), A_14) | ~v4_pre_topc(B_16, A_14) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.14/1.49  tff(c_592, plain, (~v3_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 3.14/1.49  tff(c_601, plain, (![A_84, B_85]: (k3_subset_1(A_84, k3_subset_1(A_84, B_85))=B_85 | ~m1_subset_1(B_85, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.14/1.49  tff(c_604, plain, (k3_subset_1(u1_struct_0('#skF_3'), k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_46, c_601])).
% 3.14/1.49  tff(c_740, plain, (![A_105, B_106]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_105), B_106), A_105) | ~v4_pre_topc(B_106, A_105) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.14/1.49  tff(c_750, plain, (v3_pre_topc('#skF_4', '#skF_3') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_604, c_740])).
% 3.14/1.49  tff(c_753, plain, (v3_pre_topc('#skF_4', '#skF_3') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_750])).
% 3.14/1.49  tff(c_754, plain, (~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_592, c_753])).
% 3.14/1.49  tff(c_755, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_754])).
% 3.14/1.49  tff(c_758, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_2, c_755])).
% 3.14/1.49  tff(c_762, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_758])).
% 3.14/1.49  tff(c_763, plain, (~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_754])).
% 3.14/1.49  tff(c_764, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_754])).
% 3.14/1.49  tff(c_882, plain, (![B_113, A_114]: (v4_pre_topc(B_113, A_114) | ~v3_pre_topc(B_113, A_114) | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(A_114))) | ~v3_tdlat_3(A_114) | ~l1_pre_topc(A_114) | ~v2_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.14/1.49  tff(c_885, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_764, c_882])).
% 3.14/1.49  tff(c_901, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_50, c_885])).
% 3.14/1.49  tff(c_902, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_763, c_901])).
% 3.14/1.49  tff(c_911, plain, (~v4_pre_topc('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_16, c_902])).
% 3.14/1.49  tff(c_915, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_591, c_911])).
% 3.14/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.49  
% 3.14/1.49  Inference rules
% 3.14/1.49  ----------------------
% 3.14/1.49  #Ref     : 0
% 3.14/1.49  #Sup     : 190
% 3.14/1.49  #Fact    : 0
% 3.14/1.49  #Define  : 0
% 3.14/1.49  #Split   : 10
% 3.14/1.49  #Chain   : 0
% 3.14/1.49  #Close   : 0
% 3.14/1.49  
% 3.14/1.49  Ordering : KBO
% 3.14/1.49  
% 3.14/1.49  Simplification rules
% 3.14/1.49  ----------------------
% 3.14/1.49  #Subsume      : 39
% 3.14/1.49  #Demod        : 93
% 3.14/1.49  #Tautology    : 60
% 3.14/1.49  #SimpNegUnit  : 14
% 3.14/1.49  #BackRed      : 0
% 3.14/1.49  
% 3.14/1.49  #Partial instantiations: 0
% 3.14/1.49  #Strategies tried      : 1
% 3.14/1.49  
% 3.14/1.49  Timing (in seconds)
% 3.14/1.49  ----------------------
% 3.14/1.49  Preprocessing        : 0.32
% 3.14/1.49  Parsing              : 0.18
% 3.14/1.49  CNF conversion       : 0.02
% 3.14/1.49  Main loop            : 0.40
% 3.14/1.49  Inferencing          : 0.15
% 3.14/1.49  Reduction            : 0.12
% 3.14/1.49  Demodulation         : 0.08
% 3.14/1.49  BG Simplification    : 0.02
% 3.14/1.49  Subsumption          : 0.07
% 3.14/1.49  Abstraction          : 0.02
% 3.14/1.49  MUC search           : 0.00
% 3.14/1.49  Cooper               : 0.00
% 3.14/1.49  Total                : 0.76
% 3.14/1.49  Index Insertion      : 0.00
% 3.14/1.49  Index Deletion       : 0.00
% 3.14/1.49  Index Matching       : 0.00
% 3.14/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
