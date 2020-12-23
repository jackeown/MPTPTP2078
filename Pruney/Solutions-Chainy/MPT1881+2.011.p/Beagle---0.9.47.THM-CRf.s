%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:07 EST 2020

% Result     : Theorem 6.95s
% Output     : CNFRefutation 7.33s
% Verified   : 
% Statistics : Number of formulae       :  248 (2035 expanded)
%              Number of leaves         :   47 ( 696 expanded)
%              Depth                    :   16
%              Number of atoms          :  532 (5987 expanded)
%              Number of equality atoms :   99 ( 814 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_36,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_45,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_186,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tex_2(B,A)
            <=> ~ v1_subset_1(B,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & v1_tops_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc4_tops_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_111,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_122,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(A),k2_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).

tff(f_136,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_168,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v1_tops_1(B,A)
              & v2_tex_2(B,A) )
           => v3_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).

tff(f_152,axiom,(
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

tff(c_16,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_22,plain,(
    ! [A_13] : ~ v1_subset_1(k2_subset_1(A_13),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_81,plain,(
    ! [A_13] : ~ v1_subset_1(A_13,A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_22])).

tff(c_66,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_4119,plain,(
    ! [A_430,B_431] :
      ( k2_pre_topc(A_430,B_431) = B_431
      | ~ v4_pre_topc(B_431,A_430)
      | ~ m1_subset_1(B_431,k1_zfmisc_1(u1_struct_0(A_430)))
      | ~ l1_pre_topc(A_430) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4136,plain,
    ( k2_pre_topc('#skF_5','#skF_6') = '#skF_6'
    | ~ v4_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_4119])).

tff(c_4147,plain,
    ( k2_pre_topc('#skF_5','#skF_6') = '#skF_6'
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4136])).

tff(c_4149,plain,(
    ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4147])).

tff(c_38,plain,(
    ! [A_25] :
      ( v1_tops_1('#skF_3'(A_25),A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_40,plain,(
    ! [A_25] :
      ( m1_subset_1('#skF_3'(A_25),k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4250,plain,(
    ! [A_444,B_445] :
      ( k2_pre_topc(A_444,B_445) = k2_struct_0(A_444)
      | ~ v1_tops_1(B_445,A_444)
      | ~ m1_subset_1(B_445,k1_zfmisc_1(u1_struct_0(A_444)))
      | ~ l1_pre_topc(A_444) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4281,plain,(
    ! [A_446] :
      ( k2_pre_topc(A_446,'#skF_3'(A_446)) = k2_struct_0(A_446)
      | ~ v1_tops_1('#skF_3'(A_446),A_446)
      | ~ l1_pre_topc(A_446) ) ),
    inference(resolution,[status(thm)],[c_40,c_4250])).

tff(c_4286,plain,(
    ! [A_447] :
      ( k2_pre_topc(A_447,'#skF_3'(A_447)) = k2_struct_0(A_447)
      | ~ l1_pre_topc(A_447) ) ),
    inference(resolution,[status(thm)],[c_38,c_4281])).

tff(c_4200,plain,(
    ! [A_439,B_440] :
      ( k2_pre_topc(A_439,B_440) = u1_struct_0(A_439)
      | ~ v1_tops_1(B_440,A_439)
      | ~ m1_subset_1(B_440,k1_zfmisc_1(u1_struct_0(A_439)))
      | ~ l1_pre_topc(A_439) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_4231,plain,(
    ! [A_441] :
      ( k2_pre_topc(A_441,'#skF_3'(A_441)) = u1_struct_0(A_441)
      | ~ v1_tops_1('#skF_3'(A_441),A_441)
      | ~ l1_pre_topc(A_441) ) ),
    inference(resolution,[status(thm)],[c_40,c_4200])).

tff(c_4235,plain,(
    ! [A_25] :
      ( k2_pre_topc(A_25,'#skF_3'(A_25)) = u1_struct_0(A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(resolution,[status(thm)],[c_38,c_4231])).

tff(c_4301,plain,(
    ! [A_448] :
      ( u1_struct_0(A_448) = k2_struct_0(A_448)
      | ~ l1_pre_topc(A_448)
      | ~ l1_pre_topc(A_448) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4286,c_4235])).

tff(c_4303,plain,
    ( u1_struct_0('#skF_5') = k2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_4301])).

tff(c_4306,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4303])).

tff(c_3948,plain,(
    ! [B_393,A_394] :
      ( v1_subset_1(B_393,A_394)
      | B_393 = A_394
      | ~ m1_subset_1(B_393,k1_zfmisc_1(A_394)) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_3961,plain,(
    ! [A_25] :
      ( v1_subset_1('#skF_3'(A_25),u1_struct_0(A_25))
      | u1_struct_0(A_25) = '#skF_3'(A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(resolution,[status(thm)],[c_40,c_3948])).

tff(c_4346,plain,
    ( v1_subset_1('#skF_3'('#skF_5'),k2_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = '#skF_3'('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4306,c_3961])).

tff(c_4378,plain,
    ( v1_subset_1('#skF_3'('#skF_5'),k2_struct_0('#skF_5'))
    | k2_struct_0('#skF_5') = '#skF_3'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4306,c_4346])).

tff(c_4481,plain,(
    k2_struct_0('#skF_5') = '#skF_3'('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4378])).

tff(c_4309,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4306,c_64])).

tff(c_4487,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4481,c_4309])).

tff(c_4490,plain,(
    u1_struct_0('#skF_5') = '#skF_3'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4481,c_4306])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_70,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_68,plain,(
    v1_tdlat_3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_3936,plain,(
    ! [C_386,A_387] :
      ( r2_hidden(C_386,k1_zfmisc_1(A_387))
      | ~ r1_tarski(C_386,A_387) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,B_15)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3940,plain,(
    ! [C_386,A_387] :
      ( m1_subset_1(C_386,k1_zfmisc_1(A_387))
      | ~ r1_tarski(C_386,A_387) ) ),
    inference(resolution,[status(thm)],[c_3936,c_24])).

tff(c_4087,plain,(
    ! [B_426,A_427] :
      ( v3_pre_topc(B_426,A_427)
      | ~ m1_subset_1(B_426,k1_zfmisc_1(u1_struct_0(A_427)))
      | ~ v1_tdlat_3(A_427)
      | ~ l1_pre_topc(A_427)
      | ~ v2_pre_topc(A_427) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_4112,plain,(
    ! [C_386,A_427] :
      ( v3_pre_topc(C_386,A_427)
      | ~ v1_tdlat_3(A_427)
      | ~ l1_pre_topc(A_427)
      | ~ v2_pre_topc(A_427)
      | ~ r1_tarski(C_386,u1_struct_0(A_427)) ) ),
    inference(resolution,[status(thm)],[c_3940,c_4087])).

tff(c_4328,plain,(
    ! [C_386] :
      ( v3_pre_topc(C_386,'#skF_5')
      | ~ v1_tdlat_3('#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | ~ r1_tarski(C_386,k2_struct_0('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4306,c_4112])).

tff(c_4399,plain,(
    ! [C_449] :
      ( v3_pre_topc(C_449,'#skF_5')
      | ~ r1_tarski(C_449,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_68,c_4328])).

tff(c_4414,plain,(
    ! [B_2] : v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_5'),B_2),'#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_4399])).

tff(c_4484,plain,(
    ! [B_2] : v3_pre_topc(k4_xboole_0('#skF_3'('#skF_5'),B_2),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4481,c_4414])).

tff(c_18,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_82,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_3977,plain,(
    ! [A_398,B_399,C_400] :
      ( k7_subset_1(A_398,B_399,C_400) = k4_xboole_0(B_399,C_400)
      | ~ m1_subset_1(B_399,k1_zfmisc_1(A_398)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_3989,plain,(
    ! [A_9,C_400] : k7_subset_1(A_9,A_9,C_400) = k4_xboole_0(A_9,C_400) ),
    inference(resolution,[status(thm)],[c_82,c_3977])).

tff(c_4871,plain,(
    ! [B_470,A_471] :
      ( v4_pre_topc(B_470,A_471)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(A_471),k2_struct_0(A_471),B_470),A_471)
      | ~ m1_subset_1(B_470,k1_zfmisc_1(u1_struct_0(A_471)))
      | ~ l1_pre_topc(A_471) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4877,plain,(
    ! [B_470] :
      ( v4_pre_topc(B_470,'#skF_5')
      | ~ v3_pre_topc(k7_subset_1('#skF_3'('#skF_5'),k2_struct_0('#skF_5'),B_470),'#skF_5')
      | ~ m1_subset_1(B_470,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4490,c_4871])).

tff(c_4886,plain,(
    ! [B_472] :
      ( v4_pre_topc(B_472,'#skF_5')
      | ~ m1_subset_1(B_472,k1_zfmisc_1('#skF_3'('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4490,c_4484,c_3989,c_4481,c_4877])).

tff(c_4889,plain,(
    v4_pre_topc('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_4487,c_4886])).

tff(c_4905,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4149,c_4889])).

tff(c_4907,plain,(
    k2_struct_0('#skF_5') != '#skF_3'('#skF_5') ),
    inference(splitRight,[status(thm)],[c_4378])).

tff(c_4352,plain,
    ( m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4306,c_40])).

tff(c_4382,plain,(
    m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4352])).

tff(c_32,plain,(
    ! [A_19,B_21] :
      ( k2_pre_topc(A_19,B_21) = B_21
      | ~ v4_pre_topc(B_21,A_19)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4334,plain,(
    ! [B_21] :
      ( k2_pre_topc('#skF_5',B_21) = B_21
      | ~ v4_pre_topc(B_21,'#skF_5')
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4306,c_32])).

tff(c_4978,plain,(
    ! [B_478] :
      ( k2_pre_topc('#skF_5',B_478) = B_478
      | ~ v4_pre_topc(B_478,'#skF_5')
      | ~ m1_subset_1(B_478,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4334])).

tff(c_4997,plain,
    ( k2_pre_topc('#skF_5','#skF_3'('#skF_5')) = '#skF_3'('#skF_5')
    | ~ v4_pre_topc('#skF_3'('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_4382,c_4978])).

tff(c_5003,plain,(
    ~ v4_pre_topc('#skF_3'('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4997])).

tff(c_5288,plain,(
    ! [B_497,A_498] :
      ( v4_pre_topc(B_497,A_498)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(A_498),k2_struct_0(A_498),B_497),A_498)
      | ~ m1_subset_1(B_497,k1_zfmisc_1(u1_struct_0(A_498)))
      | ~ l1_pre_topc(A_498) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_5294,plain,(
    ! [B_497] :
      ( v4_pre_topc(B_497,'#skF_5')
      | ~ v3_pre_topc(k7_subset_1(k2_struct_0('#skF_5'),k2_struct_0('#skF_5'),B_497),'#skF_5')
      | ~ m1_subset_1(B_497,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4306,c_5288])).

tff(c_5298,plain,(
    ! [B_499] :
      ( v4_pre_topc(B_499,'#skF_5')
      | ~ m1_subset_1(B_499,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4306,c_4414,c_3989,c_5294])).

tff(c_5301,plain,(
    v4_pre_topc('#skF_3'('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_4382,c_5298])).

tff(c_5320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5003,c_5301])).

tff(c_5321,plain,(
    k2_pre_topc('#skF_5','#skF_3'('#skF_5')) = '#skF_3'('#skF_5') ),
    inference(splitRight,[status(thm)],[c_4997])).

tff(c_4285,plain,(
    ! [A_25] :
      ( k2_pre_topc(A_25,'#skF_3'(A_25)) = k2_struct_0(A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(resolution,[status(thm)],[c_38,c_4281])).

tff(c_5332,plain,
    ( k2_struct_0('#skF_5') = '#skF_3'('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5321,c_4285])).

tff(c_5345,plain,(
    k2_struct_0('#skF_5') = '#skF_3'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_5332])).

tff(c_5347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4907,c_5345])).

tff(c_5348,plain,(
    k2_pre_topc('#skF_5','#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_4147])).

tff(c_5388,plain,(
    ! [A_506,B_507] :
      ( k2_pre_topc(A_506,B_507) = k2_struct_0(A_506)
      | ~ v1_tops_1(B_507,A_506)
      | ~ m1_subset_1(B_507,k1_zfmisc_1(u1_struct_0(A_506)))
      | ~ l1_pre_topc(A_506) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_5405,plain,
    ( k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5')
    | ~ v1_tops_1('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_5388])).

tff(c_5416,plain,
    ( k2_struct_0('#skF_5') = '#skF_6'
    | ~ v1_tops_1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_5348,c_5405])).

tff(c_5418,plain,(
    ~ v1_tops_1('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_5416])).

tff(c_4104,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | ~ v1_tdlat_3('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_4087])).

tff(c_4115,plain,(
    v3_pre_topc('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_68,c_4104])).

tff(c_74,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ v3_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_95,plain,(
    ~ v3_tex_2('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_80,plain,
    ( v3_tex_2('#skF_6','#skF_5')
    | ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_99,plain,(
    ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_80])).

tff(c_112,plain,(
    ! [B_63,A_64] :
      ( v1_subset_1(B_63,A_64)
      | B_63 = A_64
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_121,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_64,c_112])).

tff(c_129,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_121])).

tff(c_140,plain,
    ( m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1('#skF_6'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_40])).

tff(c_144,plain,(
    m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_140])).

tff(c_48,plain,(
    ! [B_32,A_31] :
      ( v1_subset_1(B_32,A_31)
      | B_32 = A_31
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_149,plain,
    ( v1_subset_1('#skF_3'('#skF_5'),'#skF_6')
    | '#skF_3'('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_144,c_48])).

tff(c_150,plain,(
    '#skF_3'('#skF_5') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_149])).

tff(c_159,plain,
    ( v1_tops_1('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_38])).

tff(c_165,plain,(
    v1_tops_1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_159])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_1649,plain,(
    ! [B_201,A_202] :
      ( v2_tex_2(B_201,A_202)
      | ~ m1_subset_1(B_201,k1_zfmisc_1(u1_struct_0(A_202)))
      | ~ l1_pre_topc(A_202)
      | ~ v1_tdlat_3(A_202)
      | ~ v2_pre_topc(A_202)
      | v2_struct_0(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1659,plain,(
    ! [B_201] :
      ( v2_tex_2(B_201,'#skF_5')
      | ~ m1_subset_1(B_201,k1_zfmisc_1('#skF_6'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v1_tdlat_3('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_1649])).

tff(c_1674,plain,(
    ! [B_201] :
      ( v2_tex_2(B_201,'#skF_5')
      | ~ m1_subset_1(B_201,k1_zfmisc_1('#skF_6'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_1659])).

tff(c_1679,plain,(
    ! [B_203] :
      ( v2_tex_2(B_203,'#skF_5')
      | ~ m1_subset_1(B_203,k1_zfmisc_1('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1674])).

tff(c_1694,plain,(
    v2_tex_2('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_1679])).

tff(c_2578,plain,(
    ! [B_266,A_267] :
      ( v3_tex_2(B_266,A_267)
      | ~ v2_tex_2(B_266,A_267)
      | ~ v1_tops_1(B_266,A_267)
      | ~ m1_subset_1(B_266,k1_zfmisc_1(u1_struct_0(A_267)))
      | ~ l1_pre_topc(A_267)
      | ~ v2_pre_topc(A_267)
      | v2_struct_0(A_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_2592,plain,(
    ! [B_266] :
      ( v3_tex_2(B_266,'#skF_5')
      | ~ v2_tex_2(B_266,'#skF_5')
      | ~ v1_tops_1(B_266,'#skF_5')
      | ~ m1_subset_1(B_266,k1_zfmisc_1('#skF_6'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_2578])).

tff(c_2608,plain,(
    ! [B_266] :
      ( v3_tex_2(B_266,'#skF_5')
      | ~ v2_tex_2(B_266,'#skF_5')
      | ~ v1_tops_1(B_266,'#skF_5')
      | ~ m1_subset_1(B_266,k1_zfmisc_1('#skF_6'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_2592])).

tff(c_2613,plain,(
    ! [B_268] :
      ( v3_tex_2(B_268,'#skF_5')
      | ~ v2_tex_2(B_268,'#skF_5')
      | ~ v1_tops_1(B_268,'#skF_5')
      | ~ m1_subset_1(B_268,k1_zfmisc_1('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2608])).

tff(c_2629,plain,
    ( v3_tex_2('#skF_6','#skF_5')
    | ~ v2_tex_2('#skF_6','#skF_5')
    | ~ v1_tops_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_2613])).

tff(c_2636,plain,(
    v3_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_1694,c_2629])).

tff(c_2638,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_2636])).

tff(c_2640,plain,(
    '#skF_3'('#skF_5') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_2867,plain,(
    ! [A_311,B_312] :
      ( k2_pre_topc(A_311,B_312) = B_312
      | ~ v4_pre_topc(B_312,A_311)
      | ~ m1_subset_1(B_312,k1_zfmisc_1(u1_struct_0(A_311)))
      | ~ l1_pre_topc(A_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2877,plain,(
    ! [B_312] :
      ( k2_pre_topc('#skF_5',B_312) = B_312
      | ~ v4_pre_topc(B_312,'#skF_5')
      | ~ m1_subset_1(B_312,k1_zfmisc_1('#skF_6'))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_2867])).

tff(c_2896,plain,(
    ! [B_313] :
      ( k2_pre_topc('#skF_5',B_313) = B_313
      | ~ v4_pre_topc(B_313,'#skF_5')
      | ~ m1_subset_1(B_313,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2877])).

tff(c_2913,plain,
    ( k2_pre_topc('#skF_5','#skF_3'('#skF_5')) = '#skF_3'('#skF_5')
    | ~ v4_pre_topc('#skF_3'('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_144,c_2896])).

tff(c_2917,plain,(
    ~ v4_pre_topc('#skF_3'('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2913])).

tff(c_100,plain,(
    ! [C_56,A_57] :
      ( r2_hidden(C_56,k1_zfmisc_1(A_57))
      | ~ r1_tarski(C_56,A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_104,plain,(
    ! [C_56,A_57] :
      ( m1_subset_1(C_56,k1_zfmisc_1(A_57))
      | ~ r1_tarski(C_56,A_57) ) ),
    inference(resolution,[status(thm)],[c_100,c_24])).

tff(c_2775,plain,(
    ! [B_300,A_301] :
      ( v3_pre_topc(B_300,A_301)
      | ~ m1_subset_1(B_300,k1_zfmisc_1(u1_struct_0(A_301)))
      | ~ v1_tdlat_3(A_301)
      | ~ l1_pre_topc(A_301)
      | ~ v2_pre_topc(A_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2839,plain,(
    ! [C_306,A_307] :
      ( v3_pre_topc(C_306,A_307)
      | ~ v1_tdlat_3(A_307)
      | ~ l1_pre_topc(A_307)
      | ~ v2_pre_topc(A_307)
      | ~ r1_tarski(C_306,u1_struct_0(A_307)) ) ),
    inference(resolution,[status(thm)],[c_104,c_2775])).

tff(c_2860,plain,(
    ! [A_308,B_309] :
      ( v3_pre_topc(k4_xboole_0(u1_struct_0(A_308),B_309),A_308)
      | ~ v1_tdlat_3(A_308)
      | ~ l1_pre_topc(A_308)
      | ~ v2_pre_topc(A_308) ) ),
    inference(resolution,[status(thm)],[c_2,c_2839])).

tff(c_2863,plain,(
    ! [B_309] :
      ( v3_pre_topc(k4_xboole_0('#skF_6',B_309),'#skF_5')
      | ~ v1_tdlat_3('#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_2860])).

tff(c_2865,plain,(
    ! [B_309] : v3_pre_topc(k4_xboole_0('#skF_6',B_309),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_68,c_2863])).

tff(c_2649,plain,(
    ! [A_272,B_273,C_274] :
      ( k7_subset_1(A_272,B_273,C_274) = k4_xboole_0(B_273,C_274)
      | ~ m1_subset_1(B_273,k1_zfmisc_1(A_272)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2661,plain,(
    ! [A_9,C_274] : k7_subset_1(A_9,A_9,C_274) = k4_xboole_0(A_9,C_274) ),
    inference(resolution,[status(thm)],[c_82,c_2649])).

tff(c_2947,plain,(
    ! [A_319,B_320] :
      ( k2_pre_topc(A_319,B_320) = k2_struct_0(A_319)
      | ~ v1_tops_1(B_320,A_319)
      | ~ m1_subset_1(B_320,k1_zfmisc_1(u1_struct_0(A_319)))
      | ~ l1_pre_topc(A_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2957,plain,(
    ! [B_320] :
      ( k2_pre_topc('#skF_5',B_320) = k2_struct_0('#skF_5')
      | ~ v1_tops_1(B_320,'#skF_5')
      | ~ m1_subset_1(B_320,k1_zfmisc_1('#skF_6'))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_2947])).

tff(c_2997,plain,(
    ! [B_324] :
      ( k2_pre_topc('#skF_5',B_324) = k2_struct_0('#skF_5')
      | ~ v1_tops_1(B_324,'#skF_5')
      | ~ m1_subset_1(B_324,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2957])).

tff(c_3014,plain,
    ( k2_pre_topc('#skF_5','#skF_3'('#skF_5')) = k2_struct_0('#skF_5')
    | ~ v1_tops_1('#skF_3'('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_144,c_2997])).

tff(c_3017,plain,(
    ~ v1_tops_1('#skF_3'('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3014])).

tff(c_3020,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_3017])).

tff(c_3024,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3020])).

tff(c_3026,plain,(
    v1_tops_1('#skF_3'('#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_3014])).

tff(c_3025,plain,(
    k2_pre_topc('#skF_5','#skF_3'('#skF_5')) = k2_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_3014])).

tff(c_3313,plain,(
    ! [A_345,B_346] :
      ( k2_pre_topc(A_345,B_346) = u1_struct_0(A_345)
      | ~ v1_tops_1(B_346,A_345)
      | ~ m1_subset_1(B_346,k1_zfmisc_1(u1_struct_0(A_345)))
      | ~ l1_pre_topc(A_345) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3323,plain,(
    ! [B_346] :
      ( k2_pre_topc('#skF_5',B_346) = u1_struct_0('#skF_5')
      | ~ v1_tops_1(B_346,'#skF_5')
      | ~ m1_subset_1(B_346,k1_zfmisc_1('#skF_6'))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_3313])).

tff(c_3342,plain,(
    ! [B_347] :
      ( k2_pre_topc('#skF_5',B_347) = '#skF_6'
      | ~ v1_tops_1(B_347,'#skF_5')
      | ~ m1_subset_1(B_347,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_129,c_3323])).

tff(c_3349,plain,
    ( k2_pre_topc('#skF_5','#skF_3'('#skF_5')) = '#skF_6'
    | ~ v1_tops_1('#skF_3'('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_144,c_3342])).

tff(c_3361,plain,(
    k2_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3026,c_3025,c_3349])).

tff(c_3666,plain,(
    ! [B_364,A_365] :
      ( v4_pre_topc(B_364,A_365)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(A_365),k2_struct_0(A_365),B_364),A_365)
      | ~ m1_subset_1(B_364,k1_zfmisc_1(u1_struct_0(A_365)))
      | ~ l1_pre_topc(A_365) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3669,plain,(
    ! [B_364] :
      ( v4_pre_topc(B_364,'#skF_5')
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0('#skF_5'),'#skF_6',B_364),'#skF_5')
      | ~ m1_subset_1(B_364,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3361,c_3666])).

tff(c_3684,plain,(
    ! [B_366] :
      ( v4_pre_topc(B_366,'#skF_5')
      | ~ m1_subset_1(B_366,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_129,c_2865,c_2661,c_129,c_3669])).

tff(c_3691,plain,(
    v4_pre_topc('#skF_3'('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_144,c_3684])).

tff(c_3704,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2917,c_3691])).

tff(c_3705,plain,(
    k2_pre_topc('#skF_5','#skF_3'('#skF_5')) = '#skF_3'('#skF_5') ),
    inference(splitRight,[status(thm)],[c_2913])).

tff(c_3801,plain,(
    ! [A_375,B_376] :
      ( k2_pre_topc(A_375,B_376) = k2_struct_0(A_375)
      | ~ v1_tops_1(B_376,A_375)
      | ~ m1_subset_1(B_376,k1_zfmisc_1(u1_struct_0(A_375)))
      | ~ l1_pre_topc(A_375) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3811,plain,(
    ! [B_376] :
      ( k2_pre_topc('#skF_5',B_376) = k2_struct_0('#skF_5')
      | ~ v1_tops_1(B_376,'#skF_5')
      | ~ m1_subset_1(B_376,k1_zfmisc_1('#skF_6'))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_3801])).

tff(c_3832,plain,(
    ! [B_378] :
      ( k2_pre_topc('#skF_5',B_378) = k2_struct_0('#skF_5')
      | ~ v1_tops_1(B_378,'#skF_5')
      | ~ m1_subset_1(B_378,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3811])).

tff(c_3839,plain,
    ( k2_pre_topc('#skF_5','#skF_3'('#skF_5')) = k2_struct_0('#skF_5')
    | ~ v1_tops_1('#skF_3'('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_144,c_3832])).

tff(c_3850,plain,
    ( k2_struct_0('#skF_5') = '#skF_3'('#skF_5')
    | ~ v1_tops_1('#skF_3'('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3705,c_3839])).

tff(c_3853,plain,(
    ~ v1_tops_1('#skF_3'('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3850])).

tff(c_3859,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_3853])).

tff(c_3865,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3859])).

tff(c_3867,plain,(
    v1_tops_1('#skF_3'('#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_3850])).

tff(c_3875,plain,(
    ! [A_379,B_380] :
      ( k2_pre_topc(A_379,B_380) = u1_struct_0(A_379)
      | ~ v1_tops_1(B_380,A_379)
      | ~ m1_subset_1(B_380,k1_zfmisc_1(u1_struct_0(A_379)))
      | ~ l1_pre_topc(A_379) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3885,plain,(
    ! [B_380] :
      ( k2_pre_topc('#skF_5',B_380) = u1_struct_0('#skF_5')
      | ~ v1_tops_1(B_380,'#skF_5')
      | ~ m1_subset_1(B_380,k1_zfmisc_1('#skF_6'))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_3875])).

tff(c_3908,plain,(
    ! [B_381] :
      ( k2_pre_topc('#skF_5',B_381) = '#skF_6'
      | ~ v1_tops_1(B_381,'#skF_5')
      | ~ m1_subset_1(B_381,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_129,c_3885])).

tff(c_3915,plain,
    ( k2_pre_topc('#skF_5','#skF_3'('#skF_5')) = '#skF_6'
    | ~ v1_tops_1('#skF_3'('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_144,c_3908])).

tff(c_3927,plain,(
    '#skF_3'('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3867,c_3705,c_3915])).

tff(c_3929,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2640,c_3927])).

tff(c_3931,plain,(
    v3_tex_2('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_5471,plain,(
    ! [A_516,B_517] :
      ( k2_pre_topc(A_516,B_517) = u1_struct_0(A_516)
      | ~ v1_tops_1(B_517,A_516)
      | ~ m1_subset_1(B_517,k1_zfmisc_1(u1_struct_0(A_516)))
      | ~ l1_pre_topc(A_516) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_5501,plain,(
    ! [A_518] :
      ( k2_pre_topc(A_518,'#skF_3'(A_518)) = u1_struct_0(A_518)
      | ~ v1_tops_1('#skF_3'(A_518),A_518)
      | ~ l1_pre_topc(A_518) ) ),
    inference(resolution,[status(thm)],[c_40,c_5471])).

tff(c_5506,plain,(
    ! [A_519] :
      ( k2_pre_topc(A_519,'#skF_3'(A_519)) = u1_struct_0(A_519)
      | ~ l1_pre_topc(A_519) ) ),
    inference(resolution,[status(thm)],[c_38,c_5501])).

tff(c_5419,plain,(
    ! [A_508] :
      ( k2_pre_topc(A_508,'#skF_3'(A_508)) = k2_struct_0(A_508)
      | ~ v1_tops_1('#skF_3'(A_508),A_508)
      | ~ l1_pre_topc(A_508) ) ),
    inference(resolution,[status(thm)],[c_40,c_5388])).

tff(c_5423,plain,(
    ! [A_25] :
      ( k2_pre_topc(A_25,'#skF_3'(A_25)) = k2_struct_0(A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(resolution,[status(thm)],[c_38,c_5419])).

tff(c_5521,plain,(
    ! [A_520] :
      ( u1_struct_0(A_520) = k2_struct_0(A_520)
      | ~ l1_pre_topc(A_520)
      | ~ l1_pre_topc(A_520) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5506,c_5423])).

tff(c_5523,plain,
    ( u1_struct_0('#skF_5') = k2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_5521])).

tff(c_5526,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_5523])).

tff(c_5572,plain,
    ( v1_subset_1('#skF_3'('#skF_5'),k2_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = '#skF_3'('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5526,c_3961])).

tff(c_5608,plain,
    ( v1_subset_1('#skF_3'('#skF_5'),k2_struct_0('#skF_5'))
    | k2_struct_0('#skF_5') = '#skF_3'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_5526,c_5572])).

tff(c_5713,plain,(
    k2_struct_0('#skF_5') = '#skF_3'('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_5608])).

tff(c_5529,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5526,c_64])).

tff(c_5719,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5713,c_5529])).

tff(c_5722,plain,(
    u1_struct_0('#skF_5') = '#skF_3'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5713,c_5526])).

tff(c_6229,plain,(
    ! [B_550,A_551] :
      ( v1_tops_1(B_550,A_551)
      | ~ v3_tex_2(B_550,A_551)
      | ~ v3_pre_topc(B_550,A_551)
      | ~ m1_subset_1(B_550,k1_zfmisc_1(u1_struct_0(A_551)))
      | ~ l1_pre_topc(A_551)
      | ~ v2_pre_topc(A_551)
      | v2_struct_0(A_551) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_6236,plain,(
    ! [B_550] :
      ( v1_tops_1(B_550,'#skF_5')
      | ~ v3_tex_2(B_550,'#skF_5')
      | ~ v3_pre_topc(B_550,'#skF_5')
      | ~ m1_subset_1(B_550,k1_zfmisc_1('#skF_3'('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5722,c_6229])).

tff(c_6257,plain,(
    ! [B_550] :
      ( v1_tops_1(B_550,'#skF_5')
      | ~ v3_tex_2(B_550,'#skF_5')
      | ~ v3_pre_topc(B_550,'#skF_5')
      | ~ m1_subset_1(B_550,k1_zfmisc_1('#skF_3'('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_6236])).

tff(c_6281,plain,(
    ! [B_554] :
      ( v1_tops_1(B_554,'#skF_5')
      | ~ v3_tex_2(B_554,'#skF_5')
      | ~ v3_pre_topc(B_554,'#skF_5')
      | ~ m1_subset_1(B_554,k1_zfmisc_1('#skF_3'('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_6257])).

tff(c_6288,plain,
    ( v1_tops_1('#skF_6','#skF_5')
    | ~ v3_tex_2('#skF_6','#skF_5')
    | ~ v3_pre_topc('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_5719,c_6281])).

tff(c_6305,plain,(
    v1_tops_1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4115,c_3931,c_6288])).

tff(c_6307,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5418,c_6305])).

tff(c_6309,plain,(
    k2_struct_0('#skF_5') != '#skF_3'('#skF_5') ),
    inference(splitRight,[status(thm)],[c_5608])).

tff(c_5578,plain,
    ( m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5526,c_40])).

tff(c_5612,plain,(
    m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_5578])).

tff(c_5560,plain,(
    ! [B_21] :
      ( k2_pre_topc('#skF_5',B_21) = B_21
      | ~ v4_pre_topc(B_21,'#skF_5')
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5526,c_32])).

tff(c_6507,plain,(
    ! [B_569] :
      ( k2_pre_topc('#skF_5',B_569) = B_569
      | ~ v4_pre_topc(B_569,'#skF_5')
      | ~ m1_subset_1(B_569,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_5560])).

tff(c_6526,plain,
    ( k2_pre_topc('#skF_5','#skF_3'('#skF_5')) = '#skF_3'('#skF_5')
    | ~ v4_pre_topc('#skF_3'('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_5612,c_6507])).

tff(c_6534,plain,(
    ~ v4_pre_topc('#skF_3'('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_6526])).

tff(c_5372,plain,(
    ! [C_504,A_505] :
      ( v3_pre_topc(C_504,A_505)
      | ~ v1_tdlat_3(A_505)
      | ~ l1_pre_topc(A_505)
      | ~ v2_pre_topc(A_505)
      | ~ r1_tarski(C_504,u1_struct_0(A_505)) ) ),
    inference(resolution,[status(thm)],[c_3940,c_4087])).

tff(c_5387,plain,(
    ! [A_505,B_2] :
      ( v3_pre_topc(k4_xboole_0(u1_struct_0(A_505),B_2),A_505)
      | ~ v1_tdlat_3(A_505)
      | ~ l1_pre_topc(A_505)
      | ~ v2_pre_topc(A_505) ) ),
    inference(resolution,[status(thm)],[c_2,c_5372])).

tff(c_5536,plain,(
    ! [B_2] :
      ( v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_5'),B_2),'#skF_5')
      | ~ v1_tdlat_3('#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5526,c_5387])).

tff(c_5584,plain,(
    ! [B_2] : v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_5'),B_2),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_68,c_5536])).

tff(c_6651,plain,(
    ! [B_576,A_577] :
      ( v4_pre_topc(B_576,A_577)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(A_577),k2_struct_0(A_577),B_576),A_577)
      | ~ m1_subset_1(B_576,k1_zfmisc_1(u1_struct_0(A_577)))
      | ~ l1_pre_topc(A_577) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6657,plain,(
    ! [B_576] :
      ( v4_pre_topc(B_576,'#skF_5')
      | ~ v3_pre_topc(k7_subset_1(k2_struct_0('#skF_5'),k2_struct_0('#skF_5'),B_576),'#skF_5')
      | ~ m1_subset_1(B_576,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5526,c_6651])).

tff(c_6688,plain,(
    ! [B_578] :
      ( v4_pre_topc(B_578,'#skF_5')
      | ~ m1_subset_1(B_578,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_5526,c_5584,c_3989,c_6657])).

tff(c_6691,plain,(
    v4_pre_topc('#skF_3'('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_5612,c_6688])).

tff(c_6710,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6534,c_6691])).

tff(c_6711,plain,(
    k2_pre_topc('#skF_5','#skF_3'('#skF_5')) = '#skF_3'('#skF_5') ),
    inference(splitRight,[status(thm)],[c_6526])).

tff(c_5505,plain,(
    ! [A_25] :
      ( k2_pre_topc(A_25,'#skF_3'(A_25)) = u1_struct_0(A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(resolution,[status(thm)],[c_38,c_5501])).

tff(c_6790,plain,
    ( u1_struct_0('#skF_5') = '#skF_3'('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6711,c_5505])).

tff(c_6803,plain,(
    k2_struct_0('#skF_5') = '#skF_3'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_5526,c_6790])).

tff(c_6805,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6309,c_6803])).

tff(c_6807,plain,(
    v1_tops_1('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_5416])).

tff(c_6863,plain,(
    ! [A_588,B_589] :
      ( k2_pre_topc(A_588,B_589) = u1_struct_0(A_588)
      | ~ v1_tops_1(B_589,A_588)
      | ~ m1_subset_1(B_589,k1_zfmisc_1(u1_struct_0(A_588)))
      | ~ l1_pre_topc(A_588) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6880,plain,
    ( k2_pre_topc('#skF_5','#skF_6') = u1_struct_0('#skF_5')
    | ~ v1_tops_1('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_6863])).

tff(c_6891,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_6807,c_5348,c_6880])).

tff(c_3930,plain,(
    v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_6894,plain,(
    v1_subset_1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6891,c_3930])).

tff(c_6898,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_6894])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:27:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.95/2.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.95/2.47  
% 6.95/2.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.95/2.48  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1
% 6.95/2.48  
% 6.95/2.48  %Foreground sorts:
% 6.95/2.48  
% 6.95/2.48  
% 6.95/2.48  %Background operators:
% 6.95/2.48  
% 6.95/2.48  
% 6.95/2.48  %Foreground operators:
% 6.95/2.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.95/2.48  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.95/2.48  tff('#skF_4', type, '#skF_4': $i > $i).
% 6.95/2.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.95/2.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.95/2.48  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 6.95/2.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.95/2.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.95/2.48  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 6.95/2.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.95/2.48  tff('#skF_5', type, '#skF_5': $i).
% 6.95/2.48  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 6.95/2.48  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 6.95/2.48  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 6.95/2.48  tff('#skF_6', type, '#skF_6': $i).
% 6.95/2.48  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 6.95/2.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.95/2.48  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 6.95/2.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.95/2.48  tff('#skF_3', type, '#skF_3': $i > $i).
% 6.95/2.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.95/2.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.95/2.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.95/2.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.95/2.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.95/2.48  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.95/2.48  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 6.95/2.48  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.95/2.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.95/2.48  
% 7.33/2.51  tff(f_36, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 7.33/2.51  tff(f_45, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_subset_1)).
% 7.33/2.51  tff(f_186, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tex_2)).
% 7.33/2.51  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 7.33/2.51  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v1_tops_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc4_tops_1)).
% 7.33/2.51  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 7.33/2.51  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 7.33/2.51  tff(f_111, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 7.33/2.51  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.33/2.51  tff(f_34, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 7.33/2.51  tff(f_49, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 7.33/2.51  tff(f_122, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_tdlat_3)).
% 7.33/2.51  tff(f_38, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 7.33/2.51  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 7.33/2.51  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k7_subset_1(u1_struct_0(A), k2_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_pre_topc)).
% 7.33/2.51  tff(f_136, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 7.33/2.51  tff(f_168, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tex_2)).
% 7.33/2.51  tff(f_152, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_tex_2)).
% 7.33/2.51  tff(c_16, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.33/2.51  tff(c_22, plain, (![A_13]: (~v1_subset_1(k2_subset_1(A_13), A_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.33/2.51  tff(c_81, plain, (![A_13]: (~v1_subset_1(A_13, A_13))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_22])).
% 7.33/2.51  tff(c_66, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_186])).
% 7.33/2.51  tff(c_64, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_186])).
% 7.33/2.51  tff(c_4119, plain, (![A_430, B_431]: (k2_pre_topc(A_430, B_431)=B_431 | ~v4_pre_topc(B_431, A_430) | ~m1_subset_1(B_431, k1_zfmisc_1(u1_struct_0(A_430))) | ~l1_pre_topc(A_430))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.33/2.51  tff(c_4136, plain, (k2_pre_topc('#skF_5', '#skF_6')='#skF_6' | ~v4_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_64, c_4119])).
% 7.33/2.51  tff(c_4147, plain, (k2_pre_topc('#skF_5', '#skF_6')='#skF_6' | ~v4_pre_topc('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_4136])).
% 7.33/2.51  tff(c_4149, plain, (~v4_pre_topc('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_4147])).
% 7.33/2.51  tff(c_38, plain, (![A_25]: (v1_tops_1('#skF_3'(A_25), A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.33/2.51  tff(c_40, plain, (![A_25]: (m1_subset_1('#skF_3'(A_25), k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.33/2.51  tff(c_4250, plain, (![A_444, B_445]: (k2_pre_topc(A_444, B_445)=k2_struct_0(A_444) | ~v1_tops_1(B_445, A_444) | ~m1_subset_1(B_445, k1_zfmisc_1(u1_struct_0(A_444))) | ~l1_pre_topc(A_444))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.33/2.51  tff(c_4281, plain, (![A_446]: (k2_pre_topc(A_446, '#skF_3'(A_446))=k2_struct_0(A_446) | ~v1_tops_1('#skF_3'(A_446), A_446) | ~l1_pre_topc(A_446))), inference(resolution, [status(thm)], [c_40, c_4250])).
% 7.33/2.51  tff(c_4286, plain, (![A_447]: (k2_pre_topc(A_447, '#skF_3'(A_447))=k2_struct_0(A_447) | ~l1_pre_topc(A_447))), inference(resolution, [status(thm)], [c_38, c_4281])).
% 7.33/2.51  tff(c_4200, plain, (![A_439, B_440]: (k2_pre_topc(A_439, B_440)=u1_struct_0(A_439) | ~v1_tops_1(B_440, A_439) | ~m1_subset_1(B_440, k1_zfmisc_1(u1_struct_0(A_439))) | ~l1_pre_topc(A_439))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.33/2.51  tff(c_4231, plain, (![A_441]: (k2_pre_topc(A_441, '#skF_3'(A_441))=u1_struct_0(A_441) | ~v1_tops_1('#skF_3'(A_441), A_441) | ~l1_pre_topc(A_441))), inference(resolution, [status(thm)], [c_40, c_4200])).
% 7.33/2.51  tff(c_4235, plain, (![A_25]: (k2_pre_topc(A_25, '#skF_3'(A_25))=u1_struct_0(A_25) | ~l1_pre_topc(A_25))), inference(resolution, [status(thm)], [c_38, c_4231])).
% 7.33/2.51  tff(c_4301, plain, (![A_448]: (u1_struct_0(A_448)=k2_struct_0(A_448) | ~l1_pre_topc(A_448) | ~l1_pre_topc(A_448))), inference(superposition, [status(thm), theory('equality')], [c_4286, c_4235])).
% 7.33/2.51  tff(c_4303, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_66, c_4301])).
% 7.33/2.51  tff(c_4306, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_4303])).
% 7.33/2.51  tff(c_3948, plain, (![B_393, A_394]: (v1_subset_1(B_393, A_394) | B_393=A_394 | ~m1_subset_1(B_393, k1_zfmisc_1(A_394)))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.33/2.51  tff(c_3961, plain, (![A_25]: (v1_subset_1('#skF_3'(A_25), u1_struct_0(A_25)) | u1_struct_0(A_25)='#skF_3'(A_25) | ~l1_pre_topc(A_25))), inference(resolution, [status(thm)], [c_40, c_3948])).
% 7.33/2.51  tff(c_4346, plain, (v1_subset_1('#skF_3'('#skF_5'), k2_struct_0('#skF_5')) | u1_struct_0('#skF_5')='#skF_3'('#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4306, c_3961])).
% 7.33/2.51  tff(c_4378, plain, (v1_subset_1('#skF_3'('#skF_5'), k2_struct_0('#skF_5')) | k2_struct_0('#skF_5')='#skF_3'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_4306, c_4346])).
% 7.33/2.51  tff(c_4481, plain, (k2_struct_0('#skF_5')='#skF_3'('#skF_5')), inference(splitLeft, [status(thm)], [c_4378])).
% 7.33/2.51  tff(c_4309, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_4306, c_64])).
% 7.33/2.51  tff(c_4487, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_4481, c_4309])).
% 7.33/2.51  tff(c_4490, plain, (u1_struct_0('#skF_5')='#skF_3'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4481, c_4306])).
% 7.33/2.51  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.33/2.51  tff(c_70, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_186])).
% 7.33/2.51  tff(c_68, plain, (v1_tdlat_3('#skF_5')), inference(cnfTransformation, [status(thm)], [f_186])).
% 7.33/2.51  tff(c_3936, plain, (![C_386, A_387]: (r2_hidden(C_386, k1_zfmisc_1(A_387)) | ~r1_tarski(C_386, A_387))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.33/2.51  tff(c_24, plain, (![A_14, B_15]: (m1_subset_1(A_14, B_15) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.33/2.51  tff(c_3940, plain, (![C_386, A_387]: (m1_subset_1(C_386, k1_zfmisc_1(A_387)) | ~r1_tarski(C_386, A_387))), inference(resolution, [status(thm)], [c_3936, c_24])).
% 7.33/2.51  tff(c_4087, plain, (![B_426, A_427]: (v3_pre_topc(B_426, A_427) | ~m1_subset_1(B_426, k1_zfmisc_1(u1_struct_0(A_427))) | ~v1_tdlat_3(A_427) | ~l1_pre_topc(A_427) | ~v2_pre_topc(A_427))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.33/2.51  tff(c_4112, plain, (![C_386, A_427]: (v3_pre_topc(C_386, A_427) | ~v1_tdlat_3(A_427) | ~l1_pre_topc(A_427) | ~v2_pre_topc(A_427) | ~r1_tarski(C_386, u1_struct_0(A_427)))), inference(resolution, [status(thm)], [c_3940, c_4087])).
% 7.33/2.51  tff(c_4328, plain, (![C_386]: (v3_pre_topc(C_386, '#skF_5') | ~v1_tdlat_3('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | ~r1_tarski(C_386, k2_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_4306, c_4112])).
% 7.33/2.51  tff(c_4399, plain, (![C_449]: (v3_pre_topc(C_449, '#skF_5') | ~r1_tarski(C_449, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_68, c_4328])).
% 7.33/2.51  tff(c_4414, plain, (![B_2]: (v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_5'), B_2), '#skF_5'))), inference(resolution, [status(thm)], [c_2, c_4399])).
% 7.33/2.51  tff(c_4484, plain, (![B_2]: (v3_pre_topc(k4_xboole_0('#skF_3'('#skF_5'), B_2), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4481, c_4414])).
% 7.33/2.51  tff(c_18, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.33/2.51  tff(c_82, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18])).
% 7.33/2.51  tff(c_3977, plain, (![A_398, B_399, C_400]: (k7_subset_1(A_398, B_399, C_400)=k4_xboole_0(B_399, C_400) | ~m1_subset_1(B_399, k1_zfmisc_1(A_398)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.33/2.51  tff(c_3989, plain, (![A_9, C_400]: (k7_subset_1(A_9, A_9, C_400)=k4_xboole_0(A_9, C_400))), inference(resolution, [status(thm)], [c_82, c_3977])).
% 7.33/2.51  tff(c_4871, plain, (![B_470, A_471]: (v4_pre_topc(B_470, A_471) | ~v3_pre_topc(k7_subset_1(u1_struct_0(A_471), k2_struct_0(A_471), B_470), A_471) | ~m1_subset_1(B_470, k1_zfmisc_1(u1_struct_0(A_471))) | ~l1_pre_topc(A_471))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.33/2.51  tff(c_4877, plain, (![B_470]: (v4_pre_topc(B_470, '#skF_5') | ~v3_pre_topc(k7_subset_1('#skF_3'('#skF_5'), k2_struct_0('#skF_5'), B_470), '#skF_5') | ~m1_subset_1(B_470, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4490, c_4871])).
% 7.33/2.51  tff(c_4886, plain, (![B_472]: (v4_pre_topc(B_472, '#skF_5') | ~m1_subset_1(B_472, k1_zfmisc_1('#skF_3'('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_4490, c_4484, c_3989, c_4481, c_4877])).
% 7.33/2.51  tff(c_4889, plain, (v4_pre_topc('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_4487, c_4886])).
% 7.33/2.51  tff(c_4905, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4149, c_4889])).
% 7.33/2.51  tff(c_4907, plain, (k2_struct_0('#skF_5')!='#skF_3'('#skF_5')), inference(splitRight, [status(thm)], [c_4378])).
% 7.33/2.51  tff(c_4352, plain, (m1_subset_1('#skF_3'('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4306, c_40])).
% 7.33/2.51  tff(c_4382, plain, (m1_subset_1('#skF_3'('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_4352])).
% 7.33/2.51  tff(c_32, plain, (![A_19, B_21]: (k2_pre_topc(A_19, B_21)=B_21 | ~v4_pre_topc(B_21, A_19) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.33/2.51  tff(c_4334, plain, (![B_21]: (k2_pre_topc('#skF_5', B_21)=B_21 | ~v4_pre_topc(B_21, '#skF_5') | ~m1_subset_1(B_21, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4306, c_32])).
% 7.33/2.51  tff(c_4978, plain, (![B_478]: (k2_pre_topc('#skF_5', B_478)=B_478 | ~v4_pre_topc(B_478, '#skF_5') | ~m1_subset_1(B_478, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_4334])).
% 7.33/2.51  tff(c_4997, plain, (k2_pre_topc('#skF_5', '#skF_3'('#skF_5'))='#skF_3'('#skF_5') | ~v4_pre_topc('#skF_3'('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_4382, c_4978])).
% 7.33/2.51  tff(c_5003, plain, (~v4_pre_topc('#skF_3'('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_4997])).
% 7.33/2.51  tff(c_5288, plain, (![B_497, A_498]: (v4_pre_topc(B_497, A_498) | ~v3_pre_topc(k7_subset_1(u1_struct_0(A_498), k2_struct_0(A_498), B_497), A_498) | ~m1_subset_1(B_497, k1_zfmisc_1(u1_struct_0(A_498))) | ~l1_pre_topc(A_498))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.33/2.51  tff(c_5294, plain, (![B_497]: (v4_pre_topc(B_497, '#skF_5') | ~v3_pre_topc(k7_subset_1(k2_struct_0('#skF_5'), k2_struct_0('#skF_5'), B_497), '#skF_5') | ~m1_subset_1(B_497, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4306, c_5288])).
% 7.33/2.51  tff(c_5298, plain, (![B_499]: (v4_pre_topc(B_499, '#skF_5') | ~m1_subset_1(B_499, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_4306, c_4414, c_3989, c_5294])).
% 7.33/2.51  tff(c_5301, plain, (v4_pre_topc('#skF_3'('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_4382, c_5298])).
% 7.33/2.51  tff(c_5320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5003, c_5301])).
% 7.33/2.51  tff(c_5321, plain, (k2_pre_topc('#skF_5', '#skF_3'('#skF_5'))='#skF_3'('#skF_5')), inference(splitRight, [status(thm)], [c_4997])).
% 7.33/2.51  tff(c_4285, plain, (![A_25]: (k2_pre_topc(A_25, '#skF_3'(A_25))=k2_struct_0(A_25) | ~l1_pre_topc(A_25))), inference(resolution, [status(thm)], [c_38, c_4281])).
% 7.33/2.51  tff(c_5332, plain, (k2_struct_0('#skF_5')='#skF_3'('#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5321, c_4285])).
% 7.33/2.51  tff(c_5345, plain, (k2_struct_0('#skF_5')='#skF_3'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_5332])).
% 7.33/2.51  tff(c_5347, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4907, c_5345])).
% 7.33/2.51  tff(c_5348, plain, (k2_pre_topc('#skF_5', '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_4147])).
% 7.33/2.51  tff(c_5388, plain, (![A_506, B_507]: (k2_pre_topc(A_506, B_507)=k2_struct_0(A_506) | ~v1_tops_1(B_507, A_506) | ~m1_subset_1(B_507, k1_zfmisc_1(u1_struct_0(A_506))) | ~l1_pre_topc(A_506))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.33/2.51  tff(c_5405, plain, (k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5') | ~v1_tops_1('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_64, c_5388])).
% 7.33/2.51  tff(c_5416, plain, (k2_struct_0('#skF_5')='#skF_6' | ~v1_tops_1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_5348, c_5405])).
% 7.33/2.51  tff(c_5418, plain, (~v1_tops_1('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_5416])).
% 7.33/2.51  tff(c_4104, plain, (v3_pre_topc('#skF_6', '#skF_5') | ~v1_tdlat_3('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_64, c_4087])).
% 7.33/2.51  tff(c_4115, plain, (v3_pre_topc('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_68, c_4104])).
% 7.33/2.51  tff(c_74, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~v3_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_186])).
% 7.33/2.51  tff(c_95, plain, (~v3_tex_2('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_74])).
% 7.33/2.51  tff(c_80, plain, (v3_tex_2('#skF_6', '#skF_5') | ~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_186])).
% 7.33/2.51  tff(c_99, plain, (~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_95, c_80])).
% 7.33/2.51  tff(c_112, plain, (![B_63, A_64]: (v1_subset_1(B_63, A_64) | B_63=A_64 | ~m1_subset_1(B_63, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.33/2.51  tff(c_121, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_64, c_112])).
% 7.33/2.51  tff(c_129, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_99, c_121])).
% 7.33/2.51  tff(c_140, plain, (m1_subset_1('#skF_3'('#skF_5'), k1_zfmisc_1('#skF_6')) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_129, c_40])).
% 7.33/2.51  tff(c_144, plain, (m1_subset_1('#skF_3'('#skF_5'), k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_140])).
% 7.33/2.51  tff(c_48, plain, (![B_32, A_31]: (v1_subset_1(B_32, A_31) | B_32=A_31 | ~m1_subset_1(B_32, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.33/2.51  tff(c_149, plain, (v1_subset_1('#skF_3'('#skF_5'), '#skF_6') | '#skF_3'('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_144, c_48])).
% 7.33/2.51  tff(c_150, plain, ('#skF_3'('#skF_5')='#skF_6'), inference(splitLeft, [status(thm)], [c_149])).
% 7.33/2.51  tff(c_159, plain, (v1_tops_1('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_150, c_38])).
% 7.33/2.51  tff(c_165, plain, (v1_tops_1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_159])).
% 7.33/2.51  tff(c_72, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_186])).
% 7.33/2.51  tff(c_1649, plain, (![B_201, A_202]: (v2_tex_2(B_201, A_202) | ~m1_subset_1(B_201, k1_zfmisc_1(u1_struct_0(A_202))) | ~l1_pre_topc(A_202) | ~v1_tdlat_3(A_202) | ~v2_pre_topc(A_202) | v2_struct_0(A_202))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.33/2.51  tff(c_1659, plain, (![B_201]: (v2_tex_2(B_201, '#skF_5') | ~m1_subset_1(B_201, k1_zfmisc_1('#skF_6')) | ~l1_pre_topc('#skF_5') | ~v1_tdlat_3('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_1649])).
% 7.33/2.51  tff(c_1674, plain, (![B_201]: (v2_tex_2(B_201, '#skF_5') | ~m1_subset_1(B_201, k1_zfmisc_1('#skF_6')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_1659])).
% 7.33/2.51  tff(c_1679, plain, (![B_203]: (v2_tex_2(B_203, '#skF_5') | ~m1_subset_1(B_203, k1_zfmisc_1('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_72, c_1674])).
% 7.33/2.51  tff(c_1694, plain, (v2_tex_2('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_82, c_1679])).
% 7.33/2.51  tff(c_2578, plain, (![B_266, A_267]: (v3_tex_2(B_266, A_267) | ~v2_tex_2(B_266, A_267) | ~v1_tops_1(B_266, A_267) | ~m1_subset_1(B_266, k1_zfmisc_1(u1_struct_0(A_267))) | ~l1_pre_topc(A_267) | ~v2_pre_topc(A_267) | v2_struct_0(A_267))), inference(cnfTransformation, [status(thm)], [f_168])).
% 7.33/2.51  tff(c_2592, plain, (![B_266]: (v3_tex_2(B_266, '#skF_5') | ~v2_tex_2(B_266, '#skF_5') | ~v1_tops_1(B_266, '#skF_5') | ~m1_subset_1(B_266, k1_zfmisc_1('#skF_6')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_2578])).
% 7.33/2.51  tff(c_2608, plain, (![B_266]: (v3_tex_2(B_266, '#skF_5') | ~v2_tex_2(B_266, '#skF_5') | ~v1_tops_1(B_266, '#skF_5') | ~m1_subset_1(B_266, k1_zfmisc_1('#skF_6')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_2592])).
% 7.33/2.51  tff(c_2613, plain, (![B_268]: (v3_tex_2(B_268, '#skF_5') | ~v2_tex_2(B_268, '#skF_5') | ~v1_tops_1(B_268, '#skF_5') | ~m1_subset_1(B_268, k1_zfmisc_1('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_72, c_2608])).
% 7.33/2.51  tff(c_2629, plain, (v3_tex_2('#skF_6', '#skF_5') | ~v2_tex_2('#skF_6', '#skF_5') | ~v1_tops_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_82, c_2613])).
% 7.33/2.51  tff(c_2636, plain, (v3_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_165, c_1694, c_2629])).
% 7.33/2.51  tff(c_2638, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_2636])).
% 7.33/2.51  tff(c_2640, plain, ('#skF_3'('#skF_5')!='#skF_6'), inference(splitRight, [status(thm)], [c_149])).
% 7.33/2.51  tff(c_2867, plain, (![A_311, B_312]: (k2_pre_topc(A_311, B_312)=B_312 | ~v4_pre_topc(B_312, A_311) | ~m1_subset_1(B_312, k1_zfmisc_1(u1_struct_0(A_311))) | ~l1_pre_topc(A_311))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.33/2.51  tff(c_2877, plain, (![B_312]: (k2_pre_topc('#skF_5', B_312)=B_312 | ~v4_pre_topc(B_312, '#skF_5') | ~m1_subset_1(B_312, k1_zfmisc_1('#skF_6')) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_2867])).
% 7.33/2.51  tff(c_2896, plain, (![B_313]: (k2_pre_topc('#skF_5', B_313)=B_313 | ~v4_pre_topc(B_313, '#skF_5') | ~m1_subset_1(B_313, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2877])).
% 7.33/2.51  tff(c_2913, plain, (k2_pre_topc('#skF_5', '#skF_3'('#skF_5'))='#skF_3'('#skF_5') | ~v4_pre_topc('#skF_3'('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_144, c_2896])).
% 7.33/2.51  tff(c_2917, plain, (~v4_pre_topc('#skF_3'('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_2913])).
% 7.33/2.51  tff(c_100, plain, (![C_56, A_57]: (r2_hidden(C_56, k1_zfmisc_1(A_57)) | ~r1_tarski(C_56, A_57))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.33/2.51  tff(c_104, plain, (![C_56, A_57]: (m1_subset_1(C_56, k1_zfmisc_1(A_57)) | ~r1_tarski(C_56, A_57))), inference(resolution, [status(thm)], [c_100, c_24])).
% 7.33/2.51  tff(c_2775, plain, (![B_300, A_301]: (v3_pre_topc(B_300, A_301) | ~m1_subset_1(B_300, k1_zfmisc_1(u1_struct_0(A_301))) | ~v1_tdlat_3(A_301) | ~l1_pre_topc(A_301) | ~v2_pre_topc(A_301))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.33/2.51  tff(c_2839, plain, (![C_306, A_307]: (v3_pre_topc(C_306, A_307) | ~v1_tdlat_3(A_307) | ~l1_pre_topc(A_307) | ~v2_pre_topc(A_307) | ~r1_tarski(C_306, u1_struct_0(A_307)))), inference(resolution, [status(thm)], [c_104, c_2775])).
% 7.33/2.51  tff(c_2860, plain, (![A_308, B_309]: (v3_pre_topc(k4_xboole_0(u1_struct_0(A_308), B_309), A_308) | ~v1_tdlat_3(A_308) | ~l1_pre_topc(A_308) | ~v2_pre_topc(A_308))), inference(resolution, [status(thm)], [c_2, c_2839])).
% 7.33/2.51  tff(c_2863, plain, (![B_309]: (v3_pre_topc(k4_xboole_0('#skF_6', B_309), '#skF_5') | ~v1_tdlat_3('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_2860])).
% 7.33/2.51  tff(c_2865, plain, (![B_309]: (v3_pre_topc(k4_xboole_0('#skF_6', B_309), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_68, c_2863])).
% 7.33/2.51  tff(c_2649, plain, (![A_272, B_273, C_274]: (k7_subset_1(A_272, B_273, C_274)=k4_xboole_0(B_273, C_274) | ~m1_subset_1(B_273, k1_zfmisc_1(A_272)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.33/2.51  tff(c_2661, plain, (![A_9, C_274]: (k7_subset_1(A_9, A_9, C_274)=k4_xboole_0(A_9, C_274))), inference(resolution, [status(thm)], [c_82, c_2649])).
% 7.33/2.51  tff(c_2947, plain, (![A_319, B_320]: (k2_pre_topc(A_319, B_320)=k2_struct_0(A_319) | ~v1_tops_1(B_320, A_319) | ~m1_subset_1(B_320, k1_zfmisc_1(u1_struct_0(A_319))) | ~l1_pre_topc(A_319))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.33/2.51  tff(c_2957, plain, (![B_320]: (k2_pre_topc('#skF_5', B_320)=k2_struct_0('#skF_5') | ~v1_tops_1(B_320, '#skF_5') | ~m1_subset_1(B_320, k1_zfmisc_1('#skF_6')) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_2947])).
% 7.33/2.51  tff(c_2997, plain, (![B_324]: (k2_pre_topc('#skF_5', B_324)=k2_struct_0('#skF_5') | ~v1_tops_1(B_324, '#skF_5') | ~m1_subset_1(B_324, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2957])).
% 7.33/2.51  tff(c_3014, plain, (k2_pre_topc('#skF_5', '#skF_3'('#skF_5'))=k2_struct_0('#skF_5') | ~v1_tops_1('#skF_3'('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_144, c_2997])).
% 7.33/2.51  tff(c_3017, plain, (~v1_tops_1('#skF_3'('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_3014])).
% 7.33/2.51  tff(c_3020, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_38, c_3017])).
% 7.33/2.51  tff(c_3024, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_3020])).
% 7.33/2.51  tff(c_3026, plain, (v1_tops_1('#skF_3'('#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_3014])).
% 7.33/2.51  tff(c_3025, plain, (k2_pre_topc('#skF_5', '#skF_3'('#skF_5'))=k2_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_3014])).
% 7.33/2.51  tff(c_3313, plain, (![A_345, B_346]: (k2_pre_topc(A_345, B_346)=u1_struct_0(A_345) | ~v1_tops_1(B_346, A_345) | ~m1_subset_1(B_346, k1_zfmisc_1(u1_struct_0(A_345))) | ~l1_pre_topc(A_345))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.33/2.51  tff(c_3323, plain, (![B_346]: (k2_pre_topc('#skF_5', B_346)=u1_struct_0('#skF_5') | ~v1_tops_1(B_346, '#skF_5') | ~m1_subset_1(B_346, k1_zfmisc_1('#skF_6')) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_3313])).
% 7.33/2.51  tff(c_3342, plain, (![B_347]: (k2_pre_topc('#skF_5', B_347)='#skF_6' | ~v1_tops_1(B_347, '#skF_5') | ~m1_subset_1(B_347, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_129, c_3323])).
% 7.33/2.51  tff(c_3349, plain, (k2_pre_topc('#skF_5', '#skF_3'('#skF_5'))='#skF_6' | ~v1_tops_1('#skF_3'('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_144, c_3342])).
% 7.33/2.51  tff(c_3361, plain, (k2_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3026, c_3025, c_3349])).
% 7.33/2.51  tff(c_3666, plain, (![B_364, A_365]: (v4_pre_topc(B_364, A_365) | ~v3_pre_topc(k7_subset_1(u1_struct_0(A_365), k2_struct_0(A_365), B_364), A_365) | ~m1_subset_1(B_364, k1_zfmisc_1(u1_struct_0(A_365))) | ~l1_pre_topc(A_365))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.33/2.51  tff(c_3669, plain, (![B_364]: (v4_pre_topc(B_364, '#skF_5') | ~v3_pre_topc(k7_subset_1(u1_struct_0('#skF_5'), '#skF_6', B_364), '#skF_5') | ~m1_subset_1(B_364, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3361, c_3666])).
% 7.33/2.51  tff(c_3684, plain, (![B_366]: (v4_pre_topc(B_366, '#skF_5') | ~m1_subset_1(B_366, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_129, c_2865, c_2661, c_129, c_3669])).
% 7.33/2.51  tff(c_3691, plain, (v4_pre_topc('#skF_3'('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_144, c_3684])).
% 7.33/2.51  tff(c_3704, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2917, c_3691])).
% 7.33/2.51  tff(c_3705, plain, (k2_pre_topc('#skF_5', '#skF_3'('#skF_5'))='#skF_3'('#skF_5')), inference(splitRight, [status(thm)], [c_2913])).
% 7.33/2.51  tff(c_3801, plain, (![A_375, B_376]: (k2_pre_topc(A_375, B_376)=k2_struct_0(A_375) | ~v1_tops_1(B_376, A_375) | ~m1_subset_1(B_376, k1_zfmisc_1(u1_struct_0(A_375))) | ~l1_pre_topc(A_375))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.33/2.51  tff(c_3811, plain, (![B_376]: (k2_pre_topc('#skF_5', B_376)=k2_struct_0('#skF_5') | ~v1_tops_1(B_376, '#skF_5') | ~m1_subset_1(B_376, k1_zfmisc_1('#skF_6')) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_3801])).
% 7.33/2.51  tff(c_3832, plain, (![B_378]: (k2_pre_topc('#skF_5', B_378)=k2_struct_0('#skF_5') | ~v1_tops_1(B_378, '#skF_5') | ~m1_subset_1(B_378, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3811])).
% 7.33/2.51  tff(c_3839, plain, (k2_pre_topc('#skF_5', '#skF_3'('#skF_5'))=k2_struct_0('#skF_5') | ~v1_tops_1('#skF_3'('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_144, c_3832])).
% 7.33/2.51  tff(c_3850, plain, (k2_struct_0('#skF_5')='#skF_3'('#skF_5') | ~v1_tops_1('#skF_3'('#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3705, c_3839])).
% 7.33/2.51  tff(c_3853, plain, (~v1_tops_1('#skF_3'('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_3850])).
% 7.33/2.51  tff(c_3859, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_38, c_3853])).
% 7.33/2.51  tff(c_3865, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_3859])).
% 7.33/2.51  tff(c_3867, plain, (v1_tops_1('#skF_3'('#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_3850])).
% 7.33/2.51  tff(c_3875, plain, (![A_379, B_380]: (k2_pre_topc(A_379, B_380)=u1_struct_0(A_379) | ~v1_tops_1(B_380, A_379) | ~m1_subset_1(B_380, k1_zfmisc_1(u1_struct_0(A_379))) | ~l1_pre_topc(A_379))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.33/2.51  tff(c_3885, plain, (![B_380]: (k2_pre_topc('#skF_5', B_380)=u1_struct_0('#skF_5') | ~v1_tops_1(B_380, '#skF_5') | ~m1_subset_1(B_380, k1_zfmisc_1('#skF_6')) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_3875])).
% 7.33/2.51  tff(c_3908, plain, (![B_381]: (k2_pre_topc('#skF_5', B_381)='#skF_6' | ~v1_tops_1(B_381, '#skF_5') | ~m1_subset_1(B_381, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_129, c_3885])).
% 7.33/2.51  tff(c_3915, plain, (k2_pre_topc('#skF_5', '#skF_3'('#skF_5'))='#skF_6' | ~v1_tops_1('#skF_3'('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_144, c_3908])).
% 7.33/2.51  tff(c_3927, plain, ('#skF_3'('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3867, c_3705, c_3915])).
% 7.33/2.51  tff(c_3929, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2640, c_3927])).
% 7.33/2.51  tff(c_3931, plain, (v3_tex_2('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_74])).
% 7.33/2.51  tff(c_5471, plain, (![A_516, B_517]: (k2_pre_topc(A_516, B_517)=u1_struct_0(A_516) | ~v1_tops_1(B_517, A_516) | ~m1_subset_1(B_517, k1_zfmisc_1(u1_struct_0(A_516))) | ~l1_pre_topc(A_516))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.33/2.51  tff(c_5501, plain, (![A_518]: (k2_pre_topc(A_518, '#skF_3'(A_518))=u1_struct_0(A_518) | ~v1_tops_1('#skF_3'(A_518), A_518) | ~l1_pre_topc(A_518))), inference(resolution, [status(thm)], [c_40, c_5471])).
% 7.33/2.51  tff(c_5506, plain, (![A_519]: (k2_pre_topc(A_519, '#skF_3'(A_519))=u1_struct_0(A_519) | ~l1_pre_topc(A_519))), inference(resolution, [status(thm)], [c_38, c_5501])).
% 7.33/2.51  tff(c_5419, plain, (![A_508]: (k2_pre_topc(A_508, '#skF_3'(A_508))=k2_struct_0(A_508) | ~v1_tops_1('#skF_3'(A_508), A_508) | ~l1_pre_topc(A_508))), inference(resolution, [status(thm)], [c_40, c_5388])).
% 7.33/2.51  tff(c_5423, plain, (![A_25]: (k2_pre_topc(A_25, '#skF_3'(A_25))=k2_struct_0(A_25) | ~l1_pre_topc(A_25))), inference(resolution, [status(thm)], [c_38, c_5419])).
% 7.33/2.51  tff(c_5521, plain, (![A_520]: (u1_struct_0(A_520)=k2_struct_0(A_520) | ~l1_pre_topc(A_520) | ~l1_pre_topc(A_520))), inference(superposition, [status(thm), theory('equality')], [c_5506, c_5423])).
% 7.33/2.51  tff(c_5523, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_66, c_5521])).
% 7.33/2.51  tff(c_5526, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_5523])).
% 7.33/2.51  tff(c_5572, plain, (v1_subset_1('#skF_3'('#skF_5'), k2_struct_0('#skF_5')) | u1_struct_0('#skF_5')='#skF_3'('#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5526, c_3961])).
% 7.33/2.51  tff(c_5608, plain, (v1_subset_1('#skF_3'('#skF_5'), k2_struct_0('#skF_5')) | k2_struct_0('#skF_5')='#skF_3'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_5526, c_5572])).
% 7.33/2.51  tff(c_5713, plain, (k2_struct_0('#skF_5')='#skF_3'('#skF_5')), inference(splitLeft, [status(thm)], [c_5608])).
% 7.33/2.51  tff(c_5529, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_5526, c_64])).
% 7.33/2.51  tff(c_5719, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_5713, c_5529])).
% 7.33/2.51  tff(c_5722, plain, (u1_struct_0('#skF_5')='#skF_3'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5713, c_5526])).
% 7.33/2.51  tff(c_6229, plain, (![B_550, A_551]: (v1_tops_1(B_550, A_551) | ~v3_tex_2(B_550, A_551) | ~v3_pre_topc(B_550, A_551) | ~m1_subset_1(B_550, k1_zfmisc_1(u1_struct_0(A_551))) | ~l1_pre_topc(A_551) | ~v2_pre_topc(A_551) | v2_struct_0(A_551))), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.33/2.51  tff(c_6236, plain, (![B_550]: (v1_tops_1(B_550, '#skF_5') | ~v3_tex_2(B_550, '#skF_5') | ~v3_pre_topc(B_550, '#skF_5') | ~m1_subset_1(B_550, k1_zfmisc_1('#skF_3'('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5722, c_6229])).
% 7.33/2.51  tff(c_6257, plain, (![B_550]: (v1_tops_1(B_550, '#skF_5') | ~v3_tex_2(B_550, '#skF_5') | ~v3_pre_topc(B_550, '#skF_5') | ~m1_subset_1(B_550, k1_zfmisc_1('#skF_3'('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_6236])).
% 7.33/2.51  tff(c_6281, plain, (![B_554]: (v1_tops_1(B_554, '#skF_5') | ~v3_tex_2(B_554, '#skF_5') | ~v3_pre_topc(B_554, '#skF_5') | ~m1_subset_1(B_554, k1_zfmisc_1('#skF_3'('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_6257])).
% 7.33/2.51  tff(c_6288, plain, (v1_tops_1('#skF_6', '#skF_5') | ~v3_tex_2('#skF_6', '#skF_5') | ~v3_pre_topc('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_5719, c_6281])).
% 7.33/2.51  tff(c_6305, plain, (v1_tops_1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4115, c_3931, c_6288])).
% 7.33/2.51  tff(c_6307, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5418, c_6305])).
% 7.33/2.51  tff(c_6309, plain, (k2_struct_0('#skF_5')!='#skF_3'('#skF_5')), inference(splitRight, [status(thm)], [c_5608])).
% 7.33/2.51  tff(c_5578, plain, (m1_subset_1('#skF_3'('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5526, c_40])).
% 7.33/2.51  tff(c_5612, plain, (m1_subset_1('#skF_3'('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_5578])).
% 7.33/2.51  tff(c_5560, plain, (![B_21]: (k2_pre_topc('#skF_5', B_21)=B_21 | ~v4_pre_topc(B_21, '#skF_5') | ~m1_subset_1(B_21, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5526, c_32])).
% 7.33/2.51  tff(c_6507, plain, (![B_569]: (k2_pre_topc('#skF_5', B_569)=B_569 | ~v4_pre_topc(B_569, '#skF_5') | ~m1_subset_1(B_569, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_5560])).
% 7.33/2.51  tff(c_6526, plain, (k2_pre_topc('#skF_5', '#skF_3'('#skF_5'))='#skF_3'('#skF_5') | ~v4_pre_topc('#skF_3'('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_5612, c_6507])).
% 7.33/2.51  tff(c_6534, plain, (~v4_pre_topc('#skF_3'('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_6526])).
% 7.33/2.51  tff(c_5372, plain, (![C_504, A_505]: (v3_pre_topc(C_504, A_505) | ~v1_tdlat_3(A_505) | ~l1_pre_topc(A_505) | ~v2_pre_topc(A_505) | ~r1_tarski(C_504, u1_struct_0(A_505)))), inference(resolution, [status(thm)], [c_3940, c_4087])).
% 7.33/2.51  tff(c_5387, plain, (![A_505, B_2]: (v3_pre_topc(k4_xboole_0(u1_struct_0(A_505), B_2), A_505) | ~v1_tdlat_3(A_505) | ~l1_pre_topc(A_505) | ~v2_pre_topc(A_505))), inference(resolution, [status(thm)], [c_2, c_5372])).
% 7.33/2.51  tff(c_5536, plain, (![B_2]: (v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_5'), B_2), '#skF_5') | ~v1_tdlat_3('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5526, c_5387])).
% 7.33/2.51  tff(c_5584, plain, (![B_2]: (v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_5'), B_2), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_68, c_5536])).
% 7.33/2.51  tff(c_6651, plain, (![B_576, A_577]: (v4_pre_topc(B_576, A_577) | ~v3_pre_topc(k7_subset_1(u1_struct_0(A_577), k2_struct_0(A_577), B_576), A_577) | ~m1_subset_1(B_576, k1_zfmisc_1(u1_struct_0(A_577))) | ~l1_pre_topc(A_577))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.33/2.51  tff(c_6657, plain, (![B_576]: (v4_pre_topc(B_576, '#skF_5') | ~v3_pre_topc(k7_subset_1(k2_struct_0('#skF_5'), k2_struct_0('#skF_5'), B_576), '#skF_5') | ~m1_subset_1(B_576, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5526, c_6651])).
% 7.33/2.51  tff(c_6688, plain, (![B_578]: (v4_pre_topc(B_578, '#skF_5') | ~m1_subset_1(B_578, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_5526, c_5584, c_3989, c_6657])).
% 7.33/2.51  tff(c_6691, plain, (v4_pre_topc('#skF_3'('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_5612, c_6688])).
% 7.33/2.51  tff(c_6710, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6534, c_6691])).
% 7.33/2.51  tff(c_6711, plain, (k2_pre_topc('#skF_5', '#skF_3'('#skF_5'))='#skF_3'('#skF_5')), inference(splitRight, [status(thm)], [c_6526])).
% 7.33/2.51  tff(c_5505, plain, (![A_25]: (k2_pre_topc(A_25, '#skF_3'(A_25))=u1_struct_0(A_25) | ~l1_pre_topc(A_25))), inference(resolution, [status(thm)], [c_38, c_5501])).
% 7.33/2.51  tff(c_6790, plain, (u1_struct_0('#skF_5')='#skF_3'('#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6711, c_5505])).
% 7.33/2.51  tff(c_6803, plain, (k2_struct_0('#skF_5')='#skF_3'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_5526, c_6790])).
% 7.33/2.51  tff(c_6805, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6309, c_6803])).
% 7.33/2.51  tff(c_6807, plain, (v1_tops_1('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_5416])).
% 7.33/2.51  tff(c_6863, plain, (![A_588, B_589]: (k2_pre_topc(A_588, B_589)=u1_struct_0(A_588) | ~v1_tops_1(B_589, A_588) | ~m1_subset_1(B_589, k1_zfmisc_1(u1_struct_0(A_588))) | ~l1_pre_topc(A_588))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.33/2.51  tff(c_6880, plain, (k2_pre_topc('#skF_5', '#skF_6')=u1_struct_0('#skF_5') | ~v1_tops_1('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_64, c_6863])).
% 7.33/2.51  tff(c_6891, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_6807, c_5348, c_6880])).
% 7.33/2.51  tff(c_3930, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_74])).
% 7.33/2.51  tff(c_6894, plain, (v1_subset_1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6891, c_3930])).
% 7.33/2.51  tff(c_6898, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_6894])).
% 7.33/2.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.33/2.51  
% 7.33/2.51  Inference rules
% 7.33/2.51  ----------------------
% 7.33/2.51  #Ref     : 0
% 7.33/2.51  #Sup     : 1311
% 7.33/2.51  #Fact    : 0
% 7.33/2.51  #Define  : 0
% 7.33/2.51  #Split   : 24
% 7.33/2.51  #Chain   : 0
% 7.33/2.51  #Close   : 0
% 7.33/2.51  
% 7.33/2.51  Ordering : KBO
% 7.33/2.51  
% 7.33/2.51  Simplification rules
% 7.33/2.51  ----------------------
% 7.33/2.51  #Subsume      : 134
% 7.33/2.51  #Demod        : 1134
% 7.33/2.51  #Tautology    : 400
% 7.33/2.51  #SimpNegUnit  : 83
% 7.33/2.51  #BackRed      : 44
% 7.33/2.51  
% 7.33/2.51  #Partial instantiations: 0
% 7.33/2.51  #Strategies tried      : 1
% 7.33/2.51  
% 7.33/2.51  Timing (in seconds)
% 7.33/2.51  ----------------------
% 7.33/2.51  Preprocessing        : 0.40
% 7.33/2.51  Parsing              : 0.21
% 7.33/2.51  CNF conversion       : 0.03
% 7.33/2.51  Main loop            : 1.27
% 7.33/2.51  Inferencing          : 0.48
% 7.33/2.51  Reduction            : 0.40
% 7.33/2.51  Demodulation         : 0.27
% 7.33/2.51  BG Simplification    : 0.06
% 7.33/2.51  Subsumption          : 0.22
% 7.33/2.51  Abstraction          : 0.07
% 7.33/2.51  MUC search           : 0.00
% 7.33/2.51  Cooper               : 0.00
% 7.33/2.51  Total                : 1.74
% 7.33/2.51  Index Insertion      : 0.00
% 7.33/2.51  Index Deletion       : 0.00
% 7.33/2.51  Index Matching       : 0.00
% 7.33/2.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
