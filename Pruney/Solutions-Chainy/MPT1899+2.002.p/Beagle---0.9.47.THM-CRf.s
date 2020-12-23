%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:35 EST 2020

% Result     : Theorem 16.52s
% Output     : CNFRefutation 16.63s
% Verified   : 
% Statistics : Number of formulae       :  154 (3332 expanded)
%              Number of leaves         :   30 (1184 expanded)
%              Depth                    :   32
%              Number of atoms          :  767 (22137 expanded)
%              Number of equality atoms :   12 ( 419 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_tex_2 > v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v4_tex_2,type,(
    v4_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_172,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v1_tdlat_3(B)
              & m1_pre_topc(B,A) )
           => ? [C] :
                ( ~ v2_struct_0(C)
                & v1_pre_topc(C)
                & m1_pre_topc(C,A)
                & m1_pre_topc(B,C)
                & v4_tex_2(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tex_2)).

tff(f_32,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_87,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).

tff(f_142,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ~ ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ~ ( r1_tarski(B,C)
                      & v3_tex_2(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tex_2)).

tff(f_67,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ? [C] :
              ( ~ v2_struct_0(C)
              & v1_pre_topc(C)
              & m1_pre_topc(C,A)
              & B = u1_struct_0(C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).

tff(f_46,axiom,(
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

tff(f_119,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v3_tex_2(C,A)
                <=> v4_tex_2(B,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_tex_2)).

tff(f_102,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_34,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( m1_subset_1(u1_struct_0(B_3),k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_44,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_42,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_36,plain,(
    v1_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_230,plain,(
    ! [B_96,A_97] :
      ( v2_tex_2(u1_struct_0(B_96),A_97)
      | ~ v1_tdlat_3(B_96)
      | ~ m1_subset_1(u1_struct_0(B_96),k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ m1_pre_topc(B_96,A_97)
      | v2_struct_0(B_96)
      | ~ l1_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_240,plain,(
    ! [B_3,A_1] :
      ( v2_tex_2(u1_struct_0(B_3),A_1)
      | ~ v1_tdlat_3(B_3)
      | v2_struct_0(B_3)
      | v2_struct_0(A_1)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_230])).

tff(c_249,plain,(
    ! [A_100,B_101] :
      ( m1_subset_1('#skF_2'(A_100,B_101),k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ v2_tex_2(B_101,A_100)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100)
      | ~ v3_tdlat_3(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_10,plain,(
    ! [A_11,B_15] :
      ( m1_pre_topc('#skF_1'(A_11,B_15),A_11)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_11)))
      | v1_xboole_0(B_15)
      | ~ l1_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_330,plain,(
    ! [A_120,B_121] :
      ( m1_pre_topc('#skF_1'(A_120,'#skF_2'(A_120,B_121)),A_120)
      | v1_xboole_0('#skF_2'(A_120,B_121))
      | ~ v2_tex_2(B_121,A_120)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120)
      | ~ v3_tdlat_3(A_120)
      | ~ v2_pre_topc(A_120)
      | v2_struct_0(A_120) ) ),
    inference(resolution,[status(thm)],[c_249,c_10])).

tff(c_338,plain,(
    ! [A_1,B_3] :
      ( m1_pre_topc('#skF_1'(A_1,'#skF_2'(A_1,u1_struct_0(B_3))),A_1)
      | v1_xboole_0('#skF_2'(A_1,u1_struct_0(B_3)))
      | ~ v2_tex_2(u1_struct_0(B_3),A_1)
      | ~ v3_tdlat_3(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_330])).

tff(c_186,plain,(
    ! [B_85,A_86] :
      ( r1_tarski(B_85,'#skF_2'(A_86,B_85))
      | ~ v2_tex_2(B_85,A_86)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86)
      | ~ v3_tdlat_3(A_86)
      | ~ v2_pre_topc(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_191,plain,(
    ! [B_3,A_1] :
      ( r1_tarski(u1_struct_0(B_3),'#skF_2'(A_1,u1_struct_0(B_3)))
      | ~ v2_tex_2(u1_struct_0(B_3),A_1)
      | ~ v3_tdlat_3(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_186])).

tff(c_8,plain,(
    ! [A_11,B_15] :
      ( u1_struct_0('#skF_1'(A_11,B_15)) = B_15
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_11)))
      | v1_xboole_0(B_15)
      | ~ l1_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_376,plain,(
    ! [A_135,B_136] :
      ( u1_struct_0('#skF_1'(A_135,'#skF_2'(A_135,B_136))) = '#skF_2'(A_135,B_136)
      | v1_xboole_0('#skF_2'(A_135,B_136))
      | ~ v2_tex_2(B_136,A_135)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135)
      | ~ v3_tdlat_3(A_135)
      | ~ v2_pre_topc(A_135)
      | v2_struct_0(A_135) ) ),
    inference(resolution,[status(thm)],[c_249,c_8])).

tff(c_419,plain,(
    ! [A_148,B_149] :
      ( u1_struct_0('#skF_1'(A_148,'#skF_2'(A_148,u1_struct_0(B_149)))) = '#skF_2'(A_148,u1_struct_0(B_149))
      | v1_xboole_0('#skF_2'(A_148,u1_struct_0(B_149)))
      | ~ v2_tex_2(u1_struct_0(B_149),A_148)
      | ~ v3_tdlat_3(A_148)
      | ~ v2_pre_topc(A_148)
      | v2_struct_0(A_148)
      | ~ m1_pre_topc(B_149,A_148)
      | ~ l1_pre_topc(A_148) ) ),
    inference(resolution,[status(thm)],[c_2,c_376])).

tff(c_6,plain,(
    ! [B_8,C_10,A_4] :
      ( m1_pre_topc(B_8,C_10)
      | ~ r1_tarski(u1_struct_0(B_8),u1_struct_0(C_10))
      | ~ m1_pre_topc(C_10,A_4)
      | ~ m1_pre_topc(B_8,A_4)
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_13705,plain,(
    ! [B_743,A_744,B_745,A_746] :
      ( m1_pre_topc(B_743,'#skF_1'(A_744,'#skF_2'(A_744,u1_struct_0(B_745))))
      | ~ r1_tarski(u1_struct_0(B_743),'#skF_2'(A_744,u1_struct_0(B_745)))
      | ~ m1_pre_topc('#skF_1'(A_744,'#skF_2'(A_744,u1_struct_0(B_745))),A_746)
      | ~ m1_pre_topc(B_743,A_746)
      | ~ l1_pre_topc(A_746)
      | ~ v2_pre_topc(A_746)
      | v1_xboole_0('#skF_2'(A_744,u1_struct_0(B_745)))
      | ~ v2_tex_2(u1_struct_0(B_745),A_744)
      | ~ v3_tdlat_3(A_744)
      | ~ v2_pre_topc(A_744)
      | v2_struct_0(A_744)
      | ~ m1_pre_topc(B_745,A_744)
      | ~ l1_pre_topc(A_744) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_419,c_6])).

tff(c_13769,plain,(
    ! [B_747,A_748,A_749] :
      ( m1_pre_topc(B_747,'#skF_1'(A_748,'#skF_2'(A_748,u1_struct_0(B_747))))
      | ~ m1_pre_topc('#skF_1'(A_748,'#skF_2'(A_748,u1_struct_0(B_747))),A_749)
      | ~ m1_pre_topc(B_747,A_749)
      | ~ l1_pre_topc(A_749)
      | ~ v2_pre_topc(A_749)
      | v1_xboole_0('#skF_2'(A_748,u1_struct_0(B_747)))
      | ~ v2_tex_2(u1_struct_0(B_747),A_748)
      | ~ v3_tdlat_3(A_748)
      | ~ v2_pre_topc(A_748)
      | v2_struct_0(A_748)
      | ~ m1_pre_topc(B_747,A_748)
      | ~ l1_pre_topc(A_748) ) ),
    inference(resolution,[status(thm)],[c_191,c_13705])).

tff(c_13812,plain,(
    ! [B_750,A_751] :
      ( m1_pre_topc(B_750,'#skF_1'(A_751,'#skF_2'(A_751,u1_struct_0(B_750))))
      | v1_xboole_0('#skF_2'(A_751,u1_struct_0(B_750)))
      | ~ v2_tex_2(u1_struct_0(B_750),A_751)
      | ~ v3_tdlat_3(A_751)
      | ~ v2_pre_topc(A_751)
      | v2_struct_0(A_751)
      | ~ m1_pre_topc(B_750,A_751)
      | ~ l1_pre_topc(A_751) ) ),
    inference(resolution,[status(thm)],[c_338,c_13769])).

tff(c_167,plain,(
    ! [B_81,A_82] :
      ( v4_tex_2(B_81,A_82)
      | ~ v3_tex_2(u1_struct_0(B_81),A_82)
      | ~ m1_subset_1(u1_struct_0(B_81),k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ m1_pre_topc(B_81,A_82)
      | ~ l1_pre_topc(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_177,plain,(
    ! [B_3,A_1] :
      ( v4_tex_2(B_3,A_1)
      | ~ v3_tex_2(u1_struct_0(B_3),A_1)
      | v2_struct_0(A_1)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_167])).

tff(c_3292,plain,(
    ! [A_410,B_411,A_412] :
      ( v4_tex_2('#skF_1'(A_410,'#skF_2'(A_410,u1_struct_0(B_411))),A_412)
      | ~ v3_tex_2('#skF_2'(A_410,u1_struct_0(B_411)),A_412)
      | v2_struct_0(A_412)
      | ~ m1_pre_topc('#skF_1'(A_410,'#skF_2'(A_410,u1_struct_0(B_411))),A_412)
      | ~ l1_pre_topc(A_412)
      | v1_xboole_0('#skF_2'(A_410,u1_struct_0(B_411)))
      | ~ v2_tex_2(u1_struct_0(B_411),A_410)
      | ~ v3_tdlat_3(A_410)
      | ~ v2_pre_topc(A_410)
      | v2_struct_0(A_410)
      | ~ m1_pre_topc(B_411,A_410)
      | ~ l1_pre_topc(A_410) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_419,c_177])).

tff(c_32,plain,(
    ! [C_44] :
      ( ~ v4_tex_2(C_44,'#skF_3')
      | ~ m1_pre_topc('#skF_4',C_44)
      | ~ m1_pre_topc(C_44,'#skF_3')
      | ~ v1_pre_topc(C_44)
      | v2_struct_0(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_3299,plain,(
    ! [A_410,B_411] :
      ( ~ m1_pre_topc('#skF_4','#skF_1'(A_410,'#skF_2'(A_410,u1_struct_0(B_411))))
      | ~ v1_pre_topc('#skF_1'(A_410,'#skF_2'(A_410,u1_struct_0(B_411))))
      | v2_struct_0('#skF_1'(A_410,'#skF_2'(A_410,u1_struct_0(B_411))))
      | ~ v3_tex_2('#skF_2'(A_410,u1_struct_0(B_411)),'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_1'(A_410,'#skF_2'(A_410,u1_struct_0(B_411))),'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | v1_xboole_0('#skF_2'(A_410,u1_struct_0(B_411)))
      | ~ v2_tex_2(u1_struct_0(B_411),A_410)
      | ~ v3_tdlat_3(A_410)
      | ~ v2_pre_topc(A_410)
      | v2_struct_0(A_410)
      | ~ m1_pre_topc(B_411,A_410)
      | ~ l1_pre_topc(A_410) ) ),
    inference(resolution,[status(thm)],[c_3292,c_32])).

tff(c_3315,plain,(
    ! [A_410,B_411] :
      ( ~ m1_pre_topc('#skF_4','#skF_1'(A_410,'#skF_2'(A_410,u1_struct_0(B_411))))
      | ~ v1_pre_topc('#skF_1'(A_410,'#skF_2'(A_410,u1_struct_0(B_411))))
      | v2_struct_0('#skF_1'(A_410,'#skF_2'(A_410,u1_struct_0(B_411))))
      | ~ v3_tex_2('#skF_2'(A_410,u1_struct_0(B_411)),'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_1'(A_410,'#skF_2'(A_410,u1_struct_0(B_411))),'#skF_3')
      | v1_xboole_0('#skF_2'(A_410,u1_struct_0(B_411)))
      | ~ v2_tex_2(u1_struct_0(B_411),A_410)
      | ~ v3_tdlat_3(A_410)
      | ~ v2_pre_topc(A_410)
      | v2_struct_0(A_410)
      | ~ m1_pre_topc(B_411,A_410)
      | ~ l1_pre_topc(A_410) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3299])).

tff(c_3449,plain,(
    ! [A_427,B_428] :
      ( ~ m1_pre_topc('#skF_4','#skF_1'(A_427,'#skF_2'(A_427,u1_struct_0(B_428))))
      | ~ v1_pre_topc('#skF_1'(A_427,'#skF_2'(A_427,u1_struct_0(B_428))))
      | v2_struct_0('#skF_1'(A_427,'#skF_2'(A_427,u1_struct_0(B_428))))
      | ~ v3_tex_2('#skF_2'(A_427,u1_struct_0(B_428)),'#skF_3')
      | ~ m1_pre_topc('#skF_1'(A_427,'#skF_2'(A_427,u1_struct_0(B_428))),'#skF_3')
      | v1_xboole_0('#skF_2'(A_427,u1_struct_0(B_428)))
      | ~ v2_tex_2(u1_struct_0(B_428),A_427)
      | ~ v3_tdlat_3(A_427)
      | ~ v2_pre_topc(A_427)
      | v2_struct_0(A_427)
      | ~ m1_pre_topc(B_428,A_427)
      | ~ l1_pre_topc(A_427) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_3315])).

tff(c_3462,plain,(
    ! [B_3] :
      ( ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0(B_3))))
      | ~ v1_pre_topc('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0(B_3))))
      | v2_struct_0('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0(B_3))))
      | ~ v3_tex_2('#skF_2'('#skF_3',u1_struct_0(B_3)),'#skF_3')
      | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0(B_3)))
      | ~ v2_tex_2(u1_struct_0(B_3),'#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_3,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_338,c_3449])).

tff(c_3468,plain,(
    ! [B_3] :
      ( ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0(B_3))))
      | ~ v1_pre_topc('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0(B_3))))
      | v2_struct_0('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0(B_3))))
      | ~ v3_tex_2('#skF_2'('#skF_3',u1_struct_0(B_3)),'#skF_3')
      | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0(B_3)))
      | ~ v2_tex_2(u1_struct_0(B_3),'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_3,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_42,c_3462])).

tff(c_3469,plain,(
    ! [B_3] :
      ( ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0(B_3))))
      | ~ v1_pre_topc('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0(B_3))))
      | v2_struct_0('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0(B_3))))
      | ~ v3_tex_2('#skF_2'('#skF_3',u1_struct_0(B_3)),'#skF_3')
      | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0(B_3)))
      | ~ v2_tex_2(u1_struct_0(B_3),'#skF_3')
      | ~ m1_pre_topc(B_3,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_3468])).

tff(c_13886,plain,
    ( ~ v1_pre_topc('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4'))))
    | v2_struct_0('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4'))))
    | ~ v3_tex_2('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_3')
    | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_13812,c_3469])).

tff(c_14038,plain,
    ( ~ v1_pre_topc('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4'))))
    | v2_struct_0('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4'))))
    | ~ v3_tex_2('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_3')
    | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_44,c_42,c_13886])).

tff(c_14039,plain,
    ( ~ v1_pre_topc('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4'))))
    | v2_struct_0('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4'))))
    | ~ v3_tex_2('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_3')
    | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_14038])).

tff(c_14070,plain,(
    ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_14039])).

tff(c_14073,plain,
    ( ~ v1_tdlat_3('#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_240,c_14070])).

tff(c_14076,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_36,c_14073])).

tff(c_14078,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_38,c_14076])).

tff(c_14080,plain,(
    v2_tex_2(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_14039])).

tff(c_224,plain,(
    ! [A_94,B_95] :
      ( v3_tex_2('#skF_2'(A_94,B_95),A_94)
      | ~ v2_tex_2(B_95,A_94)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94)
      | ~ v3_tdlat_3(A_94)
      | ~ v2_pre_topc(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_229,plain,(
    ! [A_1,B_3] :
      ( v3_tex_2('#skF_2'(A_1,u1_struct_0(B_3)),A_1)
      | ~ v2_tex_2(u1_struct_0(B_3),A_1)
      | ~ v3_tdlat_3(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_224])).

tff(c_12,plain,(
    ! [A_11,B_15] :
      ( v1_pre_topc('#skF_1'(A_11,B_15))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_11)))
      | v1_xboole_0(B_15)
      | ~ l1_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_309,plain,(
    ! [A_114,B_115] :
      ( v1_pre_topc('#skF_1'(A_114,'#skF_2'(A_114,B_115)))
      | v1_xboole_0('#skF_2'(A_114,B_115))
      | ~ v2_tex_2(B_115,A_114)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114)
      | ~ v3_tdlat_3(A_114)
      | ~ v2_pre_topc(A_114)
      | v2_struct_0(A_114) ) ),
    inference(resolution,[status(thm)],[c_249,c_12])).

tff(c_317,plain,(
    ! [A_1,B_3] :
      ( v1_pre_topc('#skF_1'(A_1,'#skF_2'(A_1,u1_struct_0(B_3))))
      | v1_xboole_0('#skF_2'(A_1,u1_struct_0(B_3)))
      | ~ v2_tex_2(u1_struct_0(B_3),A_1)
      | ~ v3_tdlat_3(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_309])).

tff(c_14079,plain,
    ( ~ v3_tex_2('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_3')
    | ~ v1_pre_topc('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4'))))
    | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_14039])).

tff(c_14088,plain,(
    ~ v1_pre_topc('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4')))) ),
    inference(splitLeft,[status(thm)],[c_14079])).

tff(c_14104,plain,
    ( v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_317,c_14088])).

tff(c_14123,plain,
    ( v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_44,c_42,c_14080,c_14104])).

tff(c_14124,plain,(
    v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_14123])).

tff(c_20,plain,(
    ! [B_26,A_24] :
      ( ~ v3_tex_2(B_26,A_24)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ v1_xboole_0(B_26)
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_305,plain,(
    ! [A_112,B_113] :
      ( ~ v3_tex_2('#skF_2'(A_112,B_113),A_112)
      | ~ v1_xboole_0('#skF_2'(A_112,B_113))
      | ~ v2_tex_2(B_113,A_112)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112)
      | ~ v3_tdlat_3(A_112)
      | ~ v2_pre_topc(A_112)
      | v2_struct_0(A_112) ) ),
    inference(resolution,[status(thm)],[c_249,c_20])).

tff(c_319,plain,(
    ! [A_118,B_119] :
      ( ~ v1_xboole_0('#skF_2'(A_118,u1_struct_0(B_119)))
      | ~ m1_subset_1(u1_struct_0(B_119),k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ v2_tex_2(u1_struct_0(B_119),A_118)
      | ~ v3_tdlat_3(A_118)
      | ~ v2_pre_topc(A_118)
      | v2_struct_0(A_118)
      | ~ m1_pre_topc(B_119,A_118)
      | ~ l1_pre_topc(A_118) ) ),
    inference(resolution,[status(thm)],[c_229,c_305])).

tff(c_329,plain,(
    ! [A_1,B_3] :
      ( ~ v1_xboole_0('#skF_2'(A_1,u1_struct_0(B_3)))
      | ~ v2_tex_2(u1_struct_0(B_3),A_1)
      | ~ v3_tdlat_3(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_319])).

tff(c_14130,plain,
    ( ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14124,c_329])).

tff(c_14137,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_44,c_42,c_14080,c_14130])).

tff(c_14139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_14137])).

tff(c_14140,plain,
    ( ~ v3_tex_2('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_3')
    | v2_struct_0('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4'))))
    | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_14079])).

tff(c_14142,plain,(
    ~ v3_tex_2('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_14140])).

tff(c_14245,plain,
    ( ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_229,c_14142])).

tff(c_14260,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_44,c_42,c_14080,c_14245])).

tff(c_14262,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_14260])).

tff(c_14264,plain,(
    v3_tex_2('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_14140])).

tff(c_274,plain,(
    ! [A_100,B_101] :
      ( ~ v3_tex_2('#skF_2'(A_100,B_101),A_100)
      | ~ v1_xboole_0('#skF_2'(A_100,B_101))
      | ~ v2_tex_2(B_101,A_100)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100)
      | ~ v3_tdlat_3(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(resolution,[status(thm)],[c_249,c_20])).

tff(c_14266,plain,
    ( ~ v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_14264,c_274])).

tff(c_14269,plain,
    ( ~ v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_14080,c_14266])).

tff(c_14270,plain,
    ( ~ v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_14269])).

tff(c_14271,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_14270])).

tff(c_14274,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_14271])).

tff(c_14278,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_14274])).

tff(c_14279,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_14270])).

tff(c_13811,plain,(
    ! [B_3,A_1] :
      ( m1_pre_topc(B_3,'#skF_1'(A_1,'#skF_2'(A_1,u1_struct_0(B_3))))
      | v1_xboole_0('#skF_2'(A_1,u1_struct_0(B_3)))
      | ~ v2_tex_2(u1_struct_0(B_3),A_1)
      | ~ v3_tdlat_3(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(resolution,[status(thm)],[c_338,c_13769])).

tff(c_14280,plain,(
    m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_14270])).

tff(c_273,plain,(
    ! [A_100,B_101] :
      ( m1_pre_topc('#skF_1'(A_100,'#skF_2'(A_100,B_101)),A_100)
      | v1_xboole_0('#skF_2'(A_100,B_101))
      | ~ v2_tex_2(B_101,A_100)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100)
      | ~ v3_tdlat_3(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(resolution,[status(thm)],[c_249,c_10])).

tff(c_14284,plain,
    ( m1_pre_topc('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4'))),'#skF_3')
    | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_14280,c_273])).

tff(c_14311,plain,
    ( m1_pre_topc('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4'))),'#skF_3')
    | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_14080,c_14284])).

tff(c_14312,plain,(
    m1_pre_topc('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4'))),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_14279,c_14311])).

tff(c_275,plain,(
    ! [A_100,B_101] :
      ( u1_struct_0('#skF_1'(A_100,'#skF_2'(A_100,B_101))) = '#skF_2'(A_100,B_101)
      | v1_xboole_0('#skF_2'(A_100,B_101))
      | ~ v2_tex_2(B_101,A_100)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100)
      | ~ v3_tdlat_3(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(resolution,[status(thm)],[c_249,c_8])).

tff(c_14282,plain,
    ( u1_struct_0('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4')))) = '#skF_2'('#skF_3',u1_struct_0('#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_14280,c_275])).

tff(c_14307,plain,
    ( u1_struct_0('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4')))) = '#skF_2'('#skF_3',u1_struct_0('#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_14080,c_14282])).

tff(c_14308,plain,(
    u1_struct_0('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4')))) = '#skF_2'('#skF_3',u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_14279,c_14307])).

tff(c_71,plain,(
    ! [A_60,B_61] :
      ( m1_pre_topc('#skF_1'(A_60,B_61),A_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | v1_xboole_0(B_61)
      | ~ l1_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_74,plain,(
    ! [A_1,B_3] :
      ( m1_pre_topc('#skF_1'(A_1,u1_struct_0(B_3)),A_1)
      | v1_xboole_0(u1_struct_0(B_3))
      | v2_struct_0(A_1)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_71])).

tff(c_61,plain,(
    ! [A_56,B_57] :
      ( u1_struct_0('#skF_1'(A_56,B_57)) = B_57
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | v1_xboole_0(B_57)
      | ~ l1_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_65,plain,(
    ! [A_1,B_3] :
      ( u1_struct_0('#skF_1'(A_1,u1_struct_0(B_3))) = u1_struct_0(B_3)
      | v1_xboole_0(u1_struct_0(B_3))
      | v2_struct_0(A_1)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_61])).

tff(c_178,plain,(
    ! [B_83,A_84] :
      ( v4_tex_2(B_83,A_84)
      | ~ v3_tex_2(u1_struct_0(B_83),A_84)
      | v2_struct_0(A_84)
      | ~ m1_pre_topc(B_83,A_84)
      | ~ l1_pre_topc(A_84) ) ),
    inference(resolution,[status(thm)],[c_2,c_167])).

tff(c_184,plain,(
    ! [A_1,B_3,A_84] :
      ( v4_tex_2('#skF_1'(A_1,u1_struct_0(B_3)),A_84)
      | ~ v3_tex_2(u1_struct_0(B_3),A_84)
      | v2_struct_0(A_84)
      | ~ m1_pre_topc('#skF_1'(A_1,u1_struct_0(B_3)),A_84)
      | ~ l1_pre_topc(A_84)
      | v1_xboole_0(u1_struct_0(B_3))
      | v2_struct_0(A_1)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_178])).

tff(c_145,plain,(
    ! [B_75,A_76] :
      ( v3_tex_2(u1_struct_0(B_75),A_76)
      | ~ v4_tex_2(B_75,A_76)
      | ~ m1_subset_1(u1_struct_0(B_75),k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ m1_pre_topc(B_75,A_76)
      | ~ l1_pre_topc(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_155,plain,(
    ! [B_3,A_1] :
      ( v3_tex_2(u1_struct_0(B_3),A_1)
      | ~ v4_tex_2(B_3,A_1)
      | v2_struct_0(A_1)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_145])).

tff(c_49,plain,(
    ! [A_48,B_49] :
      ( v1_pre_topc('#skF_1'(A_48,B_49))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | v1_xboole_0(B_49)
      | ~ l1_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_53,plain,(
    ! [A_1,B_3] :
      ( v1_pre_topc('#skF_1'(A_1,u1_struct_0(B_3)))
      | v1_xboole_0(u1_struct_0(B_3))
      | v2_struct_0(A_1)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_49])).

tff(c_403,plain,(
    ! [A_145,B_146,A_147] :
      ( v4_tex_2('#skF_1'(A_145,u1_struct_0(B_146)),A_147)
      | ~ v3_tex_2(u1_struct_0(B_146),A_147)
      | v2_struct_0(A_147)
      | ~ m1_pre_topc('#skF_1'(A_145,u1_struct_0(B_146)),A_147)
      | ~ l1_pre_topc(A_147)
      | v1_xboole_0(u1_struct_0(B_146))
      | v2_struct_0(A_145)
      | ~ m1_pre_topc(B_146,A_145)
      | ~ l1_pre_topc(A_145) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_178])).

tff(c_410,plain,(
    ! [A_145,B_146] :
      ( ~ m1_pre_topc('#skF_4','#skF_1'(A_145,u1_struct_0(B_146)))
      | ~ v1_pre_topc('#skF_1'(A_145,u1_struct_0(B_146)))
      | v2_struct_0('#skF_1'(A_145,u1_struct_0(B_146)))
      | ~ v3_tex_2(u1_struct_0(B_146),'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_1'(A_145,u1_struct_0(B_146)),'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | v1_xboole_0(u1_struct_0(B_146))
      | v2_struct_0(A_145)
      | ~ m1_pre_topc(B_146,A_145)
      | ~ l1_pre_topc(A_145) ) ),
    inference(resolution,[status(thm)],[c_403,c_32])).

tff(c_417,plain,(
    ! [A_145,B_146] :
      ( ~ m1_pre_topc('#skF_4','#skF_1'(A_145,u1_struct_0(B_146)))
      | ~ v1_pre_topc('#skF_1'(A_145,u1_struct_0(B_146)))
      | v2_struct_0('#skF_1'(A_145,u1_struct_0(B_146)))
      | ~ v3_tex_2(u1_struct_0(B_146),'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_1'(A_145,u1_struct_0(B_146)),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_146))
      | v2_struct_0(A_145)
      | ~ m1_pre_topc(B_146,A_145)
      | ~ l1_pre_topc(A_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_410])).

tff(c_559,plain,(
    ! [A_153,B_154] :
      ( ~ m1_pre_topc('#skF_4','#skF_1'(A_153,u1_struct_0(B_154)))
      | ~ v1_pre_topc('#skF_1'(A_153,u1_struct_0(B_154)))
      | v2_struct_0('#skF_1'(A_153,u1_struct_0(B_154)))
      | ~ v3_tex_2(u1_struct_0(B_154),'#skF_3')
      | ~ m1_pre_topc('#skF_1'(A_153,u1_struct_0(B_154)),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_154))
      | v2_struct_0(A_153)
      | ~ m1_pre_topc(B_154,A_153)
      | ~ l1_pre_topc(A_153) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_417])).

tff(c_569,plain,(
    ! [B_3] :
      ( ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3',u1_struct_0(B_3)))
      | ~ v1_pre_topc('#skF_1'('#skF_3',u1_struct_0(B_3)))
      | v2_struct_0('#skF_1'('#skF_3',u1_struct_0(B_3)))
      | ~ v3_tex_2(u1_struct_0(B_3),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_3))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_3,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_74,c_559])).

tff(c_572,plain,(
    ! [B_3] :
      ( ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3',u1_struct_0(B_3)))
      | ~ v1_pre_topc('#skF_1'('#skF_3',u1_struct_0(B_3)))
      | v2_struct_0('#skF_1'('#skF_3',u1_struct_0(B_3)))
      | ~ v3_tex_2(u1_struct_0(B_3),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_3))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_3,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_569])).

tff(c_574,plain,(
    ! [B_155] :
      ( ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3',u1_struct_0(B_155)))
      | ~ v1_pre_topc('#skF_1'('#skF_3',u1_struct_0(B_155)))
      | v2_struct_0('#skF_1'('#skF_3',u1_struct_0(B_155)))
      | ~ v3_tex_2(u1_struct_0(B_155),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_155))
      | ~ m1_pre_topc(B_155,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_572])).

tff(c_1427,plain,(
    ! [B_249,A_250] :
      ( ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3',u1_struct_0(B_249)))
      | ~ v1_pre_topc('#skF_1'('#skF_3',u1_struct_0('#skF_1'(A_250,u1_struct_0(B_249)))))
      | v2_struct_0('#skF_1'('#skF_3',u1_struct_0('#skF_1'(A_250,u1_struct_0(B_249)))))
      | ~ v3_tex_2(u1_struct_0('#skF_1'(A_250,u1_struct_0(B_249))),'#skF_3')
      | v1_xboole_0(u1_struct_0('#skF_1'(A_250,u1_struct_0(B_249))))
      | ~ m1_pre_topc('#skF_1'(A_250,u1_struct_0(B_249)),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_249))
      | v2_struct_0(A_250)
      | ~ m1_pre_topc(B_249,A_250)
      | ~ l1_pre_topc(A_250) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_574])).

tff(c_54,plain,(
    ! [A_50,B_51] :
      ( ~ v2_struct_0('#skF_1'(A_50,B_51))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | v1_xboole_0(B_51)
      | ~ l1_pre_topc(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_58,plain,(
    ! [A_1,B_3] :
      ( ~ v2_struct_0('#skF_1'(A_1,u1_struct_0(B_3)))
      | v1_xboole_0(u1_struct_0(B_3))
      | v2_struct_0(A_1)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_54])).

tff(c_1430,plain,(
    ! [B_249,A_250] :
      ( v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3',u1_struct_0(B_249)))
      | ~ v1_pre_topc('#skF_1'('#skF_3',u1_struct_0('#skF_1'(A_250,u1_struct_0(B_249)))))
      | ~ v3_tex_2(u1_struct_0('#skF_1'(A_250,u1_struct_0(B_249))),'#skF_3')
      | v1_xboole_0(u1_struct_0('#skF_1'(A_250,u1_struct_0(B_249))))
      | ~ m1_pre_topc('#skF_1'(A_250,u1_struct_0(B_249)),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_249))
      | v2_struct_0(A_250)
      | ~ m1_pre_topc(B_249,A_250)
      | ~ l1_pre_topc(A_250) ) ),
    inference(resolution,[status(thm)],[c_1427,c_58])).

tff(c_1449,plain,(
    ! [B_249,A_250] :
      ( v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3',u1_struct_0(B_249)))
      | ~ v1_pre_topc('#skF_1'('#skF_3',u1_struct_0('#skF_1'(A_250,u1_struct_0(B_249)))))
      | ~ v3_tex_2(u1_struct_0('#skF_1'(A_250,u1_struct_0(B_249))),'#skF_3')
      | v1_xboole_0(u1_struct_0('#skF_1'(A_250,u1_struct_0(B_249))))
      | ~ m1_pre_topc('#skF_1'(A_250,u1_struct_0(B_249)),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_249))
      | v2_struct_0(A_250)
      | ~ m1_pre_topc(B_249,A_250)
      | ~ l1_pre_topc(A_250) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1430])).

tff(c_1856,plain,(
    ! [B_271,A_272] :
      ( ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3',u1_struct_0(B_271)))
      | ~ v1_pre_topc('#skF_1'('#skF_3',u1_struct_0('#skF_1'(A_272,u1_struct_0(B_271)))))
      | ~ v3_tex_2(u1_struct_0('#skF_1'(A_272,u1_struct_0(B_271))),'#skF_3')
      | v1_xboole_0(u1_struct_0('#skF_1'(A_272,u1_struct_0(B_271))))
      | ~ m1_pre_topc('#skF_1'(A_272,u1_struct_0(B_271)),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_271))
      | v2_struct_0(A_272)
      | ~ m1_pre_topc(B_271,A_272)
      | ~ l1_pre_topc(A_272) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1449])).

tff(c_1878,plain,(
    ! [B_271,A_272] :
      ( ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3',u1_struct_0(B_271)))
      | ~ v3_tex_2(u1_struct_0('#skF_1'(A_272,u1_struct_0(B_271))),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_271))
      | v2_struct_0(A_272)
      | ~ m1_pre_topc(B_271,A_272)
      | ~ l1_pre_topc(A_272)
      | v1_xboole_0(u1_struct_0('#skF_1'(A_272,u1_struct_0(B_271))))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_1'(A_272,u1_struct_0(B_271)),'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_53,c_1856])).

tff(c_1881,plain,(
    ! [B_271,A_272] :
      ( ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3',u1_struct_0(B_271)))
      | ~ v3_tex_2(u1_struct_0('#skF_1'(A_272,u1_struct_0(B_271))),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_271))
      | v2_struct_0(A_272)
      | ~ m1_pre_topc(B_271,A_272)
      | ~ l1_pre_topc(A_272)
      | v1_xboole_0(u1_struct_0('#skF_1'(A_272,u1_struct_0(B_271))))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_1'(A_272,u1_struct_0(B_271)),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1878])).

tff(c_1883,plain,(
    ! [B_273,A_274] :
      ( ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3',u1_struct_0(B_273)))
      | ~ v3_tex_2(u1_struct_0('#skF_1'(A_274,u1_struct_0(B_273))),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_273))
      | v2_struct_0(A_274)
      | ~ m1_pre_topc(B_273,A_274)
      | ~ l1_pre_topc(A_274)
      | v1_xboole_0(u1_struct_0('#skF_1'(A_274,u1_struct_0(B_273))))
      | ~ m1_pre_topc('#skF_1'(A_274,u1_struct_0(B_273)),'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1881])).

tff(c_1899,plain,(
    ! [B_273,A_274] :
      ( ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3',u1_struct_0(B_273)))
      | v1_xboole_0(u1_struct_0(B_273))
      | v2_struct_0(A_274)
      | ~ m1_pre_topc(B_273,A_274)
      | ~ l1_pre_topc(A_274)
      | v1_xboole_0(u1_struct_0('#skF_1'(A_274,u1_struct_0(B_273))))
      | ~ v4_tex_2('#skF_1'(A_274,u1_struct_0(B_273)),'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_1'(A_274,u1_struct_0(B_273)),'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_155,c_1883])).

tff(c_1908,plain,(
    ! [B_273,A_274] :
      ( ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3',u1_struct_0(B_273)))
      | v1_xboole_0(u1_struct_0(B_273))
      | v2_struct_0(A_274)
      | ~ m1_pre_topc(B_273,A_274)
      | ~ l1_pre_topc(A_274)
      | v1_xboole_0(u1_struct_0('#skF_1'(A_274,u1_struct_0(B_273))))
      | ~ v4_tex_2('#skF_1'(A_274,u1_struct_0(B_273)),'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_1'(A_274,u1_struct_0(B_273)),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1899])).

tff(c_1910,plain,(
    ! [B_275,A_276] :
      ( ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3',u1_struct_0(B_275)))
      | v1_xboole_0(u1_struct_0(B_275))
      | v2_struct_0(A_276)
      | ~ m1_pre_topc(B_275,A_276)
      | ~ l1_pre_topc(A_276)
      | v1_xboole_0(u1_struct_0('#skF_1'(A_276,u1_struct_0(B_275))))
      | ~ v4_tex_2('#skF_1'(A_276,u1_struct_0(B_275)),'#skF_3')
      | ~ m1_pre_topc('#skF_1'(A_276,u1_struct_0(B_275)),'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1908])).

tff(c_2174,plain,(
    ! [B_294,A_295] :
      ( ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3',u1_struct_0(B_294)))
      | v1_xboole_0(u1_struct_0(B_294))
      | v2_struct_0(A_295)
      | ~ m1_pre_topc(B_294,A_295)
      | ~ l1_pre_topc(A_295)
      | v1_xboole_0(u1_struct_0(B_294))
      | ~ v4_tex_2('#skF_1'(A_295,u1_struct_0(B_294)),'#skF_3')
      | ~ m1_pre_topc('#skF_1'(A_295,u1_struct_0(B_294)),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_294))
      | v2_struct_0(A_295)
      | ~ m1_pre_topc(B_294,A_295)
      | ~ l1_pre_topc(A_295) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_1910])).

tff(c_2187,plain,(
    ! [B_3,A_1] :
      ( ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3',u1_struct_0(B_3)))
      | ~ v3_tex_2(u1_struct_0(B_3),'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_1'(A_1,u1_struct_0(B_3)),'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | v1_xboole_0(u1_struct_0(B_3))
      | v2_struct_0(A_1)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(resolution,[status(thm)],[c_184,c_2174])).

tff(c_2193,plain,(
    ! [B_3,A_1] :
      ( ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3',u1_struct_0(B_3)))
      | ~ v3_tex_2(u1_struct_0(B_3),'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_1'(A_1,u1_struct_0(B_3)),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_3))
      | v2_struct_0(A_1)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2187])).

tff(c_2195,plain,(
    ! [B_296,A_297] :
      ( ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3',u1_struct_0(B_296)))
      | ~ v3_tex_2(u1_struct_0(B_296),'#skF_3')
      | ~ m1_pre_topc('#skF_1'(A_297,u1_struct_0(B_296)),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_296))
      | v2_struct_0(A_297)
      | ~ m1_pre_topc(B_296,A_297)
      | ~ l1_pre_topc(A_297) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_2193])).

tff(c_2211,plain,(
    ! [B_3] :
      ( ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3',u1_struct_0(B_3)))
      | ~ v3_tex_2(u1_struct_0(B_3),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_3))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_3,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_74,c_2195])).

tff(c_2214,plain,(
    ! [B_3] :
      ( ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3',u1_struct_0(B_3)))
      | ~ v3_tex_2(u1_struct_0(B_3),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_3))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_3,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2211])).

tff(c_2215,plain,(
    ! [B_3] :
      ( ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3',u1_struct_0(B_3)))
      | ~ v3_tex_2(u1_struct_0(B_3),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_3))
      | ~ m1_pre_topc(B_3,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_2214])).

tff(c_15114,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4'))))
    | ~ v3_tex_2(u1_struct_0('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4')))),'#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4')))))
    | ~ m1_pre_topc('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4'))),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14308,c_2215])).

tff(c_15792,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4'))))
    | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14312,c_14308,c_14264,c_14308,c_15114])).

tff(c_15793,plain,(
    ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4')))) ),
    inference(negUnitSimplification,[status(thm)],[c_14279,c_15792])).

tff(c_15974,plain,
    ( v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_13811,c_15793])).

tff(c_15977,plain,
    ( v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_44,c_42,c_14080,c_15974])).

tff(c_15979,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_14279,c_15977])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:43:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.52/8.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.63/8.06  
% 16.63/8.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.63/8.06  %$ v4_tex_2 > v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 16.63/8.06  
% 16.63/8.06  %Foreground sorts:
% 16.63/8.06  
% 16.63/8.06  
% 16.63/8.06  %Background operators:
% 16.63/8.06  
% 16.63/8.06  
% 16.63/8.06  %Foreground operators:
% 16.63/8.06  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 16.63/8.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.63/8.06  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 16.63/8.06  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 16.63/8.06  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 16.63/8.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.63/8.06  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 16.63/8.06  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 16.63/8.06  tff('#skF_3', type, '#skF_3': $i).
% 16.63/8.06  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 16.63/8.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.63/8.06  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 16.63/8.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.63/8.06  tff('#skF_4', type, '#skF_4': $i).
% 16.63/8.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.63/8.06  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 16.63/8.06  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 16.63/8.06  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 16.63/8.06  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 16.63/8.06  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 16.63/8.06  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 16.63/8.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.63/8.06  
% 16.63/8.08  tff(f_172, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v1_tdlat_3(B)) & m1_pre_topc(B, A)) => (?[C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) & m1_pre_topc(B, C)) & v4_tex_2(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tex_2)).
% 16.63/8.08  tff(f_32, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 16.63/8.08  tff(f_87, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_tex_2)).
% 16.63/8.08  tff(f_142, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tex_2)).
% 16.63/8.08  tff(f_67, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (?[C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) & (B = u1_struct_0(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_tsep_1)).
% 16.63/8.08  tff(f_46, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 16.63/8.08  tff(f_119, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v3_tex_2(C, A) <=> v4_tex_2(B, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_tex_2)).
% 16.63/8.08  tff(f_102, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 16.63/8.08  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_172])).
% 16.63/8.08  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_172])).
% 16.63/8.08  tff(c_34, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_172])).
% 16.63/8.08  tff(c_2, plain, (![B_3, A_1]: (m1_subset_1(u1_struct_0(B_3), k1_zfmisc_1(u1_struct_0(A_1))) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.63/8.08  tff(c_44, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_172])).
% 16.63/8.08  tff(c_42, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_172])).
% 16.63/8.08  tff(c_38, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_172])).
% 16.63/8.08  tff(c_36, plain, (v1_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_172])).
% 16.63/8.08  tff(c_230, plain, (![B_96, A_97]: (v2_tex_2(u1_struct_0(B_96), A_97) | ~v1_tdlat_3(B_96) | ~m1_subset_1(u1_struct_0(B_96), k1_zfmisc_1(u1_struct_0(A_97))) | ~m1_pre_topc(B_96, A_97) | v2_struct_0(B_96) | ~l1_pre_topc(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_87])).
% 16.63/8.08  tff(c_240, plain, (![B_3, A_1]: (v2_tex_2(u1_struct_0(B_3), A_1) | ~v1_tdlat_3(B_3) | v2_struct_0(B_3) | v2_struct_0(A_1) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(resolution, [status(thm)], [c_2, c_230])).
% 16.63/8.08  tff(c_249, plain, (![A_100, B_101]: (m1_subset_1('#skF_2'(A_100, B_101), k1_zfmisc_1(u1_struct_0(A_100))) | ~v2_tex_2(B_101, A_100) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100) | ~v3_tdlat_3(A_100) | ~v2_pre_topc(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_142])).
% 16.63/8.08  tff(c_10, plain, (![A_11, B_15]: (m1_pre_topc('#skF_1'(A_11, B_15), A_11) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_11))) | v1_xboole_0(B_15) | ~l1_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.63/8.08  tff(c_330, plain, (![A_120, B_121]: (m1_pre_topc('#skF_1'(A_120, '#skF_2'(A_120, B_121)), A_120) | v1_xboole_0('#skF_2'(A_120, B_121)) | ~v2_tex_2(B_121, A_120) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_pre_topc(A_120) | ~v3_tdlat_3(A_120) | ~v2_pre_topc(A_120) | v2_struct_0(A_120))), inference(resolution, [status(thm)], [c_249, c_10])).
% 16.63/8.08  tff(c_338, plain, (![A_1, B_3]: (m1_pre_topc('#skF_1'(A_1, '#skF_2'(A_1, u1_struct_0(B_3))), A_1) | v1_xboole_0('#skF_2'(A_1, u1_struct_0(B_3))) | ~v2_tex_2(u1_struct_0(B_3), A_1) | ~v3_tdlat_3(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(resolution, [status(thm)], [c_2, c_330])).
% 16.63/8.08  tff(c_186, plain, (![B_85, A_86]: (r1_tarski(B_85, '#skF_2'(A_86, B_85)) | ~v2_tex_2(B_85, A_86) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86) | ~v3_tdlat_3(A_86) | ~v2_pre_topc(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_142])).
% 16.63/8.08  tff(c_191, plain, (![B_3, A_1]: (r1_tarski(u1_struct_0(B_3), '#skF_2'(A_1, u1_struct_0(B_3))) | ~v2_tex_2(u1_struct_0(B_3), A_1) | ~v3_tdlat_3(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(resolution, [status(thm)], [c_2, c_186])).
% 16.63/8.08  tff(c_8, plain, (![A_11, B_15]: (u1_struct_0('#skF_1'(A_11, B_15))=B_15 | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_11))) | v1_xboole_0(B_15) | ~l1_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.63/8.08  tff(c_376, plain, (![A_135, B_136]: (u1_struct_0('#skF_1'(A_135, '#skF_2'(A_135, B_136)))='#skF_2'(A_135, B_136) | v1_xboole_0('#skF_2'(A_135, B_136)) | ~v2_tex_2(B_136, A_135) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135) | ~v3_tdlat_3(A_135) | ~v2_pre_topc(A_135) | v2_struct_0(A_135))), inference(resolution, [status(thm)], [c_249, c_8])).
% 16.63/8.08  tff(c_419, plain, (![A_148, B_149]: (u1_struct_0('#skF_1'(A_148, '#skF_2'(A_148, u1_struct_0(B_149))))='#skF_2'(A_148, u1_struct_0(B_149)) | v1_xboole_0('#skF_2'(A_148, u1_struct_0(B_149))) | ~v2_tex_2(u1_struct_0(B_149), A_148) | ~v3_tdlat_3(A_148) | ~v2_pre_topc(A_148) | v2_struct_0(A_148) | ~m1_pre_topc(B_149, A_148) | ~l1_pre_topc(A_148))), inference(resolution, [status(thm)], [c_2, c_376])).
% 16.63/8.08  tff(c_6, plain, (![B_8, C_10, A_4]: (m1_pre_topc(B_8, C_10) | ~r1_tarski(u1_struct_0(B_8), u1_struct_0(C_10)) | ~m1_pre_topc(C_10, A_4) | ~m1_pre_topc(B_8, A_4) | ~l1_pre_topc(A_4) | ~v2_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_46])).
% 16.63/8.08  tff(c_13705, plain, (![B_743, A_744, B_745, A_746]: (m1_pre_topc(B_743, '#skF_1'(A_744, '#skF_2'(A_744, u1_struct_0(B_745)))) | ~r1_tarski(u1_struct_0(B_743), '#skF_2'(A_744, u1_struct_0(B_745))) | ~m1_pre_topc('#skF_1'(A_744, '#skF_2'(A_744, u1_struct_0(B_745))), A_746) | ~m1_pre_topc(B_743, A_746) | ~l1_pre_topc(A_746) | ~v2_pre_topc(A_746) | v1_xboole_0('#skF_2'(A_744, u1_struct_0(B_745))) | ~v2_tex_2(u1_struct_0(B_745), A_744) | ~v3_tdlat_3(A_744) | ~v2_pre_topc(A_744) | v2_struct_0(A_744) | ~m1_pre_topc(B_745, A_744) | ~l1_pre_topc(A_744))), inference(superposition, [status(thm), theory('equality')], [c_419, c_6])).
% 16.63/8.08  tff(c_13769, plain, (![B_747, A_748, A_749]: (m1_pre_topc(B_747, '#skF_1'(A_748, '#skF_2'(A_748, u1_struct_0(B_747)))) | ~m1_pre_topc('#skF_1'(A_748, '#skF_2'(A_748, u1_struct_0(B_747))), A_749) | ~m1_pre_topc(B_747, A_749) | ~l1_pre_topc(A_749) | ~v2_pre_topc(A_749) | v1_xboole_0('#skF_2'(A_748, u1_struct_0(B_747))) | ~v2_tex_2(u1_struct_0(B_747), A_748) | ~v3_tdlat_3(A_748) | ~v2_pre_topc(A_748) | v2_struct_0(A_748) | ~m1_pre_topc(B_747, A_748) | ~l1_pre_topc(A_748))), inference(resolution, [status(thm)], [c_191, c_13705])).
% 16.63/8.08  tff(c_13812, plain, (![B_750, A_751]: (m1_pre_topc(B_750, '#skF_1'(A_751, '#skF_2'(A_751, u1_struct_0(B_750)))) | v1_xboole_0('#skF_2'(A_751, u1_struct_0(B_750))) | ~v2_tex_2(u1_struct_0(B_750), A_751) | ~v3_tdlat_3(A_751) | ~v2_pre_topc(A_751) | v2_struct_0(A_751) | ~m1_pre_topc(B_750, A_751) | ~l1_pre_topc(A_751))), inference(resolution, [status(thm)], [c_338, c_13769])).
% 16.63/8.08  tff(c_167, plain, (![B_81, A_82]: (v4_tex_2(B_81, A_82) | ~v3_tex_2(u1_struct_0(B_81), A_82) | ~m1_subset_1(u1_struct_0(B_81), k1_zfmisc_1(u1_struct_0(A_82))) | ~m1_pre_topc(B_81, A_82) | ~l1_pre_topc(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_119])).
% 16.63/8.08  tff(c_177, plain, (![B_3, A_1]: (v4_tex_2(B_3, A_1) | ~v3_tex_2(u1_struct_0(B_3), A_1) | v2_struct_0(A_1) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(resolution, [status(thm)], [c_2, c_167])).
% 16.63/8.08  tff(c_3292, plain, (![A_410, B_411, A_412]: (v4_tex_2('#skF_1'(A_410, '#skF_2'(A_410, u1_struct_0(B_411))), A_412) | ~v3_tex_2('#skF_2'(A_410, u1_struct_0(B_411)), A_412) | v2_struct_0(A_412) | ~m1_pre_topc('#skF_1'(A_410, '#skF_2'(A_410, u1_struct_0(B_411))), A_412) | ~l1_pre_topc(A_412) | v1_xboole_0('#skF_2'(A_410, u1_struct_0(B_411))) | ~v2_tex_2(u1_struct_0(B_411), A_410) | ~v3_tdlat_3(A_410) | ~v2_pre_topc(A_410) | v2_struct_0(A_410) | ~m1_pre_topc(B_411, A_410) | ~l1_pre_topc(A_410))), inference(superposition, [status(thm), theory('equality')], [c_419, c_177])).
% 16.63/8.08  tff(c_32, plain, (![C_44]: (~v4_tex_2(C_44, '#skF_3') | ~m1_pre_topc('#skF_4', C_44) | ~m1_pre_topc(C_44, '#skF_3') | ~v1_pre_topc(C_44) | v2_struct_0(C_44))), inference(cnfTransformation, [status(thm)], [f_172])).
% 16.63/8.08  tff(c_3299, plain, (![A_410, B_411]: (~m1_pre_topc('#skF_4', '#skF_1'(A_410, '#skF_2'(A_410, u1_struct_0(B_411)))) | ~v1_pre_topc('#skF_1'(A_410, '#skF_2'(A_410, u1_struct_0(B_411)))) | v2_struct_0('#skF_1'(A_410, '#skF_2'(A_410, u1_struct_0(B_411)))) | ~v3_tex_2('#skF_2'(A_410, u1_struct_0(B_411)), '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_1'(A_410, '#skF_2'(A_410, u1_struct_0(B_411))), '#skF_3') | ~l1_pre_topc('#skF_3') | v1_xboole_0('#skF_2'(A_410, u1_struct_0(B_411))) | ~v2_tex_2(u1_struct_0(B_411), A_410) | ~v3_tdlat_3(A_410) | ~v2_pre_topc(A_410) | v2_struct_0(A_410) | ~m1_pre_topc(B_411, A_410) | ~l1_pre_topc(A_410))), inference(resolution, [status(thm)], [c_3292, c_32])).
% 16.63/8.08  tff(c_3315, plain, (![A_410, B_411]: (~m1_pre_topc('#skF_4', '#skF_1'(A_410, '#skF_2'(A_410, u1_struct_0(B_411)))) | ~v1_pre_topc('#skF_1'(A_410, '#skF_2'(A_410, u1_struct_0(B_411)))) | v2_struct_0('#skF_1'(A_410, '#skF_2'(A_410, u1_struct_0(B_411)))) | ~v3_tex_2('#skF_2'(A_410, u1_struct_0(B_411)), '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_1'(A_410, '#skF_2'(A_410, u1_struct_0(B_411))), '#skF_3') | v1_xboole_0('#skF_2'(A_410, u1_struct_0(B_411))) | ~v2_tex_2(u1_struct_0(B_411), A_410) | ~v3_tdlat_3(A_410) | ~v2_pre_topc(A_410) | v2_struct_0(A_410) | ~m1_pre_topc(B_411, A_410) | ~l1_pre_topc(A_410))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_3299])).
% 16.63/8.08  tff(c_3449, plain, (![A_427, B_428]: (~m1_pre_topc('#skF_4', '#skF_1'(A_427, '#skF_2'(A_427, u1_struct_0(B_428)))) | ~v1_pre_topc('#skF_1'(A_427, '#skF_2'(A_427, u1_struct_0(B_428)))) | v2_struct_0('#skF_1'(A_427, '#skF_2'(A_427, u1_struct_0(B_428)))) | ~v3_tex_2('#skF_2'(A_427, u1_struct_0(B_428)), '#skF_3') | ~m1_pre_topc('#skF_1'(A_427, '#skF_2'(A_427, u1_struct_0(B_428))), '#skF_3') | v1_xboole_0('#skF_2'(A_427, u1_struct_0(B_428))) | ~v2_tex_2(u1_struct_0(B_428), A_427) | ~v3_tdlat_3(A_427) | ~v2_pre_topc(A_427) | v2_struct_0(A_427) | ~m1_pre_topc(B_428, A_427) | ~l1_pre_topc(A_427))), inference(negUnitSimplification, [status(thm)], [c_46, c_3315])).
% 16.63/8.08  tff(c_3462, plain, (![B_3]: (~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0(B_3)))) | ~v1_pre_topc('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0(B_3)))) | v2_struct_0('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0(B_3)))) | ~v3_tex_2('#skF_2'('#skF_3', u1_struct_0(B_3)), '#skF_3') | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0(B_3))) | ~v2_tex_2(u1_struct_0(B_3), '#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_3, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_338, c_3449])).
% 16.63/8.08  tff(c_3468, plain, (![B_3]: (~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0(B_3)))) | ~v1_pre_topc('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0(B_3)))) | v2_struct_0('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0(B_3)))) | ~v3_tex_2('#skF_2'('#skF_3', u1_struct_0(B_3)), '#skF_3') | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0(B_3))) | ~v2_tex_2(u1_struct_0(B_3), '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_3, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44, c_42, c_3462])).
% 16.63/8.08  tff(c_3469, plain, (![B_3]: (~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0(B_3)))) | ~v1_pre_topc('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0(B_3)))) | v2_struct_0('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0(B_3)))) | ~v3_tex_2('#skF_2'('#skF_3', u1_struct_0(B_3)), '#skF_3') | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0(B_3))) | ~v2_tex_2(u1_struct_0(B_3), '#skF_3') | ~m1_pre_topc(B_3, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_3468])).
% 16.63/8.08  tff(c_13886, plain, (~v1_pre_topc('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4')))) | v2_struct_0('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4')))) | ~v3_tex_2('#skF_2'('#skF_3', u1_struct_0('#skF_4')), '#skF_3') | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4'))) | ~v2_tex_2(u1_struct_0('#skF_4'), '#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_13812, c_3469])).
% 16.63/8.08  tff(c_14038, plain, (~v1_pre_topc('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4')))) | v2_struct_0('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4')))) | ~v3_tex_2('#skF_2'('#skF_3', u1_struct_0('#skF_4')), '#skF_3') | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4'))) | ~v2_tex_2(u1_struct_0('#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_44, c_42, c_13886])).
% 16.63/8.08  tff(c_14039, plain, (~v1_pre_topc('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4')))) | v2_struct_0('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4')))) | ~v3_tex_2('#skF_2'('#skF_3', u1_struct_0('#skF_4')), '#skF_3') | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4'))) | ~v2_tex_2(u1_struct_0('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_46, c_14038])).
% 16.63/8.08  tff(c_14070, plain, (~v2_tex_2(u1_struct_0('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_14039])).
% 16.63/8.08  tff(c_14073, plain, (~v1_tdlat_3('#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_240, c_14070])).
% 16.63/8.08  tff(c_14076, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_36, c_14073])).
% 16.63/8.08  tff(c_14078, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_38, c_14076])).
% 16.63/8.08  tff(c_14080, plain, (v2_tex_2(u1_struct_0('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_14039])).
% 16.63/8.08  tff(c_224, plain, (![A_94, B_95]: (v3_tex_2('#skF_2'(A_94, B_95), A_94) | ~v2_tex_2(B_95, A_94) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94) | ~v3_tdlat_3(A_94) | ~v2_pre_topc(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_142])).
% 16.63/8.08  tff(c_229, plain, (![A_1, B_3]: (v3_tex_2('#skF_2'(A_1, u1_struct_0(B_3)), A_1) | ~v2_tex_2(u1_struct_0(B_3), A_1) | ~v3_tdlat_3(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(resolution, [status(thm)], [c_2, c_224])).
% 16.63/8.08  tff(c_12, plain, (![A_11, B_15]: (v1_pre_topc('#skF_1'(A_11, B_15)) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_11))) | v1_xboole_0(B_15) | ~l1_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.63/8.08  tff(c_309, plain, (![A_114, B_115]: (v1_pre_topc('#skF_1'(A_114, '#skF_2'(A_114, B_115))) | v1_xboole_0('#skF_2'(A_114, B_115)) | ~v2_tex_2(B_115, A_114) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114) | ~v3_tdlat_3(A_114) | ~v2_pre_topc(A_114) | v2_struct_0(A_114))), inference(resolution, [status(thm)], [c_249, c_12])).
% 16.63/8.08  tff(c_317, plain, (![A_1, B_3]: (v1_pre_topc('#skF_1'(A_1, '#skF_2'(A_1, u1_struct_0(B_3)))) | v1_xboole_0('#skF_2'(A_1, u1_struct_0(B_3))) | ~v2_tex_2(u1_struct_0(B_3), A_1) | ~v3_tdlat_3(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(resolution, [status(thm)], [c_2, c_309])).
% 16.63/8.08  tff(c_14079, plain, (~v3_tex_2('#skF_2'('#skF_3', u1_struct_0('#skF_4')), '#skF_3') | ~v1_pre_topc('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4')))) | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4'))) | v2_struct_0('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_14039])).
% 16.63/8.08  tff(c_14088, plain, (~v1_pre_topc('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4'))))), inference(splitLeft, [status(thm)], [c_14079])).
% 16.63/8.08  tff(c_14104, plain, (v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4'))) | ~v2_tex_2(u1_struct_0('#skF_4'), '#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_317, c_14088])).
% 16.63/8.08  tff(c_14123, plain, (v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_44, c_42, c_14080, c_14104])).
% 16.63/8.08  tff(c_14124, plain, (v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_46, c_14123])).
% 16.63/8.08  tff(c_20, plain, (![B_26, A_24]: (~v3_tex_2(B_26, A_24) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_24))) | ~v1_xboole_0(B_26) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_102])).
% 16.63/8.08  tff(c_305, plain, (![A_112, B_113]: (~v3_tex_2('#skF_2'(A_112, B_113), A_112) | ~v1_xboole_0('#skF_2'(A_112, B_113)) | ~v2_tex_2(B_113, A_112) | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112) | ~v3_tdlat_3(A_112) | ~v2_pre_topc(A_112) | v2_struct_0(A_112))), inference(resolution, [status(thm)], [c_249, c_20])).
% 16.63/8.08  tff(c_319, plain, (![A_118, B_119]: (~v1_xboole_0('#skF_2'(A_118, u1_struct_0(B_119))) | ~m1_subset_1(u1_struct_0(B_119), k1_zfmisc_1(u1_struct_0(A_118))) | ~v2_tex_2(u1_struct_0(B_119), A_118) | ~v3_tdlat_3(A_118) | ~v2_pre_topc(A_118) | v2_struct_0(A_118) | ~m1_pre_topc(B_119, A_118) | ~l1_pre_topc(A_118))), inference(resolution, [status(thm)], [c_229, c_305])).
% 16.63/8.08  tff(c_329, plain, (![A_1, B_3]: (~v1_xboole_0('#skF_2'(A_1, u1_struct_0(B_3))) | ~v2_tex_2(u1_struct_0(B_3), A_1) | ~v3_tdlat_3(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(resolution, [status(thm)], [c_2, c_319])).
% 16.63/8.08  tff(c_14130, plain, (~v2_tex_2(u1_struct_0('#skF_4'), '#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14124, c_329])).
% 16.63/8.08  tff(c_14137, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_44, c_42, c_14080, c_14130])).
% 16.63/8.08  tff(c_14139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_14137])).
% 16.63/8.08  tff(c_14140, plain, (~v3_tex_2('#skF_2'('#skF_3', u1_struct_0('#skF_4')), '#skF_3') | v2_struct_0('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4')))) | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_14079])).
% 16.63/8.08  tff(c_14142, plain, (~v3_tex_2('#skF_2'('#skF_3', u1_struct_0('#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_14140])).
% 16.63/8.08  tff(c_14245, plain, (~v2_tex_2(u1_struct_0('#skF_4'), '#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_229, c_14142])).
% 16.63/8.08  tff(c_14260, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_44, c_42, c_14080, c_14245])).
% 16.63/8.08  tff(c_14262, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_14260])).
% 16.63/8.08  tff(c_14264, plain, (v3_tex_2('#skF_2'('#skF_3', u1_struct_0('#skF_4')), '#skF_3')), inference(splitRight, [status(thm)], [c_14140])).
% 16.63/8.08  tff(c_274, plain, (![A_100, B_101]: (~v3_tex_2('#skF_2'(A_100, B_101), A_100) | ~v1_xboole_0('#skF_2'(A_100, B_101)) | ~v2_tex_2(B_101, A_100) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100) | ~v3_tdlat_3(A_100) | ~v2_pre_topc(A_100) | v2_struct_0(A_100))), inference(resolution, [status(thm)], [c_249, c_20])).
% 16.63/8.08  tff(c_14266, plain, (~v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4'))) | ~v2_tex_2(u1_struct_0('#skF_4'), '#skF_3') | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_14264, c_274])).
% 16.63/8.08  tff(c_14269, plain, (~v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4'))) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_14080, c_14266])).
% 16.63/8.08  tff(c_14270, plain, (~v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4'))) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_46, c_14269])).
% 16.63/8.08  tff(c_14271, plain, (~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_14270])).
% 16.63/8.08  tff(c_14274, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2, c_14271])).
% 16.63/8.08  tff(c_14278, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_14274])).
% 16.63/8.08  tff(c_14279, plain, (~v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_14270])).
% 16.63/8.08  tff(c_13811, plain, (![B_3, A_1]: (m1_pre_topc(B_3, '#skF_1'(A_1, '#skF_2'(A_1, u1_struct_0(B_3)))) | v1_xboole_0('#skF_2'(A_1, u1_struct_0(B_3))) | ~v2_tex_2(u1_struct_0(B_3), A_1) | ~v3_tdlat_3(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(resolution, [status(thm)], [c_338, c_13769])).
% 16.63/8.08  tff(c_14280, plain, (m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_14270])).
% 16.63/8.08  tff(c_273, plain, (![A_100, B_101]: (m1_pre_topc('#skF_1'(A_100, '#skF_2'(A_100, B_101)), A_100) | v1_xboole_0('#skF_2'(A_100, B_101)) | ~v2_tex_2(B_101, A_100) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100) | ~v3_tdlat_3(A_100) | ~v2_pre_topc(A_100) | v2_struct_0(A_100))), inference(resolution, [status(thm)], [c_249, c_10])).
% 16.63/8.08  tff(c_14284, plain, (m1_pre_topc('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4'))), '#skF_3') | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4'))) | ~v2_tex_2(u1_struct_0('#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_14280, c_273])).
% 16.63/8.08  tff(c_14311, plain, (m1_pre_topc('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4'))), '#skF_3') | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_14080, c_14284])).
% 16.63/8.08  tff(c_14312, plain, (m1_pre_topc('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4'))), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_46, c_14279, c_14311])).
% 16.63/8.08  tff(c_275, plain, (![A_100, B_101]: (u1_struct_0('#skF_1'(A_100, '#skF_2'(A_100, B_101)))='#skF_2'(A_100, B_101) | v1_xboole_0('#skF_2'(A_100, B_101)) | ~v2_tex_2(B_101, A_100) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100) | ~v3_tdlat_3(A_100) | ~v2_pre_topc(A_100) | v2_struct_0(A_100))), inference(resolution, [status(thm)], [c_249, c_8])).
% 16.63/8.08  tff(c_14282, plain, (u1_struct_0('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4'))))='#skF_2'('#skF_3', u1_struct_0('#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4'))) | ~v2_tex_2(u1_struct_0('#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_14280, c_275])).
% 16.63/8.08  tff(c_14307, plain, (u1_struct_0('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4'))))='#skF_2'('#skF_3', u1_struct_0('#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_14080, c_14282])).
% 16.63/8.08  tff(c_14308, plain, (u1_struct_0('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4'))))='#skF_2'('#skF_3', u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_46, c_14279, c_14307])).
% 16.63/8.08  tff(c_71, plain, (![A_60, B_61]: (m1_pre_topc('#skF_1'(A_60, B_61), A_60) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | v1_xboole_0(B_61) | ~l1_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.63/8.08  tff(c_74, plain, (![A_1, B_3]: (m1_pre_topc('#skF_1'(A_1, u1_struct_0(B_3)), A_1) | v1_xboole_0(u1_struct_0(B_3)) | v2_struct_0(A_1) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(resolution, [status(thm)], [c_2, c_71])).
% 16.63/8.08  tff(c_61, plain, (![A_56, B_57]: (u1_struct_0('#skF_1'(A_56, B_57))=B_57 | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | v1_xboole_0(B_57) | ~l1_pre_topc(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.63/8.08  tff(c_65, plain, (![A_1, B_3]: (u1_struct_0('#skF_1'(A_1, u1_struct_0(B_3)))=u1_struct_0(B_3) | v1_xboole_0(u1_struct_0(B_3)) | v2_struct_0(A_1) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(resolution, [status(thm)], [c_2, c_61])).
% 16.63/8.08  tff(c_178, plain, (![B_83, A_84]: (v4_tex_2(B_83, A_84) | ~v3_tex_2(u1_struct_0(B_83), A_84) | v2_struct_0(A_84) | ~m1_pre_topc(B_83, A_84) | ~l1_pre_topc(A_84))), inference(resolution, [status(thm)], [c_2, c_167])).
% 16.63/8.08  tff(c_184, plain, (![A_1, B_3, A_84]: (v4_tex_2('#skF_1'(A_1, u1_struct_0(B_3)), A_84) | ~v3_tex_2(u1_struct_0(B_3), A_84) | v2_struct_0(A_84) | ~m1_pre_topc('#skF_1'(A_1, u1_struct_0(B_3)), A_84) | ~l1_pre_topc(A_84) | v1_xboole_0(u1_struct_0(B_3)) | v2_struct_0(A_1) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_65, c_178])).
% 16.63/8.08  tff(c_145, plain, (![B_75, A_76]: (v3_tex_2(u1_struct_0(B_75), A_76) | ~v4_tex_2(B_75, A_76) | ~m1_subset_1(u1_struct_0(B_75), k1_zfmisc_1(u1_struct_0(A_76))) | ~m1_pre_topc(B_75, A_76) | ~l1_pre_topc(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_119])).
% 16.63/8.08  tff(c_155, plain, (![B_3, A_1]: (v3_tex_2(u1_struct_0(B_3), A_1) | ~v4_tex_2(B_3, A_1) | v2_struct_0(A_1) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(resolution, [status(thm)], [c_2, c_145])).
% 16.63/8.08  tff(c_49, plain, (![A_48, B_49]: (v1_pre_topc('#skF_1'(A_48, B_49)) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_48))) | v1_xboole_0(B_49) | ~l1_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.63/8.08  tff(c_53, plain, (![A_1, B_3]: (v1_pre_topc('#skF_1'(A_1, u1_struct_0(B_3))) | v1_xboole_0(u1_struct_0(B_3)) | v2_struct_0(A_1) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(resolution, [status(thm)], [c_2, c_49])).
% 16.63/8.08  tff(c_403, plain, (![A_145, B_146, A_147]: (v4_tex_2('#skF_1'(A_145, u1_struct_0(B_146)), A_147) | ~v3_tex_2(u1_struct_0(B_146), A_147) | v2_struct_0(A_147) | ~m1_pre_topc('#skF_1'(A_145, u1_struct_0(B_146)), A_147) | ~l1_pre_topc(A_147) | v1_xboole_0(u1_struct_0(B_146)) | v2_struct_0(A_145) | ~m1_pre_topc(B_146, A_145) | ~l1_pre_topc(A_145))), inference(superposition, [status(thm), theory('equality')], [c_65, c_178])).
% 16.63/8.08  tff(c_410, plain, (![A_145, B_146]: (~m1_pre_topc('#skF_4', '#skF_1'(A_145, u1_struct_0(B_146))) | ~v1_pre_topc('#skF_1'(A_145, u1_struct_0(B_146))) | v2_struct_0('#skF_1'(A_145, u1_struct_0(B_146))) | ~v3_tex_2(u1_struct_0(B_146), '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_1'(A_145, u1_struct_0(B_146)), '#skF_3') | ~l1_pre_topc('#skF_3') | v1_xboole_0(u1_struct_0(B_146)) | v2_struct_0(A_145) | ~m1_pre_topc(B_146, A_145) | ~l1_pre_topc(A_145))), inference(resolution, [status(thm)], [c_403, c_32])).
% 16.63/8.08  tff(c_417, plain, (![A_145, B_146]: (~m1_pre_topc('#skF_4', '#skF_1'(A_145, u1_struct_0(B_146))) | ~v1_pre_topc('#skF_1'(A_145, u1_struct_0(B_146))) | v2_struct_0('#skF_1'(A_145, u1_struct_0(B_146))) | ~v3_tex_2(u1_struct_0(B_146), '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_1'(A_145, u1_struct_0(B_146)), '#skF_3') | v1_xboole_0(u1_struct_0(B_146)) | v2_struct_0(A_145) | ~m1_pre_topc(B_146, A_145) | ~l1_pre_topc(A_145))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_410])).
% 16.63/8.08  tff(c_559, plain, (![A_153, B_154]: (~m1_pre_topc('#skF_4', '#skF_1'(A_153, u1_struct_0(B_154))) | ~v1_pre_topc('#skF_1'(A_153, u1_struct_0(B_154))) | v2_struct_0('#skF_1'(A_153, u1_struct_0(B_154))) | ~v3_tex_2(u1_struct_0(B_154), '#skF_3') | ~m1_pre_topc('#skF_1'(A_153, u1_struct_0(B_154)), '#skF_3') | v1_xboole_0(u1_struct_0(B_154)) | v2_struct_0(A_153) | ~m1_pre_topc(B_154, A_153) | ~l1_pre_topc(A_153))), inference(negUnitSimplification, [status(thm)], [c_46, c_417])).
% 16.63/8.08  tff(c_569, plain, (![B_3]: (~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', u1_struct_0(B_3))) | ~v1_pre_topc('#skF_1'('#skF_3', u1_struct_0(B_3))) | v2_struct_0('#skF_1'('#skF_3', u1_struct_0(B_3))) | ~v3_tex_2(u1_struct_0(B_3), '#skF_3') | v1_xboole_0(u1_struct_0(B_3)) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_3, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_74, c_559])).
% 16.63/8.08  tff(c_572, plain, (![B_3]: (~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', u1_struct_0(B_3))) | ~v1_pre_topc('#skF_1'('#skF_3', u1_struct_0(B_3))) | v2_struct_0('#skF_1'('#skF_3', u1_struct_0(B_3))) | ~v3_tex_2(u1_struct_0(B_3), '#skF_3') | v1_xboole_0(u1_struct_0(B_3)) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_3, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_569])).
% 16.63/8.08  tff(c_574, plain, (![B_155]: (~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', u1_struct_0(B_155))) | ~v1_pre_topc('#skF_1'('#skF_3', u1_struct_0(B_155))) | v2_struct_0('#skF_1'('#skF_3', u1_struct_0(B_155))) | ~v3_tex_2(u1_struct_0(B_155), '#skF_3') | v1_xboole_0(u1_struct_0(B_155)) | ~m1_pre_topc(B_155, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_572])).
% 16.63/8.08  tff(c_1427, plain, (![B_249, A_250]: (~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', u1_struct_0(B_249))) | ~v1_pre_topc('#skF_1'('#skF_3', u1_struct_0('#skF_1'(A_250, u1_struct_0(B_249))))) | v2_struct_0('#skF_1'('#skF_3', u1_struct_0('#skF_1'(A_250, u1_struct_0(B_249))))) | ~v3_tex_2(u1_struct_0('#skF_1'(A_250, u1_struct_0(B_249))), '#skF_3') | v1_xboole_0(u1_struct_0('#skF_1'(A_250, u1_struct_0(B_249)))) | ~m1_pre_topc('#skF_1'(A_250, u1_struct_0(B_249)), '#skF_3') | v1_xboole_0(u1_struct_0(B_249)) | v2_struct_0(A_250) | ~m1_pre_topc(B_249, A_250) | ~l1_pre_topc(A_250))), inference(superposition, [status(thm), theory('equality')], [c_65, c_574])).
% 16.63/8.08  tff(c_54, plain, (![A_50, B_51]: (~v2_struct_0('#skF_1'(A_50, B_51)) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | v1_xboole_0(B_51) | ~l1_pre_topc(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.63/8.08  tff(c_58, plain, (![A_1, B_3]: (~v2_struct_0('#skF_1'(A_1, u1_struct_0(B_3))) | v1_xboole_0(u1_struct_0(B_3)) | v2_struct_0(A_1) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(resolution, [status(thm)], [c_2, c_54])).
% 16.63/8.08  tff(c_1430, plain, (![B_249, A_250]: (v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', u1_struct_0(B_249))) | ~v1_pre_topc('#skF_1'('#skF_3', u1_struct_0('#skF_1'(A_250, u1_struct_0(B_249))))) | ~v3_tex_2(u1_struct_0('#skF_1'(A_250, u1_struct_0(B_249))), '#skF_3') | v1_xboole_0(u1_struct_0('#skF_1'(A_250, u1_struct_0(B_249)))) | ~m1_pre_topc('#skF_1'(A_250, u1_struct_0(B_249)), '#skF_3') | v1_xboole_0(u1_struct_0(B_249)) | v2_struct_0(A_250) | ~m1_pre_topc(B_249, A_250) | ~l1_pre_topc(A_250))), inference(resolution, [status(thm)], [c_1427, c_58])).
% 16.63/8.09  tff(c_1449, plain, (![B_249, A_250]: (v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', u1_struct_0(B_249))) | ~v1_pre_topc('#skF_1'('#skF_3', u1_struct_0('#skF_1'(A_250, u1_struct_0(B_249))))) | ~v3_tex_2(u1_struct_0('#skF_1'(A_250, u1_struct_0(B_249))), '#skF_3') | v1_xboole_0(u1_struct_0('#skF_1'(A_250, u1_struct_0(B_249)))) | ~m1_pre_topc('#skF_1'(A_250, u1_struct_0(B_249)), '#skF_3') | v1_xboole_0(u1_struct_0(B_249)) | v2_struct_0(A_250) | ~m1_pre_topc(B_249, A_250) | ~l1_pre_topc(A_250))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1430])).
% 16.63/8.09  tff(c_1856, plain, (![B_271, A_272]: (~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', u1_struct_0(B_271))) | ~v1_pre_topc('#skF_1'('#skF_3', u1_struct_0('#skF_1'(A_272, u1_struct_0(B_271))))) | ~v3_tex_2(u1_struct_0('#skF_1'(A_272, u1_struct_0(B_271))), '#skF_3') | v1_xboole_0(u1_struct_0('#skF_1'(A_272, u1_struct_0(B_271)))) | ~m1_pre_topc('#skF_1'(A_272, u1_struct_0(B_271)), '#skF_3') | v1_xboole_0(u1_struct_0(B_271)) | v2_struct_0(A_272) | ~m1_pre_topc(B_271, A_272) | ~l1_pre_topc(A_272))), inference(negUnitSimplification, [status(thm)], [c_46, c_1449])).
% 16.63/8.09  tff(c_1878, plain, (![B_271, A_272]: (~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', u1_struct_0(B_271))) | ~v3_tex_2(u1_struct_0('#skF_1'(A_272, u1_struct_0(B_271))), '#skF_3') | v1_xboole_0(u1_struct_0(B_271)) | v2_struct_0(A_272) | ~m1_pre_topc(B_271, A_272) | ~l1_pre_topc(A_272) | v1_xboole_0(u1_struct_0('#skF_1'(A_272, u1_struct_0(B_271)))) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_1'(A_272, u1_struct_0(B_271)), '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_53, c_1856])).
% 16.63/8.09  tff(c_1881, plain, (![B_271, A_272]: (~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', u1_struct_0(B_271))) | ~v3_tex_2(u1_struct_0('#skF_1'(A_272, u1_struct_0(B_271))), '#skF_3') | v1_xboole_0(u1_struct_0(B_271)) | v2_struct_0(A_272) | ~m1_pre_topc(B_271, A_272) | ~l1_pre_topc(A_272) | v1_xboole_0(u1_struct_0('#skF_1'(A_272, u1_struct_0(B_271)))) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_1'(A_272, u1_struct_0(B_271)), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1878])).
% 16.63/8.09  tff(c_1883, plain, (![B_273, A_274]: (~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', u1_struct_0(B_273))) | ~v3_tex_2(u1_struct_0('#skF_1'(A_274, u1_struct_0(B_273))), '#skF_3') | v1_xboole_0(u1_struct_0(B_273)) | v2_struct_0(A_274) | ~m1_pre_topc(B_273, A_274) | ~l1_pre_topc(A_274) | v1_xboole_0(u1_struct_0('#skF_1'(A_274, u1_struct_0(B_273)))) | ~m1_pre_topc('#skF_1'(A_274, u1_struct_0(B_273)), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_1881])).
% 16.63/8.09  tff(c_1899, plain, (![B_273, A_274]: (~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', u1_struct_0(B_273))) | v1_xboole_0(u1_struct_0(B_273)) | v2_struct_0(A_274) | ~m1_pre_topc(B_273, A_274) | ~l1_pre_topc(A_274) | v1_xboole_0(u1_struct_0('#skF_1'(A_274, u1_struct_0(B_273)))) | ~v4_tex_2('#skF_1'(A_274, u1_struct_0(B_273)), '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_1'(A_274, u1_struct_0(B_273)), '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_155, c_1883])).
% 16.63/8.09  tff(c_1908, plain, (![B_273, A_274]: (~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', u1_struct_0(B_273))) | v1_xboole_0(u1_struct_0(B_273)) | v2_struct_0(A_274) | ~m1_pre_topc(B_273, A_274) | ~l1_pre_topc(A_274) | v1_xboole_0(u1_struct_0('#skF_1'(A_274, u1_struct_0(B_273)))) | ~v4_tex_2('#skF_1'(A_274, u1_struct_0(B_273)), '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_1'(A_274, u1_struct_0(B_273)), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1899])).
% 16.63/8.09  tff(c_1910, plain, (![B_275, A_276]: (~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', u1_struct_0(B_275))) | v1_xboole_0(u1_struct_0(B_275)) | v2_struct_0(A_276) | ~m1_pre_topc(B_275, A_276) | ~l1_pre_topc(A_276) | v1_xboole_0(u1_struct_0('#skF_1'(A_276, u1_struct_0(B_275)))) | ~v4_tex_2('#skF_1'(A_276, u1_struct_0(B_275)), '#skF_3') | ~m1_pre_topc('#skF_1'(A_276, u1_struct_0(B_275)), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_1908])).
% 16.63/8.09  tff(c_2174, plain, (![B_294, A_295]: (~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', u1_struct_0(B_294))) | v1_xboole_0(u1_struct_0(B_294)) | v2_struct_0(A_295) | ~m1_pre_topc(B_294, A_295) | ~l1_pre_topc(A_295) | v1_xboole_0(u1_struct_0(B_294)) | ~v4_tex_2('#skF_1'(A_295, u1_struct_0(B_294)), '#skF_3') | ~m1_pre_topc('#skF_1'(A_295, u1_struct_0(B_294)), '#skF_3') | v1_xboole_0(u1_struct_0(B_294)) | v2_struct_0(A_295) | ~m1_pre_topc(B_294, A_295) | ~l1_pre_topc(A_295))), inference(superposition, [status(thm), theory('equality')], [c_65, c_1910])).
% 16.63/8.09  tff(c_2187, plain, (![B_3, A_1]: (~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', u1_struct_0(B_3))) | ~v3_tex_2(u1_struct_0(B_3), '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_1'(A_1, u1_struct_0(B_3)), '#skF_3') | ~l1_pre_topc('#skF_3') | v1_xboole_0(u1_struct_0(B_3)) | v2_struct_0(A_1) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(resolution, [status(thm)], [c_184, c_2174])).
% 16.63/8.09  tff(c_2193, plain, (![B_3, A_1]: (~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', u1_struct_0(B_3))) | ~v3_tex_2(u1_struct_0(B_3), '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_1'(A_1, u1_struct_0(B_3)), '#skF_3') | v1_xboole_0(u1_struct_0(B_3)) | v2_struct_0(A_1) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2187])).
% 16.63/8.09  tff(c_2195, plain, (![B_296, A_297]: (~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', u1_struct_0(B_296))) | ~v3_tex_2(u1_struct_0(B_296), '#skF_3') | ~m1_pre_topc('#skF_1'(A_297, u1_struct_0(B_296)), '#skF_3') | v1_xboole_0(u1_struct_0(B_296)) | v2_struct_0(A_297) | ~m1_pre_topc(B_296, A_297) | ~l1_pre_topc(A_297))), inference(negUnitSimplification, [status(thm)], [c_46, c_2193])).
% 16.63/8.09  tff(c_2211, plain, (![B_3]: (~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', u1_struct_0(B_3))) | ~v3_tex_2(u1_struct_0(B_3), '#skF_3') | v1_xboole_0(u1_struct_0(B_3)) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_3, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_74, c_2195])).
% 16.63/8.09  tff(c_2214, plain, (![B_3]: (~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', u1_struct_0(B_3))) | ~v3_tex_2(u1_struct_0(B_3), '#skF_3') | v1_xboole_0(u1_struct_0(B_3)) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_3, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2211])).
% 16.63/8.09  tff(c_2215, plain, (![B_3]: (~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', u1_struct_0(B_3))) | ~v3_tex_2(u1_struct_0(B_3), '#skF_3') | v1_xboole_0(u1_struct_0(B_3)) | ~m1_pre_topc(B_3, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_2214])).
% 16.63/8.09  tff(c_15114, plain, (~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4')))) | ~v3_tex_2(u1_struct_0('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4')))), '#skF_3') | v1_xboole_0(u1_struct_0('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4'))))) | ~m1_pre_topc('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4'))), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14308, c_2215])).
% 16.63/8.09  tff(c_15792, plain, (~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4')))) | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_14312, c_14308, c_14264, c_14308, c_15114])).
% 16.63/8.09  tff(c_15793, plain, (~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_14279, c_15792])).
% 16.63/8.09  tff(c_15974, plain, (v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4'))) | ~v2_tex_2(u1_struct_0('#skF_4'), '#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_13811, c_15793])).
% 16.63/8.09  tff(c_15977, plain, (v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_44, c_42, c_14080, c_15974])).
% 16.63/8.09  tff(c_15979, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_14279, c_15977])).
% 16.63/8.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.63/8.09  
% 16.63/8.09  Inference rules
% 16.63/8.09  ----------------------
% 16.63/8.09  #Ref     : 0
% 16.63/8.09  #Sup     : 4991
% 16.63/8.09  #Fact    : 0
% 16.63/8.09  #Define  : 0
% 16.63/8.09  #Split   : 6
% 16.63/8.09  #Chain   : 0
% 16.63/8.09  #Close   : 0
% 16.63/8.09  
% 16.63/8.09  Ordering : KBO
% 16.63/8.09  
% 16.63/8.09  Simplification rules
% 16.63/8.09  ----------------------
% 16.63/8.09  #Subsume      : 478
% 16.63/8.09  #Demod        : 1460
% 16.63/8.09  #Tautology    : 175
% 16.63/8.09  #SimpNegUnit  : 470
% 16.63/8.09  #BackRed      : 0
% 16.63/8.09  
% 16.63/8.09  #Partial instantiations: 0
% 16.63/8.09  #Strategies tried      : 1
% 16.63/8.09  
% 16.63/8.09  Timing (in seconds)
% 16.63/8.09  ----------------------
% 16.63/8.09  Preprocessing        : 0.32
% 16.63/8.09  Parsing              : 0.17
% 16.63/8.09  CNF conversion       : 0.03
% 16.63/8.09  Main loop            : 6.96
% 16.63/8.09  Inferencing          : 1.21
% 16.63/8.09  Reduction            : 1.22
% 16.63/8.09  Demodulation         : 0.80
% 16.63/8.09  BG Simplification    : 0.19
% 16.63/8.09  Subsumption          : 4.07
% 16.63/8.09  Abstraction          : 0.22
% 16.63/8.09  MUC search           : 0.00
% 16.63/8.09  Cooper               : 0.00
% 16.63/8.09  Total                : 7.33
% 16.63/8.09  Index Insertion      : 0.00
% 16.63/8.09  Index Deletion       : 0.00
% 16.63/8.09  Index Matching       : 0.00
% 16.63/8.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
