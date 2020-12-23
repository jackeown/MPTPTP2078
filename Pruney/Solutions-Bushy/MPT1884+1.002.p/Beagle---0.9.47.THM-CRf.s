%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1884+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:37 EST 2020

% Result     : Theorem 55.65s
% Output     : CNFRefutation 56.53s
% Verified   : 
% Statistics : Number of formulae       :  560 (238353 expanded)
%              Number of leaves         :   42 (75275 expanded)
%              Depth                    :   49
%              Number of atoms          : 2084 (1110419 expanded)
%              Number of equality atoms :  308 (127642 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_tex_2 > v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(v4_tex_2,type,(
    v4_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(f_226,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ( v4_tex_2(B,A)
            <=> ( v1_tdlat_3(B)
                & ! [C] :
                    ( ( ~ v2_struct_0(C)
                      & v1_tdlat_3(C)
                      & m1_pre_topc(C,A) )
                   => ( m1_pre_topc(B,C)
                     => g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tex_2)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_120,axiom,(
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

tff(f_184,axiom,(
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

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_149,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ ( v2_tex_2(B,A)
              & ! [C] :
                  ( ( ~ v2_struct_0(C)
                    & v1_pre_topc(C)
                    & v1_tdlat_3(C)
                    & m1_pre_topc(C,A) )
                 => B != u1_struct_0(C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_196,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( u1_struct_0(B) = u1_struct_0(C)
               => g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tsep_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_167,axiom,(
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

tff(f_153,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_68,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_64,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_125440,plain,(
    ! [B_1430,A_1431] :
      ( l1_pre_topc(B_1430)
      | ~ m1_pre_topc(B_1430,A_1431)
      | ~ l1_pre_topc(A_1431) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_125443,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_125440])).

tff(c_125446,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_125443])).

tff(c_22,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_117,plain,(
    ! [B_77,A_78] :
      ( l1_pre_topc(B_77)
      | ~ m1_pre_topc(B_77,A_78)
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_120,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_117])).

tff(c_123,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_120])).

tff(c_26,plain,(
    ! [A_21] :
      ( m1_subset_1(u1_pre_topc(A_21),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_21))))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_157,plain,(
    ! [A_90,B_91] :
      ( l1_pre_topc(g1_pre_topc(A_90,B_91))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(k1_zfmisc_1(A_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_165,plain,(
    ! [A_21] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_21),u1_pre_topc(A_21)))
      | ~ l1_pre_topc(A_21) ) ),
    inference(resolution,[status(thm)],[c_26,c_157])).

tff(c_167,plain,(
    ! [A_92,B_93] :
      ( v1_pre_topc(g1_pre_topc(A_92,B_93))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k1_zfmisc_1(A_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_175,plain,(
    ! [A_21] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_21),u1_pre_topc(A_21)))
      | ~ l1_pre_topc(A_21) ) ),
    inference(resolution,[status(thm)],[c_26,c_167])).

tff(c_98,plain,
    ( v4_tex_2('#skF_4','#skF_3')
    | v1_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_110,plain,(
    v1_tdlat_3('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_34,plain,(
    ! [B_31,A_29] :
      ( m1_subset_1(u1_struct_0(B_31),k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ m1_pre_topc(B_31,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_842,plain,(
    ! [B_215,A_216] :
      ( v2_tex_2(u1_struct_0(B_215),A_216)
      | ~ v1_tdlat_3(B_215)
      | ~ m1_subset_1(u1_struct_0(B_215),k1_zfmisc_1(u1_struct_0(A_216)))
      | ~ m1_pre_topc(B_215,A_216)
      | v2_struct_0(B_215)
      | ~ l1_pre_topc(A_216)
      | v2_struct_0(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_849,plain,(
    ! [B_31,A_29] :
      ( v2_tex_2(u1_struct_0(B_31),A_29)
      | ~ v1_tdlat_3(B_31)
      | v2_struct_0(B_31)
      | v2_struct_0(A_29)
      | ~ m1_pre_topc(B_31,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_34,c_842])).

tff(c_84,plain,
    ( ~ v2_struct_0('#skF_5')
    | ~ v1_tdlat_3('#skF_4')
    | ~ v4_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_112,plain,
    ( ~ v2_struct_0('#skF_5')
    | ~ v4_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_84])).

tff(c_113,plain,(
    ~ v4_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_70,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_603,plain,(
    ! [B_177,A_178] :
      ( v3_tex_2(u1_struct_0(B_177),A_178)
      | ~ v4_tex_2(B_177,A_178)
      | ~ m1_subset_1(u1_struct_0(B_177),k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ m1_pre_topc(B_177,A_178)
      | ~ l1_pre_topc(A_178)
      | v2_struct_0(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_612,plain,(
    ! [B_179,A_180] :
      ( v3_tex_2(u1_struct_0(B_179),A_180)
      | ~ v4_tex_2(B_179,A_180)
      | v2_struct_0(A_180)
      | ~ m1_pre_topc(B_179,A_180)
      | ~ l1_pre_topc(A_180) ) ),
    inference(resolution,[status(thm)],[c_34,c_603])).

tff(c_258,plain,(
    ! [B_105,A_106] :
      ( v2_tex_2(B_105,A_106)
      | ~ v3_tex_2(B_105,A_106)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_266,plain,(
    ! [B_31,A_29] :
      ( v2_tex_2(u1_struct_0(B_31),A_29)
      | ~ v3_tex_2(u1_struct_0(B_31),A_29)
      | ~ m1_pre_topc(B_31,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_34,c_258])).

tff(c_624,plain,(
    ! [B_179,A_180] :
      ( v2_tex_2(u1_struct_0(B_179),A_180)
      | ~ v4_tex_2(B_179,A_180)
      | v2_struct_0(A_180)
      | ~ m1_pre_topc(B_179,A_180)
      | ~ l1_pre_topc(A_180) ) ),
    inference(resolution,[status(thm)],[c_612,c_266])).

tff(c_748,plain,(
    ! [A_203,B_204] :
      ( u1_struct_0('#skF_2'(A_203,B_204)) = B_204
      | ~ v2_tex_2(B_204,A_203)
      | ~ m1_subset_1(B_204,k1_zfmisc_1(u1_struct_0(A_203)))
      | v1_xboole_0(B_204)
      | ~ l1_pre_topc(A_203)
      | ~ v2_pre_topc(A_203)
      | v2_struct_0(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_760,plain,(
    ! [A_29,B_31] :
      ( u1_struct_0('#skF_2'(A_29,u1_struct_0(B_31))) = u1_struct_0(B_31)
      | ~ v2_tex_2(u1_struct_0(B_31),A_29)
      | v1_xboole_0(u1_struct_0(B_31))
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29)
      | ~ m1_pre_topc(B_31,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_34,c_748])).

tff(c_872,plain,(
    ! [A_225,B_226] :
      ( m1_pre_topc('#skF_2'(A_225,B_226),A_225)
      | ~ v2_tex_2(B_226,A_225)
      | ~ m1_subset_1(B_226,k1_zfmisc_1(u1_struct_0(A_225)))
      | v1_xboole_0(B_226)
      | ~ l1_pre_topc(A_225)
      | ~ v2_pre_topc(A_225)
      | v2_struct_0(A_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1101,plain,(
    ! [A_251,B_252] :
      ( m1_pre_topc('#skF_2'(A_251,u1_struct_0(B_252)),A_251)
      | ~ v2_tex_2(u1_struct_0(B_252),A_251)
      | v1_xboole_0(u1_struct_0(B_252))
      | ~ v2_pre_topc(A_251)
      | v2_struct_0(A_251)
      | ~ m1_pre_topc(B_252,A_251)
      | ~ l1_pre_topc(A_251) ) ),
    inference(resolution,[status(thm)],[c_34,c_872])).

tff(c_24,plain,(
    ! [B_20,A_18] :
      ( l1_pre_topc(B_20)
      | ~ m1_pre_topc(B_20,A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1118,plain,(
    ! [A_251,B_252] :
      ( l1_pre_topc('#skF_2'(A_251,u1_struct_0(B_252)))
      | ~ v2_tex_2(u1_struct_0(B_252),A_251)
      | v1_xboole_0(u1_struct_0(B_252))
      | ~ v2_pre_topc(A_251)
      | v2_struct_0(A_251)
      | ~ m1_pre_topc(B_252,A_251)
      | ~ l1_pre_topc(A_251) ) ),
    inference(resolution,[status(thm)],[c_1101,c_24])).

tff(c_646,plain,(
    ! [A_188,B_189] :
      ( v1_pre_topc('#skF_2'(A_188,B_189))
      | ~ v2_tex_2(B_189,A_188)
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0(A_188)))
      | v1_xboole_0(B_189)
      | ~ l1_pre_topc(A_188)
      | ~ v2_pre_topc(A_188)
      | v2_struct_0(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_658,plain,(
    ! [A_29,B_31] :
      ( v1_pre_topc('#skF_2'(A_29,u1_struct_0(B_31)))
      | ~ v2_tex_2(u1_struct_0(B_31),A_29)
      | v1_xboole_0(u1_struct_0(B_31))
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29)
      | ~ m1_pre_topc(B_31,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_34,c_646])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_896,plain,(
    ! [C_229,B_230,A_231] :
      ( g1_pre_topc(u1_struct_0(C_229),u1_pre_topc(C_229)) = g1_pre_topc(u1_struct_0(B_230),u1_pre_topc(B_230))
      | u1_struct_0(C_229) != u1_struct_0(B_230)
      | ~ m1_pre_topc(C_229,A_231)
      | ~ m1_pre_topc(B_230,A_231)
      | ~ l1_pre_topc(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_898,plain,(
    ! [B_230] :
      ( g1_pre_topc(u1_struct_0(B_230),u1_pre_topc(B_230)) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
      | u1_struct_0(B_230) != u1_struct_0('#skF_4')
      | ~ m1_pre_topc(B_230,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_64,c_896])).

tff(c_902,plain,(
    ! [B_232] :
      ( g1_pre_topc(u1_struct_0(B_232),u1_pre_topc(B_232)) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
      | u1_struct_0(B_232) != u1_struct_0('#skF_4')
      | ~ m1_pre_topc(B_232,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_898])).

tff(c_981,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = A_1
      | u1_struct_0(A_1) != u1_struct_0('#skF_4')
      | ~ m1_pre_topc(A_1,'#skF_3')
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_902])).

tff(c_1104,plain,(
    ! [B_252] :
      ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0(B_252))
      | u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_252))) != u1_struct_0('#skF_4')
      | ~ v1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_252)))
      | ~ l1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_252)))
      | ~ v2_tex_2(u1_struct_0(B_252),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_252))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_252,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1101,c_981])).

tff(c_1114,plain,(
    ! [B_252] :
      ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0(B_252))
      | u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_252))) != u1_struct_0('#skF_4')
      | ~ v1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_252)))
      | ~ l1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_252)))
      | ~ v2_tex_2(u1_struct_0(B_252),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_252))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_252,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_1104])).

tff(c_1125,plain,(
    ! [B_257] :
      ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0(B_257))
      | u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_257))) != u1_struct_0('#skF_4')
      | ~ v1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_257)))
      | ~ l1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_257)))
      | ~ v2_tex_2(u1_struct_0(B_257),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_257))
      | ~ m1_pre_topc(B_257,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1114])).

tff(c_1129,plain,(
    ! [B_31] :
      ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0(B_31))
      | u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_31))) != u1_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_31)))
      | ~ v2_tex_2(u1_struct_0(B_31),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_31))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_31,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_658,c_1125])).

tff(c_1132,plain,(
    ! [B_31] :
      ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0(B_31))
      | u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_31))) != u1_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_31)))
      | ~ v2_tex_2(u1_struct_0(B_31),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_31))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_31,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_1129])).

tff(c_1554,plain,(
    ! [B_262] :
      ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0(B_262))
      | u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_262))) != u1_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_262)))
      | ~ v2_tex_2(u1_struct_0(B_262),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_262))
      | ~ m1_pre_topc(B_262,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1132])).

tff(c_1561,plain,(
    ! [B_252] :
      ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0(B_252))
      | u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_252))) != u1_struct_0('#skF_4')
      | ~ v2_tex_2(u1_struct_0(B_252),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_252))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_252,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1118,c_1554])).

tff(c_1564,plain,(
    ! [B_252] :
      ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0(B_252))
      | u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_252))) != u1_struct_0('#skF_4')
      | ~ v2_tex_2(u1_struct_0(B_252),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_252))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_252,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_1561])).

tff(c_3180,plain,(
    ! [B_302] :
      ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0(B_302))
      | u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_302))) != u1_struct_0('#skF_4')
      | ~ v2_tex_2(u1_struct_0(B_302),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_302))
      | ~ m1_pre_topc(B_302,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1564])).

tff(c_3189,plain,(
    ! [B_31] :
      ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0(B_31))
      | u1_struct_0(B_31) != u1_struct_0('#skF_4')
      | ~ v2_tex_2(u1_struct_0(B_31),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_31))
      | ~ m1_pre_topc(B_31,'#skF_3')
      | ~ v2_tex_2(u1_struct_0(B_31),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_31))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_31,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_760,c_3180])).

tff(c_3193,plain,(
    ! [B_31] :
      ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0(B_31))
      | u1_struct_0(B_31) != u1_struct_0('#skF_4')
      | ~ v2_tex_2(u1_struct_0(B_31),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_31))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_31,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_3189])).

tff(c_3481,plain,(
    ! [B_309] :
      ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0(B_309))
      | u1_struct_0(B_309) != u1_struct_0('#skF_4')
      | ~ v2_tex_2(u1_struct_0(B_309),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_309))
      | ~ m1_pre_topc(B_309,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3193])).

tff(c_3493,plain,(
    ! [B_179] :
      ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0(B_179))
      | u1_struct_0(B_179) != u1_struct_0('#skF_4')
      | v1_xboole_0(u1_struct_0(B_179))
      | ~ v4_tex_2(B_179,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_179,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_624,c_3481])).

tff(c_3503,plain,(
    ! [B_179] :
      ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0(B_179))
      | u1_struct_0(B_179) != u1_struct_0('#skF_4')
      | v1_xboole_0(u1_struct_0(B_179))
      | ~ v4_tex_2(B_179,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_179,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3493])).

tff(c_3740,plain,(
    ! [B_318] :
      ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0(B_318))
      | u1_struct_0(B_318) != u1_struct_0('#skF_4')
      | v1_xboole_0(u1_struct_0(B_318))
      | ~ v4_tex_2(B_318,'#skF_3')
      | ~ m1_pre_topc(B_318,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3503])).

tff(c_881,plain,(
    ! [A_29,B_31] :
      ( m1_pre_topc('#skF_2'(A_29,u1_struct_0(B_31)),A_29)
      | ~ v2_tex_2(u1_struct_0(B_31),A_29)
      | v1_xboole_0(u1_struct_0(B_31))
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29)
      | ~ m1_pre_topc(B_31,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_34,c_872])).

tff(c_3813,plain,(
    ! [B_318] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_3')
      | ~ v2_tex_2(u1_struct_0(B_318),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_318))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_318,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | u1_struct_0(B_318) != u1_struct_0('#skF_4')
      | v1_xboole_0(u1_struct_0(B_318))
      | ~ v4_tex_2(B_318,'#skF_3')
      | ~ m1_pre_topc(B_318,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3740,c_881])).

tff(c_3938,plain,(
    ! [B_318] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_3')
      | ~ v2_tex_2(u1_struct_0(B_318),'#skF_3')
      | v2_struct_0('#skF_3')
      | u1_struct_0(B_318) != u1_struct_0('#skF_4')
      | v1_xboole_0(u1_struct_0(B_318))
      | ~ v4_tex_2(B_318,'#skF_3')
      | ~ m1_pre_topc(B_318,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_3813])).

tff(c_3939,plain,(
    ! [B_318] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_3')
      | ~ v2_tex_2(u1_struct_0(B_318),'#skF_3')
      | u1_struct_0(B_318) != u1_struct_0('#skF_4')
      | v1_xboole_0(u1_struct_0(B_318))
      | ~ v4_tex_2(B_318,'#skF_3')
      | ~ m1_pre_topc(B_318,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3938])).

tff(c_6265,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3939])).

tff(c_86,plain,(
    ! [C_75] :
      ( v4_tex_2('#skF_4','#skF_3')
      | g1_pre_topc(u1_struct_0(C_75),u1_pre_topc(C_75)) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
      | ~ m1_pre_topc('#skF_4',C_75)
      | ~ m1_pre_topc(C_75,'#skF_3')
      | ~ v1_tdlat_3(C_75)
      | v2_struct_0(C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_185,plain,(
    ! [C_98] :
      ( g1_pre_topc(u1_struct_0(C_98),u1_pre_topc(C_98)) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
      | ~ m1_pre_topc('#skF_4',C_98)
      | ~ m1_pre_topc(C_98,'#skF_3')
      | ~ v1_tdlat_3(C_98)
      | v2_struct_0(C_98) ) ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_86])).

tff(c_201,plain,(
    ! [C_98] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc(C_98)
      | ~ m1_pre_topc('#skF_4',C_98)
      | ~ m1_pre_topc(C_98,'#skF_3')
      | ~ v1_tdlat_3(C_98)
      | v2_struct_0(C_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_165])).

tff(c_527,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_201])).

tff(c_195,plain,(
    ! [C_98] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc(C_98)
      | ~ m1_pre_topc('#skF_4',C_98)
      | ~ m1_pre_topc(C_98,'#skF_3')
      | ~ v1_tdlat_3(C_98)
      | v2_struct_0(C_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_175])).

tff(c_548,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_195])).

tff(c_302,plain,(
    ! [D_117,B_118,C_119,A_120] :
      ( D_117 = B_118
      | g1_pre_topc(C_119,D_117) != g1_pre_topc(A_120,B_118)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(k1_zfmisc_1(A_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_304,plain,(
    ! [A_1,B_118,A_120] :
      ( u1_pre_topc(A_1) = B_118
      | g1_pre_topc(A_120,B_118) != A_1
      | ~ m1_subset_1(B_118,k1_zfmisc_1(k1_zfmisc_1(A_120)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_302])).

tff(c_512,plain,(
    ! [A_163,B_164] :
      ( u1_pre_topc(g1_pre_topc(A_163,B_164)) = B_164
      | ~ m1_subset_1(B_164,k1_zfmisc_1(k1_zfmisc_1(A_163)))
      | ~ v1_pre_topc(g1_pre_topc(A_163,B_164))
      | ~ l1_pre_topc(g1_pre_topc(A_163,B_164)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_304])).

tff(c_1142,plain,(
    ! [A_259] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_259),u1_pre_topc(A_259))) = u1_pre_topc(A_259)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_259),u1_pre_topc(A_259)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_259),u1_pre_topc(A_259)))
      | ~ l1_pre_topc(A_259) ) ),
    inference(resolution,[status(thm)],[c_26,c_512])).

tff(c_1154,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = u1_pre_topc('#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_548,c_1142])).

tff(c_1177,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = u1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_527,c_1154])).

tff(c_1220,plain,
    ( m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1177,c_26])).

tff(c_1239,plain,(
    m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_1220])).

tff(c_1205,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_pre_topc('#skF_4')) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1177,c_2])).

tff(c_1231,plain,(
    g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_pre_topc('#skF_4')) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_548,c_1205])).

tff(c_32,plain,(
    ! [C_27,A_23,D_28,B_24] :
      ( C_27 = A_23
      | g1_pre_topc(C_27,D_28) != g1_pre_topc(A_23,B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k1_zfmisc_1(A_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1667,plain,(
    ! [C_27,D_28] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = C_27
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(C_27,D_28)
      | ~ m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1231,c_32])).

tff(c_1682,plain,(
    ! [C_27,D_28] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = C_27
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(C_27,D_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1239,c_1667])).

tff(c_1900,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = u1_struct_0('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1682])).

tff(c_2154,plain,(
    ! [A_29] :
      ( v2_tex_2(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),A_29)
      | ~ v3_tex_2(u1_struct_0('#skF_4'),A_29)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1900,c_266])).

tff(c_2293,plain,(
    ! [A_29] :
      ( v2_tex_2(u1_struct_0('#skF_4'),A_29)
      | ~ v3_tex_2(u1_struct_0('#skF_4'),A_29)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1900,c_2154])).

tff(c_6274,plain,
    ( v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ v3_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6265,c_2293])).

tff(c_6314,plain,
    ( v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ v3_tex_2(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_6274])).

tff(c_6416,plain,(
    ~ v3_tex_2(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_6314])).

tff(c_385,plain,(
    ! [B_135,C_136,A_137] :
      ( r1_tarski(u1_struct_0(B_135),u1_struct_0(C_136))
      | ~ m1_pre_topc(B_135,C_136)
      | ~ m1_pre_topc(C_136,A_137)
      | ~ m1_pre_topc(B_135,A_137)
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_387,plain,(
    ! [B_135] :
      ( r1_tarski(u1_struct_0(B_135),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_135,'#skF_4')
      | ~ m1_pre_topc(B_135,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_64,c_385])).

tff(c_391,plain,(
    ! [B_138] :
      ( r1_tarski(u1_struct_0(B_138),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_138,'#skF_4')
      | ~ m1_pre_topc(B_138,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_387])).

tff(c_52,plain,(
    ! [A_45,B_46] :
      ( m1_subset_1(A_45,k1_zfmisc_1(B_46))
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_137,plain,(
    ! [B_84,A_85] :
      ( v1_xboole_0(B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_85))
      | ~ v1_xboole_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_141,plain,(
    ! [A_45,B_46] :
      ( v1_xboole_0(A_45)
      | ~ v1_xboole_0(B_46)
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_52,c_137])).

tff(c_407,plain,(
    ! [B_138] :
      ( v1_xboole_0(u1_struct_0(B_138))
      | ~ v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_138,'#skF_4')
      | ~ m1_pre_topc(B_138,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_391,c_141])).

tff(c_408,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_407])).

tff(c_249,plain,(
    ! [B_103,A_104] :
      ( m1_subset_1(u1_struct_0(B_103),k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ m1_pre_topc(B_103,A_104)
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_50,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,B_46)
      | ~ m1_subset_1(A_45,k1_zfmisc_1(B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_257,plain,(
    ! [B_103,A_104] :
      ( r1_tarski(u1_struct_0(B_103),u1_struct_0(A_104))
      | ~ m1_pre_topc(B_103,A_104)
      | ~ l1_pre_topc(A_104) ) ),
    inference(resolution,[status(thm)],[c_249,c_50])).

tff(c_2162,plain,(
    ! [A_104] :
      ( r1_tarski(u1_struct_0('#skF_4'),u1_struct_0(A_104))
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),A_104)
      | ~ l1_pre_topc(A_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1900,c_257])).

tff(c_6280,plain,
    ( r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6265,c_2162])).

tff(c_6320,plain,(
    r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_6280])).

tff(c_528,plain,(
    ! [A_167,B_168] :
      ( ~ v2_struct_0('#skF_2'(A_167,B_168))
      | ~ v2_tex_2(B_168,A_167)
      | ~ m1_subset_1(B_168,k1_zfmisc_1(u1_struct_0(A_167)))
      | v1_xboole_0(B_168)
      | ~ l1_pre_topc(A_167)
      | ~ v2_pre_topc(A_167)
      | v2_struct_0(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_541,plain,(
    ! [A_167,A_45] :
      ( ~ v2_struct_0('#skF_2'(A_167,A_45))
      | ~ v2_tex_2(A_45,A_167)
      | v1_xboole_0(A_45)
      | ~ l1_pre_topc(A_167)
      | ~ v2_pre_topc(A_167)
      | v2_struct_0(A_167)
      | ~ r1_tarski(A_45,u1_struct_0(A_167)) ) ),
    inference(resolution,[status(thm)],[c_52,c_528])).

tff(c_6365,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_6320,c_541])).

tff(c_6401,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_6365])).

tff(c_6402,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_408,c_6401])).

tff(c_6459,plain,(
    ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_6402])).

tff(c_6462,plain,
    ( ~ v1_tdlat_3('#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_849,c_6459])).

tff(c_6468,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_110,c_6462])).

tff(c_6470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_6468])).

tff(c_6472,plain,(
    v2_tex_2(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_6402])).

tff(c_417,plain,(
    ! [B_143,A_144] :
      ( r1_tarski(B_143,'#skF_1'(A_144,B_143))
      | v3_tex_2(B_143,A_144)
      | ~ v2_tex_2(B_143,A_144)
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_424,plain,(
    ! [A_45,A_144] :
      ( r1_tarski(A_45,'#skF_1'(A_144,A_45))
      | v3_tex_2(A_45,A_144)
      | ~ v2_tex_2(A_45,A_144)
      | ~ l1_pre_topc(A_144)
      | ~ r1_tarski(A_45,u1_struct_0(A_144)) ) ),
    inference(resolution,[status(thm)],[c_52,c_417])).

tff(c_6367,plain,
    ( r1_tarski(u1_struct_0('#skF_4'),'#skF_1'('#skF_3',u1_struct_0('#skF_4')))
    | v3_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6320,c_424])).

tff(c_6405,plain,
    ( r1_tarski(u1_struct_0('#skF_4'),'#skF_1'('#skF_3',u1_struct_0('#skF_4')))
    | v3_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_6367])).

tff(c_8800,plain,
    ( r1_tarski(u1_struct_0('#skF_4'),'#skF_1'('#skF_3',u1_struct_0('#skF_4')))
    | v3_tex_2(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6472,c_6405])).

tff(c_8801,plain,(
    r1_tarski(u1_struct_0('#skF_4'),'#skF_1'('#skF_3',u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_6416,c_8800])).

tff(c_8806,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ v1_xboole_0('#skF_1'('#skF_3',u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_8801,c_141])).

tff(c_8812,plain,(
    ~ v1_xboole_0('#skF_1'('#skF_3',u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_408,c_8806])).

tff(c_882,plain,(
    ! [A_225,A_45] :
      ( m1_pre_topc('#skF_2'(A_225,A_45),A_225)
      | ~ v2_tex_2(A_45,A_225)
      | v1_xboole_0(A_45)
      | ~ l1_pre_topc(A_225)
      | ~ v2_pre_topc(A_225)
      | v2_struct_0(A_225)
      | ~ r1_tarski(A_45,u1_struct_0(A_225)) ) ),
    inference(resolution,[status(thm)],[c_52,c_872])).

tff(c_6350,plain,
    ( m1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_3')
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_6320,c_882])).

tff(c_6382,plain,
    ( m1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_3')
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_6350])).

tff(c_6383,plain,
    ( m1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_3')
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_408,c_6382])).

tff(c_6523,plain,(
    m1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6472,c_6383])).

tff(c_3194,plain,(
    ! [B_31] :
      ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0(B_31))
      | u1_struct_0(B_31) != u1_struct_0('#skF_4')
      | ~ v2_tex_2(u1_struct_0(B_31),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_31))
      | ~ m1_pre_topc(B_31,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3193])).

tff(c_6499,plain,
    ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_6472,c_3194])).

tff(c_6508,plain,
    ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_6499])).

tff(c_6509,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_408,c_6508])).

tff(c_6581,plain,(
    u1_struct_0('#skF_2'('#skF_3',u1_struct_0('#skF_4'))) = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6509,c_1900])).

tff(c_6541,plain,
    ( l1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6523,c_24])).

tff(c_6560,plain,(
    l1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_6541])).

tff(c_901,plain,(
    ! [B_230] :
      ( g1_pre_topc(u1_struct_0(B_230),u1_pre_topc(B_230)) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
      | u1_struct_0(B_230) != u1_struct_0('#skF_4')
      | ~ m1_pre_topc(B_230,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_898])).

tff(c_6301,plain,(
    ! [B_230] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_230),u1_pre_topc(B_230)),'#skF_3')
      | u1_struct_0(B_230) != u1_struct_0('#skF_4')
      | ~ m1_pre_topc(B_230,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_901,c_6265])).

tff(c_285,plain,(
    ! [C_113,A_114,D_115,B_116] :
      ( C_113 = A_114
      | g1_pre_topc(C_113,D_115) != g1_pre_topc(A_114,B_116)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(k1_zfmisc_1(A_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_289,plain,(
    ! [A_1,C_113,D_115] :
      ( u1_struct_0(A_1) = C_113
      | g1_pre_topc(C_113,D_115) != A_1
      | ~ m1_subset_1(u1_pre_topc(A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_285])).

tff(c_9737,plain,(
    ! [C_402,D_403] :
      ( u1_struct_0(g1_pre_topc(C_402,D_403)) = C_402
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_402,D_403)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_402,D_403)))))
      | ~ v1_pre_topc(g1_pre_topc(C_402,D_403))
      | ~ l1_pre_topc(g1_pre_topc(C_402,D_403)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_289])).

tff(c_9809,plain,(
    ! [C_404,D_405] :
      ( u1_struct_0(g1_pre_topc(C_404,D_405)) = C_404
      | ~ v1_pre_topc(g1_pre_topc(C_404,D_405))
      | ~ l1_pre_topc(g1_pre_topc(C_404,D_405)) ) ),
    inference(resolution,[status(thm)],[c_26,c_9737])).

tff(c_9859,plain,(
    ! [A_406] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_406),u1_pre_topc(A_406))) = u1_struct_0(A_406)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_406),u1_pre_topc(A_406)))
      | ~ l1_pre_topc(A_406) ) ),
    inference(resolution,[status(thm)],[c_175,c_9809])).

tff(c_9935,plain,(
    ! [A_407] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_407),u1_pre_topc(A_407))) = u1_struct_0(A_407)
      | ~ l1_pre_topc(A_407) ) ),
    inference(resolution,[status(thm)],[c_165,c_9859])).

tff(c_11014,plain,(
    ! [A_424,A_425] :
      ( m1_subset_1(u1_struct_0(A_424),k1_zfmisc_1(u1_struct_0(A_425)))
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(A_424),u1_pre_topc(A_424)),A_425)
      | ~ l1_pre_topc(A_425)
      | ~ l1_pre_topc(A_424) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9935,c_34])).

tff(c_11024,plain,(
    ! [B_230] :
      ( m1_subset_1(u1_struct_0(B_230),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(B_230)
      | u1_struct_0(B_230) != u1_struct_0('#skF_4')
      | ~ m1_pre_topc(B_230,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_6301,c_11014])).

tff(c_11084,plain,(
    ! [B_427] :
      ( m1_subset_1(u1_struct_0(B_427),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc(B_427)
      | u1_struct_0(B_427) != u1_struct_0('#skF_4')
      | ~ m1_pre_topc(B_427,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_11024])).

tff(c_11136,plain,
    ( m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | u1_struct_0('#skF_2'('#skF_3',u1_struct_0('#skF_4'))) != u1_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6581,c_11084])).

tff(c_11200,plain,(
    m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6523,c_6581,c_6560,c_11136])).

tff(c_10,plain,(
    ! [A_5,B_11] :
      ( v2_tex_2('#skF_1'(A_5,B_11),A_5)
      | v3_tex_2(B_11,A_5)
      | ~ v2_tex_2(B_11,A_5)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_11229,plain,
    ( v2_tex_2('#skF_1'('#skF_3',u1_struct_0('#skF_4')),'#skF_3')
    | v3_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_11200,c_10])).

tff(c_11290,plain,
    ( v2_tex_2('#skF_1'('#skF_3',u1_struct_0('#skF_4')),'#skF_3')
    | v3_tex_2(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_6472,c_11229])).

tff(c_11291,plain,(
    v2_tex_2('#skF_1'('#skF_3',u1_struct_0('#skF_4')),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_6416,c_11290])).

tff(c_316,plain,(
    ! [A_123,B_124] :
      ( '#skF_1'(A_123,B_124) != B_124
      | v3_tex_2(B_124,A_123)
      | ~ v2_tex_2(B_124,A_123)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_324,plain,(
    ! [A_29,B_31] :
      ( '#skF_1'(A_29,u1_struct_0(B_31)) != u1_struct_0(B_31)
      | v3_tex_2(u1_struct_0(B_31),A_29)
      | ~ v2_tex_2(u1_struct_0(B_31),A_29)
      | ~ m1_pre_topc(B_31,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_34,c_316])).

tff(c_628,plain,(
    ! [B_184,A_185] :
      ( v4_tex_2(B_184,A_185)
      | ~ v3_tex_2(u1_struct_0(B_184),A_185)
      | ~ m1_subset_1(u1_struct_0(B_184),k1_zfmisc_1(u1_struct_0(A_185)))
      | ~ m1_pre_topc(B_184,A_185)
      | ~ l1_pre_topc(A_185)
      | v2_struct_0(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_637,plain,(
    ! [B_186,A_187] :
      ( v4_tex_2(B_186,A_187)
      | ~ v3_tex_2(u1_struct_0(B_186),A_187)
      | v2_struct_0(A_187)
      | ~ m1_pre_topc(B_186,A_187)
      | ~ l1_pre_topc(A_187) ) ),
    inference(resolution,[status(thm)],[c_34,c_628])).

tff(c_645,plain,(
    ! [B_31,A_29] :
      ( v4_tex_2(B_31,A_29)
      | v2_struct_0(A_29)
      | '#skF_1'(A_29,u1_struct_0(B_31)) != u1_struct_0(B_31)
      | ~ v2_tex_2(u1_struct_0(B_31),A_29)
      | ~ m1_pre_topc(B_31,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_324,c_637])).

tff(c_6505,plain,
    ( v4_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3')
    | '#skF_1'('#skF_3',u1_struct_0('#skF_4')) != u1_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6472,c_645])).

tff(c_6516,plain,
    ( v4_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3')
    | '#skF_1'('#skF_3',u1_struct_0('#skF_4')) != u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_6505])).

tff(c_6517,plain,(
    '#skF_1'('#skF_3',u1_struct_0('#skF_4')) != u1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_113,c_6516])).

tff(c_12,plain,(
    ! [A_5,B_11] :
      ( m1_subset_1('#skF_1'(A_5,B_11),k1_zfmisc_1(u1_struct_0(A_5)))
      | v3_tex_2(B_11,A_5)
      | ~ v2_tex_2(B_11,A_5)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_880,plain,(
    ! [A_5,B_11] :
      ( m1_pre_topc('#skF_2'(A_5,'#skF_1'(A_5,B_11)),A_5)
      | ~ v2_tex_2('#skF_1'(A_5,B_11),A_5)
      | v1_xboole_0('#skF_1'(A_5,B_11))
      | ~ v2_pre_topc(A_5)
      | v2_struct_0(A_5)
      | v3_tex_2(B_11,A_5)
      | ~ v2_tex_2(B_11,A_5)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(resolution,[status(thm)],[c_12,c_872])).

tff(c_11204,plain,
    ( m1_pre_topc('#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4'))),'#skF_3')
    | ~ v2_tex_2('#skF_1'('#skF_3',u1_struct_0('#skF_4')),'#skF_3')
    | v1_xboole_0('#skF_1'('#skF_3',u1_struct_0('#skF_4')))
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v3_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_11200,c_880])).

tff(c_11250,plain,
    ( m1_pre_topc('#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4'))),'#skF_3')
    | ~ v2_tex_2('#skF_1'('#skF_3',u1_struct_0('#skF_4')),'#skF_3')
    | v1_xboole_0('#skF_1'('#skF_3',u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_3')
    | v3_tex_2(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_6472,c_70,c_11204])).

tff(c_11251,plain,
    ( m1_pre_topc('#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4'))),'#skF_3')
    | ~ v2_tex_2('#skF_1'('#skF_3',u1_struct_0('#skF_4')),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_6416,c_72,c_8812,c_11250])).

tff(c_11330,plain,(
    m1_pre_topc('#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4'))),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11291,c_11251])).

tff(c_11348,plain,
    ( l1_pre_topc('#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_11330,c_24])).

tff(c_11367,plain,(
    l1_pre_topc('#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_11348])).

tff(c_657,plain,(
    ! [A_5,B_11] :
      ( v1_pre_topc('#skF_2'(A_5,'#skF_1'(A_5,B_11)))
      | ~ v2_tex_2('#skF_1'(A_5,B_11),A_5)
      | v1_xboole_0('#skF_1'(A_5,B_11))
      | ~ v2_pre_topc(A_5)
      | v2_struct_0(A_5)
      | v3_tex_2(B_11,A_5)
      | ~ v2_tex_2(B_11,A_5)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(resolution,[status(thm)],[c_12,c_646])).

tff(c_11206,plain,
    ( v1_pre_topc('#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4'))))
    | ~ v2_tex_2('#skF_1'('#skF_3',u1_struct_0('#skF_4')),'#skF_3')
    | v1_xboole_0('#skF_1'('#skF_3',u1_struct_0('#skF_4')))
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v3_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_11200,c_657])).

tff(c_11254,plain,
    ( v1_pre_topc('#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4'))))
    | ~ v2_tex_2('#skF_1'('#skF_3',u1_struct_0('#skF_4')),'#skF_3')
    | v1_xboole_0('#skF_1'('#skF_3',u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_3')
    | v3_tex_2(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_6472,c_70,c_11206])).

tff(c_11255,plain,
    ( v1_pre_topc('#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4'))))
    | ~ v2_tex_2('#skF_1'('#skF_3',u1_struct_0('#skF_4')),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_6416,c_72,c_8812,c_11254])).

tff(c_11308,plain,(
    v1_pre_topc('#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11291,c_11255])).

tff(c_759,plain,(
    ! [A_5,B_11] :
      ( u1_struct_0('#skF_2'(A_5,'#skF_1'(A_5,B_11))) = '#skF_1'(A_5,B_11)
      | ~ v2_tex_2('#skF_1'(A_5,B_11),A_5)
      | v1_xboole_0('#skF_1'(A_5,B_11))
      | ~ v2_pre_topc(A_5)
      | v2_struct_0(A_5)
      | v3_tex_2(B_11,A_5)
      | ~ v2_tex_2(B_11,A_5)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(resolution,[status(thm)],[c_12,c_748])).

tff(c_11202,plain,
    ( u1_struct_0('#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4')))) = '#skF_1'('#skF_3',u1_struct_0('#skF_4'))
    | ~ v2_tex_2('#skF_1'('#skF_3',u1_struct_0('#skF_4')),'#skF_3')
    | v1_xboole_0('#skF_1'('#skF_3',u1_struct_0('#skF_4')))
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v3_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_11200,c_759])).

tff(c_11246,plain,
    ( u1_struct_0('#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4')))) = '#skF_1'('#skF_3',u1_struct_0('#skF_4'))
    | ~ v2_tex_2('#skF_1'('#skF_3',u1_struct_0('#skF_4')),'#skF_3')
    | v1_xboole_0('#skF_1'('#skF_3',u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_3')
    | v3_tex_2(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_6472,c_70,c_11202])).

tff(c_11247,plain,
    ( u1_struct_0('#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4')))) = '#skF_1'('#skF_3',u1_struct_0('#skF_4'))
    | ~ v2_tex_2('#skF_1'('#skF_3',u1_struct_0('#skF_4')),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_6416,c_72,c_8812,c_11246])).

tff(c_11434,plain,(
    u1_struct_0('#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4')))) = '#skF_1'('#skF_3',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11291,c_11247])).

tff(c_11796,plain,
    ( g1_pre_topc('#skF_1'('#skF_3',u1_struct_0('#skF_4')),u1_pre_topc('#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4'))))) = '#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4')))
    | ~ v1_pre_topc('#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_11434,c_2])).

tff(c_12053,plain,(
    g1_pre_topc('#skF_1'('#skF_3',u1_struct_0('#skF_4')),u1_pre_topc('#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4'))))) = '#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11367,c_11308,c_11796])).

tff(c_1974,plain,(
    ! [C_27,D_28] :
      ( u1_struct_0('#skF_4') = C_27
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(C_27,D_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1900,c_1682])).

tff(c_6580,plain,(
    ! [C_27,D_28] :
      ( u1_struct_0('#skF_4') = C_27
      | g1_pre_topc(C_27,D_28) != '#skF_2'('#skF_3',u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6509,c_1974])).

tff(c_15329,plain,
    ( '#skF_1'('#skF_3',u1_struct_0('#skF_4')) = u1_struct_0('#skF_4')
    | '#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4'))) != '#skF_2'('#skF_3',u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12053,c_6580])).

tff(c_15372,plain,(
    '#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4'))) != '#skF_2'('#skF_3',u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_6517,c_15329])).

tff(c_676,plain,(
    ! [A_192,B_193] :
      ( v1_tdlat_3('#skF_2'(A_192,B_193))
      | ~ v2_tex_2(B_193,A_192)
      | ~ m1_subset_1(B_193,k1_zfmisc_1(u1_struct_0(A_192)))
      | v1_xboole_0(B_193)
      | ~ l1_pre_topc(A_192)
      | ~ v2_pre_topc(A_192)
      | v2_struct_0(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_687,plain,(
    ! [A_5,B_11] :
      ( v1_tdlat_3('#skF_2'(A_5,'#skF_1'(A_5,B_11)))
      | ~ v2_tex_2('#skF_1'(A_5,B_11),A_5)
      | v1_xboole_0('#skF_1'(A_5,B_11))
      | ~ v2_pre_topc(A_5)
      | v2_struct_0(A_5)
      | v3_tex_2(B_11,A_5)
      | ~ v2_tex_2(B_11,A_5)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(resolution,[status(thm)],[c_12,c_676])).

tff(c_11208,plain,
    ( v1_tdlat_3('#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4'))))
    | ~ v2_tex_2('#skF_1'('#skF_3',u1_struct_0('#skF_4')),'#skF_3')
    | v1_xboole_0('#skF_1'('#skF_3',u1_struct_0('#skF_4')))
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v3_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_11200,c_687])).

tff(c_11258,plain,
    ( v1_tdlat_3('#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4'))))
    | ~ v2_tex_2('#skF_1'('#skF_3',u1_struct_0('#skF_4')),'#skF_3')
    | v1_xboole_0('#skF_1'('#skF_3',u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_3')
    | v3_tex_2(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_6472,c_70,c_11208])).

tff(c_11259,plain,
    ( v1_tdlat_3('#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4'))))
    | ~ v2_tex_2('#skF_1'('#skF_3',u1_struct_0('#skF_4')),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_6416,c_72,c_8812,c_11258])).

tff(c_11310,plain,(
    v1_tdlat_3('#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11291,c_11259])).

tff(c_184,plain,(
    ! [C_75] :
      ( g1_pre_topc(u1_struct_0(C_75),u1_pre_topc(C_75)) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
      | ~ m1_pre_topc('#skF_4',C_75)
      | ~ m1_pre_topc(C_75,'#skF_3')
      | ~ v1_tdlat_3(C_75)
      | v2_struct_0(C_75) ) ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_86])).

tff(c_17786,plain,(
    ! [C_515] :
      ( g1_pre_topc(u1_struct_0(C_515),u1_pre_topc(C_515)) = '#skF_2'('#skF_3',u1_struct_0('#skF_4'))
      | ~ m1_pre_topc('#skF_4',C_515)
      | ~ m1_pre_topc(C_515,'#skF_3')
      | ~ v1_tdlat_3(C_515)
      | v2_struct_0(C_515) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6509,c_184])).

tff(c_18060,plain,
    ( g1_pre_topc('#skF_1'('#skF_3',u1_struct_0('#skF_4')),u1_pre_topc('#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4'))))) = '#skF_2'('#skF_3',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4'))))
    | ~ m1_pre_topc('#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4'))),'#skF_3')
    | ~ v1_tdlat_3('#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4'))))
    | v2_struct_0('#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_11434,c_17786])).

tff(c_18175,plain,
    ( '#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4'))) = '#skF_2'('#skF_3',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4'))))
    | v2_struct_0('#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11310,c_11330,c_12053,c_18060])).

tff(c_18176,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4'))))
    | v2_struct_0('#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4')))) ),
    inference(negUnitSimplification,[status(thm)],[c_15372,c_18175])).

tff(c_18252,plain,(
    ~ m1_pre_topc('#skF_4','#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4')))) ),
    inference(splitLeft,[status(thm)],[c_18176])).

tff(c_7619,plain,(
    ! [A_360,B_361] :
      ( m1_pre_topc('#skF_2'(A_360,'#skF_1'(A_360,B_361)),A_360)
      | ~ v2_tex_2('#skF_1'(A_360,B_361),A_360)
      | v1_xboole_0('#skF_1'(A_360,B_361))
      | ~ v2_pre_topc(A_360)
      | v2_struct_0(A_360)
      | v3_tex_2(B_361,A_360)
      | ~ v2_tex_2(B_361,A_360)
      | ~ m1_subset_1(B_361,k1_zfmisc_1(u1_struct_0(A_360)))
      | ~ l1_pre_topc(A_360) ) ),
    inference(resolution,[status(thm)],[c_12,c_872])).

tff(c_7637,plain,(
    ! [A_29,B_31] :
      ( m1_pre_topc('#skF_2'(A_29,'#skF_1'(A_29,u1_struct_0(B_31))),A_29)
      | ~ v2_tex_2('#skF_1'(A_29,u1_struct_0(B_31)),A_29)
      | v1_xboole_0('#skF_1'(A_29,u1_struct_0(B_31)))
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29)
      | v3_tex_2(u1_struct_0(B_31),A_29)
      | ~ v2_tex_2(u1_struct_0(B_31),A_29)
      | ~ m1_pre_topc(B_31,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_34,c_7619])).

tff(c_2171,plain,(
    ! [A_29] :
      ( m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1900,c_34])).

tff(c_6575,plain,(
    ! [A_29] :
      ( m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ m1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_4')),A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6509,c_2171])).

tff(c_11503,plain,
    ( m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1('#skF_1'('#skF_3',u1_struct_0('#skF_4'))))
    | ~ m1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_11434,c_6575])).

tff(c_11868,plain,
    ( m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1('#skF_1'('#skF_3',u1_struct_0('#skF_4'))))
    | ~ m1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11367,c_11503])).

tff(c_18343,plain,(
    ~ m1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4')))) ),
    inference(splitLeft,[status(thm)],[c_11868])).

tff(c_56,plain,(
    ! [B_51,C_53,A_47] :
      ( m1_pre_topc(B_51,C_53)
      | ~ r1_tarski(u1_struct_0(B_51),u1_struct_0(C_53))
      | ~ m1_pre_topc(C_53,A_47)
      | ~ m1_pre_topc(B_51,A_47)
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_107258,plain,(
    ! [C_1249,A_1250] :
      ( m1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_4')),C_1249)
      | ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0(C_1249))
      | ~ m1_pre_topc(C_1249,A_1250)
      | ~ m1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_4')),A_1250)
      | ~ l1_pre_topc(A_1250)
      | ~ v2_pre_topc(A_1250) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6581,c_56])).

tff(c_107302,plain,(
    ! [A_1250] :
      ( m1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4'))))
      | ~ r1_tarski(u1_struct_0('#skF_4'),'#skF_1'('#skF_3',u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4'))),A_1250)
      | ~ m1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_4')),A_1250)
      | ~ l1_pre_topc(A_1250)
      | ~ v2_pre_topc(A_1250) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11434,c_107258])).

tff(c_107345,plain,(
    ! [A_1250] :
      ( m1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4'))))
      | ~ m1_pre_topc('#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4'))),A_1250)
      | ~ m1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_4')),A_1250)
      | ~ l1_pre_topc(A_1250)
      | ~ v2_pre_topc(A_1250) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8801,c_107302])).

tff(c_107358,plain,(
    ! [A_1251] :
      ( ~ m1_pre_topc('#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4'))),A_1251)
      | ~ m1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_4')),A_1251)
      | ~ l1_pre_topc(A_1251)
      | ~ v2_pre_topc(A_1251) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18343,c_107345])).

tff(c_107374,plain,
    ( ~ m1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_3')
    | ~ v2_tex_2('#skF_1'('#skF_3',u1_struct_0('#skF_4')),'#skF_3')
    | v1_xboole_0('#skF_1'('#skF_3',u1_struct_0('#skF_4')))
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v3_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_7637,c_107358])).

tff(c_107393,plain,
    ( v1_xboole_0('#skF_1'('#skF_3',u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_3')
    | v3_tex_2(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_6472,c_70,c_11291,c_6523,c_107374])).

tff(c_107395,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6416,c_72,c_8812,c_107393])).

tff(c_107397,plain,(
    m1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_11868])).

tff(c_8048,plain,(
    ! [A_379] :
      ( r1_tarski(u1_struct_0('#skF_4'),u1_struct_0(A_379))
      | ~ m1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_4')),A_379)
      | ~ l1_pre_topc(A_379) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6509,c_2162])).

tff(c_124976,plain,(
    ! [A_1416,A_1417] :
      ( m1_pre_topc('#skF_4',A_1416)
      | ~ m1_pre_topc(A_1416,A_1417)
      | ~ m1_pre_topc('#skF_4',A_1417)
      | ~ l1_pre_topc(A_1417)
      | ~ v2_pre_topc(A_1417)
      | ~ m1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_4')),A_1416)
      | ~ l1_pre_topc(A_1416) ) ),
    inference(resolution,[status(thm)],[c_8048,c_56])).

tff(c_124990,plain,
    ( m1_pre_topc('#skF_4','#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4'))))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ m1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_11330,c_124976])).

tff(c_125021,plain,(
    m1_pre_topc('#skF_4','#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11367,c_107397,c_70,c_68,c_64,c_124990])).

tff(c_125023,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18252,c_125021])).

tff(c_125024,plain,(
    v2_struct_0('#skF_2'('#skF_3','#skF_1'('#skF_3',u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_18176])).

tff(c_539,plain,(
    ! [A_5,B_11] :
      ( ~ v2_struct_0('#skF_2'(A_5,'#skF_1'(A_5,B_11)))
      | ~ v2_tex_2('#skF_1'(A_5,B_11),A_5)
      | v1_xboole_0('#skF_1'(A_5,B_11))
      | ~ v2_pre_topc(A_5)
      | v2_struct_0(A_5)
      | v3_tex_2(B_11,A_5)
      | ~ v2_tex_2(B_11,A_5)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(resolution,[status(thm)],[c_12,c_528])).

tff(c_125027,plain,
    ( ~ v2_tex_2('#skF_1'('#skF_3',u1_struct_0('#skF_4')),'#skF_3')
    | v1_xboole_0('#skF_1'('#skF_3',u1_struct_0('#skF_4')))
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v3_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_125024,c_539])).

tff(c_125030,plain,
    ( v1_xboole_0('#skF_1'('#skF_3',u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_3')
    | v3_tex_2(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_11200,c_6472,c_70,c_11291,c_125027])).

tff(c_125032,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6416,c_72,c_8812,c_125030])).

tff(c_125034,plain,(
    v3_tex_2(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_6314])).

tff(c_635,plain,(
    ! [B_31,A_29] :
      ( v4_tex_2(B_31,A_29)
      | ~ v3_tex_2(u1_struct_0(B_31),A_29)
      | v2_struct_0(A_29)
      | ~ m1_pre_topc(B_31,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_34,c_628])).

tff(c_125086,plain,
    ( v4_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_125034,c_635])).

tff(c_125092,plain,
    ( v4_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_125086])).

tff(c_125094,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_113,c_125092])).

tff(c_125096,plain,(
    ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_3939])).

tff(c_3490,plain,(
    ! [B_31] :
      ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0(B_31))
      | u1_struct_0(B_31) != u1_struct_0('#skF_4')
      | v1_xboole_0(u1_struct_0(B_31))
      | ~ v1_tdlat_3(B_31)
      | v2_struct_0(B_31)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_31,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_849,c_3481])).

tff(c_3499,plain,(
    ! [B_31] :
      ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0(B_31))
      | u1_struct_0(B_31) != u1_struct_0('#skF_4')
      | v1_xboole_0(u1_struct_0(B_31))
      | ~ v1_tdlat_3(B_31)
      | v2_struct_0(B_31)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_31,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3490])).

tff(c_4418,plain,(
    ! [B_325] :
      ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0(B_325))
      | u1_struct_0(B_325) != u1_struct_0('#skF_4')
      | v1_xboole_0(u1_struct_0(B_325))
      | ~ v1_tdlat_3(B_325)
      | v2_struct_0(B_325)
      | ~ m1_pre_topc(B_325,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3499])).

tff(c_4509,plain,(
    ! [B_325] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_3')
      | ~ v2_tex_2(u1_struct_0(B_325),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_325))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_325,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | u1_struct_0(B_325) != u1_struct_0('#skF_4')
      | v1_xboole_0(u1_struct_0(B_325))
      | ~ v1_tdlat_3(B_325)
      | v2_struct_0(B_325)
      | ~ m1_pre_topc(B_325,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4418,c_881])).

tff(c_4648,plain,(
    ! [B_325] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_3')
      | ~ v2_tex_2(u1_struct_0(B_325),'#skF_3')
      | v2_struct_0('#skF_3')
      | u1_struct_0(B_325) != u1_struct_0('#skF_4')
      | v1_xboole_0(u1_struct_0(B_325))
      | ~ v1_tdlat_3(B_325)
      | v2_struct_0(B_325)
      | ~ m1_pre_topc(B_325,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_4509])).

tff(c_4649,plain,(
    ! [B_325] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_3')
      | ~ v2_tex_2(u1_struct_0(B_325),'#skF_3')
      | u1_struct_0(B_325) != u1_struct_0('#skF_4')
      | v1_xboole_0(u1_struct_0(B_325))
      | ~ v1_tdlat_3(B_325)
      | v2_struct_0(B_325)
      | ~ m1_pre_topc(B_325,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_4648])).

tff(c_125322,plain,(
    ! [B_1428] :
      ( ~ v2_tex_2(u1_struct_0(B_1428),'#skF_3')
      | u1_struct_0(B_1428) != u1_struct_0('#skF_4')
      | v1_xboole_0(u1_struct_0(B_1428))
      | ~ v1_tdlat_3(B_1428)
      | v2_struct_0(B_1428)
      | ~ m1_pre_topc(B_1428,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_125096,c_4649])).

tff(c_125335,plain,(
    ! [B_31] :
      ( u1_struct_0(B_31) != u1_struct_0('#skF_4')
      | v1_xboole_0(u1_struct_0(B_31))
      | ~ v1_tdlat_3(B_31)
      | v2_struct_0(B_31)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_31,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_849,c_125322])).

tff(c_125345,plain,(
    ! [B_31] :
      ( u1_struct_0(B_31) != u1_struct_0('#skF_4')
      | v1_xboole_0(u1_struct_0(B_31))
      | ~ v1_tdlat_3(B_31)
      | v2_struct_0(B_31)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_31,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_125335])).

tff(c_125351,plain,(
    ! [B_1429] :
      ( u1_struct_0(B_1429) != u1_struct_0('#skF_4')
      | v1_xboole_0(u1_struct_0(B_1429))
      | ~ v1_tdlat_3(B_1429)
      | v2_struct_0(B_1429)
      | ~ m1_pre_topc(B_1429,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_125345])).

tff(c_125354,plain,
    ( ~ v1_tdlat_3('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_125351,c_408])).

tff(c_125371,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_110,c_125354])).

tff(c_125373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_125371])).

tff(c_125375,plain,(
    ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_125385,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_175,c_125375])).

tff(c_125395,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_125385])).

tff(c_125397,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_125407,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_165,c_125397])).

tff(c_125417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_125407])).

tff(c_125419,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_407])).

tff(c_28,plain,(
    ! [A_22] :
      ( ~ v1_xboole_0(u1_struct_0(A_22))
      | ~ l1_struct_0(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_125424,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_125419,c_28])).

tff(c_125430,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_125424])).

tff(c_125433,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_125430])).

tff(c_125437,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_125433])).

tff(c_125439,plain,(
    v4_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_80,plain,
    ( m1_pre_topc('#skF_5','#skF_3')
    | ~ v1_tdlat_3('#skF_4')
    | ~ v4_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_125463,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125439,c_110,c_80])).

tff(c_125466,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_125463,c_24])).

tff(c_125469,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_125466])).

tff(c_125438,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_82,plain,
    ( v1_tdlat_3('#skF_5')
    | ~ v1_tdlat_3('#skF_4')
    | ~ v4_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_125448,plain,(
    v1_tdlat_3('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125439,c_110,c_82])).

tff(c_126233,plain,(
    ! [B_1577,A_1578] :
      ( v2_tex_2(u1_struct_0(B_1577),A_1578)
      | ~ v1_tdlat_3(B_1577)
      | ~ m1_subset_1(u1_struct_0(B_1577),k1_zfmisc_1(u1_struct_0(A_1578)))
      | ~ m1_pre_topc(B_1577,A_1578)
      | v2_struct_0(B_1577)
      | ~ l1_pre_topc(A_1578)
      | v2_struct_0(A_1578) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_126240,plain,(
    ! [B_31,A_29] :
      ( v2_tex_2(u1_struct_0(B_31),A_29)
      | ~ v1_tdlat_3(B_31)
      | v2_struct_0(B_31)
      | v2_struct_0(A_29)
      | ~ m1_pre_topc(B_31,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_34,c_126233])).

tff(c_125969,plain,(
    ! [B_1541,A_1542] :
      ( v3_tex_2(u1_struct_0(B_1541),A_1542)
      | ~ v4_tex_2(B_1541,A_1542)
      | ~ m1_subset_1(u1_struct_0(B_1541),k1_zfmisc_1(u1_struct_0(A_1542)))
      | ~ m1_pre_topc(B_1541,A_1542)
      | ~ l1_pre_topc(A_1542)
      | v2_struct_0(A_1542) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_125976,plain,(
    ! [B_31,A_29] :
      ( v3_tex_2(u1_struct_0(B_31),A_29)
      | ~ v4_tex_2(B_31,A_29)
      | v2_struct_0(A_29)
      | ~ m1_pre_topc(B_31,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_34,c_125969])).

tff(c_126275,plain,(
    ! [C_1586,B_1587,A_1588] :
      ( g1_pre_topc(u1_struct_0(C_1586),u1_pre_topc(C_1586)) = g1_pre_topc(u1_struct_0(B_1587),u1_pre_topc(B_1587))
      | u1_struct_0(C_1586) != u1_struct_0(B_1587)
      | ~ m1_pre_topc(C_1586,A_1588)
      | ~ m1_pre_topc(B_1587,A_1588)
      | ~ l1_pre_topc(A_1588) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_126281,plain,(
    ! [B_1587] :
      ( g1_pre_topc(u1_struct_0(B_1587),u1_pre_topc(B_1587)) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
      | u1_struct_0(B_1587) != u1_struct_0('#skF_4')
      | ~ m1_pre_topc(B_1587,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_64,c_126275])).

tff(c_126291,plain,(
    ! [B_1589] :
      ( g1_pre_topc(u1_struct_0(B_1589),u1_pre_topc(B_1589)) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
      | u1_struct_0(B_1589) != u1_struct_0('#skF_4')
      | ~ m1_pre_topc(B_1589,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_126281])).

tff(c_76,plain,
    ( g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) != g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
    | ~ v1_tdlat_3('#skF_4')
    | ~ v4_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_125485,plain,(
    g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) != g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125439,c_110,c_76])).

tff(c_126348,plain,
    ( u1_struct_0('#skF_5') != u1_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_126291,c_125485])).

tff(c_126368,plain,(
    u1_struct_0('#skF_5') != u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125463,c_126348])).

tff(c_78,plain,
    ( m1_pre_topc('#skF_4','#skF_5')
    | ~ v1_tdlat_3('#skF_4')
    | ~ v4_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_125471,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125439,c_110,c_78])).

tff(c_125648,plain,(
    ! [B_1492,C_1493,A_1494] :
      ( r1_tarski(u1_struct_0(B_1492),u1_struct_0(C_1493))
      | ~ m1_pre_topc(B_1492,C_1493)
      | ~ m1_pre_topc(C_1493,A_1494)
      | ~ m1_pre_topc(B_1492,A_1494)
      | ~ l1_pre_topc(A_1494)
      | ~ v2_pre_topc(A_1494) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_125654,plain,(
    ! [B_1492] :
      ( r1_tarski(u1_struct_0(B_1492),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_1492,'#skF_4')
      | ~ m1_pre_topc(B_1492,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_64,c_125648])).

tff(c_125664,plain,(
    ! [B_1495] :
      ( r1_tarski(u1_struct_0(B_1495),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_1495,'#skF_4')
      | ~ m1_pre_topc(B_1495,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_125654])).

tff(c_125456,plain,(
    ! [B_1437,A_1438] :
      ( v1_xboole_0(B_1437)
      | ~ m1_subset_1(B_1437,k1_zfmisc_1(A_1438))
      | ~ v1_xboole_0(A_1438) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_125460,plain,(
    ! [A_45,B_46] :
      ( v1_xboole_0(A_45)
      | ~ v1_xboole_0(B_46)
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_52,c_125456])).

tff(c_125683,plain,(
    ! [B_1495] :
      ( v1_xboole_0(u1_struct_0(B_1495))
      | ~ v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_1495,'#skF_4')
      | ~ m1_pre_topc(B_1495,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_125664,c_125460])).

tff(c_125712,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_125683])).

tff(c_125979,plain,(
    ! [B_1543,A_1544] :
      ( v3_tex_2(u1_struct_0(B_1543),A_1544)
      | ~ v4_tex_2(B_1543,A_1544)
      | v2_struct_0(A_1544)
      | ~ m1_pre_topc(B_1543,A_1544)
      | ~ l1_pre_topc(A_1544) ) ),
    inference(resolution,[status(thm)],[c_34,c_125969])).

tff(c_125563,plain,(
    ! [B_1459,A_1460] :
      ( v2_tex_2(B_1459,A_1460)
      | ~ v3_tex_2(B_1459,A_1460)
      | ~ m1_subset_1(B_1459,k1_zfmisc_1(u1_struct_0(A_1460)))
      | ~ l1_pre_topc(A_1460) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_125571,plain,(
    ! [B_31,A_29] :
      ( v2_tex_2(u1_struct_0(B_31),A_29)
      | ~ v3_tex_2(u1_struct_0(B_31),A_29)
      | ~ m1_pre_topc(B_31,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_34,c_125563])).

tff(c_126003,plain,(
    ! [B_1543,A_1544] :
      ( v2_tex_2(u1_struct_0(B_1543),A_1544)
      | ~ v4_tex_2(B_1543,A_1544)
      | v2_struct_0(A_1544)
      | ~ m1_pre_topc(B_1543,A_1544)
      | ~ l1_pre_topc(A_1544) ) ),
    inference(resolution,[status(thm)],[c_125979,c_125571])).

tff(c_126007,plain,(
    ! [A_1549,B_1550] :
      ( u1_struct_0('#skF_2'(A_1549,B_1550)) = B_1550
      | ~ v2_tex_2(B_1550,A_1549)
      | ~ m1_subset_1(B_1550,k1_zfmisc_1(u1_struct_0(A_1549)))
      | v1_xboole_0(B_1550)
      | ~ l1_pre_topc(A_1549)
      | ~ v2_pre_topc(A_1549)
      | v2_struct_0(A_1549) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_126019,plain,(
    ! [A_29,B_31] :
      ( u1_struct_0('#skF_2'(A_29,u1_struct_0(B_31))) = u1_struct_0(B_31)
      | ~ v2_tex_2(u1_struct_0(B_31),A_29)
      | v1_xboole_0(u1_struct_0(B_31))
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29)
      | ~ m1_pre_topc(B_31,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_34,c_126007])).

tff(c_126190,plain,(
    ! [A_1572,B_1573] :
      ( m1_pre_topc('#skF_2'(A_1572,B_1573),A_1572)
      | ~ v2_tex_2(B_1573,A_1572)
      | ~ m1_subset_1(B_1573,k1_zfmisc_1(u1_struct_0(A_1572)))
      | v1_xboole_0(B_1573)
      | ~ l1_pre_topc(A_1572)
      | ~ v2_pre_topc(A_1572)
      | v2_struct_0(A_1572) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_127067,plain,(
    ! [A_1622,B_1623] :
      ( m1_pre_topc('#skF_2'(A_1622,u1_struct_0(B_1623)),A_1622)
      | ~ v2_tex_2(u1_struct_0(B_1623),A_1622)
      | v1_xboole_0(u1_struct_0(B_1623))
      | ~ v2_pre_topc(A_1622)
      | v2_struct_0(A_1622)
      | ~ m1_pre_topc(B_1623,A_1622)
      | ~ l1_pre_topc(A_1622) ) ),
    inference(resolution,[status(thm)],[c_34,c_126190])).

tff(c_127128,plain,(
    ! [A_1622,B_1623] :
      ( l1_pre_topc('#skF_2'(A_1622,u1_struct_0(B_1623)))
      | ~ v2_tex_2(u1_struct_0(B_1623),A_1622)
      | v1_xboole_0(u1_struct_0(B_1623))
      | ~ v2_pre_topc(A_1622)
      | v2_struct_0(A_1622)
      | ~ m1_pre_topc(B_1623,A_1622)
      | ~ l1_pre_topc(A_1622) ) ),
    inference(resolution,[status(thm)],[c_127067,c_24])).

tff(c_125794,plain,(
    ! [A_1521,B_1522] :
      ( v1_pre_topc('#skF_2'(A_1521,B_1522))
      | ~ v2_tex_2(B_1522,A_1521)
      | ~ m1_subset_1(B_1522,k1_zfmisc_1(u1_struct_0(A_1521)))
      | v1_xboole_0(B_1522)
      | ~ l1_pre_topc(A_1521)
      | ~ v2_pre_topc(A_1521)
      | v2_struct_0(A_1521) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_125802,plain,(
    ! [A_29,B_31] :
      ( v1_pre_topc('#skF_2'(A_29,u1_struct_0(B_31)))
      | ~ v2_tex_2(u1_struct_0(B_31),A_29)
      | v1_xboole_0(u1_struct_0(B_31))
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29)
      | ~ m1_pre_topc(B_31,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_34,c_125794])).

tff(c_126199,plain,(
    ! [A_29,B_31] :
      ( m1_pre_topc('#skF_2'(A_29,u1_struct_0(B_31)),A_29)
      | ~ v2_tex_2(u1_struct_0(B_31),A_29)
      | v1_xboole_0(u1_struct_0(B_31))
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29)
      | ~ m1_pre_topc(B_31,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_34,c_126190])).

tff(c_126290,plain,(
    ! [B_1587] :
      ( g1_pre_topc(u1_struct_0(B_1587),u1_pre_topc(B_1587)) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
      | u1_struct_0(B_1587) != u1_struct_0('#skF_4')
      | ~ m1_pre_topc(B_1587,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_126281])).

tff(c_125487,plain,(
    ! [A_1445] :
      ( m1_subset_1(u1_pre_topc(A_1445),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1445))))
      | ~ l1_pre_topc(A_1445) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( l1_pre_topc(g1_pre_topc(A_15,B_16))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(k1_zfmisc_1(A_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_125497,plain,(
    ! [A_1445] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_1445),u1_pre_topc(A_1445)))
      | ~ l1_pre_topc(A_1445) ) ),
    inference(resolution,[status(thm)],[c_125487,c_18])).

tff(c_126345,plain,(
    ! [B_1589] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc(B_1589)
      | u1_struct_0(B_1589) != u1_struct_0('#skF_4')
      | ~ m1_pre_topc(B_1589,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126291,c_125497])).

tff(c_126386,plain,(
    ! [B_1591] :
      ( ~ l1_pre_topc(B_1591)
      | u1_struct_0(B_1591) != u1_struct_0('#skF_4')
      | ~ m1_pre_topc(B_1591,'#skF_3') ) ),
    inference(splitLeft,[status(thm)],[c_126345])).

tff(c_126392,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_126386])).

tff(c_126399,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125446,c_126392])).

tff(c_126400,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_126345])).

tff(c_125510,plain,(
    ! [A_1448,B_1449] :
      ( v1_pre_topc(g1_pre_topc(A_1448,B_1449))
      | ~ m1_subset_1(B_1449,k1_zfmisc_1(k1_zfmisc_1(A_1448))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_125518,plain,(
    ! [A_21] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_21),u1_pre_topc(A_21)))
      | ~ l1_pre_topc(A_21) ) ),
    inference(resolution,[status(thm)],[c_26,c_125510])).

tff(c_126333,plain,(
    ! [B_1589] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc(B_1589)
      | u1_struct_0(B_1589) != u1_struct_0('#skF_4')
      | ~ m1_pre_topc(B_1589,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126291,c_125518])).

tff(c_126445,plain,(
    ! [B_1596] :
      ( ~ l1_pre_topc(B_1596)
      | u1_struct_0(B_1596) != u1_struct_0('#skF_4')
      | ~ m1_pre_topc(B_1596,'#skF_3') ) ),
    inference(splitLeft,[status(thm)],[c_126333])).

tff(c_126451,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_126445])).

tff(c_126458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125446,c_126451])).

tff(c_126459,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_126333])).

tff(c_126279,plain,(
    ! [B_1587] :
      ( g1_pre_topc(u1_struct_0(B_1587),u1_pre_topc(B_1587)) = g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
      | u1_struct_0(B_1587) != u1_struct_0('#skF_5')
      | ~ m1_pre_topc(B_1587,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_125463,c_126275])).

tff(c_126626,plain,(
    ! [B_1600] :
      ( g1_pre_topc(u1_struct_0(B_1600),u1_pre_topc(B_1600)) = g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
      | u1_struct_0(B_1600) != u1_struct_0('#skF_5')
      | ~ m1_pre_topc(B_1600,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_126279])).

tff(c_126862,plain,(
    ! [B_1608] :
      ( g1_pre_topc(u1_struct_0(B_1608),u1_pre_topc(B_1608)) != g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
      | u1_struct_0(B_1608) != u1_struct_0('#skF_5')
      | ~ m1_pre_topc(B_1608,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126626,c_125485])).

tff(c_126879,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != A_1
      | u1_struct_0(A_1) != u1_struct_0('#skF_5')
      | ~ m1_pre_topc(A_1,'#skF_3')
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_126862])).

tff(c_126960,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) != u1_struct_0('#skF_5')
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_3')
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_126879])).

tff(c_126962,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) != u1_struct_0('#skF_5')
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126400,c_126459,c_126960])).

tff(c_126971,plain,(
    ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_126962])).

tff(c_126979,plain,(
    ! [B_1615] :
      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(B_1615),u1_pre_topc(B_1615)),'#skF_3')
      | u1_struct_0(B_1615) != u1_struct_0('#skF_4')
      | ~ m1_pre_topc(B_1615,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126290,c_126971])).

tff(c_127000,plain,(
    ! [A_1] :
      ( ~ m1_pre_topc(A_1,'#skF_3')
      | u1_struct_0(A_1) != u1_struct_0('#skF_4')
      | ~ m1_pre_topc(A_1,'#skF_3')
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_126979])).

tff(c_127077,plain,(
    ! [B_1623] :
      ( u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_1623))) != u1_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_1623)),'#skF_3')
      | ~ v1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_1623)))
      | ~ l1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_1623)))
      | ~ v2_tex_2(u1_struct_0(B_1623),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_1623))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_1623,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_127067,c_127000])).

tff(c_127108,plain,(
    ! [B_1623] :
      ( u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_1623))) != u1_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_1623)),'#skF_3')
      | ~ v1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_1623)))
      | ~ l1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_1623)))
      | ~ v2_tex_2(u1_struct_0(B_1623),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_1623))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_1623,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_127077])).

tff(c_127599,plain,(
    ! [B_1644] :
      ( u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_1644))) != u1_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_1644)),'#skF_3')
      | ~ v1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_1644)))
      | ~ l1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_1644)))
      | ~ v2_tex_2(u1_struct_0(B_1644),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_1644))
      | ~ m1_pre_topc(B_1644,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_127108])).

tff(c_127606,plain,(
    ! [B_31] :
      ( u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_31))) != u1_struct_0('#skF_4')
      | ~ v1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_31)))
      | ~ l1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_31)))
      | ~ v2_tex_2(u1_struct_0(B_31),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_31))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_31,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_126199,c_127599])).

tff(c_127609,plain,(
    ! [B_31] :
      ( u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_31))) != u1_struct_0('#skF_4')
      | ~ v1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_31)))
      | ~ l1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_31)))
      | ~ v2_tex_2(u1_struct_0(B_31),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_31))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_31,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_127606])).

tff(c_128567,plain,(
    ! [B_1647] :
      ( u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_1647))) != u1_struct_0('#skF_4')
      | ~ v1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_1647)))
      | ~ l1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_1647)))
      | ~ v2_tex_2(u1_struct_0(B_1647),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_1647))
      | ~ m1_pre_topc(B_1647,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_127609])).

tff(c_128580,plain,(
    ! [B_31] :
      ( u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_31))) != u1_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_31)))
      | ~ v2_tex_2(u1_struct_0(B_31),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_31))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_31,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_125802,c_128567])).

tff(c_128587,plain,(
    ! [B_31] :
      ( u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_31))) != u1_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_31)))
      | ~ v2_tex_2(u1_struct_0(B_31),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_31))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_31,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_128580])).

tff(c_128676,plain,(
    ! [B_1650] :
      ( u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_1650))) != u1_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_1650)))
      | ~ v2_tex_2(u1_struct_0(B_1650),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_1650))
      | ~ m1_pre_topc(B_1650,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_128587])).

tff(c_128689,plain,(
    ! [B_1623] :
      ( u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_1623))) != u1_struct_0('#skF_4')
      | ~ v2_tex_2(u1_struct_0(B_1623),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_1623))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_1623,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_127128,c_128676])).

tff(c_128696,plain,(
    ! [B_1623] :
      ( u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_1623))) != u1_struct_0('#skF_4')
      | ~ v2_tex_2(u1_struct_0(B_1623),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_1623))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_1623,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_128689])).

tff(c_129655,plain,(
    ! [B_1656] :
      ( u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_1656))) != u1_struct_0('#skF_4')
      | ~ v2_tex_2(u1_struct_0(B_1656),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_1656))
      | ~ m1_pre_topc(B_1656,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_128696])).

tff(c_129674,plain,(
    ! [B_31] :
      ( u1_struct_0(B_31) != u1_struct_0('#skF_4')
      | ~ v2_tex_2(u1_struct_0(B_31),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_31))
      | ~ m1_pre_topc(B_31,'#skF_3')
      | ~ v2_tex_2(u1_struct_0(B_31),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_31))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_31,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126019,c_129655])).

tff(c_129684,plain,(
    ! [B_31] :
      ( u1_struct_0(B_31) != u1_struct_0('#skF_4')
      | ~ v2_tex_2(u1_struct_0(B_31),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_31))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_31,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_129674])).

tff(c_130014,plain,(
    ! [B_1667] :
      ( u1_struct_0(B_1667) != u1_struct_0('#skF_4')
      | ~ v2_tex_2(u1_struct_0(B_1667),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_1667))
      | ~ m1_pre_topc(B_1667,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_129684])).

tff(c_130031,plain,(
    ! [B_1543] :
      ( u1_struct_0(B_1543) != u1_struct_0('#skF_4')
      | v1_xboole_0(u1_struct_0(B_1543))
      | ~ v4_tex_2(B_1543,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_1543,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_126003,c_130014])).

tff(c_130043,plain,(
    ! [B_1543] :
      ( u1_struct_0(B_1543) != u1_struct_0('#skF_4')
      | v1_xboole_0(u1_struct_0(B_1543))
      | ~ v4_tex_2(B_1543,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_1543,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_130031])).

tff(c_130045,plain,(
    ! [B_1668] :
      ( u1_struct_0(B_1668) != u1_struct_0('#skF_4')
      | v1_xboole_0(u1_struct_0(B_1668))
      | ~ v4_tex_2(B_1668,'#skF_3')
      | ~ m1_pre_topc(B_1668,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_130043])).

tff(c_130051,plain,
    ( ~ v4_tex_2('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_130045,c_125712])).

tff(c_130072,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_125439,c_130051])).

tff(c_130074,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_126962])).

tff(c_125585,plain,(
    ! [C_1465,A_1466,D_1467,B_1468] :
      ( C_1465 = A_1466
      | g1_pre_topc(C_1465,D_1467) != g1_pre_topc(A_1466,B_1468)
      | ~ m1_subset_1(B_1468,k1_zfmisc_1(k1_zfmisc_1(A_1466))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_125587,plain,(
    ! [A_1,A_1466,B_1468] :
      ( u1_struct_0(A_1) = A_1466
      | g1_pre_topc(A_1466,B_1468) != A_1
      | ~ m1_subset_1(B_1468,k1_zfmisc_1(k1_zfmisc_1(A_1466)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_125585])).

tff(c_125778,plain,(
    ! [A_1515,B_1516] :
      ( u1_struct_0(g1_pre_topc(A_1515,B_1516)) = A_1515
      | ~ m1_subset_1(B_1516,k1_zfmisc_1(k1_zfmisc_1(A_1515)))
      | ~ v1_pre_topc(g1_pre_topc(A_1515,B_1516))
      | ~ l1_pre_topc(g1_pre_topc(A_1515,B_1516)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_125587])).

tff(c_131062,plain,(
    ! [A_1709] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_1709),u1_pre_topc(A_1709))) = u1_struct_0(A_1709)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_1709),u1_pre_topc(A_1709)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_1709),u1_pre_topc(A_1709)))
      | ~ l1_pre_topc(A_1709) ) ),
    inference(resolution,[status(thm)],[c_26,c_125778])).

tff(c_131083,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = u1_struct_0('#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_126459,c_131062])).

tff(c_131116,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125446,c_126400,c_131083])).

tff(c_130089,plain,(
    ! [B_1587] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_1587),u1_pre_topc(B_1587)),'#skF_3')
      | u1_struct_0(B_1587) != u1_struct_0('#skF_4')
      | ~ m1_pre_topc(B_1587,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126290,c_130074])).

tff(c_131206,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))),'#skF_3')
    | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) != u1_struct_0('#skF_4')
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_131116,c_130089])).

tff(c_131490,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130074,c_131116,c_131206])).

tff(c_131417,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_131116,c_125497])).

tff(c_131611,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126400,c_131417])).

tff(c_131408,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_131116,c_125518])).

tff(c_131605,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126400,c_131408])).

tff(c_131420,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_131116,c_26])).

tff(c_131613,plain,(
    m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126400,c_131420])).

tff(c_125603,plain,(
    ! [A_1466,B_1468] :
      ( u1_struct_0(g1_pre_topc(A_1466,B_1468)) = A_1466
      | ~ m1_subset_1(B_1468,k1_zfmisc_1(k1_zfmisc_1(A_1466)))
      | ~ v1_pre_topc(g1_pre_topc(A_1466,B_1468))
      | ~ l1_pre_topc(g1_pre_topc(A_1466,B_1468)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_125587])).

tff(c_132268,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))) = u1_struct_0('#skF_4')
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))) ),
    inference(resolution,[status(thm)],[c_131613,c_125603])).

tff(c_132291,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))) = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131611,c_131605,c_132268])).

tff(c_130334,plain,(
    ! [A_1678,B_1679] :
      ( m1_pre_topc('#skF_2'(A_1678,u1_struct_0(B_1679)),A_1678)
      | ~ v2_tex_2(u1_struct_0(B_1679),A_1678)
      | v1_xboole_0(u1_struct_0(B_1679))
      | ~ v2_pre_topc(A_1678)
      | v2_struct_0(A_1678)
      | ~ m1_pre_topc(B_1679,A_1678)
      | ~ l1_pre_topc(A_1678) ) ),
    inference(resolution,[status(thm)],[c_34,c_126190])).

tff(c_130397,plain,(
    ! [A_1678,B_1679] :
      ( l1_pre_topc('#skF_2'(A_1678,u1_struct_0(B_1679)))
      | ~ v2_tex_2(u1_struct_0(B_1679),A_1678)
      | v1_xboole_0(u1_struct_0(B_1679))
      | ~ v2_pre_topc(A_1678)
      | v2_struct_0(A_1678)
      | ~ m1_pre_topc(B_1679,A_1678)
      | ~ l1_pre_topc(A_1678) ) ),
    inference(resolution,[status(thm)],[c_130334,c_24])).

tff(c_126355,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = A_1
      | u1_struct_0(A_1) != u1_struct_0('#skF_4')
      | ~ m1_pre_topc(A_1,'#skF_3')
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_126291])).

tff(c_130352,plain,(
    ! [B_1679] :
      ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0(B_1679))
      | u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_1679))) != u1_struct_0('#skF_4')
      | ~ v1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_1679)))
      | ~ l1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_1679)))
      | ~ v2_tex_2(u1_struct_0(B_1679),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_1679))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_1679,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_130334,c_126355])).

tff(c_130385,plain,(
    ! [B_1679] :
      ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0(B_1679))
      | u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_1679))) != u1_struct_0('#skF_4')
      | ~ v1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_1679)))
      | ~ l1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_1679)))
      | ~ v2_tex_2(u1_struct_0(B_1679),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_1679))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_1679,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_130352])).

tff(c_132075,plain,(
    ! [B_1710] :
      ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0(B_1710))
      | u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_1710))) != u1_struct_0('#skF_4')
      | ~ v1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_1710)))
      | ~ l1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_1710)))
      | ~ v2_tex_2(u1_struct_0(B_1710),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_1710))
      | ~ m1_pre_topc(B_1710,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_130385])).

tff(c_132088,plain,(
    ! [B_31] :
      ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0(B_31))
      | u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_31))) != u1_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_31)))
      | ~ v2_tex_2(u1_struct_0(B_31),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_31))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_31,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_125802,c_132075])).

tff(c_132096,plain,(
    ! [B_31] :
      ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0(B_31))
      | u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_31))) != u1_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_31)))
      | ~ v2_tex_2(u1_struct_0(B_31),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_31))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_31,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_132088])).

tff(c_132241,plain,(
    ! [B_1713] :
      ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0(B_1713))
      | u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_1713))) != u1_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_1713)))
      | ~ v2_tex_2(u1_struct_0(B_1713),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_1713))
      | ~ m1_pre_topc(B_1713,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_132096])).

tff(c_132251,plain,(
    ! [B_1679] :
      ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0(B_1679))
      | u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_1679))) != u1_struct_0('#skF_4')
      | ~ v2_tex_2(u1_struct_0(B_1679),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_1679))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_1679,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_130397,c_132241])).

tff(c_132262,plain,(
    ! [B_1679] :
      ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0(B_1679))
      | u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_1679))) != u1_struct_0('#skF_4')
      | ~ v2_tex_2(u1_struct_0(B_1679),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_1679))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_1679,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_132251])).

tff(c_132351,plain,(
    ! [B_1716] :
      ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0(B_1716))
      | u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_1716))) != u1_struct_0('#skF_4')
      | ~ v2_tex_2(u1_struct_0(B_1716),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_1716))
      | ~ m1_pre_topc(B_1716,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_132262])).

tff(c_132360,plain,(
    ! [B_31] :
      ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0(B_31))
      | u1_struct_0(B_31) != u1_struct_0('#skF_4')
      | ~ v2_tex_2(u1_struct_0(B_31),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_31))
      | ~ m1_pre_topc(B_31,'#skF_3')
      | ~ v2_tex_2(u1_struct_0(B_31),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_31))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_31,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126019,c_132351])).

tff(c_132367,plain,(
    ! [B_31] :
      ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0(B_31))
      | u1_struct_0(B_31) != u1_struct_0('#skF_4')
      | ~ v2_tex_2(u1_struct_0(B_31),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_31))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_31,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_132360])).

tff(c_132368,plain,(
    ! [B_31] :
      ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0(B_31))
      | u1_struct_0(B_31) != u1_struct_0('#skF_4')
      | ~ v2_tex_2(u1_struct_0(B_31),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_31))
      | ~ m1_pre_topc(B_31,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_132367])).

tff(c_132526,plain,
    ( '#skF_2'('#skF_3',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
    | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))) != u1_struct_0('#skF_4')
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))))
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_132291,c_132368])).

tff(c_132820,plain,
    ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0('#skF_4'))
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131490,c_132291,c_132291,c_132291,c_132526])).

tff(c_132821,plain,
    ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0('#skF_4'))
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_125712,c_132820])).

tff(c_133944,plain,(
    ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_132821])).

tff(c_133947,plain,
    ( ~ v1_tdlat_3('#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_126240,c_133944])).

tff(c_133953,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_110,c_133947])).

tff(c_133955,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_133953])).

tff(c_133957,plain,(
    v2_tex_2(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_132821])).

tff(c_133956,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_2'('#skF_3',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_132821])).

tff(c_134000,plain,(
    m1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133956,c_130074])).

tff(c_133998,plain,(
    u1_struct_0('#skF_2'('#skF_3',u1_struct_0('#skF_4'))) = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133956,c_131116])).

tff(c_134006,plain,(
    l1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133956,c_126400])).

tff(c_125589,plain,(
    ! [A_1,C_1465,D_1467] :
      ( u1_struct_0(A_1) = C_1465
      | g1_pre_topc(C_1465,D_1467) != A_1
      | ~ m1_subset_1(u1_pre_topc(A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_125585])).

tff(c_141298,plain,(
    ! [C_1811,D_1812] :
      ( u1_struct_0(g1_pre_topc(C_1811,D_1812)) = C_1811
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_1811,D_1812)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_1811,D_1812)))))
      | ~ v1_pre_topc(g1_pre_topc(C_1811,D_1812))
      | ~ l1_pre_topc(g1_pre_topc(C_1811,D_1812)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_125589])).

tff(c_142636,plain,(
    ! [C_1827,D_1828] :
      ( u1_struct_0(g1_pre_topc(C_1827,D_1828)) = C_1827
      | ~ v1_pre_topc(g1_pre_topc(C_1827,D_1828))
      | ~ l1_pre_topc(g1_pre_topc(C_1827,D_1828)) ) ),
    inference(resolution,[status(thm)],[c_26,c_141298])).

tff(c_144708,plain,(
    ! [A_1863] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_1863),u1_pre_topc(A_1863))) = u1_struct_0(A_1863)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_1863),u1_pre_topc(A_1863)))
      | ~ l1_pre_topc(A_1863) ) ),
    inference(resolution,[status(thm)],[c_125518,c_142636])).

tff(c_144803,plain,(
    ! [A_1864] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_1864),u1_pre_topc(A_1864))) = u1_struct_0(A_1864)
      | ~ l1_pre_topc(A_1864) ) ),
    inference(resolution,[status(thm)],[c_125497,c_144708])).

tff(c_125549,plain,(
    ! [B_1455,A_1456] :
      ( m1_subset_1(u1_struct_0(B_1455),k1_zfmisc_1(u1_struct_0(A_1456)))
      | ~ m1_pre_topc(B_1455,A_1456)
      | ~ l1_pre_topc(A_1456) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_125557,plain,(
    ! [B_1455,A_1456] :
      ( r1_tarski(u1_struct_0(B_1455),u1_struct_0(A_1456))
      | ~ m1_pre_topc(B_1455,A_1456)
      | ~ l1_pre_topc(A_1456) ) ),
    inference(resolution,[status(thm)],[c_125549,c_50])).

tff(c_145972,plain,(
    ! [A_1878,A_1879] :
      ( r1_tarski(u1_struct_0(A_1878),u1_struct_0(A_1879))
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(A_1878),u1_pre_topc(A_1878)),A_1879)
      | ~ l1_pre_topc(A_1879)
      | ~ l1_pre_topc(A_1878) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144803,c_125557])).

tff(c_146047,plain,(
    ! [B_1587] :
      ( r1_tarski(u1_struct_0(B_1587),u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(B_1587)
      | u1_struct_0(B_1587) != u1_struct_0('#skF_4')
      | ~ m1_pre_topc(B_1587,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_130089,c_145972])).

tff(c_146075,plain,(
    ! [B_1880] :
      ( r1_tarski(u1_struct_0(B_1880),u1_struct_0('#skF_3'))
      | ~ l1_pre_topc(B_1880)
      | u1_struct_0(B_1880) != u1_struct_0('#skF_4')
      | ~ m1_pre_topc(B_1880,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_146047])).

tff(c_146125,plain,
    ( r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | u1_struct_0('#skF_2'('#skF_3',u1_struct_0('#skF_4'))) != u1_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_133998,c_146075])).

tff(c_146168,plain,(
    r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134000,c_133998,c_134006,c_146125])).

tff(c_125704,plain,(
    ! [B_1497,A_1498] :
      ( r1_tarski(B_1497,'#skF_1'(A_1498,B_1497))
      | v3_tex_2(B_1497,A_1498)
      | ~ v2_tex_2(B_1497,A_1498)
      | ~ m1_subset_1(B_1497,k1_zfmisc_1(u1_struct_0(A_1498)))
      | ~ l1_pre_topc(A_1498) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_125711,plain,(
    ! [A_45,A_1498] :
      ( r1_tarski(A_45,'#skF_1'(A_1498,A_45))
      | v3_tex_2(A_45,A_1498)
      | ~ v2_tex_2(A_45,A_1498)
      | ~ l1_pre_topc(A_1498)
      | ~ r1_tarski(A_45,u1_struct_0(A_1498)) ) ),
    inference(resolution,[status(thm)],[c_52,c_125704])).

tff(c_146189,plain,
    ( r1_tarski(u1_struct_0('#skF_4'),'#skF_1'('#skF_3',u1_struct_0('#skF_4')))
    | v3_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_146168,c_125711])).

tff(c_146227,plain,
    ( r1_tarski(u1_struct_0('#skF_4'),'#skF_1'('#skF_3',u1_struct_0('#skF_4')))
    | v3_tex_2(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_133957,c_146189])).

tff(c_146270,plain,(
    v3_tex_2(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_146227])).

tff(c_151302,plain,(
    ! [A_1952,A_1953] :
      ( m1_subset_1(u1_struct_0(A_1952),k1_zfmisc_1(u1_struct_0(A_1953)))
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(A_1952),u1_pre_topc(A_1952)),A_1953)
      | ~ l1_pre_topc(A_1953)
      | ~ l1_pre_topc(A_1952) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144803,c_34])).

tff(c_151362,plain,(
    ! [B_1587] :
      ( m1_subset_1(u1_struct_0(B_1587),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(B_1587)
      | u1_struct_0(B_1587) != u1_struct_0('#skF_4')
      | ~ m1_pre_topc(B_1587,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_130089,c_151302])).

tff(c_151388,plain,(
    ! [B_1954] :
      ( m1_subset_1(u1_struct_0(B_1954),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc(B_1954)
      | u1_struct_0(B_1954) != u1_struct_0('#skF_4')
      | ~ m1_pre_topc(B_1954,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_151362])).

tff(c_151455,plain,
    ( m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | u1_struct_0('#skF_2'('#skF_3',u1_struct_0('#skF_4'))) != u1_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_133998,c_151388])).

tff(c_151518,plain,(
    m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134000,c_133998,c_134006,c_151455])).

tff(c_125652,plain,(
    ! [B_1492] :
      ( r1_tarski(u1_struct_0(B_1492),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_1492,'#skF_5')
      | ~ m1_pre_topc(B_1492,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_125463,c_125648])).

tff(c_125684,plain,(
    ! [B_1496] :
      ( r1_tarski(u1_struct_0(B_1496),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_1496,'#skF_5')
      | ~ m1_pre_topc(B_1496,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_125652])).

tff(c_125703,plain,(
    ! [B_1496] :
      ( v1_xboole_0(u1_struct_0(B_1496))
      | ~ v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_1496,'#skF_5')
      | ~ m1_pre_topc(B_1496,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_125684,c_125460])).

tff(c_125713,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_125703])).

tff(c_126736,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = A_1
      | u1_struct_0(A_1) != u1_struct_0('#skF_5')
      | ~ m1_pre_topc(A_1,'#skF_3')
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_126626])).

tff(c_130349,plain,(
    ! [B_1679] :
      ( g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_2'('#skF_3',u1_struct_0(B_1679))
      | u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_1679))) != u1_struct_0('#skF_5')
      | ~ v1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_1679)))
      | ~ l1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_1679)))
      | ~ v2_tex_2(u1_struct_0(B_1679),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_1679))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_1679,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_130334,c_126736])).

tff(c_130381,plain,(
    ! [B_1679] :
      ( g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_2'('#skF_3',u1_struct_0(B_1679))
      | u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_1679))) != u1_struct_0('#skF_5')
      | ~ v1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_1679)))
      | ~ l1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_1679)))
      | ~ v2_tex_2(u1_struct_0(B_1679),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_1679))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_1679,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_130349])).

tff(c_134886,plain,(
    ! [B_1739] :
      ( g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_2'('#skF_3',u1_struct_0(B_1739))
      | u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_1739))) != u1_struct_0('#skF_5')
      | ~ v1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_1739)))
      | ~ l1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_1739)))
      | ~ v2_tex_2(u1_struct_0(B_1739),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_1739))
      | ~ m1_pre_topc(B_1739,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_130381])).

tff(c_134905,plain,(
    ! [B_31] :
      ( g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_2'('#skF_3',u1_struct_0(B_31))
      | u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_31))) != u1_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_31)))
      | ~ v2_tex_2(u1_struct_0(B_31),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_31))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_31,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_125802,c_134886])).

tff(c_134919,plain,(
    ! [B_31] :
      ( g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_2'('#skF_3',u1_struct_0(B_31))
      | u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_31))) != u1_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_31)))
      | ~ v2_tex_2(u1_struct_0(B_31),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_31))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_31,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_134905])).

tff(c_135038,plain,(
    ! [B_1743] :
      ( g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_2'('#skF_3',u1_struct_0(B_1743))
      | u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_1743))) != u1_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_2'('#skF_3',u1_struct_0(B_1743)))
      | ~ v2_tex_2(u1_struct_0(B_1743),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_1743))
      | ~ m1_pre_topc(B_1743,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_134919])).

tff(c_135054,plain,(
    ! [B_1679] :
      ( g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_2'('#skF_3',u1_struct_0(B_1679))
      | u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_1679))) != u1_struct_0('#skF_5')
      | ~ v2_tex_2(u1_struct_0(B_1679),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_1679))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_1679,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_130397,c_135038])).

tff(c_135071,plain,(
    ! [B_1679] :
      ( g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_2'('#skF_3',u1_struct_0(B_1679))
      | u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_1679))) != u1_struct_0('#skF_5')
      | ~ v2_tex_2(u1_struct_0(B_1679),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_1679))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_1679,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_135054])).

tff(c_135768,plain,(
    ! [B_1746] :
      ( g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_2'('#skF_3',u1_struct_0(B_1746))
      | u1_struct_0('#skF_2'('#skF_3',u1_struct_0(B_1746))) != u1_struct_0('#skF_5')
      | ~ v2_tex_2(u1_struct_0(B_1746),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_1746))
      | ~ m1_pre_topc(B_1746,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_135071])).

tff(c_135783,plain,(
    ! [B_31] :
      ( g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_2'('#skF_3',u1_struct_0(B_31))
      | u1_struct_0(B_31) != u1_struct_0('#skF_5')
      | ~ v2_tex_2(u1_struct_0(B_31),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_31))
      | ~ m1_pre_topc(B_31,'#skF_3')
      | ~ v2_tex_2(u1_struct_0(B_31),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_31))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_31,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126019,c_135768])).

tff(c_135798,plain,(
    ! [B_31] :
      ( g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_2'('#skF_3',u1_struct_0(B_31))
      | u1_struct_0(B_31) != u1_struct_0('#skF_5')
      | ~ v2_tex_2(u1_struct_0(B_31),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_31))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_31,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_135783])).

tff(c_136358,plain,(
    ! [B_1767] :
      ( g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_2'('#skF_3',u1_struct_0(B_1767))
      | u1_struct_0(B_1767) != u1_struct_0('#skF_5')
      | ~ v2_tex_2(u1_struct_0(B_1767),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_1767))
      | ~ m1_pre_topc(B_1767,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_135798])).

tff(c_136374,plain,(
    ! [B_1543] :
      ( g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_2'('#skF_3',u1_struct_0(B_1543))
      | u1_struct_0(B_1543) != u1_struct_0('#skF_5')
      | v1_xboole_0(u1_struct_0(B_1543))
      | ~ v4_tex_2(B_1543,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_1543,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_126003,c_136358])).

tff(c_136394,plain,(
    ! [B_1543] :
      ( g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_2'('#skF_3',u1_struct_0(B_1543))
      | u1_struct_0(B_1543) != u1_struct_0('#skF_5')
      | v1_xboole_0(u1_struct_0(B_1543))
      | ~ v4_tex_2(B_1543,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_1543,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_136374])).

tff(c_136545,plain,(
    ! [B_1776] :
      ( g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_2'('#skF_3',u1_struct_0(B_1776))
      | u1_struct_0(B_1776) != u1_struct_0('#skF_5')
      | v1_xboole_0(u1_struct_0(B_1776))
      | ~ v4_tex_2(B_1776,'#skF_3')
      | ~ m1_pre_topc(B_1776,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_136394])).

tff(c_136606,plain,(
    ! [B_1776] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')),'#skF_3')
      | ~ v2_tex_2(u1_struct_0(B_1776),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_1776))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_1776,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | u1_struct_0(B_1776) != u1_struct_0('#skF_5')
      | v1_xboole_0(u1_struct_0(B_1776))
      | ~ v4_tex_2(B_1776,'#skF_3')
      | ~ m1_pre_topc(B_1776,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136545,c_126199])).

tff(c_136741,plain,(
    ! [B_1776] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')),'#skF_3')
      | ~ v2_tex_2(u1_struct_0(B_1776),'#skF_3')
      | v2_struct_0('#skF_3')
      | u1_struct_0(B_1776) != u1_struct_0('#skF_5')
      | v1_xboole_0(u1_struct_0(B_1776))
      | ~ v4_tex_2(B_1776,'#skF_3')
      | ~ m1_pre_topc(B_1776,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_136606])).

tff(c_136742,plain,(
    ! [B_1776] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')),'#skF_3')
      | ~ v2_tex_2(u1_struct_0(B_1776),'#skF_3')
      | u1_struct_0(B_1776) != u1_struct_0('#skF_5')
      | v1_xboole_0(u1_struct_0(B_1776))
      | ~ v4_tex_2(B_1776,'#skF_3')
      | ~ m1_pre_topc(B_1776,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_136741])).

tff(c_139634,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_136742])).

tff(c_126716,plain,(
    ! [B_1600] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ l1_pre_topc(B_1600)
      | u1_struct_0(B_1600) != u1_struct_0('#skF_5')
      | ~ m1_pre_topc(B_1600,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126626,c_125497])).

tff(c_126907,plain,(
    ! [B_1609] :
      ( ~ l1_pre_topc(B_1609)
      | u1_struct_0(B_1609) != u1_struct_0('#skF_5')
      | ~ m1_pre_topc(B_1609,'#skF_3') ) ),
    inference(splitLeft,[status(thm)],[c_126716])).

tff(c_126910,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_125463,c_126907])).

tff(c_126917,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125469,c_126910])).

tff(c_126918,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_126716])).

tff(c_126704,plain,(
    ! [B_1600] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ l1_pre_topc(B_1600)
      | u1_struct_0(B_1600) != u1_struct_0('#skF_5')
      | ~ m1_pre_topc(B_1600,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126626,c_125518])).

tff(c_126845,plain,(
    ! [B_1607] :
      ( ~ l1_pre_topc(B_1607)
      | u1_struct_0(B_1607) != u1_struct_0('#skF_5')
      | ~ m1_pre_topc(B_1607,'#skF_3') ) ),
    inference(splitLeft,[status(thm)],[c_126704])).

tff(c_126848,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_125463,c_126845])).

tff(c_126855,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125469,c_126848])).

tff(c_126856,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_126704])).

tff(c_131068,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) = u1_struct_0('#skF_5')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_126856,c_131062])).

tff(c_131107,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) = u1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125469,c_126918,c_131068])).

tff(c_131880,plain,(
    ! [A_1456] :
      ( r1_tarski(u1_struct_0('#skF_5'),u1_struct_0(A_1456))
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')),A_1456)
      | ~ l1_pre_topc(A_1456) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131107,c_125557])).

tff(c_139646,plain,
    ( r1_tarski(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_139634,c_131880])).

tff(c_139690,plain,(
    r1_tarski(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_139646])).

tff(c_125863,plain,(
    ! [A_1529,B_1530] :
      ( v1_tdlat_3('#skF_2'(A_1529,B_1530))
      | ~ v2_tex_2(B_1530,A_1529)
      | ~ m1_subset_1(B_1530,k1_zfmisc_1(u1_struct_0(A_1529)))
      | v1_xboole_0(B_1530)
      | ~ l1_pre_topc(A_1529)
      | ~ v2_pre_topc(A_1529)
      | v2_struct_0(A_1529) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_125872,plain,(
    ! [A_1529,A_45] :
      ( v1_tdlat_3('#skF_2'(A_1529,A_45))
      | ~ v2_tex_2(A_45,A_1529)
      | v1_xboole_0(A_45)
      | ~ l1_pre_topc(A_1529)
      | ~ v2_pre_topc(A_1529)
      | v2_struct_0(A_1529)
      | ~ r1_tarski(A_45,u1_struct_0(A_1529)) ) ),
    inference(resolution,[status(thm)],[c_52,c_125863])).

tff(c_139734,plain,
    ( v1_tdlat_3('#skF_2'('#skF_3',u1_struct_0('#skF_5')))
    | ~ v2_tex_2(u1_struct_0('#skF_5'),'#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_139690,c_125872])).

tff(c_139768,plain,
    ( v1_tdlat_3('#skF_2'('#skF_3',u1_struct_0('#skF_5')))
    | ~ v2_tex_2(u1_struct_0('#skF_5'),'#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_139734])).

tff(c_139769,plain,
    ( v1_tdlat_3('#skF_2'('#skF_3',u1_struct_0('#skF_5')))
    | ~ v2_tex_2(u1_struct_0('#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_125713,c_139768])).

tff(c_140130,plain,(
    ~ v2_tex_2(u1_struct_0('#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_139769])).

tff(c_140133,plain,
    ( ~ v1_tdlat_3('#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_126240,c_140130])).

tff(c_140139,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_125463,c_125448,c_140133])).

tff(c_140141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_125438,c_140139])).

tff(c_140143,plain,(
    v2_tex_2(u1_struct_0('#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_139769])).

tff(c_126200,plain,(
    ! [A_1572,A_45] :
      ( m1_pre_topc('#skF_2'(A_1572,A_45),A_1572)
      | ~ v2_tex_2(A_45,A_1572)
      | v1_xboole_0(A_45)
      | ~ l1_pre_topc(A_1572)
      | ~ v2_pre_topc(A_1572)
      | v2_struct_0(A_1572)
      | ~ r1_tarski(A_45,u1_struct_0(A_1572)) ) ),
    inference(resolution,[status(thm)],[c_52,c_126190])).

tff(c_139725,plain,
    ( m1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_5')),'#skF_3')
    | ~ v2_tex_2(u1_struct_0('#skF_5'),'#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_139690,c_126200])).

tff(c_139757,plain,
    ( m1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_5')),'#skF_3')
    | ~ v2_tex_2(u1_struct_0('#skF_5'),'#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_139725])).

tff(c_139758,plain,
    ( m1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_5')),'#skF_3')
    | ~ v2_tex_2(u1_struct_0('#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_125713,c_139757])).

tff(c_140226,plain,(
    m1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_5')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140143,c_139758])).

tff(c_135799,plain,(
    ! [B_31] :
      ( g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_2'('#skF_3',u1_struct_0(B_31))
      | u1_struct_0(B_31) != u1_struct_0('#skF_5')
      | ~ v2_tex_2(u1_struct_0(B_31),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_31))
      | ~ m1_pre_topc(B_31,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_135798])).

tff(c_140145,plain,
    ( g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_2'('#skF_3',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_140143,c_135799])).

tff(c_140157,plain,
    ( g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_2'('#skF_3',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125463,c_140145])).

tff(c_140158,plain,(
    g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_2'('#skF_3',u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_125713,c_140157])).

tff(c_140304,plain,(
    u1_struct_0('#skF_2'('#skF_3',u1_struct_0('#skF_5'))) = u1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140158,c_131107])).

tff(c_140255,plain,
    ( l1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_140226,c_24])).

tff(c_140287,plain,(
    l1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_140255])).

tff(c_126287,plain,(
    ! [B_1587] :
      ( g1_pre_topc(u1_struct_0(B_1587),u1_pre_topc(B_1587)) = g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
      | u1_struct_0(B_1587) != u1_struct_0('#skF_5')
      | ~ m1_pre_topc(B_1587,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_126279])).

tff(c_139675,plain,(
    ! [B_1587] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_1587),u1_pre_topc(B_1587)),'#skF_3')
      | u1_struct_0(B_1587) != u1_struct_0('#skF_5')
      | ~ m1_pre_topc(B_1587,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126287,c_139634])).

tff(c_151322,plain,(
    ! [B_1587] :
      ( m1_subset_1(u1_struct_0(B_1587),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(B_1587)
      | u1_struct_0(B_1587) != u1_struct_0('#skF_5')
      | ~ m1_pre_topc(B_1587,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_139675,c_151302])).

tff(c_151830,plain,(
    ! [B_1958] :
      ( m1_subset_1(u1_struct_0(B_1958),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc(B_1958)
      | u1_struct_0(B_1958) != u1_struct_0('#skF_5')
      | ~ m1_pre_topc(B_1958,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_151322])).

tff(c_151885,plain,
    ( m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_5')))
    | u1_struct_0('#skF_2'('#skF_3',u1_struct_0('#skF_5'))) != u1_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_2'('#skF_3',u1_struct_0('#skF_5')),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_140304,c_151830])).

tff(c_151958,plain,(
    m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140226,c_140304,c_140287,c_151885])).

tff(c_126422,plain,(
    ! [C_1593,B_1594,A_1595] :
      ( C_1593 = B_1594
      | ~ r1_tarski(B_1594,C_1593)
      | ~ v2_tex_2(C_1593,A_1595)
      | ~ m1_subset_1(C_1593,k1_zfmisc_1(u1_struct_0(A_1595)))
      | ~ v3_tex_2(B_1594,A_1595)
      | ~ m1_subset_1(B_1594,k1_zfmisc_1(u1_struct_0(A_1595)))
      | ~ l1_pre_topc(A_1595) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_164682,plain,(
    ! [B_2118,A_2119,A_2120] :
      ( u1_struct_0(B_2118) = u1_struct_0(A_2119)
      | ~ v2_tex_2(u1_struct_0(A_2119),A_2120)
      | ~ m1_subset_1(u1_struct_0(A_2119),k1_zfmisc_1(u1_struct_0(A_2120)))
      | ~ v3_tex_2(u1_struct_0(B_2118),A_2120)
      | ~ m1_subset_1(u1_struct_0(B_2118),k1_zfmisc_1(u1_struct_0(A_2120)))
      | ~ l1_pre_topc(A_2120)
      | ~ m1_pre_topc(B_2118,A_2119)
      | ~ l1_pre_topc(A_2119) ) ),
    inference(resolution,[status(thm)],[c_125557,c_126422])).

tff(c_164692,plain,(
    ! [B_2118] :
      ( u1_struct_0(B_2118) = u1_struct_0('#skF_5')
      | ~ v2_tex_2(u1_struct_0('#skF_5'),'#skF_3')
      | ~ v3_tex_2(u1_struct_0(B_2118),'#skF_3')
      | ~ m1_subset_1(u1_struct_0(B_2118),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc(B_2118,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_151958,c_164682])).

tff(c_165172,plain,(
    ! [B_2126] :
      ( u1_struct_0(B_2126) = u1_struct_0('#skF_5')
      | ~ v3_tex_2(u1_struct_0(B_2126),'#skF_3')
      | ~ m1_subset_1(u1_struct_0(B_2126),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_2126,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125469,c_68,c_140143,c_164692])).

tff(c_165190,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_4')
    | ~ v3_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_151518,c_165172])).

tff(c_165243,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125471,c_146270,c_165190])).

tff(c_165245,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126368,c_165243])).

tff(c_165247,plain,(
    ~ v3_tex_2(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_146227])).

tff(c_165250,plain,
    ( ~ v4_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_125976,c_165247])).

tff(c_165256,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_125439,c_165250])).

tff(c_165258,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_165256])).

tff(c_165260,plain,(
    ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_136742])).

tff(c_136371,plain,(
    ! [B_31] :
      ( g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_2'('#skF_3',u1_struct_0(B_31))
      | u1_struct_0(B_31) != u1_struct_0('#skF_5')
      | v1_xboole_0(u1_struct_0(B_31))
      | ~ v1_tdlat_3(B_31)
      | v2_struct_0(B_31)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_31,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_126240,c_136358])).

tff(c_136390,plain,(
    ! [B_31] :
      ( g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_2'('#skF_3',u1_struct_0(B_31))
      | u1_struct_0(B_31) != u1_struct_0('#skF_5')
      | v1_xboole_0(u1_struct_0(B_31))
      | ~ v1_tdlat_3(B_31)
      | v2_struct_0(B_31)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_31,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_136371])).

tff(c_137011,plain,(
    ! [B_1785] :
      ( g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_2'('#skF_3',u1_struct_0(B_1785))
      | u1_struct_0(B_1785) != u1_struct_0('#skF_5')
      | v1_xboole_0(u1_struct_0(B_1785))
      | ~ v1_tdlat_3(B_1785)
      | v2_struct_0(B_1785)
      | ~ m1_pre_topc(B_1785,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_136390])).

tff(c_137092,plain,(
    ! [B_1785] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')),'#skF_3')
      | ~ v2_tex_2(u1_struct_0(B_1785),'#skF_3')
      | v1_xboole_0(u1_struct_0(B_1785))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_1785,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | u1_struct_0(B_1785) != u1_struct_0('#skF_5')
      | v1_xboole_0(u1_struct_0(B_1785))
      | ~ v1_tdlat_3(B_1785)
      | v2_struct_0(B_1785)
      | ~ m1_pre_topc(B_1785,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137011,c_126199])).

tff(c_137240,plain,(
    ! [B_1785] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')),'#skF_3')
      | ~ v2_tex_2(u1_struct_0(B_1785),'#skF_3')
      | v2_struct_0('#skF_3')
      | u1_struct_0(B_1785) != u1_struct_0('#skF_5')
      | v1_xboole_0(u1_struct_0(B_1785))
      | ~ v1_tdlat_3(B_1785)
      | v2_struct_0(B_1785)
      | ~ m1_pre_topc(B_1785,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_137092])).

tff(c_137241,plain,(
    ! [B_1785] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')),'#skF_3')
      | ~ v2_tex_2(u1_struct_0(B_1785),'#skF_3')
      | u1_struct_0(B_1785) != u1_struct_0('#skF_5')
      | v1_xboole_0(u1_struct_0(B_1785))
      | ~ v1_tdlat_3(B_1785)
      | v2_struct_0(B_1785)
      | ~ m1_pre_topc(B_1785,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_137240])).

tff(c_168922,plain,(
    ! [B_2156] :
      ( ~ v2_tex_2(u1_struct_0(B_2156),'#skF_3')
      | u1_struct_0(B_2156) != u1_struct_0('#skF_5')
      | v1_xboole_0(u1_struct_0(B_2156))
      | ~ v1_tdlat_3(B_2156)
      | v2_struct_0(B_2156)
      | ~ m1_pre_topc(B_2156,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_165260,c_137241])).

tff(c_168950,plain,(
    ! [B_31] :
      ( u1_struct_0(B_31) != u1_struct_0('#skF_5')
      | v1_xboole_0(u1_struct_0(B_31))
      | ~ v1_tdlat_3(B_31)
      | v2_struct_0(B_31)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_31,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_126240,c_168922])).

tff(c_168971,plain,(
    ! [B_31] :
      ( u1_struct_0(B_31) != u1_struct_0('#skF_5')
      | v1_xboole_0(u1_struct_0(B_31))
      | ~ v1_tdlat_3(B_31)
      | v2_struct_0(B_31)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_31,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_168950])).

tff(c_169073,plain,(
    ! [B_2160] :
      ( u1_struct_0(B_2160) != u1_struct_0('#skF_5')
      | v1_xboole_0(u1_struct_0(B_2160))
      | ~ v1_tdlat_3(B_2160)
      | v2_struct_0(B_2160)
      | ~ m1_pre_topc(B_2160,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_168971])).

tff(c_169091,plain,
    ( ~ v1_tdlat_3('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_169073,c_125713])).

tff(c_169129,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125463,c_125448,c_169091])).

tff(c_169131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_125438,c_169129])).

tff(c_169133,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_125703])).

tff(c_169138,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_169133,c_28])).

tff(c_169144,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_125438,c_169138])).

tff(c_169157,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_169144])).

tff(c_169161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125469,c_169157])).

tff(c_169163,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_125683])).

tff(c_169168,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_169163,c_28])).

tff(c_169174,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_169168])).

tff(c_169177,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_169174])).

tff(c_169181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125446,c_169177])).

tff(c_169183,plain,(
    ~ v1_tdlat_3('#skF_4') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_169182,plain,(
    v4_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_169504,plain,(
    ! [B_2256,A_2257] :
      ( v3_tex_2(u1_struct_0(B_2256),A_2257)
      | ~ v4_tex_2(B_2256,A_2257)
      | ~ m1_subset_1(u1_struct_0(B_2256),k1_zfmisc_1(u1_struct_0(A_2257)))
      | ~ m1_pre_topc(B_2256,A_2257)
      | ~ l1_pre_topc(A_2257)
      | v2_struct_0(A_2257) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_169513,plain,(
    ! [B_2258,A_2259] :
      ( v3_tex_2(u1_struct_0(B_2258),A_2259)
      | ~ v4_tex_2(B_2258,A_2259)
      | v2_struct_0(A_2259)
      | ~ m1_pre_topc(B_2258,A_2259)
      | ~ l1_pre_topc(A_2259) ) ),
    inference(resolution,[status(thm)],[c_34,c_169504])).

tff(c_169296,plain,(
    ! [B_2194,A_2195] :
      ( v2_tex_2(B_2194,A_2195)
      | ~ v3_tex_2(B_2194,A_2195)
      | ~ m1_subset_1(B_2194,k1_zfmisc_1(u1_struct_0(A_2195)))
      | ~ l1_pre_topc(A_2195) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_169304,plain,(
    ! [B_31,A_29] :
      ( v2_tex_2(u1_struct_0(B_31),A_29)
      | ~ v3_tex_2(u1_struct_0(B_31),A_29)
      | ~ m1_pre_topc(B_31,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_34,c_169296])).

tff(c_169525,plain,(
    ! [B_2258,A_2259] :
      ( v2_tex_2(u1_struct_0(B_2258),A_2259)
      | ~ v4_tex_2(B_2258,A_2259)
      | v2_struct_0(A_2259)
      | ~ m1_pre_topc(B_2258,A_2259)
      | ~ l1_pre_topc(A_2259) ) ),
    inference(resolution,[status(thm)],[c_169513,c_169304])).

tff(c_169808,plain,(
    ! [B_2302,A_2303] :
      ( v1_tdlat_3(B_2302)
      | ~ v2_tex_2(u1_struct_0(B_2302),A_2303)
      | ~ m1_subset_1(u1_struct_0(B_2302),k1_zfmisc_1(u1_struct_0(A_2303)))
      | ~ m1_pre_topc(B_2302,A_2303)
      | v2_struct_0(B_2302)
      | ~ l1_pre_topc(A_2303)
      | v2_struct_0(A_2303) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_169817,plain,(
    ! [B_2304,A_2305] :
      ( v1_tdlat_3(B_2304)
      | ~ v2_tex_2(u1_struct_0(B_2304),A_2305)
      | v2_struct_0(B_2304)
      | v2_struct_0(A_2305)
      | ~ m1_pre_topc(B_2304,A_2305)
      | ~ l1_pre_topc(A_2305) ) ),
    inference(resolution,[status(thm)],[c_34,c_169808])).

tff(c_169834,plain,(
    ! [B_2307,A_2308] :
      ( v1_tdlat_3(B_2307)
      | v2_struct_0(B_2307)
      | ~ v4_tex_2(B_2307,A_2308)
      | v2_struct_0(A_2308)
      | ~ m1_pre_topc(B_2307,A_2308)
      | ~ l1_pre_topc(A_2308) ) ),
    inference(resolution,[status(thm)],[c_169525,c_169817])).

tff(c_169837,plain,
    ( v1_tdlat_3('#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_169182,c_169834])).

tff(c_169840,plain,
    ( v1_tdlat_3('#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_169837])).

tff(c_169842,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_169183,c_169840])).

%------------------------------------------------------------------------------
