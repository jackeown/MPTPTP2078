%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:05 EST 2020

% Result     : Theorem 14.27s
% Output     : CNFRefutation 14.27s
% Verified   : 
% Statistics : Number of formulae       :  297 (1332 expanded)
%              Number of leaves         :   61 ( 465 expanded)
%              Depth                    :   16
%              Number of atoms          :  740 (4015 expanded)
%              Number of equality atoms :   98 ( 395 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tsep_1 > v1_tops_1 > v1_subset_1 > v1_borsuk_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k9_setfam_1 > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v1_borsuk_1,type,(
    v1_borsuk_1: ( $i * $i ) > $o )).

tff(f_310,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tex_2(B,A)
            <=> ~ v1_subset_1(B,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).

tff(f_39,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_189,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_143,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ~ v1_subset_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).

tff(f_220,axiom,(
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

tff(f_167,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_borsuk_1(B,A)
            & v1_tsep_1(B,A)
            & v1_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_tdlat_3)).

tff(f_182,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_136,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_borsuk_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v4_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tsep_1)).

tff(f_245,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_292,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v1_tops_1(B,A)
              & v2_tex_2(B,A) )
           => v3_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).

tff(f_118,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v3_pre_topc(B,A)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_tops_1)).

tff(f_37,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_subset_1)).

tff(f_27,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_260,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_231,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).

tff(f_276,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v3_pre_topc(B,A)
              & v3_tex_2(B,A) )
           => v1_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).

tff(f_199,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_subset_1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(A)) )
     => ~ v1_xboole_0(k3_subset_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tex_2)).

tff(c_104,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_102,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_98,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_106,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_160,plain,(
    ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_8,plain,(
    ! [A_5] : k2_subset_1(A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_115,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_12])).

tff(c_112,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_162,plain,(
    ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_112])).

tff(c_96,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_254,plain,(
    ! [B_103,A_104] :
      ( v1_subset_1(B_103,A_104)
      | B_103 = A_104
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_269,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_96,c_254])).

tff(c_278,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_269])).

tff(c_3493,plain,(
    ! [A_306,B_307] :
      ( k2_pre_topc(A_306,B_307) = B_307
      | ~ v4_pre_topc(B_307,A_306)
      | ~ m1_subset_1(B_307,k1_zfmisc_1(u1_struct_0(A_306)))
      | ~ l1_pre_topc(A_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_3508,plain,(
    ! [B_307] :
      ( k2_pre_topc('#skF_4',B_307) = B_307
      | ~ v4_pre_topc(B_307,'#skF_4')
      | ~ m1_subset_1(B_307,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_3493])).

tff(c_3534,plain,(
    ! [B_309] :
      ( k2_pre_topc('#skF_4',B_309) = B_309
      | ~ v4_pre_topc(B_309,'#skF_4')
      | ~ m1_subset_1(B_309,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_3508])).

tff(c_3556,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = '#skF_5'
    | ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_115,c_3534])).

tff(c_3558,plain,(
    ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3556])).

tff(c_100,plain,(
    v1_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_454,plain,(
    ! [B_121,A_122] :
      ( m1_subset_1(u1_struct_0(B_121),k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ m1_pre_topc(B_121,A_122)
      | ~ l1_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_471,plain,(
    ! [B_121] :
      ( m1_subset_1(u1_struct_0(B_121),k1_zfmisc_1('#skF_5'))
      | ~ m1_pre_topc(B_121,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_454])).

tff(c_481,plain,(
    ! [B_123] :
      ( m1_subset_1(u1_struct_0(B_123),k1_zfmisc_1('#skF_5'))
      | ~ m1_pre_topc(B_123,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_471])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ m1_subset_1(A_17,k1_zfmisc_1(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_501,plain,(
    ! [B_124] :
      ( r1_tarski(u1_struct_0(B_124),'#skF_5')
      | ~ m1_pre_topc(B_124,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_481,c_22])).

tff(c_24,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_333,plain,(
    ! [A_108,B_109] :
      ( v1_subset_1(A_108,B_109)
      | B_109 = A_108
      | ~ r1_tarski(A_108,B_109) ) ),
    inference(resolution,[status(thm)],[c_24,c_254])).

tff(c_232,plain,(
    ! [B_98,A_99] :
      ( ~ v1_subset_1(B_98,A_99)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(A_99))
      | ~ v1_xboole_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_248,plain,(
    ! [A_17,B_18] :
      ( ~ v1_subset_1(A_17,B_18)
      | ~ v1_xboole_0(B_18)
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(resolution,[status(thm)],[c_24,c_232])).

tff(c_345,plain,(
    ! [B_109,A_108] :
      ( ~ v1_xboole_0(B_109)
      | B_109 = A_108
      | ~ r1_tarski(A_108,B_109) ) ),
    inference(resolution,[status(thm)],[c_333,c_248])).

tff(c_508,plain,(
    ! [B_124] :
      ( ~ v1_xboole_0('#skF_5')
      | u1_struct_0(B_124) = '#skF_5'
      | ~ m1_pre_topc(B_124,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_501,c_345])).

tff(c_510,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_508])).

tff(c_5756,plain,(
    ! [A_369,B_370] :
      ( m1_pre_topc('#skF_2'(A_369,B_370),A_369)
      | ~ m1_subset_1(B_370,k1_zfmisc_1(u1_struct_0(A_369)))
      | v1_xboole_0(B_370)
      | ~ l1_pre_topc(A_369)
      | v2_struct_0(A_369) ) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_5774,plain,(
    ! [B_370] :
      ( m1_pre_topc('#skF_2'('#skF_4',B_370),'#skF_4')
      | ~ m1_subset_1(B_370,k1_zfmisc_1('#skF_5'))
      | v1_xboole_0(B_370)
      | ~ l1_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_5756])).

tff(c_5797,plain,(
    ! [B_370] :
      ( m1_pre_topc('#skF_2'('#skF_4',B_370),'#skF_4')
      | ~ m1_subset_1(B_370,k1_zfmisc_1('#skF_5'))
      | v1_xboole_0(B_370)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_5774])).

tff(c_5803,plain,(
    ! [B_371] :
      ( m1_pre_topc('#skF_2'('#skF_4',B_371),'#skF_4')
      | ~ m1_subset_1(B_371,k1_zfmisc_1('#skF_5'))
      | v1_xboole_0(B_371) ) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_5797])).

tff(c_5817,plain,
    ( m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_115,c_5803])).

tff(c_5829,plain,(
    m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_510,c_5817])).

tff(c_58,plain,(
    ! [B_42,A_40] :
      ( v1_borsuk_1(B_42,A_40)
      | ~ m1_pre_topc(B_42,A_40)
      | ~ l1_pre_topc(A_40)
      | ~ v1_tdlat_3(A_40)
      | ~ v2_pre_topc(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_3574,plain,(
    ! [A_310,B_311] :
      ( k2_pre_topc(A_310,B_311) = u1_struct_0(A_310)
      | ~ v1_tops_1(B_311,A_310)
      | ~ m1_subset_1(B_311,k1_zfmisc_1(u1_struct_0(A_310)))
      | ~ l1_pre_topc(A_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_3589,plain,(
    ! [B_311] :
      ( k2_pre_topc('#skF_4',B_311) = u1_struct_0('#skF_4')
      | ~ v1_tops_1(B_311,'#skF_4')
      | ~ m1_subset_1(B_311,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_3574])).

tff(c_3616,plain,(
    ! [B_313] :
      ( k2_pre_topc('#skF_4',B_313) = '#skF_5'
      | ~ v1_tops_1(B_313,'#skF_4')
      | ~ m1_subset_1(B_313,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_278,c_3589])).

tff(c_3640,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = '#skF_5'
    | ~ v1_tops_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_115,c_3616])).

tff(c_3642,plain,(
    ~ v1_tops_1('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3640])).

tff(c_3740,plain,(
    ! [B_322,A_323] :
      ( v1_tops_1(B_322,A_323)
      | k2_pre_topc(A_323,B_322) != u1_struct_0(A_323)
      | ~ m1_subset_1(B_322,k1_zfmisc_1(u1_struct_0(A_323)))
      | ~ l1_pre_topc(A_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_3755,plain,(
    ! [B_322] :
      ( v1_tops_1(B_322,'#skF_4')
      | k2_pre_topc('#skF_4',B_322) != u1_struct_0('#skF_4')
      | ~ m1_subset_1(B_322,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_3740])).

tff(c_3798,plain,(
    ! [B_325] :
      ( v1_tops_1(B_325,'#skF_4')
      | k2_pre_topc('#skF_4',B_325) != '#skF_5'
      | ~ m1_subset_1(B_325,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_278,c_3755])).

tff(c_3812,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | k2_pre_topc('#skF_4','#skF_5') != '#skF_5' ),
    inference(resolution,[status(thm)],[c_115,c_3798])).

tff(c_3824,plain,(
    k2_pre_topc('#skF_4','#skF_5') != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_3642,c_3812])).

tff(c_3982,plain,(
    ! [A_337,B_338] :
      ( u1_struct_0('#skF_2'(A_337,B_338)) = B_338
      | ~ m1_subset_1(B_338,k1_zfmisc_1(u1_struct_0(A_337)))
      | v1_xboole_0(B_338)
      | ~ l1_pre_topc(A_337)
      | v2_struct_0(A_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_3997,plain,(
    ! [B_338] :
      ( u1_struct_0('#skF_2'('#skF_4',B_338)) = B_338
      | ~ m1_subset_1(B_338,k1_zfmisc_1('#skF_5'))
      | v1_xboole_0(B_338)
      | ~ l1_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_3982])).

tff(c_4020,plain,(
    ! [B_338] :
      ( u1_struct_0('#skF_2'('#skF_4',B_338)) = B_338
      | ~ m1_subset_1(B_338,k1_zfmisc_1('#skF_5'))
      | v1_xboole_0(B_338)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_3997])).

tff(c_4026,plain,(
    ! [B_339] :
      ( u1_struct_0('#skF_2'('#skF_4',B_339)) = B_339
      | ~ m1_subset_1(B_339,k1_zfmisc_1('#skF_5'))
      | v1_xboole_0(B_339) ) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_4020])).

tff(c_4040,plain,
    ( u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_115,c_4026])).

tff(c_4052,plain,(
    u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_510,c_4040])).

tff(c_50,plain,(
    ! [B_38,A_36] :
      ( m1_subset_1(u1_struct_0(B_38),k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ m1_pre_topc(B_38,A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_7131,plain,(
    ! [B_416,A_417] :
      ( v4_pre_topc(u1_struct_0(B_416),A_417)
      | ~ v1_borsuk_1(B_416,A_417)
      | ~ m1_subset_1(u1_struct_0(B_416),k1_zfmisc_1(u1_struct_0(A_417)))
      | ~ m1_pre_topc(B_416,A_417)
      | ~ l1_pre_topc(A_417)
      | ~ v2_pre_topc(A_417) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_7187,plain,(
    ! [B_38,A_36] :
      ( v4_pre_topc(u1_struct_0(B_38),A_36)
      | ~ v1_borsuk_1(B_38,A_36)
      | ~ v2_pre_topc(A_36)
      | ~ m1_pre_topc(B_38,A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(resolution,[status(thm)],[c_50,c_7131])).

tff(c_480,plain,(
    ! [B_121] :
      ( m1_subset_1(u1_struct_0(B_121),k1_zfmisc_1('#skF_5'))
      | ~ m1_pre_topc(B_121,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_471])).

tff(c_7946,plain,(
    ! [B_445] :
      ( k2_pre_topc('#skF_4',u1_struct_0(B_445)) = u1_struct_0(B_445)
      | ~ v4_pre_topc(u1_struct_0(B_445),'#skF_4')
      | ~ m1_pre_topc(B_445,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_480,c_3534])).

tff(c_7957,plain,(
    ! [B_38] :
      ( k2_pre_topc('#skF_4',u1_struct_0(B_38)) = u1_struct_0(B_38)
      | ~ v1_borsuk_1(B_38,'#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ m1_pre_topc(B_38,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_7187,c_7946])).

tff(c_7995,plain,(
    ! [B_446] :
      ( k2_pre_topc('#skF_4',u1_struct_0(B_446)) = u1_struct_0(B_446)
      | ~ v1_borsuk_1(B_446,'#skF_4')
      | ~ m1_pre_topc(B_446,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_102,c_7957])).

tff(c_8016,plain,
    ( u1_struct_0('#skF_2'('#skF_4','#skF_5')) = k2_pre_topc('#skF_4','#skF_5')
    | ~ v1_borsuk_1('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4052,c_7995])).

tff(c_8025,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = '#skF_5'
    | ~ v1_borsuk_1('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5829,c_4052,c_8016])).

tff(c_8026,plain,(
    ~ v1_borsuk_1('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_3824,c_8025])).

tff(c_8031,plain,
    ( ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v1_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_8026])).

tff(c_8034,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_98,c_5829,c_8031])).

tff(c_8036,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_8034])).

tff(c_8037,plain,(
    k2_pre_topc('#skF_4','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3640])).

tff(c_9310,plain,(
    ! [B_492,A_493] :
      ( v4_pre_topc(B_492,A_493)
      | k2_pre_topc(A_493,B_492) != B_492
      | ~ v2_pre_topc(A_493)
      | ~ m1_subset_1(B_492,k1_zfmisc_1(u1_struct_0(A_493)))
      | ~ l1_pre_topc(A_493) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_9334,plain,(
    ! [B_492] :
      ( v4_pre_topc(B_492,'#skF_4')
      | k2_pre_topc('#skF_4',B_492) != B_492
      | ~ v2_pre_topc('#skF_4')
      | ~ m1_subset_1(B_492,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_9310])).

tff(c_9377,plain,(
    ! [B_495] :
      ( v4_pre_topc(B_495,'#skF_4')
      | k2_pre_topc('#skF_4',B_495) != B_495
      | ~ m1_subset_1(B_495,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_102,c_9334])).

tff(c_9391,plain,
    ( v4_pre_topc('#skF_5','#skF_4')
    | k2_pre_topc('#skF_4','#skF_5') != '#skF_5' ),
    inference(resolution,[status(thm)],[c_115,c_9377])).

tff(c_9403,plain,(
    v4_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8037,c_9391])).

tff(c_9405,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3558,c_9403])).

tff(c_9406,plain,(
    k2_pre_topc('#skF_4','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3556])).

tff(c_9605,plain,(
    ! [B_509,A_510] :
      ( v1_tops_1(B_509,A_510)
      | k2_pre_topc(A_510,B_509) != u1_struct_0(A_510)
      | ~ m1_subset_1(B_509,k1_zfmisc_1(u1_struct_0(A_510)))
      | ~ l1_pre_topc(A_510) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_9620,plain,(
    ! [B_509] :
      ( v1_tops_1(B_509,'#skF_4')
      | k2_pre_topc('#skF_4',B_509) != u1_struct_0('#skF_4')
      | ~ m1_subset_1(B_509,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_9605])).

tff(c_9663,plain,(
    ! [B_512] :
      ( v1_tops_1(B_512,'#skF_4')
      | k2_pre_topc('#skF_4',B_512) != '#skF_5'
      | ~ m1_subset_1(B_512,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_278,c_9620])).

tff(c_9677,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | k2_pre_topc('#skF_4','#skF_5') != '#skF_5' ),
    inference(resolution,[status(thm)],[c_115,c_9663])).

tff(c_9689,plain,(
    v1_tops_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9406,c_9677])).

tff(c_10088,plain,(
    ! [B_539,A_540] :
      ( v2_tex_2(B_539,A_540)
      | ~ m1_subset_1(B_539,k1_zfmisc_1(u1_struct_0(A_540)))
      | ~ l1_pre_topc(A_540)
      | ~ v1_tdlat_3(A_540)
      | ~ v2_pre_topc(A_540)
      | v2_struct_0(A_540) ) ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_10103,plain,(
    ! [B_539] :
      ( v2_tex_2(B_539,'#skF_4')
      | ~ m1_subset_1(B_539,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v1_tdlat_3('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_10088])).

tff(c_10124,plain,(
    ! [B_539] :
      ( v2_tex_2(B_539,'#skF_4')
      | ~ m1_subset_1(B_539,k1_zfmisc_1('#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_98,c_10103])).

tff(c_10129,plain,(
    ! [B_541] :
      ( v2_tex_2(B_541,'#skF_4')
      | ~ m1_subset_1(B_541,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_10124])).

tff(c_10151,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_115,c_10129])).

tff(c_11512,plain,(
    ! [B_568,A_569] :
      ( v3_tex_2(B_568,A_569)
      | ~ v2_tex_2(B_568,A_569)
      | ~ v1_tops_1(B_568,A_569)
      | ~ m1_subset_1(B_568,k1_zfmisc_1(u1_struct_0(A_569)))
      | ~ l1_pre_topc(A_569)
      | ~ v2_pre_topc(A_569)
      | v2_struct_0(A_569) ) ),
    inference(cnfTransformation,[status(thm)],[f_292])).

tff(c_11536,plain,(
    ! [B_568] :
      ( v3_tex_2(B_568,'#skF_4')
      | ~ v2_tex_2(B_568,'#skF_4')
      | ~ v1_tops_1(B_568,'#skF_4')
      | ~ m1_subset_1(B_568,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_11512])).

tff(c_11563,plain,(
    ! [B_568] :
      ( v3_tex_2(B_568,'#skF_4')
      | ~ v2_tex_2(B_568,'#skF_4')
      | ~ v1_tops_1(B_568,'#skF_4')
      | ~ m1_subset_1(B_568,k1_zfmisc_1('#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_98,c_11536])).

tff(c_11675,plain,(
    ! [B_572] :
      ( v3_tex_2(B_572,'#skF_4')
      | ~ v2_tex_2(B_572,'#skF_4')
      | ~ v1_tops_1(B_572,'#skF_4')
      | ~ m1_subset_1(B_572,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_11563])).

tff(c_11692,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ v1_tops_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_115,c_11675])).

tff(c_11706,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9689,c_10151,c_11692])).

tff(c_11708,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_11706])).

tff(c_11710,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_508])).

tff(c_11949,plain,(
    ! [A_590] :
      ( m1_subset_1('#skF_1'(A_590),k1_zfmisc_1(u1_struct_0(A_590)))
      | ~ l1_pre_topc(A_590)
      | ~ v2_pre_topc(A_590)
      | v2_struct_0(A_590) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_11966,plain,
    ( m1_subset_1('#skF_1'('#skF_4'),k1_zfmisc_1('#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_11949])).

tff(c_11976,plain,
    ( m1_subset_1('#skF_1'('#skF_4'),k1_zfmisc_1('#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_98,c_11966])).

tff(c_11977,plain,(
    m1_subset_1('#skF_1'('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_11976])).

tff(c_11999,plain,(
    r1_tarski('#skF_1'('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_11977,c_22])).

tff(c_12005,plain,
    ( ~ v1_xboole_0('#skF_5')
    | '#skF_1'('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_11999,c_345])).

tff(c_12009,plain,(
    '#skF_1'('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11710,c_12005])).

tff(c_40,plain,(
    ! [A_27] :
      ( ~ v1_xboole_0('#skF_1'(A_27))
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_12026,plain,
    ( ~ v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12009,c_40])).

tff(c_12039,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_98,c_11710,c_12026])).

tff(c_12041,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_12039])).

tff(c_12043,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_6,plain,(
    ! [A_4] : k1_subset_1(A_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_6] : m1_subset_1(k1_subset_1(A_6),k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_119,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10])).

tff(c_12051,plain,(
    ! [A_591,B_592] :
      ( r1_tarski(A_591,B_592)
      | ~ m1_subset_1(A_591,k1_zfmisc_1(B_592)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12062,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(resolution,[status(thm)],[c_119,c_12051])).

tff(c_2,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12072,plain,(
    ! [B_599,A_600] :
      ( ~ r1_xboole_0(B_599,A_600)
      | ~ r1_tarski(B_599,A_600)
      | v1_xboole_0(B_599) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12077,plain,(
    ! [A_601] :
      ( ~ r1_tarski(A_601,k1_xboole_0)
      | v1_xboole_0(A_601) ) ),
    inference(resolution,[status(thm)],[c_2,c_12072])).

tff(c_12086,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12062,c_12077])).

tff(c_16,plain,(
    ! [A_10] : k3_subset_1(A_10,k1_subset_1(A_10)) = k2_subset_1(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_116,plain,(
    ! [A_10] : k3_subset_1(A_10,k1_subset_1(A_10)) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_16])).

tff(c_120,plain,(
    ! [A_10] : k3_subset_1(A_10,k1_xboole_0) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_116])).

tff(c_12235,plain,(
    ! [A_622,B_623] :
      ( k3_subset_1(A_622,k3_subset_1(A_622,B_623)) = B_623
      | ~ m1_subset_1(B_623,k1_zfmisc_1(A_622)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12243,plain,(
    ! [A_6] : k3_subset_1(A_6,k3_subset_1(A_6,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_119,c_12235])).

tff(c_12249,plain,(
    ! [A_6] : k3_subset_1(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_12243])).

tff(c_23865,plain,(
    ! [A_1144,B_1145] :
      ( k2_pre_topc(A_1144,B_1145) = B_1145
      | ~ v4_pre_topc(B_1145,A_1144)
      | ~ m1_subset_1(B_1145,k1_zfmisc_1(u1_struct_0(A_1144)))
      | ~ l1_pre_topc(A_1144) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_23892,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = '#skF_5'
    | ~ v4_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_23865])).

tff(c_23901,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = '#skF_5'
    | ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_23892])).

tff(c_23902,plain,(
    ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_23901])).

tff(c_12587,plain,(
    ! [A_660,B_661] :
      ( k2_pre_topc(A_660,B_661) = B_661
      | ~ v4_pre_topc(B_661,A_660)
      | ~ m1_subset_1(B_661,k1_zfmisc_1(u1_struct_0(A_660)))
      | ~ l1_pre_topc(A_660) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_12614,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = '#skF_5'
    | ~ v4_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_12587])).

tff(c_12623,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = '#skF_5'
    | ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_12614])).

tff(c_12624,plain,(
    ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_12623])).

tff(c_14490,plain,(
    ! [A_772,B_773] :
      ( v1_pre_topc('#skF_2'(A_772,B_773))
      | ~ m1_subset_1(B_773,k1_zfmisc_1(u1_struct_0(A_772)))
      | v1_xboole_0(B_773)
      | ~ l1_pre_topc(A_772)
      | v2_struct_0(A_772) ) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_14517,plain,
    ( v1_pre_topc('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_14490])).

tff(c_14527,plain,
    ( v1_pre_topc('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_14517])).

tff(c_14528,plain,
    ( v1_pre_topc('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_14527])).

tff(c_14529,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_14528])).

tff(c_14584,plain,(
    ! [B_776,A_777] :
      ( ~ v3_tex_2(B_776,A_777)
      | ~ m1_subset_1(B_776,k1_zfmisc_1(u1_struct_0(A_777)))
      | ~ v1_xboole_0(B_776)
      | ~ l1_pre_topc(A_777)
      | ~ v2_pre_topc(A_777)
      | v2_struct_0(A_777) ) ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_14607,plain,
    ( ~ v3_tex_2('#skF_5','#skF_4')
    | ~ v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_14584])).

tff(c_14615,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_98,c_14529,c_12043,c_14607])).

tff(c_14617,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_14615])).

tff(c_14619,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_14528])).

tff(c_14842,plain,(
    ! [A_799,B_800] :
      ( m1_pre_topc('#skF_2'(A_799,B_800),A_799)
      | ~ m1_subset_1(B_800,k1_zfmisc_1(u1_struct_0(A_799)))
      | v1_xboole_0(B_800)
      | ~ l1_pre_topc(A_799)
      | v2_struct_0(A_799) ) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_14861,plain,
    ( m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_14842])).

tff(c_14871,plain,
    ( m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_14861])).

tff(c_14872,plain,(
    m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_14619,c_14871])).

tff(c_14886,plain,(
    ! [A_801,B_802] :
      ( u1_struct_0('#skF_2'(A_801,B_802)) = B_802
      | ~ m1_subset_1(B_802,k1_zfmisc_1(u1_struct_0(A_801)))
      | v1_xboole_0(B_802)
      | ~ l1_pre_topc(A_801)
      | v2_struct_0(A_801) ) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_14913,plain,
    ( u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_14886])).

tff(c_14923,plain,
    ( u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_14913])).

tff(c_14924,plain,(
    u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_14619,c_14923])).

tff(c_19294,plain,(
    ! [B_940,A_941] :
      ( v4_pre_topc(u1_struct_0(B_940),A_941)
      | ~ v1_borsuk_1(B_940,A_941)
      | ~ m1_subset_1(u1_struct_0(B_940),k1_zfmisc_1(u1_struct_0(A_941)))
      | ~ m1_pre_topc(B_940,A_941)
      | ~ l1_pre_topc(A_941)
      | ~ v2_pre_topc(A_941) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_19902,plain,(
    ! [B_970,A_971] :
      ( v4_pre_topc(u1_struct_0(B_970),A_971)
      | ~ v1_borsuk_1(B_970,A_971)
      | ~ v2_pre_topc(A_971)
      | ~ m1_pre_topc(B_970,A_971)
      | ~ l1_pre_topc(A_971) ) ),
    inference(resolution,[status(thm)],[c_50,c_19294])).

tff(c_19935,plain,(
    ! [A_973] :
      ( v4_pre_topc('#skF_5',A_973)
      | ~ v1_borsuk_1('#skF_2'('#skF_4','#skF_5'),A_973)
      | ~ v2_pre_topc(A_973)
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_973)
      | ~ l1_pre_topc(A_973) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14924,c_19902])).

tff(c_22539,plain,(
    ! [A_1063] :
      ( v4_pre_topc('#skF_5',A_1063)
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_1063)
      | ~ l1_pre_topc(A_1063)
      | ~ v1_tdlat_3(A_1063)
      | ~ v2_pre_topc(A_1063)
      | v2_struct_0(A_1063) ) ),
    inference(resolution,[status(thm)],[c_58,c_19935])).

tff(c_22545,plain,
    ( v4_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v1_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_14872,c_22539])).

tff(c_22552,plain,
    ( v4_pre_topc('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_98,c_22545])).

tff(c_22554,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_12624,c_22552])).

tff(c_22555,plain,(
    k2_pre_topc('#skF_4','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_12623])).

tff(c_22695,plain,(
    ! [B_1083,A_1084] :
      ( v1_tops_1(B_1083,A_1084)
      | k2_pre_topc(A_1084,B_1083) != u1_struct_0(A_1084)
      | ~ m1_subset_1(B_1083,k1_zfmisc_1(u1_struct_0(A_1084)))
      | ~ l1_pre_topc(A_1084) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_22722,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | k2_pre_topc('#skF_4','#skF_5') != u1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_22695])).

tff(c_22731,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | u1_struct_0('#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_22555,c_22722])).

tff(c_22732,plain,(
    u1_struct_0('#skF_4') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_22731])).

tff(c_22734,plain,(
    ! [A_1086,B_1087] :
      ( k2_pre_topc(A_1086,B_1087) = u1_struct_0(A_1086)
      | ~ v1_tops_1(B_1087,A_1086)
      | ~ m1_subset_1(B_1087,k1_zfmisc_1(u1_struct_0(A_1086)))
      | ~ l1_pre_topc(A_1086) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_22761,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = u1_struct_0('#skF_4')
    | ~ v1_tops_1('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_22734])).

tff(c_22770,plain,
    ( u1_struct_0('#skF_4') = '#skF_5'
    | ~ v1_tops_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_22555,c_22761])).

tff(c_22771,plain,(
    ~ v1_tops_1('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_22732,c_22770])).

tff(c_22599,plain,(
    ! [B_1073,A_1074] :
      ( v3_pre_topc(B_1073,A_1074)
      | ~ m1_subset_1(B_1073,k1_zfmisc_1(u1_struct_0(A_1074)))
      | ~ v1_tdlat_3(A_1074)
      | ~ l1_pre_topc(A_1074)
      | ~ v2_pre_topc(A_1074) ) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_22626,plain,
    ( v3_pre_topc('#skF_5','#skF_4')
    | ~ v1_tdlat_3('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_22599])).

tff(c_22635,plain,(
    v3_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_98,c_100,c_22626])).

tff(c_23668,plain,(
    ! [B_1125,A_1126] :
      ( v1_tops_1(B_1125,A_1126)
      | ~ v3_tex_2(B_1125,A_1126)
      | ~ v3_pre_topc(B_1125,A_1126)
      | ~ m1_subset_1(B_1125,k1_zfmisc_1(u1_struct_0(A_1126)))
      | ~ l1_pre_topc(A_1126)
      | ~ v2_pre_topc(A_1126)
      | v2_struct_0(A_1126) ) ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_23701,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | ~ v3_tex_2('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_23668])).

tff(c_23714,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_98,c_22635,c_12043,c_23701])).

tff(c_23716,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_22771,c_23714])).

tff(c_23718,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_22731])).

tff(c_12042,plain,(
    v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_12161,plain,(
    ! [B_611,A_612] :
      ( ~ v1_subset_1(B_611,A_612)
      | ~ m1_subset_1(B_611,k1_zfmisc_1(A_612))
      | ~ v1_xboole_0(A_612) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_12176,plain,
    ( ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_96,c_12161])).

tff(c_12182,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12042,c_12176])).

tff(c_12250,plain,(
    k3_subset_1(u1_struct_0('#skF_4'),k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_96,c_12235])).

tff(c_12512,plain,(
    ! [A_650,B_651] :
      ( ~ v1_xboole_0(k3_subset_1(A_650,B_651))
      | ~ m1_subset_1(B_651,k1_zfmisc_1(A_650))
      | ~ v1_subset_1(B_651,A_650)
      | v1_xboole_0(A_650) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_12550,plain,(
    ! [B_652,A_653] :
      ( ~ v1_xboole_0(k3_subset_1(B_652,A_653))
      | ~ v1_subset_1(A_653,B_652)
      | v1_xboole_0(B_652)
      | ~ r1_tarski(A_653,B_652) ) ),
    inference(resolution,[status(thm)],[c_24,c_12512])).

tff(c_12556,plain,
    ( ~ v1_xboole_0('#skF_5')
    | ~ v1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12250,c_12550])).

tff(c_12563,plain,
    ( ~ v1_xboole_0('#skF_5')
    | ~ v1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4'))
    | ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_12182,c_12556])).

tff(c_12569,plain,(
    ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_12563])).

tff(c_23720,plain,(
    ~ r1_tarski(k3_subset_1('#skF_5','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23718,c_23718,c_12569])).

tff(c_23730,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12062,c_12249,c_23720])).

tff(c_23731,plain,
    ( ~ v1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_12563])).

tff(c_23743,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_23731])).

tff(c_25243,plain,(
    ! [A_1219,B_1220] :
      ( m1_pre_topc('#skF_2'(A_1219,B_1220),A_1219)
      | ~ m1_subset_1(B_1220,k1_zfmisc_1(u1_struct_0(A_1219)))
      | v1_xboole_0(B_1220)
      | ~ l1_pre_topc(A_1219)
      | v2_struct_0(A_1219) ) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_25262,plain,
    ( m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_25243])).

tff(c_25272,plain,
    ( m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_25262])).

tff(c_25273,plain,(
    m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_23743,c_25272])).

tff(c_25337,plain,(
    ! [A_1225,B_1226] :
      ( u1_struct_0('#skF_2'(A_1225,B_1226)) = B_1226
      | ~ m1_subset_1(B_1226,k1_zfmisc_1(u1_struct_0(A_1225)))
      | v1_xboole_0(B_1226)
      | ~ l1_pre_topc(A_1225)
      | v2_struct_0(A_1225) ) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_25364,plain,
    ( u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_25337])).

tff(c_25374,plain,
    ( u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_25364])).

tff(c_25375,plain,(
    u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_23743,c_25374])).

tff(c_28335,plain,(
    ! [B_1317,A_1318] :
      ( v4_pre_topc(u1_struct_0(B_1317),A_1318)
      | ~ v1_borsuk_1(B_1317,A_1318)
      | ~ m1_subset_1(u1_struct_0(B_1317),k1_zfmisc_1(u1_struct_0(A_1318)))
      | ~ m1_pre_topc(B_1317,A_1318)
      | ~ l1_pre_topc(A_1318)
      | ~ v2_pre_topc(A_1318) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_29507,plain,(
    ! [B_1333,A_1334] :
      ( v4_pre_topc(u1_struct_0(B_1333),A_1334)
      | ~ v1_borsuk_1(B_1333,A_1334)
      | ~ v2_pre_topc(A_1334)
      | ~ m1_pre_topc(B_1333,A_1334)
      | ~ l1_pre_topc(A_1334) ) ),
    inference(resolution,[status(thm)],[c_50,c_28335])).

tff(c_29583,plain,(
    ! [A_1339] :
      ( v4_pre_topc('#skF_5',A_1339)
      | ~ v1_borsuk_1('#skF_2'('#skF_4','#skF_5'),A_1339)
      | ~ v2_pre_topc(A_1339)
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_1339)
      | ~ l1_pre_topc(A_1339) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25375,c_29507])).

tff(c_34085,plain,(
    ! [A_1458] :
      ( v4_pre_topc('#skF_5',A_1458)
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_1458)
      | ~ l1_pre_topc(A_1458)
      | ~ v1_tdlat_3(A_1458)
      | ~ v2_pre_topc(A_1458)
      | v2_struct_0(A_1458) ) ),
    inference(resolution,[status(thm)],[c_58,c_29583])).

tff(c_34091,plain,
    ( v4_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v1_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_25273,c_34085])).

tff(c_34098,plain,
    ( v4_pre_topc('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_98,c_34091])).

tff(c_34100,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_23902,c_34098])).

tff(c_34101,plain,(
    k2_pre_topc('#skF_4','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_23901])).

tff(c_34297,plain,(
    ! [B_1477,A_1478] :
      ( v1_tops_1(B_1477,A_1478)
      | k2_pre_topc(A_1478,B_1477) != u1_struct_0(A_1478)
      | ~ m1_subset_1(B_1477,k1_zfmisc_1(u1_struct_0(A_1478)))
      | ~ l1_pre_topc(A_1478) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_34324,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | k2_pre_topc('#skF_4','#skF_5') != u1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_34297])).

tff(c_34333,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | u1_struct_0('#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_34101,c_34324])).

tff(c_34334,plain,(
    u1_struct_0('#skF_4') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_34333])).

tff(c_34338,plain,(
    ! [A_1482,B_1483] :
      ( k2_pre_topc(A_1482,B_1483) = u1_struct_0(A_1482)
      | ~ v1_tops_1(B_1483,A_1482)
      | ~ m1_subset_1(B_1483,k1_zfmisc_1(u1_struct_0(A_1482)))
      | ~ l1_pre_topc(A_1482) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_34365,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = u1_struct_0('#skF_4')
    | ~ v1_tops_1('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_34338])).

tff(c_34374,plain,
    ( u1_struct_0('#skF_4') = '#skF_5'
    | ~ v1_tops_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_34101,c_34365])).

tff(c_34375,plain,(
    ~ v1_tops_1('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_34334,c_34374])).

tff(c_23755,plain,(
    ! [B_1131,A_1132] :
      ( v3_pre_topc(B_1131,A_1132)
      | ~ m1_subset_1(B_1131,k1_zfmisc_1(u1_struct_0(A_1132)))
      | ~ v1_tdlat_3(A_1132)
      | ~ l1_pre_topc(A_1132)
      | ~ v2_pre_topc(A_1132) ) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_23782,plain,
    ( v3_pre_topc('#skF_5','#skF_4')
    | ~ v1_tdlat_3('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_23755])).

tff(c_23791,plain,(
    v3_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_98,c_100,c_23782])).

tff(c_36563,plain,(
    ! [B_1565,A_1566] :
      ( v1_tops_1(B_1565,A_1566)
      | ~ v3_tex_2(B_1565,A_1566)
      | ~ v3_pre_topc(B_1565,A_1566)
      | ~ m1_subset_1(B_1565,k1_zfmisc_1(u1_struct_0(A_1566)))
      | ~ l1_pre_topc(A_1566)
      | ~ v2_pre_topc(A_1566)
      | v2_struct_0(A_1566) ) ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_36602,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | ~ v3_tex_2('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_36563])).

tff(c_36618,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_98,c_23791,c_12043,c_36602])).

tff(c_36620,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_34375,c_36618])).

tff(c_36622,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_34333])).

tff(c_12536,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'))
    | ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_96,c_12512])).

tff(c_12548,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12042,c_12536])).

tff(c_12549,plain,(
    ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_12182,c_12548])).

tff(c_36628,plain,(
    ~ v1_xboole_0(k3_subset_1('#skF_5','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36622,c_12549])).

tff(c_36641,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12086,c_12249,c_36628])).

tff(c_36643,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_23731])).

tff(c_12114,plain,(
    ! [B_603,A_604] :
      ( v1_subset_1(B_603,A_604)
      | B_603 = A_604
      | ~ m1_subset_1(B_603,k1_zfmisc_1(A_604)) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_12130,plain,(
    ! [A_17,B_18] :
      ( v1_subset_1(A_17,B_18)
      | B_18 = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(resolution,[status(thm)],[c_24,c_12114])).

tff(c_12183,plain,(
    ! [A_613] :
      ( ~ v1_subset_1(k1_xboole_0,A_613)
      | ~ v1_xboole_0(A_613) ) ),
    inference(resolution,[status(thm)],[c_119,c_12161])).

tff(c_12187,plain,(
    ! [B_18] :
      ( ~ v1_xboole_0(B_18)
      | k1_xboole_0 = B_18
      | ~ r1_tarski(k1_xboole_0,B_18) ) ),
    inference(resolution,[status(thm)],[c_12130,c_12183])).

tff(c_12193,plain,(
    ! [B_18] :
      ( ~ v1_xboole_0(B_18)
      | k1_xboole_0 = B_18 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12062,c_12187])).

tff(c_36647,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_36643,c_12193])).

tff(c_36671,plain,(
    ! [A_6] : m1_subset_1('#skF_5',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36647,c_119])).

tff(c_37174,plain,(
    ! [B_1619,A_1620] :
      ( ~ v3_tex_2(B_1619,A_1620)
      | ~ m1_subset_1(B_1619,k1_zfmisc_1(u1_struct_0(A_1620)))
      | ~ v1_xboole_0(B_1619)
      | ~ l1_pre_topc(A_1620)
      | ~ v2_pre_topc(A_1620)
      | v2_struct_0(A_1620) ) ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_37178,plain,(
    ! [A_1620] :
      ( ~ v3_tex_2('#skF_5',A_1620)
      | ~ v1_xboole_0('#skF_5')
      | ~ l1_pre_topc(A_1620)
      | ~ v2_pre_topc(A_1620)
      | v2_struct_0(A_1620) ) ),
    inference(resolution,[status(thm)],[c_36671,c_37174])).

tff(c_37207,plain,(
    ! [A_1621] :
      ( ~ v3_tex_2('#skF_5',A_1621)
      | ~ l1_pre_topc(A_1621)
      | ~ v2_pre_topc(A_1621)
      | v2_struct_0(A_1621) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36643,c_37178])).

tff(c_37210,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_12043,c_37207])).

tff(c_37213,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_98,c_37210])).

tff(c_37215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_37213])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n020.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 12:08:52 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.27/6.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.27/6.13  
% 14.27/6.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.27/6.14  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tsep_1 > v1_tops_1 > v1_subset_1 > v1_borsuk_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k9_setfam_1 > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2
% 14.27/6.14  
% 14.27/6.14  %Foreground sorts:
% 14.27/6.14  
% 14.27/6.14  
% 14.27/6.14  %Background operators:
% 14.27/6.14  
% 14.27/6.14  
% 14.27/6.14  %Foreground operators:
% 14.27/6.14  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 14.27/6.14  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 14.27/6.14  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 14.27/6.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.27/6.14  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 14.27/6.14  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 14.27/6.14  tff('#skF_1', type, '#skF_1': $i > $i).
% 14.27/6.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.27/6.14  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 14.27/6.14  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 14.27/6.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.27/6.14  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 14.27/6.14  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 14.27/6.14  tff('#skF_5', type, '#skF_5': $i).
% 14.27/6.14  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 14.27/6.14  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 14.27/6.14  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 14.27/6.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 14.27/6.14  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 14.27/6.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.27/6.14  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 14.27/6.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.27/6.14  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 14.27/6.14  tff('#skF_4', type, '#skF_4': $i).
% 14.27/6.14  tff('#skF_3', type, '#skF_3': $i > $i).
% 14.27/6.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.27/6.14  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 14.27/6.14  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 14.27/6.14  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 14.27/6.14  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 14.27/6.14  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 14.27/6.14  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 14.27/6.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.27/6.14  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 14.27/6.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.27/6.14  tff(v1_borsuk_1, type, v1_borsuk_1: ($i * $i) > $o).
% 14.27/6.14  
% 14.27/6.17  tff(f_310, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tex_2)).
% 14.27/6.17  tff(f_39, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 14.27/6.17  tff(f_43, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 14.27/6.17  tff(f_189, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 14.27/6.17  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 14.27/6.17  tff(f_143, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 14.27/6.17  tff(f_71, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 14.27/6.17  tff(f_67, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~v1_subset_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_subset_1)).
% 14.27/6.17  tff(f_220, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (?[C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) & (B = u1_struct_0(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_tsep_1)).
% 14.27/6.17  tff(f_167, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((v1_borsuk_1(B, A) & v1_tsep_1(B, A)) & v1_tdlat_3(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_tdlat_3)).
% 14.27/6.17  tff(f_182, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 14.27/6.17  tff(f_136, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_borsuk_1(B, A) & m1_pre_topc(B, A)) <=> v4_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tsep_1)).
% 14.27/6.17  tff(f_245, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 14.27/6.17  tff(f_292, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tex_2)).
% 14.27/6.17  tff(f_118, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: (((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v3_pre_topc(B, A)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_tops_1)).
% 14.27/6.17  tff(f_37, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 14.27/6.17  tff(f_41, axiom, (![A]: m1_subset_1(k1_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 14.27/6.17  tff(f_27, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 14.27/6.17  tff(f_35, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 14.27/6.17  tff(f_49, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 14.27/6.17  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 14.27/6.17  tff(f_260, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 14.27/6.17  tff(f_231, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_tdlat_3)).
% 14.27/6.17  tff(f_276, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_tex_2)).
% 14.27/6.17  tff(f_199, axiom, (![A, B]: (((~v1_xboole_0(A) & v1_subset_1(B, A)) & m1_subset_1(B, k1_zfmisc_1(A))) => ~v1_xboole_0(k3_subset_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tex_2)).
% 14.27/6.17  tff(c_104, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_310])).
% 14.27/6.17  tff(c_102, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_310])).
% 14.27/6.17  tff(c_98, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_310])).
% 14.27/6.17  tff(c_106, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_310])).
% 14.27/6.17  tff(c_160, plain, (~v3_tex_2('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_106])).
% 14.27/6.17  tff(c_8, plain, (![A_5]: (k2_subset_1(A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.27/6.17  tff(c_12, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.27/6.17  tff(c_115, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_12])).
% 14.27/6.17  tff(c_112, plain, (v3_tex_2('#skF_5', '#skF_4') | ~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_310])).
% 14.27/6.17  tff(c_162, plain, (~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_160, c_112])).
% 14.27/6.17  tff(c_96, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_310])).
% 14.27/6.17  tff(c_254, plain, (![B_103, A_104]: (v1_subset_1(B_103, A_104) | B_103=A_104 | ~m1_subset_1(B_103, k1_zfmisc_1(A_104)))), inference(cnfTransformation, [status(thm)], [f_189])).
% 14.27/6.17  tff(c_269, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_96, c_254])).
% 14.27/6.17  tff(c_278, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_162, c_269])).
% 14.27/6.17  tff(c_3493, plain, (![A_306, B_307]: (k2_pre_topc(A_306, B_307)=B_307 | ~v4_pre_topc(B_307, A_306) | ~m1_subset_1(B_307, k1_zfmisc_1(u1_struct_0(A_306))) | ~l1_pre_topc(A_306))), inference(cnfTransformation, [status(thm)], [f_101])).
% 14.27/6.17  tff(c_3508, plain, (![B_307]: (k2_pre_topc('#skF_4', B_307)=B_307 | ~v4_pre_topc(B_307, '#skF_4') | ~m1_subset_1(B_307, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_278, c_3493])).
% 14.27/6.17  tff(c_3534, plain, (![B_309]: (k2_pre_topc('#skF_4', B_309)=B_309 | ~v4_pre_topc(B_309, '#skF_4') | ~m1_subset_1(B_309, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_3508])).
% 14.27/6.17  tff(c_3556, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5' | ~v4_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_115, c_3534])).
% 14.27/6.17  tff(c_3558, plain, (~v4_pre_topc('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_3556])).
% 14.27/6.17  tff(c_100, plain, (v1_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_310])).
% 14.27/6.17  tff(c_454, plain, (![B_121, A_122]: (m1_subset_1(u1_struct_0(B_121), k1_zfmisc_1(u1_struct_0(A_122))) | ~m1_pre_topc(B_121, A_122) | ~l1_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_143])).
% 14.27/6.17  tff(c_471, plain, (![B_121]: (m1_subset_1(u1_struct_0(B_121), k1_zfmisc_1('#skF_5')) | ~m1_pre_topc(B_121, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_278, c_454])).
% 14.27/6.17  tff(c_481, plain, (![B_123]: (m1_subset_1(u1_struct_0(B_123), k1_zfmisc_1('#skF_5')) | ~m1_pre_topc(B_123, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_471])).
% 14.27/6.17  tff(c_22, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~m1_subset_1(A_17, k1_zfmisc_1(B_18)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.27/6.17  tff(c_501, plain, (![B_124]: (r1_tarski(u1_struct_0(B_124), '#skF_5') | ~m1_pre_topc(B_124, '#skF_4'))), inference(resolution, [status(thm)], [c_481, c_22])).
% 14.27/6.17  tff(c_24, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.27/6.17  tff(c_333, plain, (![A_108, B_109]: (v1_subset_1(A_108, B_109) | B_109=A_108 | ~r1_tarski(A_108, B_109))), inference(resolution, [status(thm)], [c_24, c_254])).
% 14.27/6.17  tff(c_232, plain, (![B_98, A_99]: (~v1_subset_1(B_98, A_99) | ~m1_subset_1(B_98, k1_zfmisc_1(A_99)) | ~v1_xboole_0(A_99))), inference(cnfTransformation, [status(thm)], [f_67])).
% 14.27/6.17  tff(c_248, plain, (![A_17, B_18]: (~v1_subset_1(A_17, B_18) | ~v1_xboole_0(B_18) | ~r1_tarski(A_17, B_18))), inference(resolution, [status(thm)], [c_24, c_232])).
% 14.27/6.17  tff(c_345, plain, (![B_109, A_108]: (~v1_xboole_0(B_109) | B_109=A_108 | ~r1_tarski(A_108, B_109))), inference(resolution, [status(thm)], [c_333, c_248])).
% 14.27/6.17  tff(c_508, plain, (![B_124]: (~v1_xboole_0('#skF_5') | u1_struct_0(B_124)='#skF_5' | ~m1_pre_topc(B_124, '#skF_4'))), inference(resolution, [status(thm)], [c_501, c_345])).
% 14.27/6.17  tff(c_510, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_508])).
% 14.27/6.17  tff(c_5756, plain, (![A_369, B_370]: (m1_pre_topc('#skF_2'(A_369, B_370), A_369) | ~m1_subset_1(B_370, k1_zfmisc_1(u1_struct_0(A_369))) | v1_xboole_0(B_370) | ~l1_pre_topc(A_369) | v2_struct_0(A_369))), inference(cnfTransformation, [status(thm)], [f_220])).
% 14.27/6.17  tff(c_5774, plain, (![B_370]: (m1_pre_topc('#skF_2'('#skF_4', B_370), '#skF_4') | ~m1_subset_1(B_370, k1_zfmisc_1('#skF_5')) | v1_xboole_0(B_370) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_278, c_5756])).
% 14.27/6.17  tff(c_5797, plain, (![B_370]: (m1_pre_topc('#skF_2'('#skF_4', B_370), '#skF_4') | ~m1_subset_1(B_370, k1_zfmisc_1('#skF_5')) | v1_xboole_0(B_370) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_5774])).
% 14.27/6.17  tff(c_5803, plain, (![B_371]: (m1_pre_topc('#skF_2'('#skF_4', B_371), '#skF_4') | ~m1_subset_1(B_371, k1_zfmisc_1('#skF_5')) | v1_xboole_0(B_371))), inference(negUnitSimplification, [status(thm)], [c_104, c_5797])).
% 14.27/6.17  tff(c_5817, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_115, c_5803])).
% 14.27/6.17  tff(c_5829, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_510, c_5817])).
% 14.27/6.17  tff(c_58, plain, (![B_42, A_40]: (v1_borsuk_1(B_42, A_40) | ~m1_pre_topc(B_42, A_40) | ~l1_pre_topc(A_40) | ~v1_tdlat_3(A_40) | ~v2_pre_topc(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_167])).
% 14.27/6.17  tff(c_3574, plain, (![A_310, B_311]: (k2_pre_topc(A_310, B_311)=u1_struct_0(A_310) | ~v1_tops_1(B_311, A_310) | ~m1_subset_1(B_311, k1_zfmisc_1(u1_struct_0(A_310))) | ~l1_pre_topc(A_310))), inference(cnfTransformation, [status(thm)], [f_182])).
% 14.27/6.17  tff(c_3589, plain, (![B_311]: (k2_pre_topc('#skF_4', B_311)=u1_struct_0('#skF_4') | ~v1_tops_1(B_311, '#skF_4') | ~m1_subset_1(B_311, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_278, c_3574])).
% 14.27/6.17  tff(c_3616, plain, (![B_313]: (k2_pre_topc('#skF_4', B_313)='#skF_5' | ~v1_tops_1(B_313, '#skF_4') | ~m1_subset_1(B_313, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_278, c_3589])).
% 14.27/6.17  tff(c_3640, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5' | ~v1_tops_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_115, c_3616])).
% 14.27/6.17  tff(c_3642, plain, (~v1_tops_1('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_3640])).
% 14.27/6.17  tff(c_3740, plain, (![B_322, A_323]: (v1_tops_1(B_322, A_323) | k2_pre_topc(A_323, B_322)!=u1_struct_0(A_323) | ~m1_subset_1(B_322, k1_zfmisc_1(u1_struct_0(A_323))) | ~l1_pre_topc(A_323))), inference(cnfTransformation, [status(thm)], [f_182])).
% 14.27/6.17  tff(c_3755, plain, (![B_322]: (v1_tops_1(B_322, '#skF_4') | k2_pre_topc('#skF_4', B_322)!=u1_struct_0('#skF_4') | ~m1_subset_1(B_322, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_278, c_3740])).
% 14.27/6.17  tff(c_3798, plain, (![B_325]: (v1_tops_1(B_325, '#skF_4') | k2_pre_topc('#skF_4', B_325)!='#skF_5' | ~m1_subset_1(B_325, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_278, c_3755])).
% 14.27/6.17  tff(c_3812, plain, (v1_tops_1('#skF_5', '#skF_4') | k2_pre_topc('#skF_4', '#skF_5')!='#skF_5'), inference(resolution, [status(thm)], [c_115, c_3798])).
% 14.27/6.17  tff(c_3824, plain, (k2_pre_topc('#skF_4', '#skF_5')!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_3642, c_3812])).
% 14.27/6.17  tff(c_3982, plain, (![A_337, B_338]: (u1_struct_0('#skF_2'(A_337, B_338))=B_338 | ~m1_subset_1(B_338, k1_zfmisc_1(u1_struct_0(A_337))) | v1_xboole_0(B_338) | ~l1_pre_topc(A_337) | v2_struct_0(A_337))), inference(cnfTransformation, [status(thm)], [f_220])).
% 14.27/6.17  tff(c_3997, plain, (![B_338]: (u1_struct_0('#skF_2'('#skF_4', B_338))=B_338 | ~m1_subset_1(B_338, k1_zfmisc_1('#skF_5')) | v1_xboole_0(B_338) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_278, c_3982])).
% 14.27/6.17  tff(c_4020, plain, (![B_338]: (u1_struct_0('#skF_2'('#skF_4', B_338))=B_338 | ~m1_subset_1(B_338, k1_zfmisc_1('#skF_5')) | v1_xboole_0(B_338) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_3997])).
% 14.27/6.17  tff(c_4026, plain, (![B_339]: (u1_struct_0('#skF_2'('#skF_4', B_339))=B_339 | ~m1_subset_1(B_339, k1_zfmisc_1('#skF_5')) | v1_xboole_0(B_339))), inference(negUnitSimplification, [status(thm)], [c_104, c_4020])).
% 14.27/6.17  tff(c_4040, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_115, c_4026])).
% 14.27/6.17  tff(c_4052, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_510, c_4040])).
% 14.27/6.17  tff(c_50, plain, (![B_38, A_36]: (m1_subset_1(u1_struct_0(B_38), k1_zfmisc_1(u1_struct_0(A_36))) | ~m1_pre_topc(B_38, A_36) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_143])).
% 14.27/6.17  tff(c_7131, plain, (![B_416, A_417]: (v4_pre_topc(u1_struct_0(B_416), A_417) | ~v1_borsuk_1(B_416, A_417) | ~m1_subset_1(u1_struct_0(B_416), k1_zfmisc_1(u1_struct_0(A_417))) | ~m1_pre_topc(B_416, A_417) | ~l1_pre_topc(A_417) | ~v2_pre_topc(A_417))), inference(cnfTransformation, [status(thm)], [f_136])).
% 14.27/6.17  tff(c_7187, plain, (![B_38, A_36]: (v4_pre_topc(u1_struct_0(B_38), A_36) | ~v1_borsuk_1(B_38, A_36) | ~v2_pre_topc(A_36) | ~m1_pre_topc(B_38, A_36) | ~l1_pre_topc(A_36))), inference(resolution, [status(thm)], [c_50, c_7131])).
% 14.27/6.17  tff(c_480, plain, (![B_121]: (m1_subset_1(u1_struct_0(B_121), k1_zfmisc_1('#skF_5')) | ~m1_pre_topc(B_121, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_471])).
% 14.27/6.17  tff(c_7946, plain, (![B_445]: (k2_pre_topc('#skF_4', u1_struct_0(B_445))=u1_struct_0(B_445) | ~v4_pre_topc(u1_struct_0(B_445), '#skF_4') | ~m1_pre_topc(B_445, '#skF_4'))), inference(resolution, [status(thm)], [c_480, c_3534])).
% 14.27/6.17  tff(c_7957, plain, (![B_38]: (k2_pre_topc('#skF_4', u1_struct_0(B_38))=u1_struct_0(B_38) | ~v1_borsuk_1(B_38, '#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_pre_topc(B_38, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_7187, c_7946])).
% 14.27/6.17  tff(c_7995, plain, (![B_446]: (k2_pre_topc('#skF_4', u1_struct_0(B_446))=u1_struct_0(B_446) | ~v1_borsuk_1(B_446, '#skF_4') | ~m1_pre_topc(B_446, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_102, c_7957])).
% 14.27/6.17  tff(c_8016, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))=k2_pre_topc('#skF_4', '#skF_5') | ~v1_borsuk_1('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4052, c_7995])).
% 14.27/6.17  tff(c_8025, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5' | ~v1_borsuk_1('#skF_2'('#skF_4', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5829, c_4052, c_8016])).
% 14.27/6.17  tff(c_8026, plain, (~v1_borsuk_1('#skF_2'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_3824, c_8025])).
% 14.27/6.17  tff(c_8031, plain, (~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | ~l1_pre_topc('#skF_4') | ~v1_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_58, c_8026])).
% 14.27/6.17  tff(c_8034, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_98, c_5829, c_8031])).
% 14.27/6.17  tff(c_8036, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_8034])).
% 14.27/6.17  tff(c_8037, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_3640])).
% 14.27/6.17  tff(c_9310, plain, (![B_492, A_493]: (v4_pre_topc(B_492, A_493) | k2_pre_topc(A_493, B_492)!=B_492 | ~v2_pre_topc(A_493) | ~m1_subset_1(B_492, k1_zfmisc_1(u1_struct_0(A_493))) | ~l1_pre_topc(A_493))), inference(cnfTransformation, [status(thm)], [f_101])).
% 14.27/6.17  tff(c_9334, plain, (![B_492]: (v4_pre_topc(B_492, '#skF_4') | k2_pre_topc('#skF_4', B_492)!=B_492 | ~v2_pre_topc('#skF_4') | ~m1_subset_1(B_492, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_278, c_9310])).
% 14.27/6.17  tff(c_9377, plain, (![B_495]: (v4_pre_topc(B_495, '#skF_4') | k2_pre_topc('#skF_4', B_495)!=B_495 | ~m1_subset_1(B_495, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_102, c_9334])).
% 14.27/6.17  tff(c_9391, plain, (v4_pre_topc('#skF_5', '#skF_4') | k2_pre_topc('#skF_4', '#skF_5')!='#skF_5'), inference(resolution, [status(thm)], [c_115, c_9377])).
% 14.27/6.17  tff(c_9403, plain, (v4_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8037, c_9391])).
% 14.27/6.17  tff(c_9405, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3558, c_9403])).
% 14.27/6.17  tff(c_9406, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_3556])).
% 14.27/6.17  tff(c_9605, plain, (![B_509, A_510]: (v1_tops_1(B_509, A_510) | k2_pre_topc(A_510, B_509)!=u1_struct_0(A_510) | ~m1_subset_1(B_509, k1_zfmisc_1(u1_struct_0(A_510))) | ~l1_pre_topc(A_510))), inference(cnfTransformation, [status(thm)], [f_182])).
% 14.27/6.17  tff(c_9620, plain, (![B_509]: (v1_tops_1(B_509, '#skF_4') | k2_pre_topc('#skF_4', B_509)!=u1_struct_0('#skF_4') | ~m1_subset_1(B_509, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_278, c_9605])).
% 14.27/6.17  tff(c_9663, plain, (![B_512]: (v1_tops_1(B_512, '#skF_4') | k2_pre_topc('#skF_4', B_512)!='#skF_5' | ~m1_subset_1(B_512, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_278, c_9620])).
% 14.27/6.17  tff(c_9677, plain, (v1_tops_1('#skF_5', '#skF_4') | k2_pre_topc('#skF_4', '#skF_5')!='#skF_5'), inference(resolution, [status(thm)], [c_115, c_9663])).
% 14.27/6.17  tff(c_9689, plain, (v1_tops_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9406, c_9677])).
% 14.27/6.17  tff(c_10088, plain, (![B_539, A_540]: (v2_tex_2(B_539, A_540) | ~m1_subset_1(B_539, k1_zfmisc_1(u1_struct_0(A_540))) | ~l1_pre_topc(A_540) | ~v1_tdlat_3(A_540) | ~v2_pre_topc(A_540) | v2_struct_0(A_540))), inference(cnfTransformation, [status(thm)], [f_245])).
% 14.27/6.17  tff(c_10103, plain, (![B_539]: (v2_tex_2(B_539, '#skF_4') | ~m1_subset_1(B_539, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4') | ~v1_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_278, c_10088])).
% 14.27/6.17  tff(c_10124, plain, (![B_539]: (v2_tex_2(B_539, '#skF_4') | ~m1_subset_1(B_539, k1_zfmisc_1('#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_98, c_10103])).
% 14.27/6.17  tff(c_10129, plain, (![B_541]: (v2_tex_2(B_541, '#skF_4') | ~m1_subset_1(B_541, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_104, c_10124])).
% 14.27/6.17  tff(c_10151, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_115, c_10129])).
% 14.27/6.17  tff(c_11512, plain, (![B_568, A_569]: (v3_tex_2(B_568, A_569) | ~v2_tex_2(B_568, A_569) | ~v1_tops_1(B_568, A_569) | ~m1_subset_1(B_568, k1_zfmisc_1(u1_struct_0(A_569))) | ~l1_pre_topc(A_569) | ~v2_pre_topc(A_569) | v2_struct_0(A_569))), inference(cnfTransformation, [status(thm)], [f_292])).
% 14.27/6.17  tff(c_11536, plain, (![B_568]: (v3_tex_2(B_568, '#skF_4') | ~v2_tex_2(B_568, '#skF_4') | ~v1_tops_1(B_568, '#skF_4') | ~m1_subset_1(B_568, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_278, c_11512])).
% 14.27/6.17  tff(c_11563, plain, (![B_568]: (v3_tex_2(B_568, '#skF_4') | ~v2_tex_2(B_568, '#skF_4') | ~v1_tops_1(B_568, '#skF_4') | ~m1_subset_1(B_568, k1_zfmisc_1('#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_98, c_11536])).
% 14.27/6.17  tff(c_11675, plain, (![B_572]: (v3_tex_2(B_572, '#skF_4') | ~v2_tex_2(B_572, '#skF_4') | ~v1_tops_1(B_572, '#skF_4') | ~m1_subset_1(B_572, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_104, c_11563])).
% 14.27/6.17  tff(c_11692, plain, (v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~v1_tops_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_115, c_11675])).
% 14.27/6.17  tff(c_11706, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9689, c_10151, c_11692])).
% 14.27/6.17  tff(c_11708, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160, c_11706])).
% 14.27/6.17  tff(c_11710, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_508])).
% 14.27/6.17  tff(c_11949, plain, (![A_590]: (m1_subset_1('#skF_1'(A_590), k1_zfmisc_1(u1_struct_0(A_590))) | ~l1_pre_topc(A_590) | ~v2_pre_topc(A_590) | v2_struct_0(A_590))), inference(cnfTransformation, [status(thm)], [f_118])).
% 14.27/6.17  tff(c_11966, plain, (m1_subset_1('#skF_1'('#skF_4'), k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_278, c_11949])).
% 14.27/6.17  tff(c_11976, plain, (m1_subset_1('#skF_1'('#skF_4'), k1_zfmisc_1('#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_98, c_11966])).
% 14.27/6.17  tff(c_11977, plain, (m1_subset_1('#skF_1'('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_104, c_11976])).
% 14.27/6.17  tff(c_11999, plain, (r1_tarski('#skF_1'('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_11977, c_22])).
% 14.27/6.17  tff(c_12005, plain, (~v1_xboole_0('#skF_5') | '#skF_1'('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_11999, c_345])).
% 14.27/6.17  tff(c_12009, plain, ('#skF_1'('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_11710, c_12005])).
% 14.27/6.17  tff(c_40, plain, (![A_27]: (~v1_xboole_0('#skF_1'(A_27)) | ~l1_pre_topc(A_27) | ~v2_pre_topc(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_118])).
% 14.27/6.17  tff(c_12026, plain, (~v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12009, c_40])).
% 14.27/6.17  tff(c_12039, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_98, c_11710, c_12026])).
% 14.27/6.17  tff(c_12041, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_12039])).
% 14.27/6.17  tff(c_12043, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_106])).
% 14.27/6.17  tff(c_6, plain, (![A_4]: (k1_subset_1(A_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.27/6.17  tff(c_10, plain, (![A_6]: (m1_subset_1(k1_subset_1(A_6), k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.27/6.17  tff(c_119, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10])).
% 14.27/6.17  tff(c_12051, plain, (![A_591, B_592]: (r1_tarski(A_591, B_592) | ~m1_subset_1(A_591, k1_zfmisc_1(B_592)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.27/6.17  tff(c_12062, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(resolution, [status(thm)], [c_119, c_12051])).
% 14.27/6.17  tff(c_2, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.27/6.17  tff(c_12072, plain, (![B_599, A_600]: (~r1_xboole_0(B_599, A_600) | ~r1_tarski(B_599, A_600) | v1_xboole_0(B_599))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.27/6.17  tff(c_12077, plain, (![A_601]: (~r1_tarski(A_601, k1_xboole_0) | v1_xboole_0(A_601))), inference(resolution, [status(thm)], [c_2, c_12072])).
% 14.27/6.17  tff(c_12086, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_12062, c_12077])).
% 14.27/6.17  tff(c_16, plain, (![A_10]: (k3_subset_1(A_10, k1_subset_1(A_10))=k2_subset_1(A_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 14.27/6.17  tff(c_116, plain, (![A_10]: (k3_subset_1(A_10, k1_subset_1(A_10))=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_16])).
% 14.27/6.17  tff(c_120, plain, (![A_10]: (k3_subset_1(A_10, k1_xboole_0)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_116])).
% 14.27/6.17  tff(c_12235, plain, (![A_622, B_623]: (k3_subset_1(A_622, k3_subset_1(A_622, B_623))=B_623 | ~m1_subset_1(B_623, k1_zfmisc_1(A_622)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.27/6.17  tff(c_12243, plain, (![A_6]: (k3_subset_1(A_6, k3_subset_1(A_6, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_119, c_12235])).
% 14.27/6.17  tff(c_12249, plain, (![A_6]: (k3_subset_1(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_120, c_12243])).
% 14.27/6.17  tff(c_23865, plain, (![A_1144, B_1145]: (k2_pre_topc(A_1144, B_1145)=B_1145 | ~v4_pre_topc(B_1145, A_1144) | ~m1_subset_1(B_1145, k1_zfmisc_1(u1_struct_0(A_1144))) | ~l1_pre_topc(A_1144))), inference(cnfTransformation, [status(thm)], [f_101])).
% 14.27/6.17  tff(c_23892, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5' | ~v4_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_96, c_23865])).
% 14.27/6.17  tff(c_23901, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5' | ~v4_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_23892])).
% 14.27/6.17  tff(c_23902, plain, (~v4_pre_topc('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_23901])).
% 14.27/6.17  tff(c_12587, plain, (![A_660, B_661]: (k2_pre_topc(A_660, B_661)=B_661 | ~v4_pre_topc(B_661, A_660) | ~m1_subset_1(B_661, k1_zfmisc_1(u1_struct_0(A_660))) | ~l1_pre_topc(A_660))), inference(cnfTransformation, [status(thm)], [f_101])).
% 14.27/6.17  tff(c_12614, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5' | ~v4_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_96, c_12587])).
% 14.27/6.17  tff(c_12623, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5' | ~v4_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_12614])).
% 14.27/6.17  tff(c_12624, plain, (~v4_pre_topc('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_12623])).
% 14.27/6.17  tff(c_14490, plain, (![A_772, B_773]: (v1_pre_topc('#skF_2'(A_772, B_773)) | ~m1_subset_1(B_773, k1_zfmisc_1(u1_struct_0(A_772))) | v1_xboole_0(B_773) | ~l1_pre_topc(A_772) | v2_struct_0(A_772))), inference(cnfTransformation, [status(thm)], [f_220])).
% 14.27/6.17  tff(c_14517, plain, (v1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_96, c_14490])).
% 14.27/6.17  tff(c_14527, plain, (v1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_14517])).
% 14.27/6.17  tff(c_14528, plain, (v1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_104, c_14527])).
% 14.27/6.17  tff(c_14529, plain, (v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_14528])).
% 14.27/6.17  tff(c_14584, plain, (![B_776, A_777]: (~v3_tex_2(B_776, A_777) | ~m1_subset_1(B_776, k1_zfmisc_1(u1_struct_0(A_777))) | ~v1_xboole_0(B_776) | ~l1_pre_topc(A_777) | ~v2_pre_topc(A_777) | v2_struct_0(A_777))), inference(cnfTransformation, [status(thm)], [f_260])).
% 14.27/6.17  tff(c_14607, plain, (~v3_tex_2('#skF_5', '#skF_4') | ~v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_96, c_14584])).
% 14.27/6.17  tff(c_14615, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_98, c_14529, c_12043, c_14607])).
% 14.27/6.17  tff(c_14617, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_14615])).
% 14.27/6.17  tff(c_14619, plain, (~v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_14528])).
% 14.27/6.17  tff(c_14842, plain, (![A_799, B_800]: (m1_pre_topc('#skF_2'(A_799, B_800), A_799) | ~m1_subset_1(B_800, k1_zfmisc_1(u1_struct_0(A_799))) | v1_xboole_0(B_800) | ~l1_pre_topc(A_799) | v2_struct_0(A_799))), inference(cnfTransformation, [status(thm)], [f_220])).
% 14.27/6.17  tff(c_14861, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_96, c_14842])).
% 14.27/6.17  tff(c_14871, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_14861])).
% 14.27/6.17  tff(c_14872, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_104, c_14619, c_14871])).
% 14.27/6.17  tff(c_14886, plain, (![A_801, B_802]: (u1_struct_0('#skF_2'(A_801, B_802))=B_802 | ~m1_subset_1(B_802, k1_zfmisc_1(u1_struct_0(A_801))) | v1_xboole_0(B_802) | ~l1_pre_topc(A_801) | v2_struct_0(A_801))), inference(cnfTransformation, [status(thm)], [f_220])).
% 14.27/6.17  tff(c_14913, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_96, c_14886])).
% 14.27/6.17  tff(c_14923, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_14913])).
% 14.27/6.17  tff(c_14924, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_104, c_14619, c_14923])).
% 14.27/6.17  tff(c_19294, plain, (![B_940, A_941]: (v4_pre_topc(u1_struct_0(B_940), A_941) | ~v1_borsuk_1(B_940, A_941) | ~m1_subset_1(u1_struct_0(B_940), k1_zfmisc_1(u1_struct_0(A_941))) | ~m1_pre_topc(B_940, A_941) | ~l1_pre_topc(A_941) | ~v2_pre_topc(A_941))), inference(cnfTransformation, [status(thm)], [f_136])).
% 14.27/6.17  tff(c_19902, plain, (![B_970, A_971]: (v4_pre_topc(u1_struct_0(B_970), A_971) | ~v1_borsuk_1(B_970, A_971) | ~v2_pre_topc(A_971) | ~m1_pre_topc(B_970, A_971) | ~l1_pre_topc(A_971))), inference(resolution, [status(thm)], [c_50, c_19294])).
% 14.27/6.17  tff(c_19935, plain, (![A_973]: (v4_pre_topc('#skF_5', A_973) | ~v1_borsuk_1('#skF_2'('#skF_4', '#skF_5'), A_973) | ~v2_pre_topc(A_973) | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_973) | ~l1_pre_topc(A_973))), inference(superposition, [status(thm), theory('equality')], [c_14924, c_19902])).
% 14.27/6.17  tff(c_22539, plain, (![A_1063]: (v4_pre_topc('#skF_5', A_1063) | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_1063) | ~l1_pre_topc(A_1063) | ~v1_tdlat_3(A_1063) | ~v2_pre_topc(A_1063) | v2_struct_0(A_1063))), inference(resolution, [status(thm)], [c_58, c_19935])).
% 14.27/6.17  tff(c_22545, plain, (v4_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v1_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_14872, c_22539])).
% 14.27/6.17  tff(c_22552, plain, (v4_pre_topc('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_98, c_22545])).
% 14.27/6.17  tff(c_22554, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_12624, c_22552])).
% 14.27/6.17  tff(c_22555, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_12623])).
% 14.27/6.17  tff(c_22695, plain, (![B_1083, A_1084]: (v1_tops_1(B_1083, A_1084) | k2_pre_topc(A_1084, B_1083)!=u1_struct_0(A_1084) | ~m1_subset_1(B_1083, k1_zfmisc_1(u1_struct_0(A_1084))) | ~l1_pre_topc(A_1084))), inference(cnfTransformation, [status(thm)], [f_182])).
% 14.27/6.17  tff(c_22722, plain, (v1_tops_1('#skF_5', '#skF_4') | k2_pre_topc('#skF_4', '#skF_5')!=u1_struct_0('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_96, c_22695])).
% 14.27/6.17  tff(c_22731, plain, (v1_tops_1('#skF_5', '#skF_4') | u1_struct_0('#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_22555, c_22722])).
% 14.27/6.17  tff(c_22732, plain, (u1_struct_0('#skF_4')!='#skF_5'), inference(splitLeft, [status(thm)], [c_22731])).
% 14.27/6.17  tff(c_22734, plain, (![A_1086, B_1087]: (k2_pre_topc(A_1086, B_1087)=u1_struct_0(A_1086) | ~v1_tops_1(B_1087, A_1086) | ~m1_subset_1(B_1087, k1_zfmisc_1(u1_struct_0(A_1086))) | ~l1_pre_topc(A_1086))), inference(cnfTransformation, [status(thm)], [f_182])).
% 14.27/6.17  tff(c_22761, plain, (k2_pre_topc('#skF_4', '#skF_5')=u1_struct_0('#skF_4') | ~v1_tops_1('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_96, c_22734])).
% 14.27/6.17  tff(c_22770, plain, (u1_struct_0('#skF_4')='#skF_5' | ~v1_tops_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_22555, c_22761])).
% 14.27/6.17  tff(c_22771, plain, (~v1_tops_1('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_22732, c_22770])).
% 14.27/6.17  tff(c_22599, plain, (![B_1073, A_1074]: (v3_pre_topc(B_1073, A_1074) | ~m1_subset_1(B_1073, k1_zfmisc_1(u1_struct_0(A_1074))) | ~v1_tdlat_3(A_1074) | ~l1_pre_topc(A_1074) | ~v2_pre_topc(A_1074))), inference(cnfTransformation, [status(thm)], [f_231])).
% 14.27/6.17  tff(c_22626, plain, (v3_pre_topc('#skF_5', '#skF_4') | ~v1_tdlat_3('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_96, c_22599])).
% 14.27/6.17  tff(c_22635, plain, (v3_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_98, c_100, c_22626])).
% 14.27/6.17  tff(c_23668, plain, (![B_1125, A_1126]: (v1_tops_1(B_1125, A_1126) | ~v3_tex_2(B_1125, A_1126) | ~v3_pre_topc(B_1125, A_1126) | ~m1_subset_1(B_1125, k1_zfmisc_1(u1_struct_0(A_1126))) | ~l1_pre_topc(A_1126) | ~v2_pre_topc(A_1126) | v2_struct_0(A_1126))), inference(cnfTransformation, [status(thm)], [f_276])).
% 14.27/6.17  tff(c_23701, plain, (v1_tops_1('#skF_5', '#skF_4') | ~v3_tex_2('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_96, c_23668])).
% 14.27/6.17  tff(c_23714, plain, (v1_tops_1('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_98, c_22635, c_12043, c_23701])).
% 14.27/6.17  tff(c_23716, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_22771, c_23714])).
% 14.27/6.17  tff(c_23718, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_22731])).
% 14.27/6.17  tff(c_12042, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_106])).
% 14.27/6.17  tff(c_12161, plain, (![B_611, A_612]: (~v1_subset_1(B_611, A_612) | ~m1_subset_1(B_611, k1_zfmisc_1(A_612)) | ~v1_xboole_0(A_612))), inference(cnfTransformation, [status(thm)], [f_67])).
% 14.27/6.17  tff(c_12176, plain, (~v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_96, c_12161])).
% 14.27/6.17  tff(c_12182, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12042, c_12176])).
% 14.27/6.17  tff(c_12250, plain, (k3_subset_1(u1_struct_0('#skF_4'), k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_96, c_12235])).
% 14.27/6.17  tff(c_12512, plain, (![A_650, B_651]: (~v1_xboole_0(k3_subset_1(A_650, B_651)) | ~m1_subset_1(B_651, k1_zfmisc_1(A_650)) | ~v1_subset_1(B_651, A_650) | v1_xboole_0(A_650))), inference(cnfTransformation, [status(thm)], [f_199])).
% 14.27/6.17  tff(c_12550, plain, (![B_652, A_653]: (~v1_xboole_0(k3_subset_1(B_652, A_653)) | ~v1_subset_1(A_653, B_652) | v1_xboole_0(B_652) | ~r1_tarski(A_653, B_652))), inference(resolution, [status(thm)], [c_24, c_12512])).
% 14.27/6.17  tff(c_12556, plain, (~v1_xboole_0('#skF_5') | ~v1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~r1_tarski(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), u1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_12250, c_12550])).
% 14.27/6.17  tff(c_12563, plain, (~v1_xboole_0('#skF_5') | ~v1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), u1_struct_0('#skF_4')) | ~r1_tarski(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_12182, c_12556])).
% 14.27/6.17  tff(c_12569, plain, (~r1_tarski(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_12563])).
% 14.27/6.17  tff(c_23720, plain, (~r1_tarski(k3_subset_1('#skF_5', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_23718, c_23718, c_12569])).
% 14.27/6.17  tff(c_23730, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12062, c_12249, c_23720])).
% 14.27/6.17  tff(c_23731, plain, (~v1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), u1_struct_0('#skF_4')) | ~v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_12563])).
% 14.27/6.17  tff(c_23743, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_23731])).
% 14.27/6.17  tff(c_25243, plain, (![A_1219, B_1220]: (m1_pre_topc('#skF_2'(A_1219, B_1220), A_1219) | ~m1_subset_1(B_1220, k1_zfmisc_1(u1_struct_0(A_1219))) | v1_xboole_0(B_1220) | ~l1_pre_topc(A_1219) | v2_struct_0(A_1219))), inference(cnfTransformation, [status(thm)], [f_220])).
% 14.27/6.17  tff(c_25262, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_96, c_25243])).
% 14.27/6.17  tff(c_25272, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_25262])).
% 14.27/6.17  tff(c_25273, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_104, c_23743, c_25272])).
% 14.27/6.17  tff(c_25337, plain, (![A_1225, B_1226]: (u1_struct_0('#skF_2'(A_1225, B_1226))=B_1226 | ~m1_subset_1(B_1226, k1_zfmisc_1(u1_struct_0(A_1225))) | v1_xboole_0(B_1226) | ~l1_pre_topc(A_1225) | v2_struct_0(A_1225))), inference(cnfTransformation, [status(thm)], [f_220])).
% 14.27/6.17  tff(c_25364, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_96, c_25337])).
% 14.27/6.17  tff(c_25374, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_25364])).
% 14.27/6.17  tff(c_25375, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_104, c_23743, c_25374])).
% 14.27/6.17  tff(c_28335, plain, (![B_1317, A_1318]: (v4_pre_topc(u1_struct_0(B_1317), A_1318) | ~v1_borsuk_1(B_1317, A_1318) | ~m1_subset_1(u1_struct_0(B_1317), k1_zfmisc_1(u1_struct_0(A_1318))) | ~m1_pre_topc(B_1317, A_1318) | ~l1_pre_topc(A_1318) | ~v2_pre_topc(A_1318))), inference(cnfTransformation, [status(thm)], [f_136])).
% 14.27/6.17  tff(c_29507, plain, (![B_1333, A_1334]: (v4_pre_topc(u1_struct_0(B_1333), A_1334) | ~v1_borsuk_1(B_1333, A_1334) | ~v2_pre_topc(A_1334) | ~m1_pre_topc(B_1333, A_1334) | ~l1_pre_topc(A_1334))), inference(resolution, [status(thm)], [c_50, c_28335])).
% 14.27/6.17  tff(c_29583, plain, (![A_1339]: (v4_pre_topc('#skF_5', A_1339) | ~v1_borsuk_1('#skF_2'('#skF_4', '#skF_5'), A_1339) | ~v2_pre_topc(A_1339) | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_1339) | ~l1_pre_topc(A_1339))), inference(superposition, [status(thm), theory('equality')], [c_25375, c_29507])).
% 14.27/6.17  tff(c_34085, plain, (![A_1458]: (v4_pre_topc('#skF_5', A_1458) | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_1458) | ~l1_pre_topc(A_1458) | ~v1_tdlat_3(A_1458) | ~v2_pre_topc(A_1458) | v2_struct_0(A_1458))), inference(resolution, [status(thm)], [c_58, c_29583])).
% 14.27/6.17  tff(c_34091, plain, (v4_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v1_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_25273, c_34085])).
% 14.27/6.17  tff(c_34098, plain, (v4_pre_topc('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_98, c_34091])).
% 14.27/6.17  tff(c_34100, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_23902, c_34098])).
% 14.27/6.17  tff(c_34101, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_23901])).
% 14.27/6.17  tff(c_34297, plain, (![B_1477, A_1478]: (v1_tops_1(B_1477, A_1478) | k2_pre_topc(A_1478, B_1477)!=u1_struct_0(A_1478) | ~m1_subset_1(B_1477, k1_zfmisc_1(u1_struct_0(A_1478))) | ~l1_pre_topc(A_1478))), inference(cnfTransformation, [status(thm)], [f_182])).
% 14.27/6.17  tff(c_34324, plain, (v1_tops_1('#skF_5', '#skF_4') | k2_pre_topc('#skF_4', '#skF_5')!=u1_struct_0('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_96, c_34297])).
% 14.27/6.17  tff(c_34333, plain, (v1_tops_1('#skF_5', '#skF_4') | u1_struct_0('#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_34101, c_34324])).
% 14.27/6.17  tff(c_34334, plain, (u1_struct_0('#skF_4')!='#skF_5'), inference(splitLeft, [status(thm)], [c_34333])).
% 14.27/6.17  tff(c_34338, plain, (![A_1482, B_1483]: (k2_pre_topc(A_1482, B_1483)=u1_struct_0(A_1482) | ~v1_tops_1(B_1483, A_1482) | ~m1_subset_1(B_1483, k1_zfmisc_1(u1_struct_0(A_1482))) | ~l1_pre_topc(A_1482))), inference(cnfTransformation, [status(thm)], [f_182])).
% 14.27/6.17  tff(c_34365, plain, (k2_pre_topc('#skF_4', '#skF_5')=u1_struct_0('#skF_4') | ~v1_tops_1('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_96, c_34338])).
% 14.27/6.17  tff(c_34374, plain, (u1_struct_0('#skF_4')='#skF_5' | ~v1_tops_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_34101, c_34365])).
% 14.27/6.17  tff(c_34375, plain, (~v1_tops_1('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_34334, c_34374])).
% 14.27/6.17  tff(c_23755, plain, (![B_1131, A_1132]: (v3_pre_topc(B_1131, A_1132) | ~m1_subset_1(B_1131, k1_zfmisc_1(u1_struct_0(A_1132))) | ~v1_tdlat_3(A_1132) | ~l1_pre_topc(A_1132) | ~v2_pre_topc(A_1132))), inference(cnfTransformation, [status(thm)], [f_231])).
% 14.27/6.17  tff(c_23782, plain, (v3_pre_topc('#skF_5', '#skF_4') | ~v1_tdlat_3('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_96, c_23755])).
% 14.27/6.17  tff(c_23791, plain, (v3_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_98, c_100, c_23782])).
% 14.27/6.17  tff(c_36563, plain, (![B_1565, A_1566]: (v1_tops_1(B_1565, A_1566) | ~v3_tex_2(B_1565, A_1566) | ~v3_pre_topc(B_1565, A_1566) | ~m1_subset_1(B_1565, k1_zfmisc_1(u1_struct_0(A_1566))) | ~l1_pre_topc(A_1566) | ~v2_pre_topc(A_1566) | v2_struct_0(A_1566))), inference(cnfTransformation, [status(thm)], [f_276])).
% 14.27/6.17  tff(c_36602, plain, (v1_tops_1('#skF_5', '#skF_4') | ~v3_tex_2('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_96, c_36563])).
% 14.27/6.17  tff(c_36618, plain, (v1_tops_1('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_98, c_23791, c_12043, c_36602])).
% 14.27/6.17  tff(c_36620, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_34375, c_36618])).
% 14.27/6.17  tff(c_36622, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_34333])).
% 14.27/6.17  tff(c_12536, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5')) | ~v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_96, c_12512])).
% 14.27/6.17  tff(c_12548, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12042, c_12536])).
% 14.27/6.17  tff(c_12549, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_12182, c_12548])).
% 14.27/6.17  tff(c_36628, plain, (~v1_xboole_0(k3_subset_1('#skF_5', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_36622, c_12549])).
% 14.27/6.17  tff(c_36641, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12086, c_12249, c_36628])).
% 14.27/6.17  tff(c_36643, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_23731])).
% 14.27/6.17  tff(c_12114, plain, (![B_603, A_604]: (v1_subset_1(B_603, A_604) | B_603=A_604 | ~m1_subset_1(B_603, k1_zfmisc_1(A_604)))), inference(cnfTransformation, [status(thm)], [f_189])).
% 14.27/6.17  tff(c_12130, plain, (![A_17, B_18]: (v1_subset_1(A_17, B_18) | B_18=A_17 | ~r1_tarski(A_17, B_18))), inference(resolution, [status(thm)], [c_24, c_12114])).
% 14.27/6.17  tff(c_12183, plain, (![A_613]: (~v1_subset_1(k1_xboole_0, A_613) | ~v1_xboole_0(A_613))), inference(resolution, [status(thm)], [c_119, c_12161])).
% 14.27/6.17  tff(c_12187, plain, (![B_18]: (~v1_xboole_0(B_18) | k1_xboole_0=B_18 | ~r1_tarski(k1_xboole_0, B_18))), inference(resolution, [status(thm)], [c_12130, c_12183])).
% 14.27/6.17  tff(c_12193, plain, (![B_18]: (~v1_xboole_0(B_18) | k1_xboole_0=B_18)), inference(demodulation, [status(thm), theory('equality')], [c_12062, c_12187])).
% 14.27/6.17  tff(c_36647, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_36643, c_12193])).
% 14.27/6.17  tff(c_36671, plain, (![A_6]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_36647, c_119])).
% 14.27/6.17  tff(c_37174, plain, (![B_1619, A_1620]: (~v3_tex_2(B_1619, A_1620) | ~m1_subset_1(B_1619, k1_zfmisc_1(u1_struct_0(A_1620))) | ~v1_xboole_0(B_1619) | ~l1_pre_topc(A_1620) | ~v2_pre_topc(A_1620) | v2_struct_0(A_1620))), inference(cnfTransformation, [status(thm)], [f_260])).
% 14.27/6.17  tff(c_37178, plain, (![A_1620]: (~v3_tex_2('#skF_5', A_1620) | ~v1_xboole_0('#skF_5') | ~l1_pre_topc(A_1620) | ~v2_pre_topc(A_1620) | v2_struct_0(A_1620))), inference(resolution, [status(thm)], [c_36671, c_37174])).
% 14.27/6.17  tff(c_37207, plain, (![A_1621]: (~v3_tex_2('#skF_5', A_1621) | ~l1_pre_topc(A_1621) | ~v2_pre_topc(A_1621) | v2_struct_0(A_1621))), inference(demodulation, [status(thm), theory('equality')], [c_36643, c_37178])).
% 14.27/6.17  tff(c_37210, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_12043, c_37207])).
% 14.27/6.17  tff(c_37213, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_98, c_37210])).
% 14.27/6.17  tff(c_37215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_37213])).
% 14.27/6.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.27/6.17  
% 14.27/6.17  Inference rules
% 14.27/6.17  ----------------------
% 14.27/6.17  #Ref     : 0
% 14.27/6.17  #Sup     : 8157
% 14.27/6.17  #Fact    : 0
% 14.27/6.17  #Define  : 0
% 14.27/6.17  #Split   : 82
% 14.27/6.17  #Chain   : 0
% 14.27/6.17  #Close   : 0
% 14.27/6.17  
% 14.27/6.17  Ordering : KBO
% 14.27/6.17  
% 14.27/6.17  Simplification rules
% 14.27/6.17  ----------------------
% 14.27/6.17  #Subsume      : 1551
% 14.27/6.17  #Demod        : 6787
% 14.27/6.17  #Tautology    : 1828
% 14.27/6.17  #SimpNegUnit  : 1403
% 14.27/6.17  #BackRed      : 165
% 14.27/6.17  
% 14.27/6.17  #Partial instantiations: 0
% 14.27/6.17  #Strategies tried      : 1
% 14.27/6.17  
% 14.27/6.17  Timing (in seconds)
% 14.27/6.17  ----------------------
% 14.27/6.18  Preprocessing        : 0.40
% 14.27/6.18  Parsing              : 0.22
% 14.27/6.18  CNF conversion       : 0.03
% 14.27/6.18  Main loop            : 4.97
% 14.27/6.18  Inferencing          : 1.50
% 14.27/6.18  Reduction            : 1.84
% 14.27/6.18  Demodulation         : 1.28
% 14.27/6.18  BG Simplification    : 0.14
% 14.27/6.18  Subsumption          : 1.14
% 14.27/6.18  Abstraction          : 0.17
% 14.27/6.18  MUC search           : 0.00
% 14.27/6.18  Cooper               : 0.00
% 14.27/6.18  Total                : 5.45
% 14.27/6.18  Index Insertion      : 0.00
% 14.27/6.18  Index Deletion       : 0.00
% 14.27/6.18  Index Matching       : 0.00
% 14.27/6.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
