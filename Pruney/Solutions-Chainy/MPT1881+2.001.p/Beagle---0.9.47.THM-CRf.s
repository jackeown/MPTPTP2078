%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:05 EST 2020

% Result     : Theorem 11.93s
% Output     : CNFRefutation 12.09s
% Verified   : 
% Statistics : Number of formulae       :  241 ( 865 expanded)
%              Number of leaves         :   64 ( 311 expanded)
%              Depth                    :   14
%              Number of atoms          :  564 (2593 expanded)
%              Number of equality atoms :   74 ( 264 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tsep_1 > v1_tops_1 > v1_subset_1 > v1_borsuk_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k9_setfam_1 > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_7 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v1_borsuk_1,type,(
    v1_borsuk_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_46,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_48,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_58,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_50,axiom,(
    ! [A] : m1_subset_1(k1_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_315,negated_conjecture,(
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

tff(f_123,axiom,(
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

tff(f_52,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_194,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_148,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ~ v1_subset_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).

tff(f_225,axiom,(
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

tff(f_172,axiom,(
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

tff(f_187,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_141,axiom,(
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

tff(f_250,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_297,axiom,(
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

tff(f_108,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_pre_topc)).

tff(f_265,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_236,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).

tff(f_281,axiom,(
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

tff(f_204,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_subset_1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(A)) )
     => ~ v1_xboole_0(k3_subset_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tex_2)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : r1_xboole_0(A_2,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12538,plain,(
    ! [B_574,A_575] :
      ( ~ r1_xboole_0(B_574,A_575)
      | ~ r1_tarski(B_574,A_575)
      | v1_xboole_0(B_574) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12543,plain,(
    ! [A_576] :
      ( ~ r1_tarski(A_576,k1_xboole_0)
      | v1_xboole_0(A_576) ) ),
    inference(resolution,[status(thm)],[c_4,c_12538])).

tff(c_12548,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_12543])).

tff(c_20,plain,(
    ! [A_10] : k1_subset_1(A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_22,plain,(
    ! [A_11] : k2_subset_1(A_11) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_30,plain,(
    ! [A_16] : k3_subset_1(A_16,k1_subset_1(A_16)) = k2_subset_1(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_123,plain,(
    ! [A_16] : k3_subset_1(A_16,k1_subset_1(A_16)) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_30])).

tff(c_128,plain,(
    ! [A_16] : k3_subset_1(A_16,k1_xboole_0) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_123])).

tff(c_24,plain,(
    ! [A_12] : m1_subset_1(k1_subset_1(A_12),k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_127,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_24])).

tff(c_12648,plain,(
    ! [A_591,B_592] :
      ( k3_subset_1(A_591,k3_subset_1(A_591,B_592)) = B_592
      | ~ m1_subset_1(B_592,k1_zfmisc_1(A_591)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12654,plain,(
    ! [A_12] : k3_subset_1(A_12,k3_subset_1(A_12,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_127,c_12648])).

tff(c_12659,plain,(
    ! [A_12] : k3_subset_1(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_12654])).

tff(c_112,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_106,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_104,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_12852,plain,(
    ! [A_624,B_625] :
      ( k2_pre_topc(A_624,B_625) = B_625
      | ~ v4_pre_topc(B_625,A_624)
      | ~ m1_subset_1(B_625,k1_zfmisc_1(u1_struct_0(A_624)))
      | ~ l1_pre_topc(A_624) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_12875,plain,
    ( k2_pre_topc('#skF_6','#skF_7') = '#skF_7'
    | ~ v4_pre_topc('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_104,c_12852])).

tff(c_12883,plain,
    ( k2_pre_topc('#skF_6','#skF_7') = '#skF_7'
    | ~ v4_pre_topc('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_12875])).

tff(c_12884,plain,(
    ~ v4_pre_topc('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_12883])).

tff(c_110,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_108,plain,(
    v1_tdlat_3('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_120,plain,
    ( v3_tex_2('#skF_7','#skF_6')
    | ~ v1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_176,plain,(
    ~ v1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_114,plain,
    ( v1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ v3_tex_2('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_177,plain,(
    ~ v3_tex_2('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_26,plain,(
    ! [A_13] : m1_subset_1(k2_subset_1(A_13),k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_124,plain,(
    ! [A_13] : m1_subset_1(A_13,k1_zfmisc_1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26])).

tff(c_237,plain,(
    ! [B_103,A_104] :
      ( v1_subset_1(B_103,A_104)
      | B_103 = A_104
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_249,plain,
    ( v1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | u1_struct_0('#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_104,c_237])).

tff(c_257,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_249])).

tff(c_2910,plain,(
    ! [A_288,B_289] :
      ( k2_pre_topc(A_288,B_289) = B_289
      | ~ v4_pre_topc(B_289,A_288)
      | ~ m1_subset_1(B_289,k1_zfmisc_1(u1_struct_0(A_288)))
      | ~ l1_pre_topc(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2925,plain,(
    ! [B_289] :
      ( k2_pre_topc('#skF_6',B_289) = B_289
      | ~ v4_pre_topc(B_289,'#skF_6')
      | ~ m1_subset_1(B_289,k1_zfmisc_1('#skF_7'))
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_2910])).

tff(c_2946,plain,(
    ! [B_291] :
      ( k2_pre_topc('#skF_6',B_291) = B_291
      | ~ v4_pre_topc(B_291,'#skF_6')
      | ~ m1_subset_1(B_291,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_2925])).

tff(c_2963,plain,
    ( k2_pre_topc('#skF_6','#skF_7') = '#skF_7'
    | ~ v4_pre_topc('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_124,c_2946])).

tff(c_2965,plain,(
    ~ v4_pre_topc('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2963])).

tff(c_392,plain,(
    ! [B_118,A_119] :
      ( m1_subset_1(u1_struct_0(B_118),k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ m1_pre_topc(B_118,A_119)
      | ~ l1_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_409,plain,(
    ! [B_118] :
      ( m1_subset_1(u1_struct_0(B_118),k1_zfmisc_1('#skF_7'))
      | ~ m1_pre_topc(B_118,'#skF_6')
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_392])).

tff(c_419,plain,(
    ! [B_120] :
      ( m1_subset_1(u1_struct_0(B_120),k1_zfmisc_1('#skF_7'))
      | ~ m1_pre_topc(B_120,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_409])).

tff(c_34,plain,(
    ! [B_22,A_20] :
      ( ~ v1_subset_1(B_22,A_20)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_20))
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_437,plain,(
    ! [B_120] :
      ( ~ v1_subset_1(u1_struct_0(B_120),'#skF_7')
      | ~ v1_xboole_0('#skF_7')
      | ~ m1_pre_topc(B_120,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_419,c_34])).

tff(c_439,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_437])).

tff(c_5357,plain,(
    ! [A_383,B_384] :
      ( m1_pre_topc('#skF_4'(A_383,B_384),A_383)
      | ~ m1_subset_1(B_384,k1_zfmisc_1(u1_struct_0(A_383)))
      | v1_xboole_0(B_384)
      | ~ l1_pre_topc(A_383)
      | v2_struct_0(A_383) ) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_5379,plain,(
    ! [B_384] :
      ( m1_pre_topc('#skF_4'('#skF_6',B_384),'#skF_6')
      | ~ m1_subset_1(B_384,k1_zfmisc_1('#skF_7'))
      | v1_xboole_0(B_384)
      | ~ l1_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_5357])).

tff(c_5405,plain,(
    ! [B_384] :
      ( m1_pre_topc('#skF_4'('#skF_6',B_384),'#skF_6')
      | ~ m1_subset_1(B_384,k1_zfmisc_1('#skF_7'))
      | v1_xboole_0(B_384)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_5379])).

tff(c_5410,plain,(
    ! [B_385] :
      ( m1_pre_topc('#skF_4'('#skF_6',B_385),'#skF_6')
      | ~ m1_subset_1(B_385,k1_zfmisc_1('#skF_7'))
      | v1_xboole_0(B_385) ) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_5405])).

tff(c_5420,plain,
    ( m1_pre_topc('#skF_4'('#skF_6','#skF_7'),'#skF_6')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_124,c_5410])).

tff(c_5431,plain,(
    m1_pre_topc('#skF_4'('#skF_6','#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_439,c_5420])).

tff(c_66,plain,(
    ! [B_46,A_44] :
      ( v1_borsuk_1(B_46,A_44)
      | ~ m1_pre_topc(B_46,A_44)
      | ~ l1_pre_topc(A_44)
      | ~ v1_tdlat_3(A_44)
      | ~ v2_pre_topc(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_3062,plain,(
    ! [B_305,A_306] :
      ( v1_tops_1(B_305,A_306)
      | k2_pre_topc(A_306,B_305) != u1_struct_0(A_306)
      | ~ m1_subset_1(B_305,k1_zfmisc_1(u1_struct_0(A_306)))
      | ~ l1_pre_topc(A_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_3077,plain,(
    ! [B_305] :
      ( v1_tops_1(B_305,'#skF_6')
      | k2_pre_topc('#skF_6',B_305) != u1_struct_0('#skF_6')
      | ~ m1_subset_1(B_305,k1_zfmisc_1('#skF_7'))
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_3062])).

tff(c_3098,plain,(
    ! [B_308] :
      ( v1_tops_1(B_308,'#skF_6')
      | k2_pre_topc('#skF_6',B_308) != '#skF_7'
      | ~ m1_subset_1(B_308,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_257,c_3077])).

tff(c_3116,plain,
    ( v1_tops_1('#skF_7','#skF_6')
    | k2_pre_topc('#skF_6','#skF_7') != '#skF_7' ),
    inference(resolution,[status(thm)],[c_124,c_3098])).

tff(c_3118,plain,(
    k2_pre_topc('#skF_6','#skF_7') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_3116])).

tff(c_3738,plain,(
    ! [A_367,B_368] :
      ( u1_struct_0('#skF_4'(A_367,B_368)) = B_368
      | ~ m1_subset_1(B_368,k1_zfmisc_1(u1_struct_0(A_367)))
      | v1_xboole_0(B_368)
      | ~ l1_pre_topc(A_367)
      | v2_struct_0(A_367) ) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_3753,plain,(
    ! [B_368] :
      ( u1_struct_0('#skF_4'('#skF_6',B_368)) = B_368
      | ~ m1_subset_1(B_368,k1_zfmisc_1('#skF_7'))
      | v1_xboole_0(B_368)
      | ~ l1_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_3738])).

tff(c_3772,plain,(
    ! [B_368] :
      ( u1_struct_0('#skF_4'('#skF_6',B_368)) = B_368
      | ~ m1_subset_1(B_368,k1_zfmisc_1('#skF_7'))
      | v1_xboole_0(B_368)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_3753])).

tff(c_3777,plain,(
    ! [B_369] :
      ( u1_struct_0('#skF_4'('#skF_6',B_369)) = B_369
      | ~ m1_subset_1(B_369,k1_zfmisc_1('#skF_7'))
      | v1_xboole_0(B_369) ) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_3772])).

tff(c_3787,plain,
    ( u1_struct_0('#skF_4'('#skF_6','#skF_7')) = '#skF_7'
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_124,c_3777])).

tff(c_3798,plain,(
    u1_struct_0('#skF_4'('#skF_6','#skF_7')) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_439,c_3787])).

tff(c_58,plain,(
    ! [B_42,A_40] :
      ( m1_subset_1(u1_struct_0(B_42),k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ m1_pre_topc(B_42,A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_6649,plain,(
    ! [B_406,A_407] :
      ( v4_pre_topc(u1_struct_0(B_406),A_407)
      | ~ v1_borsuk_1(B_406,A_407)
      | ~ m1_subset_1(u1_struct_0(B_406),k1_zfmisc_1(u1_struct_0(A_407)))
      | ~ m1_pre_topc(B_406,A_407)
      | ~ l1_pre_topc(A_407)
      | ~ v2_pre_topc(A_407) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_7569,plain,(
    ! [B_409,A_410] :
      ( v4_pre_topc(u1_struct_0(B_409),A_410)
      | ~ v1_borsuk_1(B_409,A_410)
      | ~ v2_pre_topc(A_410)
      | ~ m1_pre_topc(B_409,A_410)
      | ~ l1_pre_topc(A_410) ) ),
    inference(resolution,[status(thm)],[c_58,c_6649])).

tff(c_418,plain,(
    ! [B_118] :
      ( m1_subset_1(u1_struct_0(B_118),k1_zfmisc_1('#skF_7'))
      | ~ m1_pre_topc(B_118,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_409])).

tff(c_2962,plain,(
    ! [B_118] :
      ( k2_pre_topc('#skF_6',u1_struct_0(B_118)) = u1_struct_0(B_118)
      | ~ v4_pre_topc(u1_struct_0(B_118),'#skF_6')
      | ~ m1_pre_topc(B_118,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_418,c_2946])).

tff(c_7573,plain,(
    ! [B_409] :
      ( k2_pre_topc('#skF_6',u1_struct_0(B_409)) = u1_struct_0(B_409)
      | ~ v1_borsuk_1(B_409,'#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | ~ m1_pre_topc(B_409,'#skF_6')
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_7569,c_2962])).

tff(c_8117,plain,(
    ! [B_412] :
      ( k2_pre_topc('#skF_6',u1_struct_0(B_412)) = u1_struct_0(B_412)
      | ~ v1_borsuk_1(B_412,'#skF_6')
      | ~ m1_pre_topc(B_412,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_110,c_7573])).

tff(c_8150,plain,
    ( u1_struct_0('#skF_4'('#skF_6','#skF_7')) = k2_pre_topc('#skF_6','#skF_7')
    | ~ v1_borsuk_1('#skF_4'('#skF_6','#skF_7'),'#skF_6')
    | ~ m1_pre_topc('#skF_4'('#skF_6','#skF_7'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3798,c_8117])).

tff(c_8166,plain,
    ( k2_pre_topc('#skF_6','#skF_7') = '#skF_7'
    | ~ v1_borsuk_1('#skF_4'('#skF_6','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5431,c_3798,c_8150])).

tff(c_8167,plain,(
    ~ v1_borsuk_1('#skF_4'('#skF_6','#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_3118,c_8166])).

tff(c_8172,plain,
    ( ~ m1_pre_topc('#skF_4'('#skF_6','#skF_7'),'#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v1_tdlat_3('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_8167])).

tff(c_8175,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_108,c_106,c_5431,c_8172])).

tff(c_8177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_8175])).

tff(c_8179,plain,(
    k2_pre_topc('#skF_6','#skF_7') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_3116])).

tff(c_9539,plain,(
    ! [B_459,A_460] :
      ( v4_pre_topc(B_459,A_460)
      | k2_pre_topc(A_460,B_459) != B_459
      | ~ v2_pre_topc(A_460)
      | ~ m1_subset_1(B_459,k1_zfmisc_1(u1_struct_0(A_460)))
      | ~ l1_pre_topc(A_460) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_9563,plain,(
    ! [B_459] :
      ( v4_pre_topc(B_459,'#skF_6')
      | k2_pre_topc('#skF_6',B_459) != B_459
      | ~ v2_pre_topc('#skF_6')
      | ~ m1_subset_1(B_459,k1_zfmisc_1('#skF_7'))
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_9539])).

tff(c_9967,plain,(
    ! [B_471] :
      ( v4_pre_topc(B_471,'#skF_6')
      | k2_pre_topc('#skF_6',B_471) != B_471
      | ~ m1_subset_1(B_471,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_110,c_9563])).

tff(c_9980,plain,
    ( v4_pre_topc('#skF_7','#skF_6')
    | k2_pre_topc('#skF_6','#skF_7') != '#skF_7' ),
    inference(resolution,[status(thm)],[c_124,c_9967])).

tff(c_9992,plain,(
    v4_pre_topc('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8179,c_9980])).

tff(c_9994,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2965,c_9992])).

tff(c_9995,plain,(
    k2_pre_topc('#skF_6','#skF_7') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_2963])).

tff(c_10099,plain,(
    ! [B_483,A_484] :
      ( v1_tops_1(B_483,A_484)
      | k2_pre_topc(A_484,B_483) != u1_struct_0(A_484)
      | ~ m1_subset_1(B_483,k1_zfmisc_1(u1_struct_0(A_484)))
      | ~ l1_pre_topc(A_484) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_10114,plain,(
    ! [B_483] :
      ( v1_tops_1(B_483,'#skF_6')
      | k2_pre_topc('#skF_6',B_483) != u1_struct_0('#skF_6')
      | ~ m1_subset_1(B_483,k1_zfmisc_1('#skF_7'))
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_10099])).

tff(c_10139,plain,(
    ! [B_486] :
      ( v1_tops_1(B_486,'#skF_6')
      | k2_pre_topc('#skF_6',B_486) != '#skF_7'
      | ~ m1_subset_1(B_486,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_257,c_10114])).

tff(c_10149,plain,
    ( v1_tops_1('#skF_7','#skF_6')
    | k2_pre_topc('#skF_6','#skF_7') != '#skF_7' ),
    inference(resolution,[status(thm)],[c_124,c_10139])).

tff(c_10159,plain,(
    v1_tops_1('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9995,c_10149])).

tff(c_11615,plain,(
    ! [B_542,A_543] :
      ( v2_tex_2(B_542,A_543)
      | ~ m1_subset_1(B_542,k1_zfmisc_1(u1_struct_0(A_543)))
      | ~ l1_pre_topc(A_543)
      | ~ v1_tdlat_3(A_543)
      | ~ v2_pre_topc(A_543)
      | v2_struct_0(A_543) ) ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_11639,plain,(
    ! [B_542] :
      ( v2_tex_2(B_542,'#skF_6')
      | ~ m1_subset_1(B_542,k1_zfmisc_1('#skF_7'))
      | ~ l1_pre_topc('#skF_6')
      | ~ v1_tdlat_3('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_11615])).

tff(c_11662,plain,(
    ! [B_542] :
      ( v2_tex_2(B_542,'#skF_6')
      | ~ m1_subset_1(B_542,k1_zfmisc_1('#skF_7'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_108,c_106,c_11639])).

tff(c_11666,plain,(
    ! [B_544] :
      ( v2_tex_2(B_544,'#skF_6')
      | ~ m1_subset_1(B_544,k1_zfmisc_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_11662])).

tff(c_11683,plain,(
    v2_tex_2('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_124,c_11666])).

tff(c_12128,plain,(
    ! [B_556,A_557] :
      ( v3_tex_2(B_556,A_557)
      | ~ v2_tex_2(B_556,A_557)
      | ~ v1_tops_1(B_556,A_557)
      | ~ m1_subset_1(B_556,k1_zfmisc_1(u1_struct_0(A_557)))
      | ~ l1_pre_topc(A_557)
      | ~ v2_pre_topc(A_557)
      | v2_struct_0(A_557) ) ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_12155,plain,(
    ! [B_556] :
      ( v3_tex_2(B_556,'#skF_6')
      | ~ v2_tex_2(B_556,'#skF_6')
      | ~ v1_tops_1(B_556,'#skF_6')
      | ~ m1_subset_1(B_556,k1_zfmisc_1('#skF_7'))
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_12128])).

tff(c_12179,plain,(
    ! [B_556] :
      ( v3_tex_2(B_556,'#skF_6')
      | ~ v2_tex_2(B_556,'#skF_6')
      | ~ v1_tops_1(B_556,'#skF_6')
      | ~ m1_subset_1(B_556,k1_zfmisc_1('#skF_7'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_106,c_12155])).

tff(c_12257,plain,(
    ! [B_559] :
      ( v3_tex_2(B_559,'#skF_6')
      | ~ v2_tex_2(B_559,'#skF_6')
      | ~ v1_tops_1(B_559,'#skF_6')
      | ~ m1_subset_1(B_559,k1_zfmisc_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_12179])).

tff(c_12273,plain,
    ( v3_tex_2('#skF_7','#skF_6')
    | ~ v2_tex_2('#skF_7','#skF_6')
    | ~ v1_tops_1('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_124,c_12257])).

tff(c_12287,plain,(
    v3_tex_2('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10159,c_11683,c_12273])).

tff(c_12289,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_12287])).

tff(c_12291,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_437])).

tff(c_12462,plain,(
    ! [A_573] :
      ( m1_subset_1('#skF_3'(A_573),k1_zfmisc_1(u1_struct_0(A_573)))
      | ~ l1_pre_topc(A_573)
      | ~ v2_pre_topc(A_573)
      | v2_struct_0(A_573) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_12476,plain,
    ( m1_subset_1('#skF_3'('#skF_6'),k1_zfmisc_1('#skF_7'))
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_12462])).

tff(c_12485,plain,
    ( m1_subset_1('#skF_3'('#skF_6'),k1_zfmisc_1('#skF_7'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_106,c_12476])).

tff(c_12486,plain,(
    m1_subset_1('#skF_3'('#skF_6'),k1_zfmisc_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_12485])).

tff(c_12497,plain,
    ( ~ v1_subset_1('#skF_3'('#skF_6'),'#skF_7')
    | ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_12486,c_34])).

tff(c_12504,plain,(
    ~ v1_subset_1('#skF_3'('#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12291,c_12497])).

tff(c_76,plain,(
    ! [B_52,A_51] :
      ( v1_subset_1(B_52,A_51)
      | B_52 = A_51
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_12501,plain,
    ( v1_subset_1('#skF_3'('#skF_6'),'#skF_7')
    | '#skF_3'('#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_12486,c_76])).

tff(c_12505,plain,(
    '#skF_3'('#skF_6') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_12504,c_12501])).

tff(c_44,plain,(
    ! [A_28] :
      ( ~ v1_xboole_0('#skF_3'(A_28))
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_12518,plain,
    ( ~ v1_xboole_0('#skF_7')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_12505,c_44])).

tff(c_12528,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_106,c_12291,c_12518])).

tff(c_12530,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_12528])).

tff(c_12531,plain,(
    v1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_12533,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_12531])).

tff(c_12534,plain,(
    v3_tex_2('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_12922,plain,(
    ! [A_633,B_634] :
      ( v1_pre_topc('#skF_4'(A_633,B_634))
      | ~ m1_subset_1(B_634,k1_zfmisc_1(u1_struct_0(A_633)))
      | v1_xboole_0(B_634)
      | ~ l1_pre_topc(A_633)
      | v2_struct_0(A_633) ) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_12945,plain,
    ( v1_pre_topc('#skF_4'('#skF_6','#skF_7'))
    | v1_xboole_0('#skF_7')
    | ~ l1_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_104,c_12922])).

tff(c_12954,plain,
    ( v1_pre_topc('#skF_4'('#skF_6','#skF_7'))
    | v1_xboole_0('#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_12945])).

tff(c_12955,plain,
    ( v1_pre_topc('#skF_4'('#skF_6','#skF_7'))
    | v1_xboole_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_12954])).

tff(c_12956,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_12955])).

tff(c_12550,plain,(
    ! [B_578,A_579] :
      ( v1_subset_1(B_578,A_579)
      | B_578 = A_579
      | ~ m1_subset_1(B_578,k1_zfmisc_1(A_579)) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_12564,plain,(
    ! [A_12] :
      ( v1_subset_1(k1_xboole_0,A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(resolution,[status(thm)],[c_127,c_12550])).

tff(c_12574,plain,(
    ! [B_581,A_582] :
      ( ~ v1_subset_1(B_581,A_582)
      | ~ m1_subset_1(B_581,k1_zfmisc_1(A_582))
      | ~ v1_xboole_0(A_582) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12589,plain,(
    ! [A_583] :
      ( ~ v1_subset_1(k1_xboole_0,A_583)
      | ~ v1_xboole_0(A_583) ) ),
    inference(resolution,[status(thm)],[c_127,c_12574])).

tff(c_12593,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(resolution,[status(thm)],[c_12564,c_12589])).

tff(c_12960,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_12956,c_12593])).

tff(c_12972,plain,(
    ! [A_12] : m1_subset_1('#skF_7',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12960,c_127])).

tff(c_13289,plain,(
    ! [B_668,A_669] :
      ( ~ v3_tex_2(B_668,A_669)
      | ~ m1_subset_1(B_668,k1_zfmisc_1(u1_struct_0(A_669)))
      | ~ v1_xboole_0(B_668)
      | ~ l1_pre_topc(A_669)
      | ~ v2_pre_topc(A_669)
      | v2_struct_0(A_669) ) ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_13293,plain,(
    ! [A_669] :
      ( ~ v3_tex_2('#skF_7',A_669)
      | ~ v1_xboole_0('#skF_7')
      | ~ l1_pre_topc(A_669)
      | ~ v2_pre_topc(A_669)
      | v2_struct_0(A_669) ) ),
    inference(resolution,[status(thm)],[c_12972,c_13289])).

tff(c_13317,plain,(
    ! [A_670] :
      ( ~ v3_tex_2('#skF_7',A_670)
      | ~ l1_pre_topc(A_670)
      | ~ v2_pre_topc(A_670)
      | v2_struct_0(A_670) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12956,c_13293])).

tff(c_13320,plain,
    ( ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_12534,c_13317])).

tff(c_13323,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_106,c_13320])).

tff(c_13325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_13323])).

tff(c_13327,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_12955])).

tff(c_16286,plain,(
    ! [A_800,B_801] :
      ( m1_pre_topc('#skF_4'(A_800,B_801),A_800)
      | ~ m1_subset_1(B_801,k1_zfmisc_1(u1_struct_0(A_800)))
      | v1_xboole_0(B_801)
      | ~ l1_pre_topc(A_800)
      | v2_struct_0(A_800) ) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_16308,plain,
    ( m1_pre_topc('#skF_4'('#skF_6','#skF_7'),'#skF_6')
    | v1_xboole_0('#skF_7')
    | ~ l1_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_104,c_16286])).

tff(c_16323,plain,
    ( m1_pre_topc('#skF_4'('#skF_6','#skF_7'),'#skF_6')
    | v1_xboole_0('#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_16308])).

tff(c_16324,plain,(
    m1_pre_topc('#skF_4'('#skF_6','#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_13327,c_16323])).

tff(c_15561,plain,(
    ! [A_774,B_775] :
      ( u1_struct_0('#skF_4'(A_774,B_775)) = B_775
      | ~ m1_subset_1(B_775,k1_zfmisc_1(u1_struct_0(A_774)))
      | v1_xboole_0(B_775)
      | ~ l1_pre_topc(A_774)
      | v2_struct_0(A_774) ) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_15584,plain,
    ( u1_struct_0('#skF_4'('#skF_6','#skF_7')) = '#skF_7'
    | v1_xboole_0('#skF_7')
    | ~ l1_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_104,c_15561])).

tff(c_15593,plain,
    ( u1_struct_0('#skF_4'('#skF_6','#skF_7')) = '#skF_7'
    | v1_xboole_0('#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_15584])).

tff(c_15594,plain,(
    u1_struct_0('#skF_4'('#skF_6','#skF_7')) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_13327,c_15593])).

tff(c_17011,plain,(
    ! [B_831,A_832] :
      ( v4_pre_topc(u1_struct_0(B_831),A_832)
      | ~ v1_borsuk_1(B_831,A_832)
      | ~ m1_subset_1(u1_struct_0(B_831),k1_zfmisc_1(u1_struct_0(A_832)))
      | ~ m1_pre_topc(B_831,A_832)
      | ~ l1_pre_topc(A_832)
      | ~ v2_pre_topc(A_832) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_17056,plain,(
    ! [B_834,A_835] :
      ( v4_pre_topc(u1_struct_0(B_834),A_835)
      | ~ v1_borsuk_1(B_834,A_835)
      | ~ v2_pre_topc(A_835)
      | ~ m1_pre_topc(B_834,A_835)
      | ~ l1_pre_topc(A_835) ) ),
    inference(resolution,[status(thm)],[c_58,c_17011])).

tff(c_19546,plain,(
    ! [A_936] :
      ( v4_pre_topc('#skF_7',A_936)
      | ~ v1_borsuk_1('#skF_4'('#skF_6','#skF_7'),A_936)
      | ~ v2_pre_topc(A_936)
      | ~ m1_pre_topc('#skF_4'('#skF_6','#skF_7'),A_936)
      | ~ l1_pre_topc(A_936) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15594,c_17056])).

tff(c_20672,plain,(
    ! [A_977] :
      ( v4_pre_topc('#skF_7',A_977)
      | ~ m1_pre_topc('#skF_4'('#skF_6','#skF_7'),A_977)
      | ~ l1_pre_topc(A_977)
      | ~ v1_tdlat_3(A_977)
      | ~ v2_pre_topc(A_977)
      | v2_struct_0(A_977) ) ),
    inference(resolution,[status(thm)],[c_66,c_19546])).

tff(c_20678,plain,
    ( v4_pre_topc('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v1_tdlat_3('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_16324,c_20672])).

tff(c_20685,plain,
    ( v4_pre_topc('#skF_7','#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_108,c_106,c_20678])).

tff(c_20687,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_12884,c_20685])).

tff(c_20688,plain,(
    k2_pre_topc('#skF_6','#skF_7') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_12883])).

tff(c_21107,plain,(
    ! [B_1016,A_1017] :
      ( v1_tops_1(B_1016,A_1017)
      | k2_pre_topc(A_1017,B_1016) != u1_struct_0(A_1017)
      | ~ m1_subset_1(B_1016,k1_zfmisc_1(u1_struct_0(A_1017)))
      | ~ l1_pre_topc(A_1017) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_21130,plain,
    ( v1_tops_1('#skF_7','#skF_6')
    | k2_pre_topc('#skF_6','#skF_7') != u1_struct_0('#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_104,c_21107])).

tff(c_21138,plain,
    ( v1_tops_1('#skF_7','#skF_6')
    | u1_struct_0('#skF_6') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_20688,c_21130])).

tff(c_21139,plain,(
    u1_struct_0('#skF_6') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_21138])).

tff(c_21143,plain,(
    ! [A_1022,B_1023] :
      ( k2_pre_topc(A_1022,B_1023) = u1_struct_0(A_1022)
      | ~ v1_tops_1(B_1023,A_1022)
      | ~ m1_subset_1(B_1023,k1_zfmisc_1(u1_struct_0(A_1022)))
      | ~ l1_pre_topc(A_1022) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_21166,plain,
    ( k2_pre_topc('#skF_6','#skF_7') = u1_struct_0('#skF_6')
    | ~ v1_tops_1('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_104,c_21143])).

tff(c_21174,plain,
    ( u1_struct_0('#skF_6') = '#skF_7'
    | ~ v1_tops_1('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_20688,c_21166])).

tff(c_21175,plain,(
    ~ v1_tops_1('#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_21139,c_21174])).

tff(c_20690,plain,(
    ! [B_978,A_979] :
      ( v3_pre_topc(B_978,A_979)
      | ~ m1_subset_1(B_978,k1_zfmisc_1(u1_struct_0(A_979)))
      | ~ v1_tdlat_3(A_979)
      | ~ l1_pre_topc(A_979)
      | ~ v2_pre_topc(A_979) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_20713,plain,
    ( v3_pre_topc('#skF_7','#skF_6')
    | ~ v1_tdlat_3('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_104,c_20690])).

tff(c_20721,plain,(
    v3_pre_topc('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_106,c_108,c_20713])).

tff(c_22077,plain,(
    ! [B_1064,A_1065] :
      ( v1_tops_1(B_1064,A_1065)
      | ~ v3_tex_2(B_1064,A_1065)
      | ~ v3_pre_topc(B_1064,A_1065)
      | ~ m1_subset_1(B_1064,k1_zfmisc_1(u1_struct_0(A_1065)))
      | ~ l1_pre_topc(A_1065)
      | ~ v2_pre_topc(A_1065)
      | v2_struct_0(A_1065) ) ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_22109,plain,
    ( v1_tops_1('#skF_7','#skF_6')
    | ~ v3_tex_2('#skF_7','#skF_6')
    | ~ v3_pre_topc('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_104,c_22077])).

tff(c_22121,plain,
    ( v1_tops_1('#skF_7','#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_106,c_20721,c_12534,c_22109])).

tff(c_22123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_21175,c_22121])).

tff(c_22125,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_21138])).

tff(c_12535,plain,(
    v1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_12583,plain,
    ( ~ v1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_104,c_12574])).

tff(c_12588,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12535,c_12583])).

tff(c_12801,plain,(
    ! [A_612,B_613] :
      ( ~ v1_xboole_0(k3_subset_1(A_612,B_613))
      | ~ m1_subset_1(B_613,k1_zfmisc_1(A_612))
      | ~ v1_subset_1(B_613,A_612)
      | v1_xboole_0(A_612) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_12822,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_6'),'#skF_7'))
    | ~ v1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_104,c_12801])).

tff(c_12833,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_6'),'#skF_7'))
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12535,c_12822])).

tff(c_12834,plain,(
    ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_6'),'#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_12588,c_12833])).

tff(c_22126,plain,(
    ~ v1_xboole_0(k3_subset_1('#skF_7','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22125,c_12834])).

tff(c_22133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12548,c_12659,c_22126])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:55:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.93/4.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.93/4.57  
% 11.93/4.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.93/4.58  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tsep_1 > v1_tops_1 > v1_subset_1 > v1_borsuk_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k9_setfam_1 > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_7 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_4
% 11.93/4.58  
% 11.93/4.58  %Foreground sorts:
% 11.93/4.58  
% 11.93/4.58  
% 11.93/4.58  %Background operators:
% 11.93/4.58  
% 11.93/4.58  
% 11.93/4.58  %Foreground operators:
% 11.93/4.58  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 11.93/4.58  tff('#skF_5', type, '#skF_5': $i > $i).
% 11.93/4.58  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 11.93/4.58  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 11.93/4.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.93/4.58  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 11.93/4.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.93/4.58  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 11.93/4.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.93/4.58  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.93/4.58  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 11.93/4.58  tff('#skF_7', type, '#skF_7': $i).
% 11.93/4.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.93/4.58  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 11.93/4.58  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 11.93/4.58  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 11.93/4.58  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 11.93/4.58  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 11.93/4.58  tff('#skF_6', type, '#skF_6': $i).
% 11.93/4.58  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.93/4.58  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 11.93/4.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.93/4.58  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 11.93/4.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.93/4.58  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 11.93/4.58  tff('#skF_3', type, '#skF_3': $i > $i).
% 11.93/4.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.93/4.58  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.93/4.58  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 11.93/4.58  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 11.93/4.58  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.93/4.58  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.93/4.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.93/4.58  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 11.93/4.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.93/4.58  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 11.93/4.58  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 11.93/4.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.93/4.58  tff(v1_borsuk_1, type, v1_borsuk_1: ($i * $i) > $o).
% 11.93/4.58  
% 12.09/4.61  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 12.09/4.61  tff(f_29, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 12.09/4.61  tff(f_37, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 12.09/4.61  tff(f_46, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 12.09/4.61  tff(f_48, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 12.09/4.61  tff(f_58, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 12.09/4.61  tff(f_50, axiom, (![A]: m1_subset_1(k1_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 12.09/4.61  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 12.09/4.61  tff(f_315, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tex_2)).
% 12.09/4.61  tff(f_123, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 12.09/4.61  tff(f_52, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 12.09/4.61  tff(f_194, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 12.09/4.61  tff(f_148, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 12.09/4.61  tff(f_78, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~v1_subset_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_subset_1)).
% 12.09/4.61  tff(f_225, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (?[C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) & (B = u1_struct_0(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_tsep_1)).
% 12.09/4.61  tff(f_172, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((v1_borsuk_1(B, A) & v1_tsep_1(B, A)) & v1_tdlat_3(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_tdlat_3)).
% 12.09/4.61  tff(f_187, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 12.09/4.61  tff(f_141, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_borsuk_1(B, A) & m1_pre_topc(B, A)) <=> v4_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tsep_1)).
% 12.09/4.61  tff(f_250, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 12.09/4.61  tff(f_297, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tex_2)).
% 12.09/4.61  tff(f_108, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc7_pre_topc)).
% 12.09/4.61  tff(f_265, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 12.09/4.61  tff(f_236, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_tdlat_3)).
% 12.09/4.61  tff(f_281, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_tex_2)).
% 12.09/4.61  tff(f_204, axiom, (![A, B]: (((~v1_xboole_0(A) & v1_subset_1(B, A)) & m1_subset_1(B, k1_zfmisc_1(A))) => ~v1_xboole_0(k3_subset_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tex_2)).
% 12.09/4.61  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.09/4.61  tff(c_4, plain, (![A_2]: (r1_xboole_0(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.09/4.61  tff(c_12538, plain, (![B_574, A_575]: (~r1_xboole_0(B_574, A_575) | ~r1_tarski(B_574, A_575) | v1_xboole_0(B_574))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.09/4.61  tff(c_12543, plain, (![A_576]: (~r1_tarski(A_576, k1_xboole_0) | v1_xboole_0(A_576))), inference(resolution, [status(thm)], [c_4, c_12538])).
% 12.09/4.61  tff(c_12548, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_12543])).
% 12.09/4.61  tff(c_20, plain, (![A_10]: (k1_subset_1(A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.09/4.61  tff(c_22, plain, (![A_11]: (k2_subset_1(A_11)=A_11)), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.09/4.61  tff(c_30, plain, (![A_16]: (k3_subset_1(A_16, k1_subset_1(A_16))=k2_subset_1(A_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 12.09/4.61  tff(c_123, plain, (![A_16]: (k3_subset_1(A_16, k1_subset_1(A_16))=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_30])).
% 12.09/4.61  tff(c_128, plain, (![A_16]: (k3_subset_1(A_16, k1_xboole_0)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_123])).
% 12.09/4.61  tff(c_24, plain, (![A_12]: (m1_subset_1(k1_subset_1(A_12), k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.09/4.61  tff(c_127, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_24])).
% 12.09/4.61  tff(c_12648, plain, (![A_591, B_592]: (k3_subset_1(A_591, k3_subset_1(A_591, B_592))=B_592 | ~m1_subset_1(B_592, k1_zfmisc_1(A_591)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.09/4.61  tff(c_12654, plain, (![A_12]: (k3_subset_1(A_12, k3_subset_1(A_12, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_127, c_12648])).
% 12.09/4.61  tff(c_12659, plain, (![A_12]: (k3_subset_1(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_128, c_12654])).
% 12.09/4.61  tff(c_112, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_315])).
% 12.09/4.61  tff(c_106, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_315])).
% 12.09/4.61  tff(c_104, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_315])).
% 12.09/4.61  tff(c_12852, plain, (![A_624, B_625]: (k2_pre_topc(A_624, B_625)=B_625 | ~v4_pre_topc(B_625, A_624) | ~m1_subset_1(B_625, k1_zfmisc_1(u1_struct_0(A_624))) | ~l1_pre_topc(A_624))), inference(cnfTransformation, [status(thm)], [f_123])).
% 12.09/4.61  tff(c_12875, plain, (k2_pre_topc('#skF_6', '#skF_7')='#skF_7' | ~v4_pre_topc('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_104, c_12852])).
% 12.09/4.61  tff(c_12883, plain, (k2_pre_topc('#skF_6', '#skF_7')='#skF_7' | ~v4_pre_topc('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_12875])).
% 12.09/4.61  tff(c_12884, plain, (~v4_pre_topc('#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_12883])).
% 12.09/4.61  tff(c_110, plain, (v2_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_315])).
% 12.09/4.61  tff(c_108, plain, (v1_tdlat_3('#skF_6')), inference(cnfTransformation, [status(thm)], [f_315])).
% 12.09/4.61  tff(c_120, plain, (v3_tex_2('#skF_7', '#skF_6') | ~v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_315])).
% 12.09/4.61  tff(c_176, plain, (~v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_120])).
% 12.09/4.61  tff(c_114, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~v3_tex_2('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_315])).
% 12.09/4.61  tff(c_177, plain, (~v3_tex_2('#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_114])).
% 12.09/4.61  tff(c_26, plain, (![A_13]: (m1_subset_1(k2_subset_1(A_13), k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.09/4.61  tff(c_124, plain, (![A_13]: (m1_subset_1(A_13, k1_zfmisc_1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_26])).
% 12.09/4.61  tff(c_237, plain, (![B_103, A_104]: (v1_subset_1(B_103, A_104) | B_103=A_104 | ~m1_subset_1(B_103, k1_zfmisc_1(A_104)))), inference(cnfTransformation, [status(thm)], [f_194])).
% 12.09/4.61  tff(c_249, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6')) | u1_struct_0('#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_104, c_237])).
% 12.09/4.61  tff(c_257, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_176, c_249])).
% 12.09/4.61  tff(c_2910, plain, (![A_288, B_289]: (k2_pre_topc(A_288, B_289)=B_289 | ~v4_pre_topc(B_289, A_288) | ~m1_subset_1(B_289, k1_zfmisc_1(u1_struct_0(A_288))) | ~l1_pre_topc(A_288))), inference(cnfTransformation, [status(thm)], [f_123])).
% 12.09/4.61  tff(c_2925, plain, (![B_289]: (k2_pre_topc('#skF_6', B_289)=B_289 | ~v4_pre_topc(B_289, '#skF_6') | ~m1_subset_1(B_289, k1_zfmisc_1('#skF_7')) | ~l1_pre_topc('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_257, c_2910])).
% 12.09/4.61  tff(c_2946, plain, (![B_291]: (k2_pre_topc('#skF_6', B_291)=B_291 | ~v4_pre_topc(B_291, '#skF_6') | ~m1_subset_1(B_291, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_2925])).
% 12.09/4.61  tff(c_2963, plain, (k2_pre_topc('#skF_6', '#skF_7')='#skF_7' | ~v4_pre_topc('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_124, c_2946])).
% 12.09/4.61  tff(c_2965, plain, (~v4_pre_topc('#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_2963])).
% 12.09/4.61  tff(c_392, plain, (![B_118, A_119]: (m1_subset_1(u1_struct_0(B_118), k1_zfmisc_1(u1_struct_0(A_119))) | ~m1_pre_topc(B_118, A_119) | ~l1_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_148])).
% 12.09/4.61  tff(c_409, plain, (![B_118]: (m1_subset_1(u1_struct_0(B_118), k1_zfmisc_1('#skF_7')) | ~m1_pre_topc(B_118, '#skF_6') | ~l1_pre_topc('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_257, c_392])).
% 12.09/4.61  tff(c_419, plain, (![B_120]: (m1_subset_1(u1_struct_0(B_120), k1_zfmisc_1('#skF_7')) | ~m1_pre_topc(B_120, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_409])).
% 12.09/4.61  tff(c_34, plain, (![B_22, A_20]: (~v1_subset_1(B_22, A_20) | ~m1_subset_1(B_22, k1_zfmisc_1(A_20)) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_78])).
% 12.09/4.61  tff(c_437, plain, (![B_120]: (~v1_subset_1(u1_struct_0(B_120), '#skF_7') | ~v1_xboole_0('#skF_7') | ~m1_pre_topc(B_120, '#skF_6'))), inference(resolution, [status(thm)], [c_419, c_34])).
% 12.09/4.61  tff(c_439, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_437])).
% 12.09/4.61  tff(c_5357, plain, (![A_383, B_384]: (m1_pre_topc('#skF_4'(A_383, B_384), A_383) | ~m1_subset_1(B_384, k1_zfmisc_1(u1_struct_0(A_383))) | v1_xboole_0(B_384) | ~l1_pre_topc(A_383) | v2_struct_0(A_383))), inference(cnfTransformation, [status(thm)], [f_225])).
% 12.09/4.61  tff(c_5379, plain, (![B_384]: (m1_pre_topc('#skF_4'('#skF_6', B_384), '#skF_6') | ~m1_subset_1(B_384, k1_zfmisc_1('#skF_7')) | v1_xboole_0(B_384) | ~l1_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_257, c_5357])).
% 12.09/4.61  tff(c_5405, plain, (![B_384]: (m1_pre_topc('#skF_4'('#skF_6', B_384), '#skF_6') | ~m1_subset_1(B_384, k1_zfmisc_1('#skF_7')) | v1_xboole_0(B_384) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_5379])).
% 12.09/4.61  tff(c_5410, plain, (![B_385]: (m1_pre_topc('#skF_4'('#skF_6', B_385), '#skF_6') | ~m1_subset_1(B_385, k1_zfmisc_1('#skF_7')) | v1_xboole_0(B_385))), inference(negUnitSimplification, [status(thm)], [c_112, c_5405])).
% 12.09/4.61  tff(c_5420, plain, (m1_pre_topc('#skF_4'('#skF_6', '#skF_7'), '#skF_6') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_124, c_5410])).
% 12.09/4.61  tff(c_5431, plain, (m1_pre_topc('#skF_4'('#skF_6', '#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_439, c_5420])).
% 12.09/4.61  tff(c_66, plain, (![B_46, A_44]: (v1_borsuk_1(B_46, A_44) | ~m1_pre_topc(B_46, A_44) | ~l1_pre_topc(A_44) | ~v1_tdlat_3(A_44) | ~v2_pre_topc(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_172])).
% 12.09/4.61  tff(c_3062, plain, (![B_305, A_306]: (v1_tops_1(B_305, A_306) | k2_pre_topc(A_306, B_305)!=u1_struct_0(A_306) | ~m1_subset_1(B_305, k1_zfmisc_1(u1_struct_0(A_306))) | ~l1_pre_topc(A_306))), inference(cnfTransformation, [status(thm)], [f_187])).
% 12.09/4.61  tff(c_3077, plain, (![B_305]: (v1_tops_1(B_305, '#skF_6') | k2_pre_topc('#skF_6', B_305)!=u1_struct_0('#skF_6') | ~m1_subset_1(B_305, k1_zfmisc_1('#skF_7')) | ~l1_pre_topc('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_257, c_3062])).
% 12.09/4.61  tff(c_3098, plain, (![B_308]: (v1_tops_1(B_308, '#skF_6') | k2_pre_topc('#skF_6', B_308)!='#skF_7' | ~m1_subset_1(B_308, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_257, c_3077])).
% 12.09/4.61  tff(c_3116, plain, (v1_tops_1('#skF_7', '#skF_6') | k2_pre_topc('#skF_6', '#skF_7')!='#skF_7'), inference(resolution, [status(thm)], [c_124, c_3098])).
% 12.09/4.61  tff(c_3118, plain, (k2_pre_topc('#skF_6', '#skF_7')!='#skF_7'), inference(splitLeft, [status(thm)], [c_3116])).
% 12.09/4.61  tff(c_3738, plain, (![A_367, B_368]: (u1_struct_0('#skF_4'(A_367, B_368))=B_368 | ~m1_subset_1(B_368, k1_zfmisc_1(u1_struct_0(A_367))) | v1_xboole_0(B_368) | ~l1_pre_topc(A_367) | v2_struct_0(A_367))), inference(cnfTransformation, [status(thm)], [f_225])).
% 12.09/4.61  tff(c_3753, plain, (![B_368]: (u1_struct_0('#skF_4'('#skF_6', B_368))=B_368 | ~m1_subset_1(B_368, k1_zfmisc_1('#skF_7')) | v1_xboole_0(B_368) | ~l1_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_257, c_3738])).
% 12.09/4.61  tff(c_3772, plain, (![B_368]: (u1_struct_0('#skF_4'('#skF_6', B_368))=B_368 | ~m1_subset_1(B_368, k1_zfmisc_1('#skF_7')) | v1_xboole_0(B_368) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_3753])).
% 12.09/4.61  tff(c_3777, plain, (![B_369]: (u1_struct_0('#skF_4'('#skF_6', B_369))=B_369 | ~m1_subset_1(B_369, k1_zfmisc_1('#skF_7')) | v1_xboole_0(B_369))), inference(negUnitSimplification, [status(thm)], [c_112, c_3772])).
% 12.09/4.61  tff(c_3787, plain, (u1_struct_0('#skF_4'('#skF_6', '#skF_7'))='#skF_7' | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_124, c_3777])).
% 12.09/4.61  tff(c_3798, plain, (u1_struct_0('#skF_4'('#skF_6', '#skF_7'))='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_439, c_3787])).
% 12.09/4.61  tff(c_58, plain, (![B_42, A_40]: (m1_subset_1(u1_struct_0(B_42), k1_zfmisc_1(u1_struct_0(A_40))) | ~m1_pre_topc(B_42, A_40) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_148])).
% 12.09/4.61  tff(c_6649, plain, (![B_406, A_407]: (v4_pre_topc(u1_struct_0(B_406), A_407) | ~v1_borsuk_1(B_406, A_407) | ~m1_subset_1(u1_struct_0(B_406), k1_zfmisc_1(u1_struct_0(A_407))) | ~m1_pre_topc(B_406, A_407) | ~l1_pre_topc(A_407) | ~v2_pre_topc(A_407))), inference(cnfTransformation, [status(thm)], [f_141])).
% 12.09/4.61  tff(c_7569, plain, (![B_409, A_410]: (v4_pre_topc(u1_struct_0(B_409), A_410) | ~v1_borsuk_1(B_409, A_410) | ~v2_pre_topc(A_410) | ~m1_pre_topc(B_409, A_410) | ~l1_pre_topc(A_410))), inference(resolution, [status(thm)], [c_58, c_6649])).
% 12.09/4.61  tff(c_418, plain, (![B_118]: (m1_subset_1(u1_struct_0(B_118), k1_zfmisc_1('#skF_7')) | ~m1_pre_topc(B_118, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_409])).
% 12.09/4.61  tff(c_2962, plain, (![B_118]: (k2_pre_topc('#skF_6', u1_struct_0(B_118))=u1_struct_0(B_118) | ~v4_pre_topc(u1_struct_0(B_118), '#skF_6') | ~m1_pre_topc(B_118, '#skF_6'))), inference(resolution, [status(thm)], [c_418, c_2946])).
% 12.09/4.61  tff(c_7573, plain, (![B_409]: (k2_pre_topc('#skF_6', u1_struct_0(B_409))=u1_struct_0(B_409) | ~v1_borsuk_1(B_409, '#skF_6') | ~v2_pre_topc('#skF_6') | ~m1_pre_topc(B_409, '#skF_6') | ~l1_pre_topc('#skF_6'))), inference(resolution, [status(thm)], [c_7569, c_2962])).
% 12.09/4.61  tff(c_8117, plain, (![B_412]: (k2_pre_topc('#skF_6', u1_struct_0(B_412))=u1_struct_0(B_412) | ~v1_borsuk_1(B_412, '#skF_6') | ~m1_pre_topc(B_412, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_110, c_7573])).
% 12.09/4.61  tff(c_8150, plain, (u1_struct_0('#skF_4'('#skF_6', '#skF_7'))=k2_pre_topc('#skF_6', '#skF_7') | ~v1_borsuk_1('#skF_4'('#skF_6', '#skF_7'), '#skF_6') | ~m1_pre_topc('#skF_4'('#skF_6', '#skF_7'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3798, c_8117])).
% 12.09/4.61  tff(c_8166, plain, (k2_pre_topc('#skF_6', '#skF_7')='#skF_7' | ~v1_borsuk_1('#skF_4'('#skF_6', '#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5431, c_3798, c_8150])).
% 12.09/4.61  tff(c_8167, plain, (~v1_borsuk_1('#skF_4'('#skF_6', '#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_3118, c_8166])).
% 12.09/4.61  tff(c_8172, plain, (~m1_pre_topc('#skF_4'('#skF_6', '#skF_7'), '#skF_6') | ~l1_pre_topc('#skF_6') | ~v1_tdlat_3('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_66, c_8167])).
% 12.09/4.61  tff(c_8175, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_108, c_106, c_5431, c_8172])).
% 12.09/4.61  tff(c_8177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_8175])).
% 12.09/4.61  tff(c_8179, plain, (k2_pre_topc('#skF_6', '#skF_7')='#skF_7'), inference(splitRight, [status(thm)], [c_3116])).
% 12.09/4.61  tff(c_9539, plain, (![B_459, A_460]: (v4_pre_topc(B_459, A_460) | k2_pre_topc(A_460, B_459)!=B_459 | ~v2_pre_topc(A_460) | ~m1_subset_1(B_459, k1_zfmisc_1(u1_struct_0(A_460))) | ~l1_pre_topc(A_460))), inference(cnfTransformation, [status(thm)], [f_123])).
% 12.09/4.61  tff(c_9563, plain, (![B_459]: (v4_pre_topc(B_459, '#skF_6') | k2_pre_topc('#skF_6', B_459)!=B_459 | ~v2_pre_topc('#skF_6') | ~m1_subset_1(B_459, k1_zfmisc_1('#skF_7')) | ~l1_pre_topc('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_257, c_9539])).
% 12.09/4.61  tff(c_9967, plain, (![B_471]: (v4_pre_topc(B_471, '#skF_6') | k2_pre_topc('#skF_6', B_471)!=B_471 | ~m1_subset_1(B_471, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_110, c_9563])).
% 12.09/4.61  tff(c_9980, plain, (v4_pre_topc('#skF_7', '#skF_6') | k2_pre_topc('#skF_6', '#skF_7')!='#skF_7'), inference(resolution, [status(thm)], [c_124, c_9967])).
% 12.09/4.61  tff(c_9992, plain, (v4_pre_topc('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8179, c_9980])).
% 12.09/4.61  tff(c_9994, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2965, c_9992])).
% 12.09/4.61  tff(c_9995, plain, (k2_pre_topc('#skF_6', '#skF_7')='#skF_7'), inference(splitRight, [status(thm)], [c_2963])).
% 12.09/4.61  tff(c_10099, plain, (![B_483, A_484]: (v1_tops_1(B_483, A_484) | k2_pre_topc(A_484, B_483)!=u1_struct_0(A_484) | ~m1_subset_1(B_483, k1_zfmisc_1(u1_struct_0(A_484))) | ~l1_pre_topc(A_484))), inference(cnfTransformation, [status(thm)], [f_187])).
% 12.09/4.61  tff(c_10114, plain, (![B_483]: (v1_tops_1(B_483, '#skF_6') | k2_pre_topc('#skF_6', B_483)!=u1_struct_0('#skF_6') | ~m1_subset_1(B_483, k1_zfmisc_1('#skF_7')) | ~l1_pre_topc('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_257, c_10099])).
% 12.09/4.61  tff(c_10139, plain, (![B_486]: (v1_tops_1(B_486, '#skF_6') | k2_pre_topc('#skF_6', B_486)!='#skF_7' | ~m1_subset_1(B_486, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_257, c_10114])).
% 12.09/4.61  tff(c_10149, plain, (v1_tops_1('#skF_7', '#skF_6') | k2_pre_topc('#skF_6', '#skF_7')!='#skF_7'), inference(resolution, [status(thm)], [c_124, c_10139])).
% 12.09/4.61  tff(c_10159, plain, (v1_tops_1('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9995, c_10149])).
% 12.09/4.61  tff(c_11615, plain, (![B_542, A_543]: (v2_tex_2(B_542, A_543) | ~m1_subset_1(B_542, k1_zfmisc_1(u1_struct_0(A_543))) | ~l1_pre_topc(A_543) | ~v1_tdlat_3(A_543) | ~v2_pre_topc(A_543) | v2_struct_0(A_543))), inference(cnfTransformation, [status(thm)], [f_250])).
% 12.09/4.61  tff(c_11639, plain, (![B_542]: (v2_tex_2(B_542, '#skF_6') | ~m1_subset_1(B_542, k1_zfmisc_1('#skF_7')) | ~l1_pre_topc('#skF_6') | ~v1_tdlat_3('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_257, c_11615])).
% 12.09/4.61  tff(c_11662, plain, (![B_542]: (v2_tex_2(B_542, '#skF_6') | ~m1_subset_1(B_542, k1_zfmisc_1('#skF_7')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_108, c_106, c_11639])).
% 12.09/4.61  tff(c_11666, plain, (![B_544]: (v2_tex_2(B_544, '#skF_6') | ~m1_subset_1(B_544, k1_zfmisc_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_112, c_11662])).
% 12.09/4.61  tff(c_11683, plain, (v2_tex_2('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_124, c_11666])).
% 12.09/4.61  tff(c_12128, plain, (![B_556, A_557]: (v3_tex_2(B_556, A_557) | ~v2_tex_2(B_556, A_557) | ~v1_tops_1(B_556, A_557) | ~m1_subset_1(B_556, k1_zfmisc_1(u1_struct_0(A_557))) | ~l1_pre_topc(A_557) | ~v2_pre_topc(A_557) | v2_struct_0(A_557))), inference(cnfTransformation, [status(thm)], [f_297])).
% 12.09/4.61  tff(c_12155, plain, (![B_556]: (v3_tex_2(B_556, '#skF_6') | ~v2_tex_2(B_556, '#skF_6') | ~v1_tops_1(B_556, '#skF_6') | ~m1_subset_1(B_556, k1_zfmisc_1('#skF_7')) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_257, c_12128])).
% 12.09/4.61  tff(c_12179, plain, (![B_556]: (v3_tex_2(B_556, '#skF_6') | ~v2_tex_2(B_556, '#skF_6') | ~v1_tops_1(B_556, '#skF_6') | ~m1_subset_1(B_556, k1_zfmisc_1('#skF_7')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_106, c_12155])).
% 12.09/4.61  tff(c_12257, plain, (![B_559]: (v3_tex_2(B_559, '#skF_6') | ~v2_tex_2(B_559, '#skF_6') | ~v1_tops_1(B_559, '#skF_6') | ~m1_subset_1(B_559, k1_zfmisc_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_112, c_12179])).
% 12.09/4.61  tff(c_12273, plain, (v3_tex_2('#skF_7', '#skF_6') | ~v2_tex_2('#skF_7', '#skF_6') | ~v1_tops_1('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_124, c_12257])).
% 12.09/4.61  tff(c_12287, plain, (v3_tex_2('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10159, c_11683, c_12273])).
% 12.09/4.61  tff(c_12289, plain, $false, inference(negUnitSimplification, [status(thm)], [c_177, c_12287])).
% 12.09/4.61  tff(c_12291, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_437])).
% 12.09/4.61  tff(c_12462, plain, (![A_573]: (m1_subset_1('#skF_3'(A_573), k1_zfmisc_1(u1_struct_0(A_573))) | ~l1_pre_topc(A_573) | ~v2_pre_topc(A_573) | v2_struct_0(A_573))), inference(cnfTransformation, [status(thm)], [f_108])).
% 12.09/4.61  tff(c_12476, plain, (m1_subset_1('#skF_3'('#skF_6'), k1_zfmisc_1('#skF_7')) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_257, c_12462])).
% 12.09/4.61  tff(c_12485, plain, (m1_subset_1('#skF_3'('#skF_6'), k1_zfmisc_1('#skF_7')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_106, c_12476])).
% 12.09/4.61  tff(c_12486, plain, (m1_subset_1('#skF_3'('#skF_6'), k1_zfmisc_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_112, c_12485])).
% 12.09/4.61  tff(c_12497, plain, (~v1_subset_1('#skF_3'('#skF_6'), '#skF_7') | ~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_12486, c_34])).
% 12.09/4.61  tff(c_12504, plain, (~v1_subset_1('#skF_3'('#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_12291, c_12497])).
% 12.09/4.61  tff(c_76, plain, (![B_52, A_51]: (v1_subset_1(B_52, A_51) | B_52=A_51 | ~m1_subset_1(B_52, k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_194])).
% 12.09/4.61  tff(c_12501, plain, (v1_subset_1('#skF_3'('#skF_6'), '#skF_7') | '#skF_3'('#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_12486, c_76])).
% 12.09/4.61  tff(c_12505, plain, ('#skF_3'('#skF_6')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_12504, c_12501])).
% 12.09/4.61  tff(c_44, plain, (![A_28]: (~v1_xboole_0('#skF_3'(A_28)) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_108])).
% 12.09/4.61  tff(c_12518, plain, (~v1_xboole_0('#skF_7') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_12505, c_44])).
% 12.09/4.61  tff(c_12528, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_106, c_12291, c_12518])).
% 12.09/4.61  tff(c_12530, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_12528])).
% 12.09/4.61  tff(c_12531, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_114])).
% 12.09/4.61  tff(c_12533, plain, $false, inference(negUnitSimplification, [status(thm)], [c_176, c_12531])).
% 12.09/4.61  tff(c_12534, plain, (v3_tex_2('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_120])).
% 12.09/4.61  tff(c_12922, plain, (![A_633, B_634]: (v1_pre_topc('#skF_4'(A_633, B_634)) | ~m1_subset_1(B_634, k1_zfmisc_1(u1_struct_0(A_633))) | v1_xboole_0(B_634) | ~l1_pre_topc(A_633) | v2_struct_0(A_633))), inference(cnfTransformation, [status(thm)], [f_225])).
% 12.09/4.61  tff(c_12945, plain, (v1_pre_topc('#skF_4'('#skF_6', '#skF_7')) | v1_xboole_0('#skF_7') | ~l1_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_104, c_12922])).
% 12.09/4.61  tff(c_12954, plain, (v1_pre_topc('#skF_4'('#skF_6', '#skF_7')) | v1_xboole_0('#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_12945])).
% 12.09/4.61  tff(c_12955, plain, (v1_pre_topc('#skF_4'('#skF_6', '#skF_7')) | v1_xboole_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_112, c_12954])).
% 12.09/4.61  tff(c_12956, plain, (v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_12955])).
% 12.09/4.61  tff(c_12550, plain, (![B_578, A_579]: (v1_subset_1(B_578, A_579) | B_578=A_579 | ~m1_subset_1(B_578, k1_zfmisc_1(A_579)))), inference(cnfTransformation, [status(thm)], [f_194])).
% 12.09/4.61  tff(c_12564, plain, (![A_12]: (v1_subset_1(k1_xboole_0, A_12) | k1_xboole_0=A_12)), inference(resolution, [status(thm)], [c_127, c_12550])).
% 12.09/4.61  tff(c_12574, plain, (![B_581, A_582]: (~v1_subset_1(B_581, A_582) | ~m1_subset_1(B_581, k1_zfmisc_1(A_582)) | ~v1_xboole_0(A_582))), inference(cnfTransformation, [status(thm)], [f_78])).
% 12.09/4.61  tff(c_12589, plain, (![A_583]: (~v1_subset_1(k1_xboole_0, A_583) | ~v1_xboole_0(A_583))), inference(resolution, [status(thm)], [c_127, c_12574])).
% 12.09/4.61  tff(c_12593, plain, (![A_12]: (~v1_xboole_0(A_12) | k1_xboole_0=A_12)), inference(resolution, [status(thm)], [c_12564, c_12589])).
% 12.09/4.61  tff(c_12960, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_12956, c_12593])).
% 12.09/4.61  tff(c_12972, plain, (![A_12]: (m1_subset_1('#skF_7', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_12960, c_127])).
% 12.09/4.61  tff(c_13289, plain, (![B_668, A_669]: (~v3_tex_2(B_668, A_669) | ~m1_subset_1(B_668, k1_zfmisc_1(u1_struct_0(A_669))) | ~v1_xboole_0(B_668) | ~l1_pre_topc(A_669) | ~v2_pre_topc(A_669) | v2_struct_0(A_669))), inference(cnfTransformation, [status(thm)], [f_265])).
% 12.09/4.61  tff(c_13293, plain, (![A_669]: (~v3_tex_2('#skF_7', A_669) | ~v1_xboole_0('#skF_7') | ~l1_pre_topc(A_669) | ~v2_pre_topc(A_669) | v2_struct_0(A_669))), inference(resolution, [status(thm)], [c_12972, c_13289])).
% 12.09/4.61  tff(c_13317, plain, (![A_670]: (~v3_tex_2('#skF_7', A_670) | ~l1_pre_topc(A_670) | ~v2_pre_topc(A_670) | v2_struct_0(A_670))), inference(demodulation, [status(thm), theory('equality')], [c_12956, c_13293])).
% 12.09/4.61  tff(c_13320, plain, (~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_12534, c_13317])).
% 12.09/4.61  tff(c_13323, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_106, c_13320])).
% 12.09/4.61  tff(c_13325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_13323])).
% 12.09/4.61  tff(c_13327, plain, (~v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_12955])).
% 12.09/4.61  tff(c_16286, plain, (![A_800, B_801]: (m1_pre_topc('#skF_4'(A_800, B_801), A_800) | ~m1_subset_1(B_801, k1_zfmisc_1(u1_struct_0(A_800))) | v1_xboole_0(B_801) | ~l1_pre_topc(A_800) | v2_struct_0(A_800))), inference(cnfTransformation, [status(thm)], [f_225])).
% 12.09/4.61  tff(c_16308, plain, (m1_pre_topc('#skF_4'('#skF_6', '#skF_7'), '#skF_6') | v1_xboole_0('#skF_7') | ~l1_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_104, c_16286])).
% 12.09/4.61  tff(c_16323, plain, (m1_pre_topc('#skF_4'('#skF_6', '#skF_7'), '#skF_6') | v1_xboole_0('#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_16308])).
% 12.09/4.61  tff(c_16324, plain, (m1_pre_topc('#skF_4'('#skF_6', '#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_112, c_13327, c_16323])).
% 12.09/4.61  tff(c_15561, plain, (![A_774, B_775]: (u1_struct_0('#skF_4'(A_774, B_775))=B_775 | ~m1_subset_1(B_775, k1_zfmisc_1(u1_struct_0(A_774))) | v1_xboole_0(B_775) | ~l1_pre_topc(A_774) | v2_struct_0(A_774))), inference(cnfTransformation, [status(thm)], [f_225])).
% 12.09/4.61  tff(c_15584, plain, (u1_struct_0('#skF_4'('#skF_6', '#skF_7'))='#skF_7' | v1_xboole_0('#skF_7') | ~l1_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_104, c_15561])).
% 12.09/4.61  tff(c_15593, plain, (u1_struct_0('#skF_4'('#skF_6', '#skF_7'))='#skF_7' | v1_xboole_0('#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_15584])).
% 12.09/4.61  tff(c_15594, plain, (u1_struct_0('#skF_4'('#skF_6', '#skF_7'))='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_112, c_13327, c_15593])).
% 12.09/4.61  tff(c_17011, plain, (![B_831, A_832]: (v4_pre_topc(u1_struct_0(B_831), A_832) | ~v1_borsuk_1(B_831, A_832) | ~m1_subset_1(u1_struct_0(B_831), k1_zfmisc_1(u1_struct_0(A_832))) | ~m1_pre_topc(B_831, A_832) | ~l1_pre_topc(A_832) | ~v2_pre_topc(A_832))), inference(cnfTransformation, [status(thm)], [f_141])).
% 12.09/4.61  tff(c_17056, plain, (![B_834, A_835]: (v4_pre_topc(u1_struct_0(B_834), A_835) | ~v1_borsuk_1(B_834, A_835) | ~v2_pre_topc(A_835) | ~m1_pre_topc(B_834, A_835) | ~l1_pre_topc(A_835))), inference(resolution, [status(thm)], [c_58, c_17011])).
% 12.09/4.61  tff(c_19546, plain, (![A_936]: (v4_pre_topc('#skF_7', A_936) | ~v1_borsuk_1('#skF_4'('#skF_6', '#skF_7'), A_936) | ~v2_pre_topc(A_936) | ~m1_pre_topc('#skF_4'('#skF_6', '#skF_7'), A_936) | ~l1_pre_topc(A_936))), inference(superposition, [status(thm), theory('equality')], [c_15594, c_17056])).
% 12.09/4.61  tff(c_20672, plain, (![A_977]: (v4_pre_topc('#skF_7', A_977) | ~m1_pre_topc('#skF_4'('#skF_6', '#skF_7'), A_977) | ~l1_pre_topc(A_977) | ~v1_tdlat_3(A_977) | ~v2_pre_topc(A_977) | v2_struct_0(A_977))), inference(resolution, [status(thm)], [c_66, c_19546])).
% 12.09/4.61  tff(c_20678, plain, (v4_pre_topc('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_6') | ~v1_tdlat_3('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_16324, c_20672])).
% 12.09/4.61  tff(c_20685, plain, (v4_pre_topc('#skF_7', '#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_108, c_106, c_20678])).
% 12.09/4.61  tff(c_20687, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_12884, c_20685])).
% 12.09/4.61  tff(c_20688, plain, (k2_pre_topc('#skF_6', '#skF_7')='#skF_7'), inference(splitRight, [status(thm)], [c_12883])).
% 12.09/4.61  tff(c_21107, plain, (![B_1016, A_1017]: (v1_tops_1(B_1016, A_1017) | k2_pre_topc(A_1017, B_1016)!=u1_struct_0(A_1017) | ~m1_subset_1(B_1016, k1_zfmisc_1(u1_struct_0(A_1017))) | ~l1_pre_topc(A_1017))), inference(cnfTransformation, [status(thm)], [f_187])).
% 12.09/4.61  tff(c_21130, plain, (v1_tops_1('#skF_7', '#skF_6') | k2_pre_topc('#skF_6', '#skF_7')!=u1_struct_0('#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_104, c_21107])).
% 12.09/4.61  tff(c_21138, plain, (v1_tops_1('#skF_7', '#skF_6') | u1_struct_0('#skF_6')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_20688, c_21130])).
% 12.09/4.61  tff(c_21139, plain, (u1_struct_0('#skF_6')!='#skF_7'), inference(splitLeft, [status(thm)], [c_21138])).
% 12.09/4.61  tff(c_21143, plain, (![A_1022, B_1023]: (k2_pre_topc(A_1022, B_1023)=u1_struct_0(A_1022) | ~v1_tops_1(B_1023, A_1022) | ~m1_subset_1(B_1023, k1_zfmisc_1(u1_struct_0(A_1022))) | ~l1_pre_topc(A_1022))), inference(cnfTransformation, [status(thm)], [f_187])).
% 12.09/4.61  tff(c_21166, plain, (k2_pre_topc('#skF_6', '#skF_7')=u1_struct_0('#skF_6') | ~v1_tops_1('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_104, c_21143])).
% 12.09/4.61  tff(c_21174, plain, (u1_struct_0('#skF_6')='#skF_7' | ~v1_tops_1('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_20688, c_21166])).
% 12.09/4.61  tff(c_21175, plain, (~v1_tops_1('#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_21139, c_21174])).
% 12.09/4.61  tff(c_20690, plain, (![B_978, A_979]: (v3_pre_topc(B_978, A_979) | ~m1_subset_1(B_978, k1_zfmisc_1(u1_struct_0(A_979))) | ~v1_tdlat_3(A_979) | ~l1_pre_topc(A_979) | ~v2_pre_topc(A_979))), inference(cnfTransformation, [status(thm)], [f_236])).
% 12.09/4.61  tff(c_20713, plain, (v3_pre_topc('#skF_7', '#skF_6') | ~v1_tdlat_3('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_104, c_20690])).
% 12.09/4.61  tff(c_20721, plain, (v3_pre_topc('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_106, c_108, c_20713])).
% 12.09/4.61  tff(c_22077, plain, (![B_1064, A_1065]: (v1_tops_1(B_1064, A_1065) | ~v3_tex_2(B_1064, A_1065) | ~v3_pre_topc(B_1064, A_1065) | ~m1_subset_1(B_1064, k1_zfmisc_1(u1_struct_0(A_1065))) | ~l1_pre_topc(A_1065) | ~v2_pre_topc(A_1065) | v2_struct_0(A_1065))), inference(cnfTransformation, [status(thm)], [f_281])).
% 12.09/4.61  tff(c_22109, plain, (v1_tops_1('#skF_7', '#skF_6') | ~v3_tex_2('#skF_7', '#skF_6') | ~v3_pre_topc('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_104, c_22077])).
% 12.09/4.61  tff(c_22121, plain, (v1_tops_1('#skF_7', '#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_106, c_20721, c_12534, c_22109])).
% 12.09/4.61  tff(c_22123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_21175, c_22121])).
% 12.09/4.61  tff(c_22125, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_21138])).
% 12.09/4.61  tff(c_12535, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_120])).
% 12.09/4.61  tff(c_12583, plain, (~v1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~v1_xboole_0(u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_104, c_12574])).
% 12.09/4.61  tff(c_12588, plain, (~v1_xboole_0(u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_12535, c_12583])).
% 12.09/4.61  tff(c_12801, plain, (![A_612, B_613]: (~v1_xboole_0(k3_subset_1(A_612, B_613)) | ~m1_subset_1(B_613, k1_zfmisc_1(A_612)) | ~v1_subset_1(B_613, A_612) | v1_xboole_0(A_612))), inference(cnfTransformation, [status(thm)], [f_204])).
% 12.09/4.61  tff(c_12822, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_6'), '#skF_7')) | ~v1_subset_1('#skF_7', u1_struct_0('#skF_6')) | v1_xboole_0(u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_104, c_12801])).
% 12.09/4.61  tff(c_12833, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_6'), '#skF_7')) | v1_xboole_0(u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_12535, c_12822])).
% 12.09/4.61  tff(c_12834, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_6'), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_12588, c_12833])).
% 12.09/4.61  tff(c_22126, plain, (~v1_xboole_0(k3_subset_1('#skF_7', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_22125, c_12834])).
% 12.09/4.61  tff(c_22133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12548, c_12659, c_22126])).
% 12.09/4.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.09/4.61  
% 12.09/4.61  Inference rules
% 12.09/4.61  ----------------------
% 12.09/4.61  #Ref     : 0
% 12.09/4.61  #Sup     : 4800
% 12.09/4.61  #Fact    : 0
% 12.09/4.61  #Define  : 0
% 12.09/4.61  #Split   : 57
% 12.09/4.61  #Chain   : 0
% 12.09/4.61  #Close   : 0
% 12.09/4.61  
% 12.09/4.61  Ordering : KBO
% 12.09/4.61  
% 12.09/4.61  Simplification rules
% 12.09/4.61  ----------------------
% 12.09/4.61  #Subsume      : 702
% 12.09/4.61  #Demod        : 4423
% 12.09/4.61  #Tautology    : 1119
% 12.09/4.61  #SimpNegUnit  : 1003
% 12.09/4.61  #BackRed      : 87
% 12.09/4.61  
% 12.09/4.61  #Partial instantiations: 0
% 12.09/4.61  #Strategies tried      : 1
% 12.09/4.61  
% 12.09/4.61  Timing (in seconds)
% 12.09/4.61  ----------------------
% 12.09/4.61  Preprocessing        : 0.40
% 12.09/4.61  Parsing              : 0.21
% 12.09/4.61  CNF conversion       : 0.03
% 12.09/4.61  Main loop            : 3.40
% 12.09/4.61  Inferencing          : 1.06
% 12.09/4.61  Reduction            : 1.26
% 12.09/4.61  Demodulation         : 0.88
% 12.09/4.61  BG Simplification    : 0.10
% 12.09/4.61  Subsumption          : 0.73
% 12.09/4.61  Abstraction          : 0.13
% 12.09/4.61  MUC search           : 0.00
% 12.09/4.61  Cooper               : 0.00
% 12.09/4.61  Total                : 3.87
% 12.09/4.61  Index Insertion      : 0.00
% 12.09/4.61  Index Deletion       : 0.00
% 12.09/4.61  Index Matching       : 0.00
% 12.09/4.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
