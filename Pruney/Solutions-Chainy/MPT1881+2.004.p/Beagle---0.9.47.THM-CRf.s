%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:06 EST 2020

% Result     : Theorem 11.69s
% Output     : CNFRefutation 11.94s
% Verified   : 
% Statistics : Number of formulae       :  287 (1342 expanded)
%              Number of leaves         :   58 ( 465 expanded)
%              Depth                    :   16
%              Number of atoms          :  712 (3955 expanded)
%              Number of equality atoms :   92 ( 397 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tsep_1 > v1_tops_1 > v1_subset_1 > v1_borsuk_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_291,negated_conjecture,(
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

tff(f_170,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_88,axiom,(
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

tff(f_130,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ~ v1_subset_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).

tff(f_201,axiom,(
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

tff(f_154,axiom,(
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

tff(f_163,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_123,axiom,(
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

tff(f_226,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_273,axiom,(
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

tff(f_105,axiom,(
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

tff(f_180,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_subset_1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(A)) )
     => ~ v1_xboole_0(k3_subset_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tex_2)).

tff(f_212,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).

tff(f_257,axiom,(
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

tff(f_241,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

tff(c_94,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_291])).

tff(c_92,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_291])).

tff(c_88,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_291])).

tff(c_96,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_291])).

tff(c_139,plain,(
    ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_8,plain,(
    ! [A_5] : k2_subset_1(A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_103,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_12])).

tff(c_102,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_291])).

tff(c_140,plain,(
    ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_102])).

tff(c_86,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_291])).

tff(c_179,plain,(
    ! [B_86,A_87] :
      ( v1_subset_1(B_86,A_87)
      | B_86 = A_87
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_191,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_86,c_179])).

tff(c_200,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_191])).

tff(c_4742,plain,(
    ! [A_311,B_312] :
      ( k2_pre_topc(A_311,B_312) = B_312
      | ~ v4_pre_topc(B_312,A_311)
      | ~ m1_subset_1(B_312,k1_zfmisc_1(u1_struct_0(A_311)))
      | ~ l1_pre_topc(A_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4757,plain,(
    ! [B_312] :
      ( k2_pre_topc('#skF_4',B_312) = B_312
      | ~ v4_pre_topc(B_312,'#skF_4')
      | ~ m1_subset_1(B_312,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_4742])).

tff(c_4780,plain,(
    ! [B_314] :
      ( k2_pre_topc('#skF_4',B_314) = B_314
      | ~ v4_pre_topc(B_314,'#skF_4')
      | ~ m1_subset_1(B_314,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_4757])).

tff(c_4802,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = '#skF_5'
    | ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_103,c_4780])).

tff(c_4804,plain,(
    ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4802])).

tff(c_90,plain,(
    v1_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_291])).

tff(c_390,plain,(
    ! [B_112,A_113] :
      ( m1_subset_1(u1_struct_0(B_112),k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ m1_pre_topc(B_112,A_113)
      | ~ l1_pre_topc(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_410,plain,(
    ! [B_112] :
      ( m1_subset_1(u1_struct_0(B_112),k1_zfmisc_1('#skF_5'))
      | ~ m1_pre_topc(B_112,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_390])).

tff(c_418,plain,(
    ! [B_114] :
      ( m1_subset_1(u1_struct_0(B_114),k1_zfmisc_1('#skF_5'))
      | ~ m1_pre_topc(B_114,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_410])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ m1_subset_1(A_17,k1_zfmisc_1(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_442,plain,(
    ! [B_115] :
      ( r1_tarski(u1_struct_0(B_115),'#skF_5')
      | ~ m1_pre_topc(B_115,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_418,c_22])).

tff(c_24,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_192,plain,(
    ! [A_17,B_18] :
      ( v1_subset_1(A_17,B_18)
      | B_18 = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(resolution,[status(thm)],[c_24,c_179])).

tff(c_217,plain,(
    ! [B_89,A_90] :
      ( ~ v1_subset_1(B_89,A_90)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_90))
      | ~ v1_xboole_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_257,plain,(
    ! [A_95,B_96] :
      ( ~ v1_subset_1(A_95,B_96)
      | ~ v1_xboole_0(B_96)
      | ~ r1_tarski(A_95,B_96) ) ),
    inference(resolution,[status(thm)],[c_24,c_217])).

tff(c_264,plain,(
    ! [B_18,A_17] :
      ( ~ v1_xboole_0(B_18)
      | B_18 = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(resolution,[status(thm)],[c_192,c_257])).

tff(c_449,plain,(
    ! [B_115] :
      ( ~ v1_xboole_0('#skF_5')
      | u1_struct_0(B_115) = '#skF_5'
      | ~ m1_pre_topc(B_115,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_442,c_264])).

tff(c_451,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_449])).

tff(c_5357,plain,(
    ! [A_353,B_354] :
      ( m1_pre_topc('#skF_2'(A_353,B_354),A_353)
      | ~ m1_subset_1(B_354,k1_zfmisc_1(u1_struct_0(A_353)))
      | v1_xboole_0(B_354)
      | ~ l1_pre_topc(A_353)
      | v2_struct_0(A_353) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_5367,plain,(
    ! [B_354] :
      ( m1_pre_topc('#skF_2'('#skF_4',B_354),'#skF_4')
      | ~ m1_subset_1(B_354,k1_zfmisc_1('#skF_5'))
      | v1_xboole_0(B_354)
      | ~ l1_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_5357])).

tff(c_5384,plain,(
    ! [B_354] :
      ( m1_pre_topc('#skF_2'('#skF_4',B_354),'#skF_4')
      | ~ m1_subset_1(B_354,k1_zfmisc_1('#skF_5'))
      | v1_xboole_0(B_354)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_5367])).

tff(c_5390,plain,(
    ! [B_355] :
      ( m1_pre_topc('#skF_2'('#skF_4',B_355),'#skF_4')
      | ~ m1_subset_1(B_355,k1_zfmisc_1('#skF_5'))
      | v1_xboole_0(B_355) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_5384])).

tff(c_5404,plain,
    ( m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_103,c_5390])).

tff(c_5416,plain,(
    m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_451,c_5404])).

tff(c_52,plain,(
    ! [B_37,A_35] :
      ( v1_borsuk_1(B_37,A_35)
      | ~ m1_pre_topc(B_37,A_35)
      | ~ l1_pre_topc(A_35)
      | ~ v1_tdlat_3(A_35)
      | ~ v2_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_5005,plain,(
    ! [A_328,B_329] :
      ( k2_pre_topc(A_328,B_329) = u1_struct_0(A_328)
      | ~ v1_tops_1(B_329,A_328)
      | ~ m1_subset_1(B_329,k1_zfmisc_1(u1_struct_0(A_328)))
      | ~ l1_pre_topc(A_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_5020,plain,(
    ! [B_329] :
      ( k2_pre_topc('#skF_4',B_329) = u1_struct_0('#skF_4')
      | ~ v1_tops_1(B_329,'#skF_4')
      | ~ m1_subset_1(B_329,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_5005])).

tff(c_5043,plain,(
    ! [B_331] :
      ( k2_pre_topc('#skF_4',B_331) = '#skF_5'
      | ~ v1_tops_1(B_331,'#skF_4')
      | ~ m1_subset_1(B_331,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_200,c_5020])).

tff(c_5067,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = '#skF_5'
    | ~ v1_tops_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_103,c_5043])).

tff(c_5070,plain,(
    ~ v1_tops_1('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5067])).

tff(c_5073,plain,(
    ! [B_334,A_335] :
      ( v1_tops_1(B_334,A_335)
      | k2_pre_topc(A_335,B_334) != u1_struct_0(A_335)
      | ~ m1_subset_1(B_334,k1_zfmisc_1(u1_struct_0(A_335)))
      | ~ l1_pre_topc(A_335) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_5088,plain,(
    ! [B_334] :
      ( v1_tops_1(B_334,'#skF_4')
      | k2_pre_topc('#skF_4',B_334) != u1_struct_0('#skF_4')
      | ~ m1_subset_1(B_334,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_5073])).

tff(c_5128,plain,(
    ! [B_337] :
      ( v1_tops_1(B_337,'#skF_4')
      | k2_pre_topc('#skF_4',B_337) != '#skF_5'
      | ~ m1_subset_1(B_337,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_200,c_5088])).

tff(c_5142,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | k2_pre_topc('#skF_4','#skF_5') != '#skF_5' ),
    inference(resolution,[status(thm)],[c_103,c_5128])).

tff(c_5154,plain,(
    k2_pre_topc('#skF_4','#skF_5') != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_5070,c_5142])).

tff(c_5461,plain,(
    ! [A_360,B_361] :
      ( u1_struct_0('#skF_2'(A_360,B_361)) = B_361
      | ~ m1_subset_1(B_361,k1_zfmisc_1(u1_struct_0(A_360)))
      | v1_xboole_0(B_361)
      | ~ l1_pre_topc(A_360)
      | v2_struct_0(A_360) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_5476,plain,(
    ! [B_361] :
      ( u1_struct_0('#skF_2'('#skF_4',B_361)) = B_361
      | ~ m1_subset_1(B_361,k1_zfmisc_1('#skF_5'))
      | v1_xboole_0(B_361)
      | ~ l1_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_5461])).

tff(c_5496,plain,(
    ! [B_361] :
      ( u1_struct_0('#skF_2'('#skF_4',B_361)) = B_361
      | ~ m1_subset_1(B_361,k1_zfmisc_1('#skF_5'))
      | v1_xboole_0(B_361)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_5476])).

tff(c_5502,plain,(
    ! [B_362] :
      ( u1_struct_0('#skF_2'('#skF_4',B_362)) = B_362
      | ~ m1_subset_1(B_362,k1_zfmisc_1('#skF_5'))
      | v1_xboole_0(B_362) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_5496])).

tff(c_5516,plain,
    ( u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_103,c_5502])).

tff(c_5528,plain,(
    u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_451,c_5516])).

tff(c_44,plain,(
    ! [B_33,A_31] :
      ( m1_subset_1(u1_struct_0(B_33),k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ m1_pre_topc(B_33,A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_7851,plain,(
    ! [B_415,A_416] :
      ( v4_pre_topc(u1_struct_0(B_415),A_416)
      | ~ v1_borsuk_1(B_415,A_416)
      | ~ m1_subset_1(u1_struct_0(B_415),k1_zfmisc_1(u1_struct_0(A_416)))
      | ~ m1_pre_topc(B_415,A_416)
      | ~ l1_pre_topc(A_416)
      | ~ v2_pre_topc(A_416) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_8408,plain,(
    ! [B_424,A_425] :
      ( v4_pre_topc(u1_struct_0(B_424),A_425)
      | ~ v1_borsuk_1(B_424,A_425)
      | ~ v2_pre_topc(A_425)
      | ~ m1_pre_topc(B_424,A_425)
      | ~ l1_pre_topc(A_425) ) ),
    inference(resolution,[status(thm)],[c_44,c_7851])).

tff(c_417,plain,(
    ! [B_112] :
      ( m1_subset_1(u1_struct_0(B_112),k1_zfmisc_1('#skF_5'))
      | ~ m1_pre_topc(B_112,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_410])).

tff(c_4800,plain,(
    ! [B_112] :
      ( k2_pre_topc('#skF_4',u1_struct_0(B_112)) = u1_struct_0(B_112)
      | ~ v4_pre_topc(u1_struct_0(B_112),'#skF_4')
      | ~ m1_pre_topc(B_112,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_417,c_4780])).

tff(c_8412,plain,(
    ! [B_424] :
      ( k2_pre_topc('#skF_4',u1_struct_0(B_424)) = u1_struct_0(B_424)
      | ~ v1_borsuk_1(B_424,'#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ m1_pre_topc(B_424,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8408,c_4800])).

tff(c_8449,plain,(
    ! [B_426] :
      ( k2_pre_topc('#skF_4',u1_struct_0(B_426)) = u1_struct_0(B_426)
      | ~ v1_borsuk_1(B_426,'#skF_4')
      | ~ m1_pre_topc(B_426,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_92,c_8412])).

tff(c_8473,plain,
    ( u1_struct_0('#skF_2'('#skF_4','#skF_5')) = k2_pre_topc('#skF_4','#skF_5')
    | ~ v1_borsuk_1('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5528,c_8449])).

tff(c_8482,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = '#skF_5'
    | ~ v1_borsuk_1('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5416,c_5528,c_8473])).

tff(c_8483,plain,(
    ~ v1_borsuk_1('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_5154,c_8482])).

tff(c_8557,plain,
    ( ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v1_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_8483])).

tff(c_8560,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_5416,c_8557])).

tff(c_8562,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_8560])).

tff(c_8563,plain,(
    k2_pre_topc('#skF_4','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_5067])).

tff(c_9974,plain,(
    ! [B_470,A_471] :
      ( v4_pre_topc(B_470,A_471)
      | k2_pre_topc(A_471,B_470) != B_470
      | ~ v2_pre_topc(A_471)
      | ~ m1_subset_1(B_470,k1_zfmisc_1(u1_struct_0(A_471)))
      | ~ l1_pre_topc(A_471) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_10001,plain,(
    ! [B_470] :
      ( v4_pre_topc(B_470,'#skF_4')
      | k2_pre_topc('#skF_4',B_470) != B_470
      | ~ v2_pre_topc('#skF_4')
      | ~ m1_subset_1(B_470,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_9974])).

tff(c_10041,plain,(
    ! [B_473] :
      ( v4_pre_topc(B_473,'#skF_4')
      | k2_pre_topc('#skF_4',B_473) != B_473
      | ~ m1_subset_1(B_473,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_92,c_10001])).

tff(c_10055,plain,
    ( v4_pre_topc('#skF_5','#skF_4')
    | k2_pre_topc('#skF_4','#skF_5') != '#skF_5' ),
    inference(resolution,[status(thm)],[c_103,c_10041])).

tff(c_10067,plain,(
    v4_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8563,c_10055])).

tff(c_10069,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4804,c_10067])).

tff(c_10070,plain,(
    k2_pre_topc('#skF_4','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_4802])).

tff(c_10362,plain,(
    ! [B_494,A_495] :
      ( v1_tops_1(B_494,A_495)
      | k2_pre_topc(A_495,B_494) != u1_struct_0(A_495)
      | ~ m1_subset_1(B_494,k1_zfmisc_1(u1_struct_0(A_495)))
      | ~ l1_pre_topc(A_495) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_10377,plain,(
    ! [B_494] :
      ( v1_tops_1(B_494,'#skF_4')
      | k2_pre_topc('#skF_4',B_494) != u1_struct_0('#skF_4')
      | ~ m1_subset_1(B_494,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_10362])).

tff(c_10417,plain,(
    ! [B_497] :
      ( v1_tops_1(B_497,'#skF_4')
      | k2_pre_topc('#skF_4',B_497) != '#skF_5'
      | ~ m1_subset_1(B_497,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_200,c_10377])).

tff(c_10431,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | k2_pre_topc('#skF_4','#skF_5') != '#skF_5' ),
    inference(resolution,[status(thm)],[c_103,c_10417])).

tff(c_10443,plain,(
    v1_tops_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10070,c_10431])).

tff(c_10665,plain,(
    ! [B_514,A_515] :
      ( v2_tex_2(B_514,A_515)
      | ~ m1_subset_1(B_514,k1_zfmisc_1(u1_struct_0(A_515)))
      | ~ l1_pre_topc(A_515)
      | ~ v1_tdlat_3(A_515)
      | ~ v2_pre_topc(A_515)
      | v2_struct_0(A_515) ) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_10680,plain,(
    ! [B_514] :
      ( v2_tex_2(B_514,'#skF_4')
      | ~ m1_subset_1(B_514,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v1_tdlat_3('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_10665])).

tff(c_10698,plain,(
    ! [B_514] :
      ( v2_tex_2(B_514,'#skF_4')
      | ~ m1_subset_1(B_514,k1_zfmisc_1('#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_10680])).

tff(c_10703,plain,(
    ! [B_516] :
      ( v2_tex_2(B_516,'#skF_4')
      | ~ m1_subset_1(B_516,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_10698])).

tff(c_10725,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_103,c_10703])).

tff(c_12981,plain,(
    ! [B_574,A_575] :
      ( v3_tex_2(B_574,A_575)
      | ~ v2_tex_2(B_574,A_575)
      | ~ v1_tops_1(B_574,A_575)
      | ~ m1_subset_1(B_574,k1_zfmisc_1(u1_struct_0(A_575)))
      | ~ l1_pre_topc(A_575)
      | ~ v2_pre_topc(A_575)
      | v2_struct_0(A_575) ) ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_13014,plain,(
    ! [B_574] :
      ( v3_tex_2(B_574,'#skF_4')
      | ~ v2_tex_2(B_574,'#skF_4')
      | ~ v1_tops_1(B_574,'#skF_4')
      | ~ m1_subset_1(B_574,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_12981])).

tff(c_13035,plain,(
    ! [B_574] :
      ( v3_tex_2(B_574,'#skF_4')
      | ~ v2_tex_2(B_574,'#skF_4')
      | ~ v1_tops_1(B_574,'#skF_4')
      | ~ m1_subset_1(B_574,k1_zfmisc_1('#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_13014])).

tff(c_13040,plain,(
    ! [B_576] :
      ( v3_tex_2(B_576,'#skF_4')
      | ~ v2_tex_2(B_576,'#skF_4')
      | ~ v1_tops_1(B_576,'#skF_4')
      | ~ m1_subset_1(B_576,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_13035])).

tff(c_13054,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ v1_tops_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_103,c_13040])).

tff(c_13067,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10443,c_10725,c_13054])).

tff(c_13069,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_13067])).

tff(c_13071,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_449])).

tff(c_13279,plain,(
    ! [A_589] :
      ( m1_subset_1('#skF_1'(A_589),k1_zfmisc_1(u1_struct_0(A_589)))
      | ~ l1_pre_topc(A_589)
      | ~ v2_pre_topc(A_589)
      | v2_struct_0(A_589) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_13296,plain,
    ( m1_subset_1('#skF_1'('#skF_4'),k1_zfmisc_1('#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_13279])).

tff(c_13303,plain,
    ( m1_subset_1('#skF_1'('#skF_4'),k1_zfmisc_1('#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_13296])).

tff(c_13304,plain,(
    m1_subset_1('#skF_1'('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_13303])).

tff(c_13326,plain,(
    r1_tarski('#skF_1'('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_13304,c_22])).

tff(c_13332,plain,
    ( ~ v1_xboole_0('#skF_5')
    | '#skF_1'('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_13326,c_264])).

tff(c_13336,plain,(
    '#skF_1'('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13071,c_13332])).

tff(c_34,plain,(
    ! [A_22] :
      ( ~ v1_xboole_0('#skF_1'(A_22))
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_13353,plain,
    ( ~ v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_13336,c_34])).

tff(c_13366,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_13071,c_13353])).

tff(c_13368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_13366])).

tff(c_13370,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_6,plain,(
    ! [A_4] : k1_subset_1(A_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_6] : m1_subset_1(k1_subset_1(A_6),k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_107,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10])).

tff(c_13378,plain,(
    ! [A_590,B_591] :
      ( r1_tarski(A_590,B_591)
      | ~ m1_subset_1(A_590,k1_zfmisc_1(B_591)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_13389,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(resolution,[status(thm)],[c_107,c_13378])).

tff(c_2,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_13398,plain,(
    ! [B_596,A_597] :
      ( ~ r1_xboole_0(B_596,A_597)
      | ~ r1_tarski(B_596,A_597)
      | v1_xboole_0(B_596) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_13403,plain,(
    ! [A_598] :
      ( ~ r1_tarski(A_598,k1_xboole_0)
      | v1_xboole_0(A_598) ) ),
    inference(resolution,[status(thm)],[c_2,c_13398])).

tff(c_13412,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_13389,c_13403])).

tff(c_16,plain,(
    ! [A_10] : k3_subset_1(A_10,k1_subset_1(A_10)) = k2_subset_1(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_104,plain,(
    ! [A_10] : k3_subset_1(A_10,k1_subset_1(A_10)) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_16])).

tff(c_108,plain,(
    ! [A_10] : k3_subset_1(A_10,k1_xboole_0) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_104])).

tff(c_13490,plain,(
    ! [A_609,B_610] :
      ( k3_subset_1(A_609,k3_subset_1(A_609,B_610)) = B_610
      | ~ m1_subset_1(B_610,k1_zfmisc_1(A_609)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_13496,plain,(
    ! [A_6] : k3_subset_1(A_6,k3_subset_1(A_6,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_107,c_13490])).

tff(c_13502,plain,(
    ! [A_6] : k3_subset_1(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_13496])).

tff(c_19170,plain,(
    ! [A_954,B_955] :
      ( k2_pre_topc(A_954,B_955) = B_955
      | ~ v4_pre_topc(B_955,A_954)
      | ~ m1_subset_1(B_955,k1_zfmisc_1(u1_struct_0(A_954)))
      | ~ l1_pre_topc(A_954) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_19194,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = '#skF_5'
    | ~ v4_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_19170])).

tff(c_19203,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = '#skF_5'
    | ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_19194])).

tff(c_19204,plain,(
    ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_19203])).

tff(c_13872,plain,(
    ! [A_658,B_659] :
      ( k2_pre_topc(A_658,B_659) = B_659
      | ~ v4_pre_topc(B_659,A_658)
      | ~ m1_subset_1(B_659,k1_zfmisc_1(u1_struct_0(A_658)))
      | ~ l1_pre_topc(A_658) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_13896,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = '#skF_5'
    | ~ v4_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_13872])).

tff(c_13905,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = '#skF_5'
    | ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_13896])).

tff(c_13906,plain,(
    ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_13905])).

tff(c_13388,plain,(
    ! [A_7] : r1_tarski(A_7,A_7) ),
    inference(resolution,[status(thm)],[c_103,c_13378])).

tff(c_15290,plain,(
    ! [A_740,B_741] :
      ( v1_pre_topc('#skF_2'(A_740,B_741))
      | ~ m1_subset_1(B_741,k1_zfmisc_1(u1_struct_0(A_740)))
      | v1_xboole_0(B_741)
      | ~ l1_pre_topc(A_740)
      | v2_struct_0(A_740) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_15314,plain,
    ( v1_pre_topc('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_15290])).

tff(c_15324,plain,
    ( v1_pre_topc('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_15314])).

tff(c_15325,plain,
    ( v1_pre_topc('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_15324])).

tff(c_15326,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_15325])).

tff(c_13414,plain,(
    ! [B_599,A_600] :
      ( v1_subset_1(B_599,A_600)
      | B_599 = A_600
      | ~ m1_subset_1(B_599,k1_zfmisc_1(A_600)) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_13427,plain,(
    ! [A_17,B_18] :
      ( v1_subset_1(A_17,B_18)
      | B_18 = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(resolution,[status(thm)],[c_24,c_13414])).

tff(c_13453,plain,(
    ! [B_605,A_606] :
      ( ~ v1_subset_1(B_605,A_606)
      | ~ m1_subset_1(B_605,k1_zfmisc_1(A_606))
      | ~ v1_xboole_0(A_606) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_13472,plain,(
    ! [A_607] :
      ( ~ v1_subset_1(k1_xboole_0,A_607)
      | ~ v1_xboole_0(A_607) ) ),
    inference(resolution,[status(thm)],[c_107,c_13453])).

tff(c_13476,plain,(
    ! [B_18] :
      ( ~ v1_xboole_0(B_18)
      | k1_xboole_0 = B_18
      | ~ r1_tarski(k1_xboole_0,B_18) ) ),
    inference(resolution,[status(thm)],[c_13427,c_13472])).

tff(c_13482,plain,(
    ! [B_18] :
      ( ~ v1_xboole_0(B_18)
      | k1_xboole_0 = B_18 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13389,c_13476])).

tff(c_15330,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_15326,c_13482])).

tff(c_15343,plain,(
    ! [A_10] : k3_subset_1(A_10,'#skF_5') = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_15330,c_108])).

tff(c_13369,plain,(
    v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_13465,plain,
    ( ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_86,c_13453])).

tff(c_13471,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13369,c_13465])).

tff(c_13503,plain,(
    k3_subset_1(u1_struct_0('#skF_4'),k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_86,c_13490])).

tff(c_13738,plain,(
    ! [A_636,B_637] :
      ( ~ v1_xboole_0(k3_subset_1(A_636,B_637))
      | ~ m1_subset_1(B_637,k1_zfmisc_1(A_636))
      | ~ v1_subset_1(B_637,A_636)
      | v1_xboole_0(A_636) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_13773,plain,(
    ! [B_638,A_639] :
      ( ~ v1_xboole_0(k3_subset_1(B_638,A_639))
      | ~ v1_subset_1(A_639,B_638)
      | v1_xboole_0(B_638)
      | ~ r1_tarski(A_639,B_638) ) ),
    inference(resolution,[status(thm)],[c_24,c_13738])).

tff(c_13779,plain,
    ( ~ v1_xboole_0('#skF_5')
    | ~ v1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13503,c_13773])).

tff(c_13786,plain,
    ( ~ v1_xboole_0('#skF_5')
    | ~ v1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4'))
    | ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_13471,c_13779])).

tff(c_13792,plain,(
    ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_13786])).

tff(c_15463,plain,(
    ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15343,c_13792])).

tff(c_15468,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13388,c_15463])).

tff(c_15470,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_15325])).

tff(c_15510,plain,(
    ! [A_751,B_752] :
      ( m1_pre_topc('#skF_2'(A_751,B_752),A_751)
      | ~ m1_subset_1(B_752,k1_zfmisc_1(u1_struct_0(A_751)))
      | v1_xboole_0(B_752)
      | ~ l1_pre_topc(A_751)
      | v2_struct_0(A_751) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_15527,plain,
    ( m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_15510])).

tff(c_15537,plain,
    ( m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_15527])).

tff(c_15538,plain,(
    m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_15470,c_15537])).

tff(c_15719,plain,(
    ! [A_773,B_774] :
      ( u1_struct_0('#skF_2'(A_773,B_774)) = B_774
      | ~ m1_subset_1(B_774,k1_zfmisc_1(u1_struct_0(A_773)))
      | v1_xboole_0(B_774)
      | ~ l1_pre_topc(A_773)
      | v2_struct_0(A_773) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_15743,plain,
    ( u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_15719])).

tff(c_15753,plain,
    ( u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_15743])).

tff(c_15754,plain,(
    u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_15470,c_15753])).

tff(c_16442,plain,(
    ! [B_798,A_799] :
      ( v4_pre_topc(u1_struct_0(B_798),A_799)
      | ~ v1_borsuk_1(B_798,A_799)
      | ~ m1_subset_1(u1_struct_0(B_798),k1_zfmisc_1(u1_struct_0(A_799)))
      | ~ m1_pre_topc(B_798,A_799)
      | ~ l1_pre_topc(A_799)
      | ~ v2_pre_topc(A_799) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_16541,plain,(
    ! [B_806,A_807] :
      ( v4_pre_topc(u1_struct_0(B_806),A_807)
      | ~ v1_borsuk_1(B_806,A_807)
      | ~ v2_pre_topc(A_807)
      | ~ m1_pre_topc(B_806,A_807)
      | ~ l1_pre_topc(A_807) ) ),
    inference(resolution,[status(thm)],[c_44,c_16442])).

tff(c_16696,plain,(
    ! [A_819] :
      ( v4_pre_topc('#skF_5',A_819)
      | ~ v1_borsuk_1('#skF_2'('#skF_4','#skF_5'),A_819)
      | ~ v2_pre_topc(A_819)
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_819)
      | ~ l1_pre_topc(A_819) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15754,c_16541])).

tff(c_17929,plain,(
    ! [A_882] :
      ( v4_pre_topc('#skF_5',A_882)
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_882)
      | ~ l1_pre_topc(A_882)
      | ~ v1_tdlat_3(A_882)
      | ~ v2_pre_topc(A_882)
      | v2_struct_0(A_882) ) ),
    inference(resolution,[status(thm)],[c_52,c_16696])).

tff(c_17932,plain,
    ( v4_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v1_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_15538,c_17929])).

tff(c_17935,plain,
    ( v4_pre_topc('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_17932])).

tff(c_17937,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_13906,c_17935])).

tff(c_17938,plain,(
    k2_pre_topc('#skF_4','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_13905])).

tff(c_17984,plain,(
    ! [A_888,B_889] :
      ( k2_pre_topc(A_888,B_889) = u1_struct_0(A_888)
      | ~ v1_tops_1(B_889,A_888)
      | ~ m1_subset_1(B_889,k1_zfmisc_1(u1_struct_0(A_888)))
      | ~ l1_pre_topc(A_888) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_18008,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = u1_struct_0('#skF_4')
    | ~ v1_tops_1('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_17984])).

tff(c_18017,plain,
    ( u1_struct_0('#skF_4') = '#skF_5'
    | ~ v1_tops_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_17938,c_18008])).

tff(c_18018,plain,(
    ~ v1_tops_1('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_18017])).

tff(c_13805,plain,(
    ! [B_648,A_649] :
      ( v3_pre_topc(B_648,A_649)
      | ~ m1_subset_1(B_648,k1_zfmisc_1(u1_struct_0(A_649)))
      | ~ v1_tdlat_3(A_649)
      | ~ l1_pre_topc(A_649)
      | ~ v2_pre_topc(A_649) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_13829,plain,
    ( v3_pre_topc('#skF_5','#skF_4')
    | ~ v1_tdlat_3('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_13805])).

tff(c_13838,plain,(
    v3_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_90,c_13829])).

tff(c_19092,plain,(
    ! [B_946,A_947] :
      ( v1_tops_1(B_946,A_947)
      | ~ v3_tex_2(B_946,A_947)
      | ~ v3_pre_topc(B_946,A_947)
      | ~ m1_subset_1(B_946,k1_zfmisc_1(u1_struct_0(A_947)))
      | ~ l1_pre_topc(A_947)
      | ~ v2_pre_topc(A_947)
      | v2_struct_0(A_947) ) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_19125,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | ~ v3_tex_2('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_19092])).

tff(c_19136,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_13838,c_13370,c_19125])).

tff(c_19138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_18018,c_19136])).

tff(c_19139,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_18017])).

tff(c_19141,plain,(
    ~ r1_tarski(k3_subset_1('#skF_5','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19139,c_19139,c_13792])).

tff(c_19150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13389,c_13502,c_19141])).

tff(c_19151,plain,
    ( ~ v1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_13786])).

tff(c_19157,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_19151])).

tff(c_20755,plain,(
    ! [A_1071,B_1072] :
      ( m1_pre_topc('#skF_2'(A_1071,B_1072),A_1071)
      | ~ m1_subset_1(B_1072,k1_zfmisc_1(u1_struct_0(A_1071)))
      | v1_xboole_0(B_1072)
      | ~ l1_pre_topc(A_1071)
      | v2_struct_0(A_1071) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_20772,plain,
    ( m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_20755])).

tff(c_20782,plain,
    ( m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_20772])).

tff(c_20783,plain,(
    m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_19157,c_20782])).

tff(c_20881,plain,(
    ! [A_1081,B_1082] :
      ( u1_struct_0('#skF_2'(A_1081,B_1082)) = B_1082
      | ~ m1_subset_1(B_1082,k1_zfmisc_1(u1_struct_0(A_1081)))
      | v1_xboole_0(B_1082)
      | ~ l1_pre_topc(A_1081)
      | v2_struct_0(A_1081) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_20905,plain,
    ( u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_20881])).

tff(c_20915,plain,
    ( u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_20905])).

tff(c_20916,plain,(
    u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_19157,c_20915])).

tff(c_21302,plain,(
    ! [B_1090,A_1091] :
      ( v4_pre_topc(u1_struct_0(B_1090),A_1091)
      | ~ v1_borsuk_1(B_1090,A_1091)
      | ~ m1_subset_1(u1_struct_0(B_1090),k1_zfmisc_1(u1_struct_0(A_1091)))
      | ~ m1_pre_topc(B_1090,A_1091)
      | ~ l1_pre_topc(A_1091)
      | ~ v2_pre_topc(A_1091) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_21533,plain,(
    ! [B_1095,A_1096] :
      ( v4_pre_topc(u1_struct_0(B_1095),A_1096)
      | ~ v1_borsuk_1(B_1095,A_1096)
      | ~ v2_pre_topc(A_1096)
      | ~ m1_pre_topc(B_1095,A_1096)
      | ~ l1_pre_topc(A_1096) ) ),
    inference(resolution,[status(thm)],[c_44,c_21302])).

tff(c_23245,plain,(
    ! [A_1169] :
      ( v4_pre_topc('#skF_5',A_1169)
      | ~ v1_borsuk_1('#skF_2'('#skF_4','#skF_5'),A_1169)
      | ~ v2_pre_topc(A_1169)
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_1169)
      | ~ l1_pre_topc(A_1169) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20916,c_21533])).

tff(c_23255,plain,(
    ! [A_1170] :
      ( v4_pre_topc('#skF_5',A_1170)
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_1170)
      | ~ l1_pre_topc(A_1170)
      | ~ v1_tdlat_3(A_1170)
      | ~ v2_pre_topc(A_1170)
      | v2_struct_0(A_1170) ) ),
    inference(resolution,[status(thm)],[c_52,c_23245])).

tff(c_23258,plain,
    ( v4_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v1_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_20783,c_23255])).

tff(c_23261,plain,
    ( v4_pre_topc('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_23258])).

tff(c_23263,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_19204,c_23261])).

tff(c_23264,plain,(
    k2_pre_topc('#skF_4','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_19203])).

tff(c_23345,plain,(
    ! [A_1181,B_1182] :
      ( k2_pre_topc(A_1181,B_1182) = u1_struct_0(A_1181)
      | ~ v1_tops_1(B_1182,A_1181)
      | ~ m1_subset_1(B_1182,k1_zfmisc_1(u1_struct_0(A_1181)))
      | ~ l1_pre_topc(A_1181) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_23369,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = u1_struct_0('#skF_4')
    | ~ v1_tops_1('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_23345])).

tff(c_23378,plain,
    ( u1_struct_0('#skF_4') = '#skF_5'
    | ~ v1_tops_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_23264,c_23369])).

tff(c_23379,plain,(
    ~ v1_tops_1('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_23378])).

tff(c_23309,plain,(
    ! [B_1177,A_1178] :
      ( v3_pre_topc(B_1177,A_1178)
      | ~ m1_subset_1(B_1177,k1_zfmisc_1(u1_struct_0(A_1178)))
      | ~ v1_tdlat_3(A_1178)
      | ~ l1_pre_topc(A_1178)
      | ~ v2_pre_topc(A_1178) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_23333,plain,
    ( v3_pre_topc('#skF_5','#skF_4')
    | ~ v1_tdlat_3('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_23309])).

tff(c_23342,plain,(
    v3_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_90,c_23333])).

tff(c_24559,plain,(
    ! [B_1250,A_1251] :
      ( v1_tops_1(B_1250,A_1251)
      | ~ v3_tex_2(B_1250,A_1251)
      | ~ v3_pre_topc(B_1250,A_1251)
      | ~ m1_subset_1(B_1250,k1_zfmisc_1(u1_struct_0(A_1251)))
      | ~ l1_pre_topc(A_1251)
      | ~ v2_pre_topc(A_1251)
      | v2_struct_0(A_1251) ) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_24592,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | ~ v3_tex_2('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_24559])).

tff(c_24603,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_23342,c_13370,c_24592])).

tff(c_24605,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_23379,c_24603])).

tff(c_24606,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_23378])).

tff(c_13759,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'))
    | ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_86,c_13738])).

tff(c_13771,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13369,c_13759])).

tff(c_13772,plain,(
    ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_13471,c_13771])).

tff(c_24610,plain,(
    ~ v1_xboole_0(k3_subset_1('#skF_5','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24606,c_13772])).

tff(c_24620,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13412,c_13502,c_24610])).

tff(c_24622,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_19151])).

tff(c_24626,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_24622,c_13482])).

tff(c_24648,plain,(
    ! [A_6] : m1_subset_1('#skF_5',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24626,c_107])).

tff(c_25216,plain,(
    ! [B_1313,A_1314] :
      ( ~ v3_tex_2(B_1313,A_1314)
      | ~ m1_subset_1(B_1313,k1_zfmisc_1(u1_struct_0(A_1314)))
      | ~ v1_xboole_0(B_1313)
      | ~ l1_pre_topc(A_1314)
      | ~ v2_pre_topc(A_1314)
      | v2_struct_0(A_1314) ) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_25220,plain,(
    ! [A_1314] :
      ( ~ v3_tex_2('#skF_5',A_1314)
      | ~ v1_xboole_0('#skF_5')
      | ~ l1_pre_topc(A_1314)
      | ~ v2_pre_topc(A_1314)
      | v2_struct_0(A_1314) ) ),
    inference(resolution,[status(thm)],[c_24648,c_25216])).

tff(c_25246,plain,(
    ! [A_1315] :
      ( ~ v3_tex_2('#skF_5',A_1315)
      | ~ l1_pre_topc(A_1315)
      | ~ v2_pre_topc(A_1315)
      | v2_struct_0(A_1315) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24622,c_25220])).

tff(c_25249,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_13370,c_25246])).

tff(c_25252,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_25249])).

tff(c_25254,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_25252])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:20:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.69/4.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.74/4.63  
% 11.74/4.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.92/4.64  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tsep_1 > v1_tops_1 > v1_subset_1 > v1_borsuk_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2
% 11.92/4.64  
% 11.92/4.64  %Foreground sorts:
% 11.92/4.64  
% 11.92/4.64  
% 11.92/4.64  %Background operators:
% 11.92/4.64  
% 11.92/4.64  
% 11.92/4.64  %Foreground operators:
% 11.92/4.64  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 11.92/4.64  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 11.92/4.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.92/4.64  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 11.92/4.64  tff('#skF_1', type, '#skF_1': $i > $i).
% 11.92/4.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.92/4.64  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.92/4.64  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 11.92/4.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.92/4.64  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 11.92/4.64  tff('#skF_5', type, '#skF_5': $i).
% 11.92/4.64  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 11.92/4.64  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 11.92/4.64  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 11.92/4.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.92/4.64  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 11.92/4.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.92/4.64  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 11.92/4.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.92/4.64  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 11.92/4.64  tff('#skF_4', type, '#skF_4': $i).
% 11.92/4.64  tff('#skF_3', type, '#skF_3': $i > $i).
% 11.92/4.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.92/4.64  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.92/4.64  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 11.92/4.64  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 11.92/4.64  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.92/4.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.92/4.64  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 11.92/4.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.92/4.64  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 11.92/4.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.92/4.64  tff(v1_borsuk_1, type, v1_borsuk_1: ($i * $i) > $o).
% 11.92/4.64  
% 11.94/4.67  tff(f_291, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tex_2)).
% 11.94/4.67  tff(f_39, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 11.94/4.67  tff(f_43, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 11.94/4.67  tff(f_170, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 11.94/4.67  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 11.94/4.67  tff(f_130, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 11.94/4.67  tff(f_73, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 11.94/4.67  tff(f_69, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~v1_subset_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_subset_1)).
% 11.94/4.67  tff(f_201, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (?[C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) & (B = u1_struct_0(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_tsep_1)).
% 11.94/4.67  tff(f_154, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((v1_borsuk_1(B, A) & v1_tsep_1(B, A)) & v1_tdlat_3(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_tdlat_3)).
% 11.94/4.67  tff(f_163, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 11.94/4.67  tff(f_123, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_borsuk_1(B, A) & m1_pre_topc(B, A)) <=> v4_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tsep_1)).
% 11.94/4.67  tff(f_226, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 11.94/4.67  tff(f_273, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tex_2)).
% 11.94/4.67  tff(f_105, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: (((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v3_pre_topc(B, A)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_tops_1)).
% 11.94/4.67  tff(f_37, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 11.94/4.67  tff(f_41, axiom, (![A]: m1_subset_1(k1_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 11.94/4.67  tff(f_27, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 11.94/4.67  tff(f_35, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 11.94/4.67  tff(f_49, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 11.94/4.67  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 11.94/4.67  tff(f_180, axiom, (![A, B]: (((~v1_xboole_0(A) & v1_subset_1(B, A)) & m1_subset_1(B, k1_zfmisc_1(A))) => ~v1_xboole_0(k3_subset_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tex_2)).
% 11.94/4.67  tff(f_212, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_tdlat_3)).
% 11.94/4.67  tff(f_257, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_tex_2)).
% 11.94/4.67  tff(f_241, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 11.94/4.67  tff(c_94, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_291])).
% 11.94/4.67  tff(c_92, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_291])).
% 11.94/4.67  tff(c_88, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_291])).
% 11.94/4.67  tff(c_96, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_291])).
% 11.94/4.67  tff(c_139, plain, (~v3_tex_2('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_96])).
% 11.94/4.67  tff(c_8, plain, (![A_5]: (k2_subset_1(A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.94/4.67  tff(c_12, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.94/4.67  tff(c_103, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_12])).
% 11.94/4.67  tff(c_102, plain, (v3_tex_2('#skF_5', '#skF_4') | ~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_291])).
% 11.94/4.67  tff(c_140, plain, (~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_139, c_102])).
% 11.94/4.67  tff(c_86, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_291])).
% 11.94/4.67  tff(c_179, plain, (![B_86, A_87]: (v1_subset_1(B_86, A_87) | B_86=A_87 | ~m1_subset_1(B_86, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_170])).
% 11.94/4.67  tff(c_191, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_86, c_179])).
% 11.94/4.67  tff(c_200, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_140, c_191])).
% 11.94/4.67  tff(c_4742, plain, (![A_311, B_312]: (k2_pre_topc(A_311, B_312)=B_312 | ~v4_pre_topc(B_312, A_311) | ~m1_subset_1(B_312, k1_zfmisc_1(u1_struct_0(A_311))) | ~l1_pre_topc(A_311))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.94/4.67  tff(c_4757, plain, (![B_312]: (k2_pre_topc('#skF_4', B_312)=B_312 | ~v4_pre_topc(B_312, '#skF_4') | ~m1_subset_1(B_312, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_200, c_4742])).
% 11.94/4.67  tff(c_4780, plain, (![B_314]: (k2_pre_topc('#skF_4', B_314)=B_314 | ~v4_pre_topc(B_314, '#skF_4') | ~m1_subset_1(B_314, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_4757])).
% 11.94/4.67  tff(c_4802, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5' | ~v4_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_103, c_4780])).
% 11.94/4.67  tff(c_4804, plain, (~v4_pre_topc('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_4802])).
% 11.94/4.67  tff(c_90, plain, (v1_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_291])).
% 11.94/4.67  tff(c_390, plain, (![B_112, A_113]: (m1_subset_1(u1_struct_0(B_112), k1_zfmisc_1(u1_struct_0(A_113))) | ~m1_pre_topc(B_112, A_113) | ~l1_pre_topc(A_113))), inference(cnfTransformation, [status(thm)], [f_130])).
% 11.94/4.67  tff(c_410, plain, (![B_112]: (m1_subset_1(u1_struct_0(B_112), k1_zfmisc_1('#skF_5')) | ~m1_pre_topc(B_112, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_200, c_390])).
% 11.94/4.67  tff(c_418, plain, (![B_114]: (m1_subset_1(u1_struct_0(B_114), k1_zfmisc_1('#skF_5')) | ~m1_pre_topc(B_114, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_410])).
% 11.94/4.67  tff(c_22, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~m1_subset_1(A_17, k1_zfmisc_1(B_18)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.94/4.67  tff(c_442, plain, (![B_115]: (r1_tarski(u1_struct_0(B_115), '#skF_5') | ~m1_pre_topc(B_115, '#skF_4'))), inference(resolution, [status(thm)], [c_418, c_22])).
% 11.94/4.67  tff(c_24, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.94/4.67  tff(c_192, plain, (![A_17, B_18]: (v1_subset_1(A_17, B_18) | B_18=A_17 | ~r1_tarski(A_17, B_18))), inference(resolution, [status(thm)], [c_24, c_179])).
% 11.94/4.67  tff(c_217, plain, (![B_89, A_90]: (~v1_subset_1(B_89, A_90) | ~m1_subset_1(B_89, k1_zfmisc_1(A_90)) | ~v1_xboole_0(A_90))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.94/4.67  tff(c_257, plain, (![A_95, B_96]: (~v1_subset_1(A_95, B_96) | ~v1_xboole_0(B_96) | ~r1_tarski(A_95, B_96))), inference(resolution, [status(thm)], [c_24, c_217])).
% 11.94/4.67  tff(c_264, plain, (![B_18, A_17]: (~v1_xboole_0(B_18) | B_18=A_17 | ~r1_tarski(A_17, B_18))), inference(resolution, [status(thm)], [c_192, c_257])).
% 11.94/4.67  tff(c_449, plain, (![B_115]: (~v1_xboole_0('#skF_5') | u1_struct_0(B_115)='#skF_5' | ~m1_pre_topc(B_115, '#skF_4'))), inference(resolution, [status(thm)], [c_442, c_264])).
% 11.94/4.67  tff(c_451, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_449])).
% 11.94/4.67  tff(c_5357, plain, (![A_353, B_354]: (m1_pre_topc('#skF_2'(A_353, B_354), A_353) | ~m1_subset_1(B_354, k1_zfmisc_1(u1_struct_0(A_353))) | v1_xboole_0(B_354) | ~l1_pre_topc(A_353) | v2_struct_0(A_353))), inference(cnfTransformation, [status(thm)], [f_201])).
% 11.94/4.67  tff(c_5367, plain, (![B_354]: (m1_pre_topc('#skF_2'('#skF_4', B_354), '#skF_4') | ~m1_subset_1(B_354, k1_zfmisc_1('#skF_5')) | v1_xboole_0(B_354) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_200, c_5357])).
% 11.94/4.67  tff(c_5384, plain, (![B_354]: (m1_pre_topc('#skF_2'('#skF_4', B_354), '#skF_4') | ~m1_subset_1(B_354, k1_zfmisc_1('#skF_5')) | v1_xboole_0(B_354) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_5367])).
% 11.94/4.67  tff(c_5390, plain, (![B_355]: (m1_pre_topc('#skF_2'('#skF_4', B_355), '#skF_4') | ~m1_subset_1(B_355, k1_zfmisc_1('#skF_5')) | v1_xboole_0(B_355))), inference(negUnitSimplification, [status(thm)], [c_94, c_5384])).
% 11.94/4.67  tff(c_5404, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_103, c_5390])).
% 11.94/4.67  tff(c_5416, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_451, c_5404])).
% 11.94/4.67  tff(c_52, plain, (![B_37, A_35]: (v1_borsuk_1(B_37, A_35) | ~m1_pre_topc(B_37, A_35) | ~l1_pre_topc(A_35) | ~v1_tdlat_3(A_35) | ~v2_pre_topc(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_154])).
% 11.94/4.67  tff(c_5005, plain, (![A_328, B_329]: (k2_pre_topc(A_328, B_329)=u1_struct_0(A_328) | ~v1_tops_1(B_329, A_328) | ~m1_subset_1(B_329, k1_zfmisc_1(u1_struct_0(A_328))) | ~l1_pre_topc(A_328))), inference(cnfTransformation, [status(thm)], [f_163])).
% 11.94/4.67  tff(c_5020, plain, (![B_329]: (k2_pre_topc('#skF_4', B_329)=u1_struct_0('#skF_4') | ~v1_tops_1(B_329, '#skF_4') | ~m1_subset_1(B_329, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_200, c_5005])).
% 11.94/4.67  tff(c_5043, plain, (![B_331]: (k2_pre_topc('#skF_4', B_331)='#skF_5' | ~v1_tops_1(B_331, '#skF_4') | ~m1_subset_1(B_331, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_200, c_5020])).
% 11.94/4.67  tff(c_5067, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5' | ~v1_tops_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_103, c_5043])).
% 11.94/4.67  tff(c_5070, plain, (~v1_tops_1('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_5067])).
% 11.94/4.67  tff(c_5073, plain, (![B_334, A_335]: (v1_tops_1(B_334, A_335) | k2_pre_topc(A_335, B_334)!=u1_struct_0(A_335) | ~m1_subset_1(B_334, k1_zfmisc_1(u1_struct_0(A_335))) | ~l1_pre_topc(A_335))), inference(cnfTransformation, [status(thm)], [f_163])).
% 11.94/4.67  tff(c_5088, plain, (![B_334]: (v1_tops_1(B_334, '#skF_4') | k2_pre_topc('#skF_4', B_334)!=u1_struct_0('#skF_4') | ~m1_subset_1(B_334, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_200, c_5073])).
% 11.94/4.67  tff(c_5128, plain, (![B_337]: (v1_tops_1(B_337, '#skF_4') | k2_pre_topc('#skF_4', B_337)!='#skF_5' | ~m1_subset_1(B_337, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_200, c_5088])).
% 11.94/4.67  tff(c_5142, plain, (v1_tops_1('#skF_5', '#skF_4') | k2_pre_topc('#skF_4', '#skF_5')!='#skF_5'), inference(resolution, [status(thm)], [c_103, c_5128])).
% 11.94/4.67  tff(c_5154, plain, (k2_pre_topc('#skF_4', '#skF_5')!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_5070, c_5142])).
% 11.94/4.67  tff(c_5461, plain, (![A_360, B_361]: (u1_struct_0('#skF_2'(A_360, B_361))=B_361 | ~m1_subset_1(B_361, k1_zfmisc_1(u1_struct_0(A_360))) | v1_xboole_0(B_361) | ~l1_pre_topc(A_360) | v2_struct_0(A_360))), inference(cnfTransformation, [status(thm)], [f_201])).
% 11.94/4.67  tff(c_5476, plain, (![B_361]: (u1_struct_0('#skF_2'('#skF_4', B_361))=B_361 | ~m1_subset_1(B_361, k1_zfmisc_1('#skF_5')) | v1_xboole_0(B_361) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_200, c_5461])).
% 11.94/4.67  tff(c_5496, plain, (![B_361]: (u1_struct_0('#skF_2'('#skF_4', B_361))=B_361 | ~m1_subset_1(B_361, k1_zfmisc_1('#skF_5')) | v1_xboole_0(B_361) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_5476])).
% 11.94/4.67  tff(c_5502, plain, (![B_362]: (u1_struct_0('#skF_2'('#skF_4', B_362))=B_362 | ~m1_subset_1(B_362, k1_zfmisc_1('#skF_5')) | v1_xboole_0(B_362))), inference(negUnitSimplification, [status(thm)], [c_94, c_5496])).
% 11.94/4.67  tff(c_5516, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_103, c_5502])).
% 11.94/4.67  tff(c_5528, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_451, c_5516])).
% 11.94/4.67  tff(c_44, plain, (![B_33, A_31]: (m1_subset_1(u1_struct_0(B_33), k1_zfmisc_1(u1_struct_0(A_31))) | ~m1_pre_topc(B_33, A_31) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_130])).
% 11.94/4.67  tff(c_7851, plain, (![B_415, A_416]: (v4_pre_topc(u1_struct_0(B_415), A_416) | ~v1_borsuk_1(B_415, A_416) | ~m1_subset_1(u1_struct_0(B_415), k1_zfmisc_1(u1_struct_0(A_416))) | ~m1_pre_topc(B_415, A_416) | ~l1_pre_topc(A_416) | ~v2_pre_topc(A_416))), inference(cnfTransformation, [status(thm)], [f_123])).
% 11.94/4.67  tff(c_8408, plain, (![B_424, A_425]: (v4_pre_topc(u1_struct_0(B_424), A_425) | ~v1_borsuk_1(B_424, A_425) | ~v2_pre_topc(A_425) | ~m1_pre_topc(B_424, A_425) | ~l1_pre_topc(A_425))), inference(resolution, [status(thm)], [c_44, c_7851])).
% 11.94/4.67  tff(c_417, plain, (![B_112]: (m1_subset_1(u1_struct_0(B_112), k1_zfmisc_1('#skF_5')) | ~m1_pre_topc(B_112, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_410])).
% 11.94/4.67  tff(c_4800, plain, (![B_112]: (k2_pre_topc('#skF_4', u1_struct_0(B_112))=u1_struct_0(B_112) | ~v4_pre_topc(u1_struct_0(B_112), '#skF_4') | ~m1_pre_topc(B_112, '#skF_4'))), inference(resolution, [status(thm)], [c_417, c_4780])).
% 11.94/4.67  tff(c_8412, plain, (![B_424]: (k2_pre_topc('#skF_4', u1_struct_0(B_424))=u1_struct_0(B_424) | ~v1_borsuk_1(B_424, '#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_pre_topc(B_424, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_8408, c_4800])).
% 11.94/4.67  tff(c_8449, plain, (![B_426]: (k2_pre_topc('#skF_4', u1_struct_0(B_426))=u1_struct_0(B_426) | ~v1_borsuk_1(B_426, '#skF_4') | ~m1_pre_topc(B_426, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_92, c_8412])).
% 11.94/4.67  tff(c_8473, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))=k2_pre_topc('#skF_4', '#skF_5') | ~v1_borsuk_1('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5528, c_8449])).
% 11.94/4.67  tff(c_8482, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5' | ~v1_borsuk_1('#skF_2'('#skF_4', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5416, c_5528, c_8473])).
% 11.94/4.67  tff(c_8483, plain, (~v1_borsuk_1('#skF_2'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_5154, c_8482])).
% 11.94/4.67  tff(c_8557, plain, (~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | ~l1_pre_topc('#skF_4') | ~v1_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_8483])).
% 11.94/4.67  tff(c_8560, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_5416, c_8557])).
% 11.94/4.67  tff(c_8562, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_8560])).
% 11.94/4.67  tff(c_8563, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_5067])).
% 11.94/4.67  tff(c_9974, plain, (![B_470, A_471]: (v4_pre_topc(B_470, A_471) | k2_pre_topc(A_471, B_470)!=B_470 | ~v2_pre_topc(A_471) | ~m1_subset_1(B_470, k1_zfmisc_1(u1_struct_0(A_471))) | ~l1_pre_topc(A_471))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.94/4.67  tff(c_10001, plain, (![B_470]: (v4_pre_topc(B_470, '#skF_4') | k2_pre_topc('#skF_4', B_470)!=B_470 | ~v2_pre_topc('#skF_4') | ~m1_subset_1(B_470, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_200, c_9974])).
% 11.94/4.67  tff(c_10041, plain, (![B_473]: (v4_pre_topc(B_473, '#skF_4') | k2_pre_topc('#skF_4', B_473)!=B_473 | ~m1_subset_1(B_473, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_92, c_10001])).
% 11.94/4.67  tff(c_10055, plain, (v4_pre_topc('#skF_5', '#skF_4') | k2_pre_topc('#skF_4', '#skF_5')!='#skF_5'), inference(resolution, [status(thm)], [c_103, c_10041])).
% 11.94/4.67  tff(c_10067, plain, (v4_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8563, c_10055])).
% 11.94/4.67  tff(c_10069, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4804, c_10067])).
% 11.94/4.67  tff(c_10070, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_4802])).
% 11.94/4.67  tff(c_10362, plain, (![B_494, A_495]: (v1_tops_1(B_494, A_495) | k2_pre_topc(A_495, B_494)!=u1_struct_0(A_495) | ~m1_subset_1(B_494, k1_zfmisc_1(u1_struct_0(A_495))) | ~l1_pre_topc(A_495))), inference(cnfTransformation, [status(thm)], [f_163])).
% 11.94/4.67  tff(c_10377, plain, (![B_494]: (v1_tops_1(B_494, '#skF_4') | k2_pre_topc('#skF_4', B_494)!=u1_struct_0('#skF_4') | ~m1_subset_1(B_494, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_200, c_10362])).
% 11.94/4.67  tff(c_10417, plain, (![B_497]: (v1_tops_1(B_497, '#skF_4') | k2_pre_topc('#skF_4', B_497)!='#skF_5' | ~m1_subset_1(B_497, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_200, c_10377])).
% 11.94/4.67  tff(c_10431, plain, (v1_tops_1('#skF_5', '#skF_4') | k2_pre_topc('#skF_4', '#skF_5')!='#skF_5'), inference(resolution, [status(thm)], [c_103, c_10417])).
% 11.94/4.67  tff(c_10443, plain, (v1_tops_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10070, c_10431])).
% 11.94/4.67  tff(c_10665, plain, (![B_514, A_515]: (v2_tex_2(B_514, A_515) | ~m1_subset_1(B_514, k1_zfmisc_1(u1_struct_0(A_515))) | ~l1_pre_topc(A_515) | ~v1_tdlat_3(A_515) | ~v2_pre_topc(A_515) | v2_struct_0(A_515))), inference(cnfTransformation, [status(thm)], [f_226])).
% 11.94/4.67  tff(c_10680, plain, (![B_514]: (v2_tex_2(B_514, '#skF_4') | ~m1_subset_1(B_514, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4') | ~v1_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_200, c_10665])).
% 11.94/4.67  tff(c_10698, plain, (![B_514]: (v2_tex_2(B_514, '#skF_4') | ~m1_subset_1(B_514, k1_zfmisc_1('#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_10680])).
% 11.94/4.67  tff(c_10703, plain, (![B_516]: (v2_tex_2(B_516, '#skF_4') | ~m1_subset_1(B_516, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_94, c_10698])).
% 11.94/4.67  tff(c_10725, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_103, c_10703])).
% 11.94/4.67  tff(c_12981, plain, (![B_574, A_575]: (v3_tex_2(B_574, A_575) | ~v2_tex_2(B_574, A_575) | ~v1_tops_1(B_574, A_575) | ~m1_subset_1(B_574, k1_zfmisc_1(u1_struct_0(A_575))) | ~l1_pre_topc(A_575) | ~v2_pre_topc(A_575) | v2_struct_0(A_575))), inference(cnfTransformation, [status(thm)], [f_273])).
% 11.94/4.67  tff(c_13014, plain, (![B_574]: (v3_tex_2(B_574, '#skF_4') | ~v2_tex_2(B_574, '#skF_4') | ~v1_tops_1(B_574, '#skF_4') | ~m1_subset_1(B_574, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_200, c_12981])).
% 11.94/4.67  tff(c_13035, plain, (![B_574]: (v3_tex_2(B_574, '#skF_4') | ~v2_tex_2(B_574, '#skF_4') | ~v1_tops_1(B_574, '#skF_4') | ~m1_subset_1(B_574, k1_zfmisc_1('#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_13014])).
% 11.94/4.67  tff(c_13040, plain, (![B_576]: (v3_tex_2(B_576, '#skF_4') | ~v2_tex_2(B_576, '#skF_4') | ~v1_tops_1(B_576, '#skF_4') | ~m1_subset_1(B_576, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_94, c_13035])).
% 11.94/4.67  tff(c_13054, plain, (v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~v1_tops_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_103, c_13040])).
% 11.94/4.67  tff(c_13067, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10443, c_10725, c_13054])).
% 11.94/4.67  tff(c_13069, plain, $false, inference(negUnitSimplification, [status(thm)], [c_139, c_13067])).
% 11.94/4.67  tff(c_13071, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_449])).
% 11.94/4.67  tff(c_13279, plain, (![A_589]: (m1_subset_1('#skF_1'(A_589), k1_zfmisc_1(u1_struct_0(A_589))) | ~l1_pre_topc(A_589) | ~v2_pre_topc(A_589) | v2_struct_0(A_589))), inference(cnfTransformation, [status(thm)], [f_105])).
% 11.94/4.67  tff(c_13296, plain, (m1_subset_1('#skF_1'('#skF_4'), k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_200, c_13279])).
% 11.94/4.67  tff(c_13303, plain, (m1_subset_1('#skF_1'('#skF_4'), k1_zfmisc_1('#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_13296])).
% 11.94/4.67  tff(c_13304, plain, (m1_subset_1('#skF_1'('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_94, c_13303])).
% 11.94/4.67  tff(c_13326, plain, (r1_tarski('#skF_1'('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_13304, c_22])).
% 11.94/4.67  tff(c_13332, plain, (~v1_xboole_0('#skF_5') | '#skF_1'('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_13326, c_264])).
% 11.94/4.67  tff(c_13336, plain, ('#skF_1'('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_13071, c_13332])).
% 11.94/4.67  tff(c_34, plain, (![A_22]: (~v1_xboole_0('#skF_1'(A_22)) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_105])).
% 11.94/4.67  tff(c_13353, plain, (~v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_13336, c_34])).
% 11.94/4.67  tff(c_13366, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_13071, c_13353])).
% 11.94/4.67  tff(c_13368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_13366])).
% 11.94/4.67  tff(c_13370, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_96])).
% 11.94/4.67  tff(c_6, plain, (![A_4]: (k1_subset_1(A_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.94/4.67  tff(c_10, plain, (![A_6]: (m1_subset_1(k1_subset_1(A_6), k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.94/4.67  tff(c_107, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10])).
% 11.94/4.67  tff(c_13378, plain, (![A_590, B_591]: (r1_tarski(A_590, B_591) | ~m1_subset_1(A_590, k1_zfmisc_1(B_591)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.94/4.67  tff(c_13389, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(resolution, [status(thm)], [c_107, c_13378])).
% 11.94/4.67  tff(c_2, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.94/4.67  tff(c_13398, plain, (![B_596, A_597]: (~r1_xboole_0(B_596, A_597) | ~r1_tarski(B_596, A_597) | v1_xboole_0(B_596))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.94/4.67  tff(c_13403, plain, (![A_598]: (~r1_tarski(A_598, k1_xboole_0) | v1_xboole_0(A_598))), inference(resolution, [status(thm)], [c_2, c_13398])).
% 11.94/4.67  tff(c_13412, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_13389, c_13403])).
% 11.94/4.67  tff(c_16, plain, (![A_10]: (k3_subset_1(A_10, k1_subset_1(A_10))=k2_subset_1(A_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.94/4.67  tff(c_104, plain, (![A_10]: (k3_subset_1(A_10, k1_subset_1(A_10))=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_16])).
% 11.94/4.67  tff(c_108, plain, (![A_10]: (k3_subset_1(A_10, k1_xboole_0)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_104])).
% 11.94/4.67  tff(c_13490, plain, (![A_609, B_610]: (k3_subset_1(A_609, k3_subset_1(A_609, B_610))=B_610 | ~m1_subset_1(B_610, k1_zfmisc_1(A_609)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.94/4.67  tff(c_13496, plain, (![A_6]: (k3_subset_1(A_6, k3_subset_1(A_6, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_107, c_13490])).
% 11.94/4.67  tff(c_13502, plain, (![A_6]: (k3_subset_1(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_108, c_13496])).
% 11.94/4.67  tff(c_19170, plain, (![A_954, B_955]: (k2_pre_topc(A_954, B_955)=B_955 | ~v4_pre_topc(B_955, A_954) | ~m1_subset_1(B_955, k1_zfmisc_1(u1_struct_0(A_954))) | ~l1_pre_topc(A_954))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.94/4.67  tff(c_19194, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5' | ~v4_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_86, c_19170])).
% 11.94/4.67  tff(c_19203, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5' | ~v4_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_19194])).
% 11.94/4.67  tff(c_19204, plain, (~v4_pre_topc('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_19203])).
% 11.94/4.67  tff(c_13872, plain, (![A_658, B_659]: (k2_pre_topc(A_658, B_659)=B_659 | ~v4_pre_topc(B_659, A_658) | ~m1_subset_1(B_659, k1_zfmisc_1(u1_struct_0(A_658))) | ~l1_pre_topc(A_658))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.94/4.67  tff(c_13896, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5' | ~v4_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_86, c_13872])).
% 11.94/4.67  tff(c_13905, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5' | ~v4_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_13896])).
% 11.94/4.67  tff(c_13906, plain, (~v4_pre_topc('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_13905])).
% 11.94/4.67  tff(c_13388, plain, (![A_7]: (r1_tarski(A_7, A_7))), inference(resolution, [status(thm)], [c_103, c_13378])).
% 11.94/4.67  tff(c_15290, plain, (![A_740, B_741]: (v1_pre_topc('#skF_2'(A_740, B_741)) | ~m1_subset_1(B_741, k1_zfmisc_1(u1_struct_0(A_740))) | v1_xboole_0(B_741) | ~l1_pre_topc(A_740) | v2_struct_0(A_740))), inference(cnfTransformation, [status(thm)], [f_201])).
% 11.94/4.67  tff(c_15314, plain, (v1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_86, c_15290])).
% 11.94/4.67  tff(c_15324, plain, (v1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_15314])).
% 11.94/4.67  tff(c_15325, plain, (v1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_94, c_15324])).
% 11.94/4.67  tff(c_15326, plain, (v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_15325])).
% 11.94/4.67  tff(c_13414, plain, (![B_599, A_600]: (v1_subset_1(B_599, A_600) | B_599=A_600 | ~m1_subset_1(B_599, k1_zfmisc_1(A_600)))), inference(cnfTransformation, [status(thm)], [f_170])).
% 11.94/4.67  tff(c_13427, plain, (![A_17, B_18]: (v1_subset_1(A_17, B_18) | B_18=A_17 | ~r1_tarski(A_17, B_18))), inference(resolution, [status(thm)], [c_24, c_13414])).
% 11.94/4.67  tff(c_13453, plain, (![B_605, A_606]: (~v1_subset_1(B_605, A_606) | ~m1_subset_1(B_605, k1_zfmisc_1(A_606)) | ~v1_xboole_0(A_606))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.94/4.67  tff(c_13472, plain, (![A_607]: (~v1_subset_1(k1_xboole_0, A_607) | ~v1_xboole_0(A_607))), inference(resolution, [status(thm)], [c_107, c_13453])).
% 11.94/4.67  tff(c_13476, plain, (![B_18]: (~v1_xboole_0(B_18) | k1_xboole_0=B_18 | ~r1_tarski(k1_xboole_0, B_18))), inference(resolution, [status(thm)], [c_13427, c_13472])).
% 11.94/4.67  tff(c_13482, plain, (![B_18]: (~v1_xboole_0(B_18) | k1_xboole_0=B_18)), inference(demodulation, [status(thm), theory('equality')], [c_13389, c_13476])).
% 11.94/4.67  tff(c_15330, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_15326, c_13482])).
% 11.94/4.67  tff(c_15343, plain, (![A_10]: (k3_subset_1(A_10, '#skF_5')=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_15330, c_108])).
% 11.94/4.67  tff(c_13369, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_96])).
% 11.94/4.67  tff(c_13465, plain, (~v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_86, c_13453])).
% 11.94/4.67  tff(c_13471, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_13369, c_13465])).
% 11.94/4.67  tff(c_13503, plain, (k3_subset_1(u1_struct_0('#skF_4'), k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_86, c_13490])).
% 11.94/4.67  tff(c_13738, plain, (![A_636, B_637]: (~v1_xboole_0(k3_subset_1(A_636, B_637)) | ~m1_subset_1(B_637, k1_zfmisc_1(A_636)) | ~v1_subset_1(B_637, A_636) | v1_xboole_0(A_636))), inference(cnfTransformation, [status(thm)], [f_180])).
% 11.94/4.67  tff(c_13773, plain, (![B_638, A_639]: (~v1_xboole_0(k3_subset_1(B_638, A_639)) | ~v1_subset_1(A_639, B_638) | v1_xboole_0(B_638) | ~r1_tarski(A_639, B_638))), inference(resolution, [status(thm)], [c_24, c_13738])).
% 11.94/4.67  tff(c_13779, plain, (~v1_xboole_0('#skF_5') | ~v1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~r1_tarski(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), u1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_13503, c_13773])).
% 11.94/4.67  tff(c_13786, plain, (~v1_xboole_0('#skF_5') | ~v1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), u1_struct_0('#skF_4')) | ~r1_tarski(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_13471, c_13779])).
% 11.94/4.67  tff(c_13792, plain, (~r1_tarski(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_13786])).
% 11.94/4.67  tff(c_15463, plain, (~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_15343, c_13792])).
% 11.94/4.67  tff(c_15468, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13388, c_15463])).
% 11.94/4.67  tff(c_15470, plain, (~v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_15325])).
% 11.94/4.67  tff(c_15510, plain, (![A_751, B_752]: (m1_pre_topc('#skF_2'(A_751, B_752), A_751) | ~m1_subset_1(B_752, k1_zfmisc_1(u1_struct_0(A_751))) | v1_xboole_0(B_752) | ~l1_pre_topc(A_751) | v2_struct_0(A_751))), inference(cnfTransformation, [status(thm)], [f_201])).
% 11.94/4.67  tff(c_15527, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_86, c_15510])).
% 11.94/4.67  tff(c_15537, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_15527])).
% 11.94/4.67  tff(c_15538, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_94, c_15470, c_15537])).
% 11.94/4.67  tff(c_15719, plain, (![A_773, B_774]: (u1_struct_0('#skF_2'(A_773, B_774))=B_774 | ~m1_subset_1(B_774, k1_zfmisc_1(u1_struct_0(A_773))) | v1_xboole_0(B_774) | ~l1_pre_topc(A_773) | v2_struct_0(A_773))), inference(cnfTransformation, [status(thm)], [f_201])).
% 11.94/4.67  tff(c_15743, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_86, c_15719])).
% 11.94/4.67  tff(c_15753, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_15743])).
% 11.94/4.67  tff(c_15754, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_94, c_15470, c_15753])).
% 11.94/4.67  tff(c_16442, plain, (![B_798, A_799]: (v4_pre_topc(u1_struct_0(B_798), A_799) | ~v1_borsuk_1(B_798, A_799) | ~m1_subset_1(u1_struct_0(B_798), k1_zfmisc_1(u1_struct_0(A_799))) | ~m1_pre_topc(B_798, A_799) | ~l1_pre_topc(A_799) | ~v2_pre_topc(A_799))), inference(cnfTransformation, [status(thm)], [f_123])).
% 11.94/4.67  tff(c_16541, plain, (![B_806, A_807]: (v4_pre_topc(u1_struct_0(B_806), A_807) | ~v1_borsuk_1(B_806, A_807) | ~v2_pre_topc(A_807) | ~m1_pre_topc(B_806, A_807) | ~l1_pre_topc(A_807))), inference(resolution, [status(thm)], [c_44, c_16442])).
% 11.94/4.67  tff(c_16696, plain, (![A_819]: (v4_pre_topc('#skF_5', A_819) | ~v1_borsuk_1('#skF_2'('#skF_4', '#skF_5'), A_819) | ~v2_pre_topc(A_819) | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_819) | ~l1_pre_topc(A_819))), inference(superposition, [status(thm), theory('equality')], [c_15754, c_16541])).
% 11.94/4.67  tff(c_17929, plain, (![A_882]: (v4_pre_topc('#skF_5', A_882) | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_882) | ~l1_pre_topc(A_882) | ~v1_tdlat_3(A_882) | ~v2_pre_topc(A_882) | v2_struct_0(A_882))), inference(resolution, [status(thm)], [c_52, c_16696])).
% 11.94/4.67  tff(c_17932, plain, (v4_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v1_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_15538, c_17929])).
% 11.94/4.67  tff(c_17935, plain, (v4_pre_topc('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_17932])).
% 11.94/4.67  tff(c_17937, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_13906, c_17935])).
% 11.94/4.67  tff(c_17938, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_13905])).
% 11.94/4.67  tff(c_17984, plain, (![A_888, B_889]: (k2_pre_topc(A_888, B_889)=u1_struct_0(A_888) | ~v1_tops_1(B_889, A_888) | ~m1_subset_1(B_889, k1_zfmisc_1(u1_struct_0(A_888))) | ~l1_pre_topc(A_888))), inference(cnfTransformation, [status(thm)], [f_163])).
% 11.94/4.67  tff(c_18008, plain, (k2_pre_topc('#skF_4', '#skF_5')=u1_struct_0('#skF_4') | ~v1_tops_1('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_86, c_17984])).
% 11.94/4.67  tff(c_18017, plain, (u1_struct_0('#skF_4')='#skF_5' | ~v1_tops_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_17938, c_18008])).
% 11.94/4.67  tff(c_18018, plain, (~v1_tops_1('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_18017])).
% 11.94/4.67  tff(c_13805, plain, (![B_648, A_649]: (v3_pre_topc(B_648, A_649) | ~m1_subset_1(B_648, k1_zfmisc_1(u1_struct_0(A_649))) | ~v1_tdlat_3(A_649) | ~l1_pre_topc(A_649) | ~v2_pre_topc(A_649))), inference(cnfTransformation, [status(thm)], [f_212])).
% 11.94/4.67  tff(c_13829, plain, (v3_pre_topc('#skF_5', '#skF_4') | ~v1_tdlat_3('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_86, c_13805])).
% 11.94/4.67  tff(c_13838, plain, (v3_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_90, c_13829])).
% 11.94/4.67  tff(c_19092, plain, (![B_946, A_947]: (v1_tops_1(B_946, A_947) | ~v3_tex_2(B_946, A_947) | ~v3_pre_topc(B_946, A_947) | ~m1_subset_1(B_946, k1_zfmisc_1(u1_struct_0(A_947))) | ~l1_pre_topc(A_947) | ~v2_pre_topc(A_947) | v2_struct_0(A_947))), inference(cnfTransformation, [status(thm)], [f_257])).
% 11.94/4.67  tff(c_19125, plain, (v1_tops_1('#skF_5', '#skF_4') | ~v3_tex_2('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_86, c_19092])).
% 11.94/4.67  tff(c_19136, plain, (v1_tops_1('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_13838, c_13370, c_19125])).
% 11.94/4.67  tff(c_19138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_18018, c_19136])).
% 11.94/4.67  tff(c_19139, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_18017])).
% 11.94/4.67  tff(c_19141, plain, (~r1_tarski(k3_subset_1('#skF_5', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_19139, c_19139, c_13792])).
% 11.94/4.67  tff(c_19150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13389, c_13502, c_19141])).
% 11.94/4.67  tff(c_19151, plain, (~v1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), u1_struct_0('#skF_4')) | ~v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_13786])).
% 11.94/4.67  tff(c_19157, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_19151])).
% 11.94/4.67  tff(c_20755, plain, (![A_1071, B_1072]: (m1_pre_topc('#skF_2'(A_1071, B_1072), A_1071) | ~m1_subset_1(B_1072, k1_zfmisc_1(u1_struct_0(A_1071))) | v1_xboole_0(B_1072) | ~l1_pre_topc(A_1071) | v2_struct_0(A_1071))), inference(cnfTransformation, [status(thm)], [f_201])).
% 11.94/4.67  tff(c_20772, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_86, c_20755])).
% 11.94/4.67  tff(c_20782, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_20772])).
% 11.94/4.67  tff(c_20783, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_94, c_19157, c_20782])).
% 11.94/4.67  tff(c_20881, plain, (![A_1081, B_1082]: (u1_struct_0('#skF_2'(A_1081, B_1082))=B_1082 | ~m1_subset_1(B_1082, k1_zfmisc_1(u1_struct_0(A_1081))) | v1_xboole_0(B_1082) | ~l1_pre_topc(A_1081) | v2_struct_0(A_1081))), inference(cnfTransformation, [status(thm)], [f_201])).
% 11.94/4.67  tff(c_20905, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_86, c_20881])).
% 11.94/4.67  tff(c_20915, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_20905])).
% 11.94/4.67  tff(c_20916, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_94, c_19157, c_20915])).
% 11.94/4.67  tff(c_21302, plain, (![B_1090, A_1091]: (v4_pre_topc(u1_struct_0(B_1090), A_1091) | ~v1_borsuk_1(B_1090, A_1091) | ~m1_subset_1(u1_struct_0(B_1090), k1_zfmisc_1(u1_struct_0(A_1091))) | ~m1_pre_topc(B_1090, A_1091) | ~l1_pre_topc(A_1091) | ~v2_pre_topc(A_1091))), inference(cnfTransformation, [status(thm)], [f_123])).
% 11.94/4.67  tff(c_21533, plain, (![B_1095, A_1096]: (v4_pre_topc(u1_struct_0(B_1095), A_1096) | ~v1_borsuk_1(B_1095, A_1096) | ~v2_pre_topc(A_1096) | ~m1_pre_topc(B_1095, A_1096) | ~l1_pre_topc(A_1096))), inference(resolution, [status(thm)], [c_44, c_21302])).
% 11.94/4.67  tff(c_23245, plain, (![A_1169]: (v4_pre_topc('#skF_5', A_1169) | ~v1_borsuk_1('#skF_2'('#skF_4', '#skF_5'), A_1169) | ~v2_pre_topc(A_1169) | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_1169) | ~l1_pre_topc(A_1169))), inference(superposition, [status(thm), theory('equality')], [c_20916, c_21533])).
% 11.94/4.67  tff(c_23255, plain, (![A_1170]: (v4_pre_topc('#skF_5', A_1170) | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_1170) | ~l1_pre_topc(A_1170) | ~v1_tdlat_3(A_1170) | ~v2_pre_topc(A_1170) | v2_struct_0(A_1170))), inference(resolution, [status(thm)], [c_52, c_23245])).
% 11.94/4.67  tff(c_23258, plain, (v4_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v1_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_20783, c_23255])).
% 11.94/4.67  tff(c_23261, plain, (v4_pre_topc('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_23258])).
% 11.94/4.67  tff(c_23263, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_19204, c_23261])).
% 11.94/4.67  tff(c_23264, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_19203])).
% 11.94/4.67  tff(c_23345, plain, (![A_1181, B_1182]: (k2_pre_topc(A_1181, B_1182)=u1_struct_0(A_1181) | ~v1_tops_1(B_1182, A_1181) | ~m1_subset_1(B_1182, k1_zfmisc_1(u1_struct_0(A_1181))) | ~l1_pre_topc(A_1181))), inference(cnfTransformation, [status(thm)], [f_163])).
% 11.94/4.67  tff(c_23369, plain, (k2_pre_topc('#skF_4', '#skF_5')=u1_struct_0('#skF_4') | ~v1_tops_1('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_86, c_23345])).
% 11.94/4.67  tff(c_23378, plain, (u1_struct_0('#skF_4')='#skF_5' | ~v1_tops_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_23264, c_23369])).
% 11.94/4.67  tff(c_23379, plain, (~v1_tops_1('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_23378])).
% 11.94/4.67  tff(c_23309, plain, (![B_1177, A_1178]: (v3_pre_topc(B_1177, A_1178) | ~m1_subset_1(B_1177, k1_zfmisc_1(u1_struct_0(A_1178))) | ~v1_tdlat_3(A_1178) | ~l1_pre_topc(A_1178) | ~v2_pre_topc(A_1178))), inference(cnfTransformation, [status(thm)], [f_212])).
% 11.94/4.67  tff(c_23333, plain, (v3_pre_topc('#skF_5', '#skF_4') | ~v1_tdlat_3('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_86, c_23309])).
% 11.94/4.67  tff(c_23342, plain, (v3_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_90, c_23333])).
% 11.94/4.67  tff(c_24559, plain, (![B_1250, A_1251]: (v1_tops_1(B_1250, A_1251) | ~v3_tex_2(B_1250, A_1251) | ~v3_pre_topc(B_1250, A_1251) | ~m1_subset_1(B_1250, k1_zfmisc_1(u1_struct_0(A_1251))) | ~l1_pre_topc(A_1251) | ~v2_pre_topc(A_1251) | v2_struct_0(A_1251))), inference(cnfTransformation, [status(thm)], [f_257])).
% 11.94/4.67  tff(c_24592, plain, (v1_tops_1('#skF_5', '#skF_4') | ~v3_tex_2('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_86, c_24559])).
% 11.94/4.67  tff(c_24603, plain, (v1_tops_1('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_23342, c_13370, c_24592])).
% 11.94/4.67  tff(c_24605, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_23379, c_24603])).
% 11.94/4.67  tff(c_24606, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_23378])).
% 11.94/4.67  tff(c_13759, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5')) | ~v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_86, c_13738])).
% 11.94/4.67  tff(c_13771, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_13369, c_13759])).
% 11.94/4.67  tff(c_13772, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_13471, c_13771])).
% 11.94/4.67  tff(c_24610, plain, (~v1_xboole_0(k3_subset_1('#skF_5', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_24606, c_13772])).
% 11.94/4.67  tff(c_24620, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13412, c_13502, c_24610])).
% 11.94/4.67  tff(c_24622, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_19151])).
% 11.94/4.67  tff(c_24626, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_24622, c_13482])).
% 11.94/4.67  tff(c_24648, plain, (![A_6]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_24626, c_107])).
% 11.94/4.67  tff(c_25216, plain, (![B_1313, A_1314]: (~v3_tex_2(B_1313, A_1314) | ~m1_subset_1(B_1313, k1_zfmisc_1(u1_struct_0(A_1314))) | ~v1_xboole_0(B_1313) | ~l1_pre_topc(A_1314) | ~v2_pre_topc(A_1314) | v2_struct_0(A_1314))), inference(cnfTransformation, [status(thm)], [f_241])).
% 11.94/4.67  tff(c_25220, plain, (![A_1314]: (~v3_tex_2('#skF_5', A_1314) | ~v1_xboole_0('#skF_5') | ~l1_pre_topc(A_1314) | ~v2_pre_topc(A_1314) | v2_struct_0(A_1314))), inference(resolution, [status(thm)], [c_24648, c_25216])).
% 11.94/4.67  tff(c_25246, plain, (![A_1315]: (~v3_tex_2('#skF_5', A_1315) | ~l1_pre_topc(A_1315) | ~v2_pre_topc(A_1315) | v2_struct_0(A_1315))), inference(demodulation, [status(thm), theory('equality')], [c_24622, c_25220])).
% 11.94/4.67  tff(c_25249, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_13370, c_25246])).
% 11.94/4.67  tff(c_25252, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_25249])).
% 11.94/4.67  tff(c_25254, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_25252])).
% 11.94/4.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.94/4.67  
% 11.94/4.67  Inference rules
% 11.94/4.67  ----------------------
% 11.94/4.67  #Ref     : 0
% 11.94/4.67  #Sup     : 5773
% 11.94/4.67  #Fact    : 0
% 11.94/4.67  #Define  : 0
% 11.94/4.68  #Split   : 51
% 11.94/4.68  #Chain   : 0
% 11.94/4.68  #Close   : 0
% 11.94/4.68  
% 11.94/4.68  Ordering : KBO
% 11.94/4.68  
% 11.94/4.68  Simplification rules
% 11.94/4.68  ----------------------
% 11.94/4.68  #Subsume      : 1253
% 11.94/4.68  #Demod        : 3150
% 11.94/4.68  #Tautology    : 1084
% 11.94/4.68  #SimpNegUnit  : 885
% 11.94/4.68  #BackRed      : 104
% 11.94/4.68  
% 11.94/4.68  #Partial instantiations: 0
% 11.94/4.68  #Strategies tried      : 1
% 11.94/4.68  
% 11.94/4.68  Timing (in seconds)
% 11.94/4.68  ----------------------
% 11.94/4.68  Preprocessing        : 0.40
% 11.94/4.68  Parsing              : 0.22
% 11.94/4.68  CNF conversion       : 0.03
% 11.94/4.68  Main loop            : 3.43
% 11.94/4.68  Inferencing          : 1.06
% 11.94/4.68  Reduction            : 1.18
% 11.94/4.68  Demodulation         : 0.81
% 11.94/4.68  BG Simplification    : 0.12
% 11.94/4.68  Subsumption          : 0.81
% 11.94/4.68  Abstraction          : 0.13
% 11.94/4.68  MUC search           : 0.00
% 11.94/4.68  Cooper               : 0.00
% 11.94/4.68  Total                : 3.93
% 11.94/4.68  Index Insertion      : 0.00
% 11.94/4.68  Index Deletion       : 0.00
% 11.94/4.68  Index Matching       : 0.00
% 11.94/4.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
