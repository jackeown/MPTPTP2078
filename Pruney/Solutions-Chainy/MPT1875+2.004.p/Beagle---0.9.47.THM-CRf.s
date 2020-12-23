%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:46 EST 2020

% Result     : Theorem 5.72s
% Output     : CNFRefutation 6.02s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 524 expanded)
%              Number of leaves         :   43 ( 197 expanded)
%              Depth                    :   14
%              Number of atoms          :  293 (1533 expanded)
%              Number of equality atoms :   45 ( 110 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > v1_tsep_1 > v1_borsuk_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v1_borsuk_1,type,(
    v1_borsuk_1: ( $i * $i ) > $o )).

tff(f_173,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_119,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tsep_1)).

tff(f_158,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r1_tarski(C,B)
                 => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_52,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_98,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_tdlat_3)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_139,axiom,(
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

tff(c_72,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_62,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_70,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_66,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_794,plain,(
    ! [A_167,B_168] :
      ( v1_pre_topc('#skF_2'(A_167,B_168))
      | ~ m1_subset_1(B_168,k1_zfmisc_1(u1_struct_0(A_167)))
      | v1_xboole_0(B_168)
      | ~ l1_pre_topc(A_167)
      | v2_struct_0(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_804,plain,
    ( v1_pre_topc('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_794])).

tff(c_813,plain,
    ( v1_pre_topc('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_804])).

tff(c_814,plain,
    ( v1_pre_topc('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_813])).

tff(c_816,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_814])).

tff(c_1460,plain,(
    ! [A_200,B_201] :
      ( r1_tarski('#skF_3'(A_200,B_201),B_201)
      | v2_tex_2(B_201,A_200)
      | ~ m1_subset_1(B_201,k1_zfmisc_1(u1_struct_0(A_200)))
      | ~ l1_pre_topc(A_200)
      | ~ v2_pre_topc(A_200)
      | v2_struct_0(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_1467,plain,
    ( r1_tarski('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_1460])).

tff(c_1475,plain,
    ( r1_tarski('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v2_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_1467])).

tff(c_1476,plain,(
    r1_tarski('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_62,c_1475])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_20,plain,(
    ! [A_15] : k2_subset_1(A_15) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_22,plain,(
    ! [A_16] : m1_subset_1(k2_subset_1(A_16),k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_73,plain,(
    ! [A_16] : m1_subset_1(A_16,k1_zfmisc_1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_180,plain,(
    ! [C_78,B_79,A_80] :
      ( ~ v1_xboole_0(C_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(C_78))
      | ~ r2_hidden(A_80,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_190,plain,(
    ! [A_81,A_82] :
      ( ~ v1_xboole_0(A_81)
      | ~ r2_hidden(A_82,A_81) ) ),
    inference(resolution,[status(thm)],[c_73,c_180])).

tff(c_203,plain,(
    ! [A_85,B_86] :
      ( ~ v1_xboole_0(A_85)
      | r1_tarski(A_85,B_86) ) ),
    inference(resolution,[status(thm)],[c_8,c_190])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( B_9 = A_8
      | ~ r1_tarski(B_9,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_213,plain,(
    ! [B_86,A_85] :
      ( B_86 = A_85
      | ~ r1_tarski(B_86,A_85)
      | ~ v1_xboole_0(A_85) ) ),
    inference(resolution,[status(thm)],[c_203,c_10])).

tff(c_1492,plain,
    ( '#skF_3'('#skF_4','#skF_5') = '#skF_5'
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1476,c_213])).

tff(c_1512,plain,(
    '#skF_3'('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_816,c_1492])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_214,plain,(
    ! [A_85,B_86] :
      ( k3_xboole_0(A_85,B_86) = A_85
      | ~ v1_xboole_0(A_85) ) ),
    inference(resolution,[status(thm)],[c_203,c_16])).

tff(c_830,plain,(
    ! [B_169] : k3_xboole_0('#skF_5',B_169) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_816,c_214])).

tff(c_864,plain,(
    ! [A_1] : k3_xboole_0(A_1,'#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_830])).

tff(c_194,plain,(
    ! [A_3,B_4] :
      ( ~ v1_xboole_0(A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_190])).

tff(c_28,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_215,plain,(
    ! [A_87,B_88,C_89] :
      ( k9_subset_1(A_87,B_88,C_89) = k3_xboole_0(B_88,C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_364,plain,(
    ! [B_113,B_114,A_115] :
      ( k9_subset_1(B_113,B_114,A_115) = k3_xboole_0(B_114,A_115)
      | ~ r1_tarski(A_115,B_113) ) ),
    inference(resolution,[status(thm)],[c_28,c_215])).

tff(c_374,plain,(
    ! [B_4,B_114,A_3] :
      ( k9_subset_1(B_4,B_114,A_3) = k3_xboole_0(B_114,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(resolution,[status(thm)],[c_194,c_364])).

tff(c_826,plain,(
    ! [B_4,B_114] : k9_subset_1(B_4,B_114,'#skF_5') = k3_xboole_0(B_114,'#skF_5') ),
    inference(resolution,[status(thm)],[c_816,c_374])).

tff(c_1023,plain,(
    ! [B_4,B_114] : k9_subset_1(B_4,B_114,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_864,c_826])).

tff(c_257,plain,(
    ! [A_101,C_102,B_103] :
      ( k9_subset_1(A_101,C_102,B_103) = k9_subset_1(A_101,B_103,C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(A_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_396,plain,(
    ! [B_122,B_123,A_124] :
      ( k9_subset_1(B_122,B_123,A_124) = k9_subset_1(B_122,A_124,B_123)
      | ~ r1_tarski(A_124,B_122) ) ),
    inference(resolution,[status(thm)],[c_28,c_257])).

tff(c_406,plain,(
    ! [B_4,B_123,A_3] :
      ( k9_subset_1(B_4,B_123,A_3) = k9_subset_1(B_4,A_3,B_123)
      | ~ v1_xboole_0(A_3) ) ),
    inference(resolution,[status(thm)],[c_194,c_396])).

tff(c_825,plain,(
    ! [B_4,B_123] : k9_subset_1(B_4,B_123,'#skF_5') = k9_subset_1(B_4,'#skF_5',B_123) ),
    inference(resolution,[status(thm)],[c_816,c_406])).

tff(c_1072,plain,(
    ! [B_4,B_123] : k9_subset_1(B_4,'#skF_5',B_123) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1023,c_825])).

tff(c_2249,plain,(
    ! [A_241,B_242] :
      ( k9_subset_1(u1_struct_0(A_241),B_242,k2_pre_topc(A_241,'#skF_3'(A_241,B_242))) != '#skF_3'(A_241,B_242)
      | v2_tex_2(B_242,A_241)
      | ~ m1_subset_1(B_242,k1_zfmisc_1(u1_struct_0(A_241)))
      | ~ l1_pre_topc(A_241)
      | ~ v2_pre_topc(A_241)
      | v2_struct_0(A_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_2263,plain,
    ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4','#skF_5')) != '#skF_3'('#skF_4','#skF_5')
    | v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1512,c_2249])).

tff(c_2283,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_1512,c_1072,c_2263])).

tff(c_2285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_62,c_2283])).

tff(c_2287,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_814])).

tff(c_2655,plain,(
    ! [A_259,B_260] :
      ( m1_pre_topc('#skF_2'(A_259,B_260),A_259)
      | ~ m1_subset_1(B_260,k1_zfmisc_1(u1_struct_0(A_259)))
      | v1_xboole_0(B_260)
      | ~ l1_pre_topc(A_259)
      | v2_struct_0(A_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2666,plain,
    ( m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_2655])).

tff(c_2678,plain,
    ( m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2666])).

tff(c_2679,plain,(
    m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2287,c_2678])).

tff(c_681,plain,(
    ! [A_159,B_160] :
      ( ~ v2_struct_0('#skF_2'(A_159,B_160))
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0(A_159)))
      | v1_xboole_0(B_160)
      | ~ l1_pre_topc(A_159)
      | v2_struct_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_691,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_681])).

tff(c_700,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_691])).

tff(c_701,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_700])).

tff(c_703,plain,(
    ~ v2_struct_0('#skF_2'('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_701])).

tff(c_68,plain,(
    v1_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_36,plain,(
    ! [B_31,A_29] :
      ( v1_tdlat_3(B_31)
      | ~ m1_pre_topc(B_31,A_29)
      | ~ l1_pre_topc(A_29)
      | ~ v1_tdlat_3(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2686,plain,
    ( v1_tdlat_3('#skF_2'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v1_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_2679,c_36])).

tff(c_2692,plain,
    ( v1_tdlat_3('#skF_2'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_2686])).

tff(c_2693,plain,(
    v1_tdlat_3('#skF_2'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2692])).

tff(c_2493,plain,(
    ! [A_254,B_255] :
      ( u1_struct_0('#skF_2'(A_254,B_255)) = B_255
      | ~ m1_subset_1(B_255,k1_zfmisc_1(u1_struct_0(A_254)))
      | v1_xboole_0(B_255)
      | ~ l1_pre_topc(A_254)
      | v2_struct_0(A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2503,plain,
    ( u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_2493])).

tff(c_2512,plain,
    ( u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2503])).

tff(c_2513,plain,(
    u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2287,c_2512])).

tff(c_32,plain,(
    ! [B_27,A_25] :
      ( m1_subset_1(u1_struct_0(B_27),k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ m1_pre_topc(B_27,A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2946,plain,(
    ! [B_276,A_277] :
      ( v2_tex_2(u1_struct_0(B_276),A_277)
      | ~ v1_tdlat_3(B_276)
      | ~ m1_subset_1(u1_struct_0(B_276),k1_zfmisc_1(u1_struct_0(A_277)))
      | ~ m1_pre_topc(B_276,A_277)
      | v2_struct_0(B_276)
      | ~ l1_pre_topc(A_277)
      | v2_struct_0(A_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_3686,plain,(
    ! [B_309,A_310] :
      ( v2_tex_2(u1_struct_0(B_309),A_310)
      | ~ v1_tdlat_3(B_309)
      | v2_struct_0(B_309)
      | v2_struct_0(A_310)
      | ~ m1_pre_topc(B_309,A_310)
      | ~ l1_pre_topc(A_310) ) ),
    inference(resolution,[status(thm)],[c_32,c_2946])).

tff(c_3696,plain,(
    ! [A_310] :
      ( v2_tex_2('#skF_5',A_310)
      | ~ v1_tdlat_3('#skF_2'('#skF_4','#skF_5'))
      | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
      | v2_struct_0(A_310)
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_310)
      | ~ l1_pre_topc(A_310) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2513,c_3686])).

tff(c_3699,plain,(
    ! [A_310] :
      ( v2_tex_2('#skF_5',A_310)
      | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
      | v2_struct_0(A_310)
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_310)
      | ~ l1_pre_topc(A_310) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2693,c_3696])).

tff(c_3757,plain,(
    ! [A_312] :
      ( v2_tex_2('#skF_5',A_312)
      | v2_struct_0(A_312)
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_312)
      | ~ l1_pre_topc(A_312) ) ),
    inference(negUnitSimplification,[status(thm)],[c_703,c_3699])).

tff(c_3760,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_2679,c_3757])).

tff(c_3763,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3760])).

tff(c_3765,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_62,c_3763])).

tff(c_3766,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_701])).

tff(c_4379,plain,(
    ! [A_346,B_347] :
      ( r1_tarski('#skF_3'(A_346,B_347),B_347)
      | v2_tex_2(B_347,A_346)
      | ~ m1_subset_1(B_347,k1_zfmisc_1(u1_struct_0(A_346)))
      | ~ l1_pre_topc(A_346)
      | ~ v2_pre_topc(A_346)
      | v2_struct_0(A_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_4386,plain,
    ( r1_tarski('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_4379])).

tff(c_4394,plain,
    ( r1_tarski('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v2_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_4386])).

tff(c_4395,plain,(
    r1_tarski('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_62,c_4394])).

tff(c_4409,plain,
    ( '#skF_3'('#skF_4','#skF_5') = '#skF_5'
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4395,c_213])).

tff(c_4426,plain,(
    '#skF_3'('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3766,c_4409])).

tff(c_3803,plain,(
    ! [B_315] : k3_xboole_0('#skF_5',B_315) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3766,c_214])).

tff(c_3837,plain,(
    ! [A_1] : k3_xboole_0(A_1,'#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3803])).

tff(c_3799,plain,(
    ! [B_4,B_114] : k9_subset_1(B_4,B_114,'#skF_5') = k3_xboole_0(B_114,'#skF_5') ),
    inference(resolution,[status(thm)],[c_3766,c_374])).

tff(c_3981,plain,(
    ! [B_4,B_114] : k9_subset_1(B_4,B_114,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3837,c_3799])).

tff(c_3798,plain,(
    ! [B_4,B_123] : k9_subset_1(B_4,B_123,'#skF_5') = k9_subset_1(B_4,'#skF_5',B_123) ),
    inference(resolution,[status(thm)],[c_3766,c_406])).

tff(c_4018,plain,(
    ! [B_4,B_123] : k9_subset_1(B_4,'#skF_5',B_123) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3981,c_3798])).

tff(c_5084,plain,(
    ! [A_380,B_381] :
      ( k9_subset_1(u1_struct_0(A_380),B_381,k2_pre_topc(A_380,'#skF_3'(A_380,B_381))) != '#skF_3'(A_380,B_381)
      | v2_tex_2(B_381,A_380)
      | ~ m1_subset_1(B_381,k1_zfmisc_1(u1_struct_0(A_380)))
      | ~ l1_pre_topc(A_380)
      | ~ v2_pre_topc(A_380)
      | v2_struct_0(A_380) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_5098,plain,
    ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4','#skF_5')) != '#skF_3'('#skF_4','#skF_5')
    | v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4426,c_5084])).

tff(c_5118,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_4426,c_4018,c_5098])).

tff(c_5120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_62,c_5118])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.09  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.09/0.29  % Computer   : n018.cluster.edu
% 0.09/0.29  % Model      : x86_64 x86_64
% 0.09/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.29  % Memory     : 8042.1875MB
% 0.09/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.29  % CPULimit   : 60
% 0.09/0.29  % DateTime   : Tue Dec  1 20:27:12 EST 2020
% 0.09/0.29  % CPUTime    : 
% 0.09/0.30  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.72/2.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.72/2.03  
% 5.72/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.72/2.03  %$ v2_tex_2 > v1_tsep_1 > v1_borsuk_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 5.72/2.03  
% 5.72/2.03  %Foreground sorts:
% 5.72/2.03  
% 5.72/2.03  
% 5.72/2.03  %Background operators:
% 5.72/2.03  
% 5.72/2.03  
% 5.72/2.03  %Foreground operators:
% 5.72/2.03  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.72/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.72/2.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.72/2.03  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.72/2.03  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 5.72/2.03  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.72/2.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.72/2.03  tff('#skF_5', type, '#skF_5': $i).
% 5.72/2.03  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 5.72/2.03  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 5.72/2.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.72/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.72/2.03  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 5.72/2.03  tff('#skF_4', type, '#skF_4': $i).
% 5.72/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.72/2.03  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.72/2.03  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.72/2.03  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.72/2.03  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.72/2.03  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.72/2.03  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.72/2.03  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.72/2.03  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.72/2.03  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.72/2.03  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.72/2.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.72/2.03  tff(v1_borsuk_1, type, v1_borsuk_1: ($i * $i) > $o).
% 5.72/2.03  
% 6.02/2.05  tff(f_173, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 6.02/2.05  tff(f_119, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (?[C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) & (B = u1_struct_0(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_tsep_1)).
% 6.02/2.05  tff(f_158, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 6.02/2.05  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.02/2.05  tff(f_50, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 6.02/2.05  tff(f_52, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 6.02/2.05  tff(f_67, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 6.02/2.05  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.02/2.05  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.02/2.05  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.02/2.05  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.02/2.05  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 6.02/2.05  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 6.02/2.05  tff(f_98, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((v1_borsuk_1(B, A) & v1_tsep_1(B, A)) & v1_tdlat_3(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_tdlat_3)).
% 6.02/2.05  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 6.02/2.05  tff(f_139, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_tex_2)).
% 6.02/2.05  tff(c_72, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_173])).
% 6.02/2.05  tff(c_62, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_173])).
% 6.02/2.05  tff(c_70, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_173])).
% 6.02/2.05  tff(c_66, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_173])).
% 6.02/2.05  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_173])).
% 6.02/2.05  tff(c_794, plain, (![A_167, B_168]: (v1_pre_topc('#skF_2'(A_167, B_168)) | ~m1_subset_1(B_168, k1_zfmisc_1(u1_struct_0(A_167))) | v1_xboole_0(B_168) | ~l1_pre_topc(A_167) | v2_struct_0(A_167))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.02/2.05  tff(c_804, plain, (v1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_64, c_794])).
% 6.02/2.05  tff(c_813, plain, (v1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_804])).
% 6.02/2.05  tff(c_814, plain, (v1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_72, c_813])).
% 6.02/2.05  tff(c_816, plain, (v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_814])).
% 6.02/2.05  tff(c_1460, plain, (![A_200, B_201]: (r1_tarski('#skF_3'(A_200, B_201), B_201) | v2_tex_2(B_201, A_200) | ~m1_subset_1(B_201, k1_zfmisc_1(u1_struct_0(A_200))) | ~l1_pre_topc(A_200) | ~v2_pre_topc(A_200) | v2_struct_0(A_200))), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.02/2.05  tff(c_1467, plain, (r1_tarski('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_64, c_1460])).
% 6.02/2.05  tff(c_1475, plain, (r1_tarski('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_1467])).
% 6.02/2.05  tff(c_1476, plain, (r1_tarski('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_72, c_62, c_1475])).
% 6.02/2.05  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.02/2.05  tff(c_20, plain, (![A_15]: (k2_subset_1(A_15)=A_15)), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.02/2.05  tff(c_22, plain, (![A_16]: (m1_subset_1(k2_subset_1(A_16), k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.02/2.05  tff(c_73, plain, (![A_16]: (m1_subset_1(A_16, k1_zfmisc_1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 6.02/2.05  tff(c_180, plain, (![C_78, B_79, A_80]: (~v1_xboole_0(C_78) | ~m1_subset_1(B_79, k1_zfmisc_1(C_78)) | ~r2_hidden(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.02/2.05  tff(c_190, plain, (![A_81, A_82]: (~v1_xboole_0(A_81) | ~r2_hidden(A_82, A_81))), inference(resolution, [status(thm)], [c_73, c_180])).
% 6.02/2.05  tff(c_203, plain, (![A_85, B_86]: (~v1_xboole_0(A_85) | r1_tarski(A_85, B_86))), inference(resolution, [status(thm)], [c_8, c_190])).
% 6.02/2.05  tff(c_10, plain, (![B_9, A_8]: (B_9=A_8 | ~r1_tarski(B_9, A_8) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.02/2.05  tff(c_213, plain, (![B_86, A_85]: (B_86=A_85 | ~r1_tarski(B_86, A_85) | ~v1_xboole_0(A_85))), inference(resolution, [status(thm)], [c_203, c_10])).
% 6.02/2.05  tff(c_1492, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5' | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_1476, c_213])).
% 6.02/2.05  tff(c_1512, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_816, c_1492])).
% 6.02/2.05  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.02/2.05  tff(c_16, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.02/2.05  tff(c_214, plain, (![A_85, B_86]: (k3_xboole_0(A_85, B_86)=A_85 | ~v1_xboole_0(A_85))), inference(resolution, [status(thm)], [c_203, c_16])).
% 6.02/2.05  tff(c_830, plain, (![B_169]: (k3_xboole_0('#skF_5', B_169)='#skF_5')), inference(resolution, [status(thm)], [c_816, c_214])).
% 6.02/2.05  tff(c_864, plain, (![A_1]: (k3_xboole_0(A_1, '#skF_5')='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2, c_830])).
% 6.02/2.05  tff(c_194, plain, (![A_3, B_4]: (~v1_xboole_0(A_3) | r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_8, c_190])).
% 6.02/2.05  tff(c_28, plain, (![A_20, B_21]: (m1_subset_1(A_20, k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.02/2.05  tff(c_215, plain, (![A_87, B_88, C_89]: (k9_subset_1(A_87, B_88, C_89)=k3_xboole_0(B_88, C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.02/2.05  tff(c_364, plain, (![B_113, B_114, A_115]: (k9_subset_1(B_113, B_114, A_115)=k3_xboole_0(B_114, A_115) | ~r1_tarski(A_115, B_113))), inference(resolution, [status(thm)], [c_28, c_215])).
% 6.02/2.05  tff(c_374, plain, (![B_4, B_114, A_3]: (k9_subset_1(B_4, B_114, A_3)=k3_xboole_0(B_114, A_3) | ~v1_xboole_0(A_3))), inference(resolution, [status(thm)], [c_194, c_364])).
% 6.02/2.05  tff(c_826, plain, (![B_4, B_114]: (k9_subset_1(B_4, B_114, '#skF_5')=k3_xboole_0(B_114, '#skF_5'))), inference(resolution, [status(thm)], [c_816, c_374])).
% 6.02/2.05  tff(c_1023, plain, (![B_4, B_114]: (k9_subset_1(B_4, B_114, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_864, c_826])).
% 6.02/2.05  tff(c_257, plain, (![A_101, C_102, B_103]: (k9_subset_1(A_101, C_102, B_103)=k9_subset_1(A_101, B_103, C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(A_101)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.02/2.05  tff(c_396, plain, (![B_122, B_123, A_124]: (k9_subset_1(B_122, B_123, A_124)=k9_subset_1(B_122, A_124, B_123) | ~r1_tarski(A_124, B_122))), inference(resolution, [status(thm)], [c_28, c_257])).
% 6.02/2.05  tff(c_406, plain, (![B_4, B_123, A_3]: (k9_subset_1(B_4, B_123, A_3)=k9_subset_1(B_4, A_3, B_123) | ~v1_xboole_0(A_3))), inference(resolution, [status(thm)], [c_194, c_396])).
% 6.02/2.05  tff(c_825, plain, (![B_4, B_123]: (k9_subset_1(B_4, B_123, '#skF_5')=k9_subset_1(B_4, '#skF_5', B_123))), inference(resolution, [status(thm)], [c_816, c_406])).
% 6.02/2.05  tff(c_1072, plain, (![B_4, B_123]: (k9_subset_1(B_4, '#skF_5', B_123)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1023, c_825])).
% 6.02/2.05  tff(c_2249, plain, (![A_241, B_242]: (k9_subset_1(u1_struct_0(A_241), B_242, k2_pre_topc(A_241, '#skF_3'(A_241, B_242)))!='#skF_3'(A_241, B_242) | v2_tex_2(B_242, A_241) | ~m1_subset_1(B_242, k1_zfmisc_1(u1_struct_0(A_241))) | ~l1_pre_topc(A_241) | ~v2_pre_topc(A_241) | v2_struct_0(A_241))), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.02/2.05  tff(c_2263, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', '#skF_5'))!='#skF_3'('#skF_4', '#skF_5') | v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1512, c_2249])).
% 6.02/2.05  tff(c_2283, plain, (v2_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_1512, c_1072, c_2263])).
% 6.02/2.05  tff(c_2285, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_62, c_2283])).
% 6.02/2.05  tff(c_2287, plain, (~v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_814])).
% 6.02/2.05  tff(c_2655, plain, (![A_259, B_260]: (m1_pre_topc('#skF_2'(A_259, B_260), A_259) | ~m1_subset_1(B_260, k1_zfmisc_1(u1_struct_0(A_259))) | v1_xboole_0(B_260) | ~l1_pre_topc(A_259) | v2_struct_0(A_259))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.02/2.05  tff(c_2666, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_64, c_2655])).
% 6.02/2.05  tff(c_2678, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2666])).
% 6.02/2.05  tff(c_2679, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_72, c_2287, c_2678])).
% 6.02/2.05  tff(c_681, plain, (![A_159, B_160]: (~v2_struct_0('#skF_2'(A_159, B_160)) | ~m1_subset_1(B_160, k1_zfmisc_1(u1_struct_0(A_159))) | v1_xboole_0(B_160) | ~l1_pre_topc(A_159) | v2_struct_0(A_159))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.02/2.05  tff(c_691, plain, (~v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_64, c_681])).
% 6.02/2.05  tff(c_700, plain, (~v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_691])).
% 6.02/2.05  tff(c_701, plain, (~v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_72, c_700])).
% 6.02/2.05  tff(c_703, plain, (~v2_struct_0('#skF_2'('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_701])).
% 6.02/2.05  tff(c_68, plain, (v1_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_173])).
% 6.02/2.05  tff(c_36, plain, (![B_31, A_29]: (v1_tdlat_3(B_31) | ~m1_pre_topc(B_31, A_29) | ~l1_pre_topc(A_29) | ~v1_tdlat_3(A_29) | ~v2_pre_topc(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.02/2.05  tff(c_2686, plain, (v1_tdlat_3('#skF_2'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v1_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_2679, c_36])).
% 6.02/2.05  tff(c_2692, plain, (v1_tdlat_3('#skF_2'('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_2686])).
% 6.02/2.05  tff(c_2693, plain, (v1_tdlat_3('#skF_2'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_72, c_2692])).
% 6.02/2.05  tff(c_2493, plain, (![A_254, B_255]: (u1_struct_0('#skF_2'(A_254, B_255))=B_255 | ~m1_subset_1(B_255, k1_zfmisc_1(u1_struct_0(A_254))) | v1_xboole_0(B_255) | ~l1_pre_topc(A_254) | v2_struct_0(A_254))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.02/2.05  tff(c_2503, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_64, c_2493])).
% 6.02/2.05  tff(c_2512, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2503])).
% 6.02/2.05  tff(c_2513, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_72, c_2287, c_2512])).
% 6.02/2.05  tff(c_32, plain, (![B_27, A_25]: (m1_subset_1(u1_struct_0(B_27), k1_zfmisc_1(u1_struct_0(A_25))) | ~m1_pre_topc(B_27, A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.02/2.05  tff(c_2946, plain, (![B_276, A_277]: (v2_tex_2(u1_struct_0(B_276), A_277) | ~v1_tdlat_3(B_276) | ~m1_subset_1(u1_struct_0(B_276), k1_zfmisc_1(u1_struct_0(A_277))) | ~m1_pre_topc(B_276, A_277) | v2_struct_0(B_276) | ~l1_pre_topc(A_277) | v2_struct_0(A_277))), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.02/2.05  tff(c_3686, plain, (![B_309, A_310]: (v2_tex_2(u1_struct_0(B_309), A_310) | ~v1_tdlat_3(B_309) | v2_struct_0(B_309) | v2_struct_0(A_310) | ~m1_pre_topc(B_309, A_310) | ~l1_pre_topc(A_310))), inference(resolution, [status(thm)], [c_32, c_2946])).
% 6.02/2.05  tff(c_3696, plain, (![A_310]: (v2_tex_2('#skF_5', A_310) | ~v1_tdlat_3('#skF_2'('#skF_4', '#skF_5')) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | v2_struct_0(A_310) | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_310) | ~l1_pre_topc(A_310))), inference(superposition, [status(thm), theory('equality')], [c_2513, c_3686])).
% 6.02/2.05  tff(c_3699, plain, (![A_310]: (v2_tex_2('#skF_5', A_310) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | v2_struct_0(A_310) | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_310) | ~l1_pre_topc(A_310))), inference(demodulation, [status(thm), theory('equality')], [c_2693, c_3696])).
% 6.02/2.05  tff(c_3757, plain, (![A_312]: (v2_tex_2('#skF_5', A_312) | v2_struct_0(A_312) | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_312) | ~l1_pre_topc(A_312))), inference(negUnitSimplification, [status(thm)], [c_703, c_3699])).
% 6.02/2.05  tff(c_3760, plain, (v2_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_2679, c_3757])).
% 6.02/2.05  tff(c_3763, plain, (v2_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3760])).
% 6.02/2.05  tff(c_3765, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_62, c_3763])).
% 6.02/2.05  tff(c_3766, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_701])).
% 6.02/2.05  tff(c_4379, plain, (![A_346, B_347]: (r1_tarski('#skF_3'(A_346, B_347), B_347) | v2_tex_2(B_347, A_346) | ~m1_subset_1(B_347, k1_zfmisc_1(u1_struct_0(A_346))) | ~l1_pre_topc(A_346) | ~v2_pre_topc(A_346) | v2_struct_0(A_346))), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.02/2.05  tff(c_4386, plain, (r1_tarski('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_64, c_4379])).
% 6.02/2.05  tff(c_4394, plain, (r1_tarski('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_4386])).
% 6.02/2.05  tff(c_4395, plain, (r1_tarski('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_72, c_62, c_4394])).
% 6.02/2.05  tff(c_4409, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5' | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4395, c_213])).
% 6.02/2.05  tff(c_4426, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3766, c_4409])).
% 6.02/2.05  tff(c_3803, plain, (![B_315]: (k3_xboole_0('#skF_5', B_315)='#skF_5')), inference(resolution, [status(thm)], [c_3766, c_214])).
% 6.02/2.05  tff(c_3837, plain, (![A_1]: (k3_xboole_0(A_1, '#skF_5')='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2, c_3803])).
% 6.02/2.05  tff(c_3799, plain, (![B_4, B_114]: (k9_subset_1(B_4, B_114, '#skF_5')=k3_xboole_0(B_114, '#skF_5'))), inference(resolution, [status(thm)], [c_3766, c_374])).
% 6.02/2.05  tff(c_3981, plain, (![B_4, B_114]: (k9_subset_1(B_4, B_114, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3837, c_3799])).
% 6.02/2.05  tff(c_3798, plain, (![B_4, B_123]: (k9_subset_1(B_4, B_123, '#skF_5')=k9_subset_1(B_4, '#skF_5', B_123))), inference(resolution, [status(thm)], [c_3766, c_406])).
% 6.02/2.05  tff(c_4018, plain, (![B_4, B_123]: (k9_subset_1(B_4, '#skF_5', B_123)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3981, c_3798])).
% 6.02/2.05  tff(c_5084, plain, (![A_380, B_381]: (k9_subset_1(u1_struct_0(A_380), B_381, k2_pre_topc(A_380, '#skF_3'(A_380, B_381)))!='#skF_3'(A_380, B_381) | v2_tex_2(B_381, A_380) | ~m1_subset_1(B_381, k1_zfmisc_1(u1_struct_0(A_380))) | ~l1_pre_topc(A_380) | ~v2_pre_topc(A_380) | v2_struct_0(A_380))), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.02/2.05  tff(c_5098, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', '#skF_5'))!='#skF_3'('#skF_4', '#skF_5') | v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4426, c_5084])).
% 6.02/2.05  tff(c_5118, plain, (v2_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_4426, c_4018, c_5098])).
% 6.02/2.05  tff(c_5120, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_62, c_5118])).
% 6.02/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.02/2.05  
% 6.02/2.05  Inference rules
% 6.02/2.05  ----------------------
% 6.02/2.05  #Ref     : 0
% 6.02/2.05  #Sup     : 1162
% 6.02/2.05  #Fact    : 0
% 6.02/2.05  #Define  : 0
% 6.02/2.05  #Split   : 11
% 6.02/2.05  #Chain   : 0
% 6.02/2.05  #Close   : 0
% 6.02/2.05  
% 6.02/2.05  Ordering : KBO
% 6.02/2.05  
% 6.02/2.05  Simplification rules
% 6.02/2.05  ----------------------
% 6.02/2.05  #Subsume      : 339
% 6.02/2.05  #Demod        : 473
% 6.02/2.05  #Tautology    : 452
% 6.02/2.05  #SimpNegUnit  : 65
% 6.02/2.05  #BackRed      : 6
% 6.02/2.05  
% 6.02/2.05  #Partial instantiations: 0
% 6.02/2.05  #Strategies tried      : 1
% 6.02/2.05  
% 6.02/2.05  Timing (in seconds)
% 6.02/2.05  ----------------------
% 6.02/2.05  Preprocessing        : 0.35
% 6.02/2.05  Parsing              : 0.19
% 6.02/2.05  CNF conversion       : 0.02
% 6.02/2.05  Main loop            : 1.04
% 6.02/2.05  Inferencing          : 0.34
% 6.02/2.05  Reduction            : 0.34
% 6.02/2.05  Demodulation         : 0.23
% 6.02/2.05  BG Simplification    : 0.04
% 6.02/2.05  Subsumption          : 0.24
% 6.02/2.05  Abstraction          : 0.05
% 6.02/2.05  MUC search           : 0.00
% 6.02/2.05  Cooper               : 0.00
% 6.02/2.05  Total                : 1.43
% 6.02/2.05  Index Insertion      : 0.00
% 6.02/2.05  Index Deletion       : 0.00
% 6.02/2.05  Index Matching       : 0.00
% 6.02/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
