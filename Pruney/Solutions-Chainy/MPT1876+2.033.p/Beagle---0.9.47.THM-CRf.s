%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:55 EST 2020

% Result     : Theorem 8.06s
% Output     : CNFRefutation 8.06s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 508 expanded)
%              Number of leaves         :   53 ( 201 expanded)
%              Depth                    :   12
%              Number of atoms          :  355 (1870 expanded)
%              Number of equality atoms :   42 (  87 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_230,negated_conjecture,(
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

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_41,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_210,axiom,(
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

tff(f_162,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_111,axiom,(
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

tff(f_191,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_149,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_tdlat_3(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_tdlat_3)).

tff(f_117,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_tdlat_3(A)
       => v2_pre_topc(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).

tff(f_135,axiom,(
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

tff(f_89,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

tff(c_76,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_80,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_90,plain,
    ( v2_tex_2('#skF_6','#skF_5')
    | v1_zfmisc_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_98,plain,(
    v1_zfmisc_1('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_84,plain,
    ( ~ v1_zfmisc_1('#skF_6')
    | ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_101,plain,(
    ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_84])).

tff(c_72,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_347,plain,(
    ! [B_104,A_105] :
      ( r1_tarski(B_104,k2_pre_topc(A_105,B_104))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_352,plain,
    ( r1_tarski('#skF_6',k2_pre_topc('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_347])).

tff(c_356,plain,(
    r1_tarski('#skF_6',k2_pre_topc('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_352])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,B_14) = A_13
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_372,plain,(
    k3_xboole_0('#skF_6',k2_pre_topc('#skF_5','#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_356,c_18])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_205,plain,(
    ! [A_90,B_91,C_92] :
      ( k9_subset_1(A_90,B_91,C_92) = k3_xboole_0(B_91,C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(A_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_211,plain,(
    ! [B_91] : k9_subset_1(u1_struct_0('#skF_5'),B_91,'#skF_6') = k3_xboole_0(B_91,'#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_205])).

tff(c_416,plain,(
    ! [A_115,C_116,B_117] :
      ( k9_subset_1(A_115,C_116,B_117) = k9_subset_1(A_115,B_117,C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(A_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_420,plain,(
    ! [B_117] : k9_subset_1(u1_struct_0('#skF_5'),B_117,'#skF_6') = k9_subset_1(u1_struct_0('#skF_5'),'#skF_6',B_117) ),
    inference(resolution,[status(thm)],[c_72,c_416])).

tff(c_423,plain,(
    ! [B_117] : k9_subset_1(u1_struct_0('#skF_5'),'#skF_6',B_117) = k3_xboole_0(B_117,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_420])).

tff(c_14,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_169,plain,(
    ! [A_81,B_82] :
      ( r2_hidden('#skF_2'(A_81,B_82),A_81)
      | r1_tarski(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_200,plain,(
    ! [A_88,B_89] :
      ( ~ v1_xboole_0(A_88)
      | r1_tarski(A_88,B_89) ) ),
    inference(resolution,[status(thm)],[c_169,c_4])).

tff(c_212,plain,(
    ! [A_93,B_94] :
      ( k3_xboole_0(A_93,B_94) = A_93
      | ~ v1_xboole_0(A_93) ) ),
    inference(resolution,[status(thm)],[c_200,c_18])).

tff(c_215,plain,(
    ! [B_94] : k3_xboole_0(k1_xboole_0,B_94) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_212])).

tff(c_930,plain,(
    ! [A_176,B_177] :
      ( r1_tarski('#skF_4'(A_176,B_177),B_177)
      | v2_tex_2(B_177,A_176)
      | ~ m1_subset_1(B_177,k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | v2_struct_0(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_935,plain,
    ( r1_tarski('#skF_4'('#skF_5','#skF_6'),'#skF_6')
    | v2_tex_2('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_930])).

tff(c_939,plain,
    ( r1_tarski('#skF_4'('#skF_5','#skF_6'),'#skF_6')
    | v2_tex_2('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_935])).

tff(c_940,plain,(
    r1_tarski('#skF_4'('#skF_5','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_101,c_939])).

tff(c_52,plain,(
    ! [B_44,A_42] :
      ( B_44 = A_42
      | ~ r1_tarski(A_42,B_44)
      | ~ v1_zfmisc_1(B_44)
      | v1_xboole_0(B_44)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_954,plain,
    ( '#skF_4'('#skF_5','#skF_6') = '#skF_6'
    | ~ v1_zfmisc_1('#skF_6')
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_940,c_52])).

tff(c_965,plain,
    ( '#skF_4'('#skF_5','#skF_6') = '#skF_6'
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_954])).

tff(c_966,plain,
    ( '#skF_4'('#skF_5','#skF_6') = '#skF_6'
    | v1_xboole_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_965])).

tff(c_968,plain,(
    v1_xboole_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_966])).

tff(c_16,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_981,plain,(
    '#skF_4'('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_968,c_16])).

tff(c_178,plain,(
    ! [A_81,B_82] :
      ( ~ v1_xboole_0(A_81)
      | r1_tarski(A_81,B_82) ) ),
    inference(resolution,[status(thm)],[c_169,c_4])).

tff(c_26,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(A_21,k1_zfmisc_1(B_22))
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_753,plain,(
    ! [B_151,A_152] :
      ( v4_pre_topc(B_151,A_152)
      | ~ v1_xboole_0(B_151)
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_pre_topc(A_152)
      | ~ v2_pre_topc(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_896,plain,(
    ! [A_172,A_173] :
      ( v4_pre_topc(A_172,A_173)
      | ~ v1_xboole_0(A_172)
      | ~ l1_pre_topc(A_173)
      | ~ v2_pre_topc(A_173)
      | ~ r1_tarski(A_172,u1_struct_0(A_173)) ) ),
    inference(resolution,[status(thm)],[c_26,c_753])).

tff(c_914,plain,(
    ! [A_174,A_175] :
      ( v4_pre_topc(A_174,A_175)
      | ~ l1_pre_topc(A_175)
      | ~ v2_pre_topc(A_175)
      | ~ v1_xboole_0(A_174) ) ),
    inference(resolution,[status(thm)],[c_178,c_896])).

tff(c_701,plain,(
    ! [A_143,B_144] :
      ( k2_pre_topc(A_143,B_144) = B_144
      | ~ v4_pre_topc(B_144,A_143)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_851,plain,(
    ! [A_164,A_165] :
      ( k2_pre_topc(A_164,A_165) = A_165
      | ~ v4_pre_topc(A_165,A_164)
      | ~ l1_pre_topc(A_164)
      | ~ r1_tarski(A_165,u1_struct_0(A_164)) ) ),
    inference(resolution,[status(thm)],[c_26,c_701])).

tff(c_863,plain,(
    ! [A_164,A_81] :
      ( k2_pre_topc(A_164,A_81) = A_81
      | ~ v4_pre_topc(A_81,A_164)
      | ~ l1_pre_topc(A_164)
      | ~ v1_xboole_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_178,c_851])).

tff(c_1065,plain,(
    ! [A_181,A_182] :
      ( k2_pre_topc(A_181,A_182) = A_182
      | ~ l1_pre_topc(A_181)
      | ~ v2_pre_topc(A_181)
      | ~ v1_xboole_0(A_182) ) ),
    inference(resolution,[status(thm)],[c_914,c_863])).

tff(c_1067,plain,(
    ! [A_182] :
      ( k2_pre_topc('#skF_5',A_182) = A_182
      | ~ l1_pre_topc('#skF_5')
      | ~ v1_xboole_0(A_182) ) ),
    inference(resolution,[status(thm)],[c_80,c_1065])).

tff(c_1071,plain,(
    ! [A_183] :
      ( k2_pre_topc('#skF_5',A_183) = A_183
      | ~ v1_xboole_0(A_183) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1067])).

tff(c_1075,plain,(
    k2_pre_topc('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_1071])).

tff(c_2058,plain,(
    ! [A_236,B_237] :
      ( k9_subset_1(u1_struct_0(A_236),B_237,k2_pre_topc(A_236,'#skF_4'(A_236,B_237))) != '#skF_4'(A_236,B_237)
      | v2_tex_2(B_237,A_236)
      | ~ m1_subset_1(B_237,k1_zfmisc_1(u1_struct_0(A_236)))
      | ~ l1_pre_topc(A_236)
      | ~ v2_pre_topc(A_236)
      | v2_struct_0(A_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_2061,plain,
    ( k9_subset_1(u1_struct_0('#skF_5'),'#skF_6',k2_pre_topc('#skF_5',k1_xboole_0)) != '#skF_4'('#skF_5','#skF_6')
    | v2_tex_2('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_981,c_2058])).

tff(c_2075,plain,
    ( v2_tex_2('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_72,c_215,c_423,c_981,c_1075,c_2061])).

tff(c_2077,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_101,c_2075])).

tff(c_2078,plain,(
    '#skF_4'('#skF_5','#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_966])).

tff(c_3350,plain,(
    ! [A_308,B_309] :
      ( k9_subset_1(u1_struct_0(A_308),B_309,k2_pre_topc(A_308,'#skF_4'(A_308,B_309))) != '#skF_4'(A_308,B_309)
      | v2_tex_2(B_309,A_308)
      | ~ m1_subset_1(B_309,k1_zfmisc_1(u1_struct_0(A_308)))
      | ~ l1_pre_topc(A_308)
      | ~ v2_pre_topc(A_308)
      | v2_struct_0(A_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_3357,plain,
    ( k9_subset_1(u1_struct_0('#skF_5'),'#skF_6',k2_pre_topc('#skF_5','#skF_6')) != '#skF_4'('#skF_5','#skF_6')
    | v2_tex_2('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2078,c_3350])).

tff(c_3374,plain,
    ( v2_tex_2('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_72,c_372,c_2,c_423,c_2078,c_3357])).

tff(c_3376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_101,c_3374])).

tff(c_3377,plain,(
    v2_tex_2('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_5092,plain,(
    ! [A_478,B_479] :
      ( m1_pre_topc('#skF_3'(A_478,B_479),A_478)
      | ~ v2_tex_2(B_479,A_478)
      | ~ m1_subset_1(B_479,k1_zfmisc_1(u1_struct_0(A_478)))
      | v1_xboole_0(B_479)
      | ~ l1_pre_topc(A_478)
      | ~ v2_pre_topc(A_478)
      | v2_struct_0(A_478) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_5097,plain,
    ( m1_pre_topc('#skF_3'('#skF_5','#skF_6'),'#skF_5')
    | ~ v2_tex_2('#skF_6','#skF_5')
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_5092])).

tff(c_5101,plain,
    ( m1_pre_topc('#skF_3'('#skF_5','#skF_6'),'#skF_5')
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_3377,c_5097])).

tff(c_5102,plain,(
    m1_pre_topc('#skF_3'('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_74,c_5101])).

tff(c_32,plain,(
    ! [B_29,A_27] :
      ( l1_pre_topc(B_29)
      | ~ m1_pre_topc(B_29,A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_5108,plain,
    ( l1_pre_topc('#skF_3'('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_5102,c_32])).

tff(c_5115,plain,(
    l1_pre_topc('#skF_3'('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_5108])).

tff(c_30,plain,(
    ! [A_26] :
      ( l1_struct_0(A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4853,plain,(
    ! [A_459,B_460] :
      ( ~ v2_struct_0('#skF_3'(A_459,B_460))
      | ~ v2_tex_2(B_460,A_459)
      | ~ m1_subset_1(B_460,k1_zfmisc_1(u1_struct_0(A_459)))
      | v1_xboole_0(B_460)
      | ~ l1_pre_topc(A_459)
      | ~ v2_pre_topc(A_459)
      | v2_struct_0(A_459) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_4860,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_5','#skF_6'))
    | ~ v2_tex_2('#skF_6','#skF_5')
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_4853])).

tff(c_4864,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_5','#skF_6'))
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_3377,c_4860])).

tff(c_4865,plain,(
    ~ v2_struct_0('#skF_3'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_74,c_4864])).

tff(c_78,plain,(
    v2_tdlat_3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_50,plain,(
    ! [B_41,A_39] :
      ( v2_tdlat_3(B_41)
      | ~ m1_pre_topc(B_41,A_39)
      | ~ l1_pre_topc(A_39)
      | ~ v2_tdlat_3(A_39)
      | ~ v2_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_5105,plain,
    ( v2_tdlat_3('#skF_3'('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_tdlat_3('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_5102,c_50])).

tff(c_5111,plain,
    ( v2_tdlat_3('#skF_3'('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_5105])).

tff(c_5112,plain,(
    v2_tdlat_3('#skF_3'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_5111])).

tff(c_42,plain,(
    ! [A_37] :
      ( v2_pre_topc(A_37)
      | ~ v2_tdlat_3(A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_5119,plain,
    ( v2_pre_topc('#skF_3'('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_3'('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_5112,c_42])).

tff(c_5121,plain,(
    v2_pre_topc('#skF_3'('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5115,c_5119])).

tff(c_4754,plain,(
    ! [A_451,B_452] :
      ( v1_tdlat_3('#skF_3'(A_451,B_452))
      | ~ v2_tex_2(B_452,A_451)
      | ~ m1_subset_1(B_452,k1_zfmisc_1(u1_struct_0(A_451)))
      | v1_xboole_0(B_452)
      | ~ l1_pre_topc(A_451)
      | ~ v2_pre_topc(A_451)
      | v2_struct_0(A_451) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_4761,plain,
    ( v1_tdlat_3('#skF_3'('#skF_5','#skF_6'))
    | ~ v2_tex_2('#skF_6','#skF_5')
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_4754])).

tff(c_4765,plain,
    ( v1_tdlat_3('#skF_3'('#skF_5','#skF_6'))
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_3377,c_4761])).

tff(c_4766,plain,(
    v1_tdlat_3('#skF_3'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_74,c_4765])).

tff(c_46,plain,(
    ! [A_38] :
      ( v7_struct_0(A_38)
      | ~ v2_tdlat_3(A_38)
      | ~ v1_tdlat_3(A_38)
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_3378,plain,(
    ~ v1_zfmisc_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_5267,plain,(
    ! [A_485,B_486] :
      ( u1_struct_0('#skF_3'(A_485,B_486)) = B_486
      | ~ v2_tex_2(B_486,A_485)
      | ~ m1_subset_1(B_486,k1_zfmisc_1(u1_struct_0(A_485)))
      | v1_xboole_0(B_486)
      | ~ l1_pre_topc(A_485)
      | ~ v2_pre_topc(A_485)
      | v2_struct_0(A_485) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_5274,plain,
    ( u1_struct_0('#skF_3'('#skF_5','#skF_6')) = '#skF_6'
    | ~ v2_tex_2('#skF_6','#skF_5')
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_5267])).

tff(c_5278,plain,
    ( u1_struct_0('#skF_3'('#skF_5','#skF_6')) = '#skF_6'
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_3377,c_5274])).

tff(c_5279,plain,(
    u1_struct_0('#skF_3'('#skF_5','#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_74,c_5278])).

tff(c_34,plain,(
    ! [A_30] :
      ( v1_zfmisc_1(u1_struct_0(A_30))
      | ~ l1_struct_0(A_30)
      | ~ v7_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_5334,plain,
    ( v1_zfmisc_1('#skF_6')
    | ~ l1_struct_0('#skF_3'('#skF_5','#skF_6'))
    | ~ v7_struct_0('#skF_3'('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5279,c_34])).

tff(c_5382,plain,
    ( ~ l1_struct_0('#skF_3'('#skF_5','#skF_6'))
    | ~ v7_struct_0('#skF_3'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_3378,c_5334])).

tff(c_5387,plain,(
    ~ v7_struct_0('#skF_3'('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_5382])).

tff(c_5452,plain,
    ( ~ v2_tdlat_3('#skF_3'('#skF_5','#skF_6'))
    | ~ v1_tdlat_3('#skF_3'('#skF_5','#skF_6'))
    | ~ v2_pre_topc('#skF_3'('#skF_5','#skF_6'))
    | v2_struct_0('#skF_3'('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_3'('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_46,c_5387])).

tff(c_5455,plain,(
    v2_struct_0('#skF_3'('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5115,c_5121,c_4766,c_5112,c_5452])).

tff(c_5457,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4865,c_5455])).

tff(c_5458,plain,(
    ~ l1_struct_0('#skF_3'('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_5382])).

tff(c_5462,plain,(
    ~ l1_pre_topc('#skF_3'('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_30,c_5458])).

tff(c_5466,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5115,c_5462])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:27:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.06/2.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.06/2.97  
% 8.06/2.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.06/2.97  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 8.06/2.97  
% 8.06/2.97  %Foreground sorts:
% 8.06/2.97  
% 8.06/2.97  
% 8.06/2.97  %Background operators:
% 8.06/2.97  
% 8.06/2.97  
% 8.06/2.97  %Foreground operators:
% 8.06/2.97  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.06/2.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.06/2.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.06/2.97  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.06/2.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.06/2.97  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 8.06/2.97  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.06/2.97  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 8.06/2.97  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.06/2.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.06/2.97  tff('#skF_5', type, '#skF_5': $i).
% 8.06/2.97  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 8.06/2.97  tff('#skF_6', type, '#skF_6': $i).
% 8.06/2.97  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 8.06/2.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.06/2.97  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.06/2.97  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 8.06/2.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.06/2.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.06/2.97  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.06/2.97  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 8.06/2.97  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.06/2.97  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.06/2.97  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.06/2.97  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.06/2.97  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.06/2.97  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.06/2.97  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.06/2.97  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 8.06/2.97  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 8.06/2.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.06/2.97  
% 8.06/2.99  tff(f_230, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 8.06/2.99  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 8.06/2.99  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.06/2.99  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.06/2.99  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 8.06/2.99  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 8.06/2.99  tff(f_41, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.06/2.99  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.06/2.99  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.06/2.99  tff(f_210, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 8.06/2.99  tff(f_162, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 8.06/2.99  tff(f_45, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 8.06/2.99  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.06/2.99  tff(f_72, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 8.06/2.99  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 8.06/2.99  tff(f_191, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tex_2)).
% 8.06/2.99  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 8.06/2.99  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 8.06/2.99  tff(f_149, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_tdlat_3(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_tdlat_3)).
% 8.06/2.99  tff(f_117, axiom, (![A]: (l1_pre_topc(A) => (v2_tdlat_3(A) => v2_pre_topc(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tdlat_3)).
% 8.06/2.99  tff(f_135, axiom, (![A]: (l1_pre_topc(A) => ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & v2_tdlat_3(A)) => ((~v2_struct_0(A) & v7_struct_0(A)) & v2_pre_topc(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_1)).
% 8.06/2.99  tff(f_89, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 8.06/2.99  tff(c_76, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.06/2.99  tff(c_82, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.06/2.99  tff(c_74, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.06/2.99  tff(c_80, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.06/2.99  tff(c_90, plain, (v2_tex_2('#skF_6', '#skF_5') | v1_zfmisc_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.06/2.99  tff(c_98, plain, (v1_zfmisc_1('#skF_6')), inference(splitLeft, [status(thm)], [c_90])).
% 8.06/2.99  tff(c_84, plain, (~v1_zfmisc_1('#skF_6') | ~v2_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.06/2.99  tff(c_101, plain, (~v2_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_84])).
% 8.06/2.99  tff(c_72, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.06/2.99  tff(c_347, plain, (![B_104, A_105]: (r1_tarski(B_104, k2_pre_topc(A_105, B_104)) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.06/2.99  tff(c_352, plain, (r1_tarski('#skF_6', k2_pre_topc('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_72, c_347])).
% 8.06/2.99  tff(c_356, plain, (r1_tarski('#skF_6', k2_pre_topc('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_352])).
% 8.06/2.99  tff(c_18, plain, (![A_13, B_14]: (k3_xboole_0(A_13, B_14)=A_13 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.06/2.99  tff(c_372, plain, (k3_xboole_0('#skF_6', k2_pre_topc('#skF_5', '#skF_6'))='#skF_6'), inference(resolution, [status(thm)], [c_356, c_18])).
% 8.06/2.99  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.06/2.99  tff(c_205, plain, (![A_90, B_91, C_92]: (k9_subset_1(A_90, B_91, C_92)=k3_xboole_0(B_91, C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(A_90)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.06/2.99  tff(c_211, plain, (![B_91]: (k9_subset_1(u1_struct_0('#skF_5'), B_91, '#skF_6')=k3_xboole_0(B_91, '#skF_6'))), inference(resolution, [status(thm)], [c_72, c_205])).
% 8.06/2.99  tff(c_416, plain, (![A_115, C_116, B_117]: (k9_subset_1(A_115, C_116, B_117)=k9_subset_1(A_115, B_117, C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(A_115)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.06/2.99  tff(c_420, plain, (![B_117]: (k9_subset_1(u1_struct_0('#skF_5'), B_117, '#skF_6')=k9_subset_1(u1_struct_0('#skF_5'), '#skF_6', B_117))), inference(resolution, [status(thm)], [c_72, c_416])).
% 8.06/2.99  tff(c_423, plain, (![B_117]: (k9_subset_1(u1_struct_0('#skF_5'), '#skF_6', B_117)=k3_xboole_0(B_117, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_420])).
% 8.06/2.99  tff(c_14, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.06/2.99  tff(c_169, plain, (![A_81, B_82]: (r2_hidden('#skF_2'(A_81, B_82), A_81) | r1_tarski(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.06/2.99  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.06/2.99  tff(c_200, plain, (![A_88, B_89]: (~v1_xboole_0(A_88) | r1_tarski(A_88, B_89))), inference(resolution, [status(thm)], [c_169, c_4])).
% 8.06/2.99  tff(c_212, plain, (![A_93, B_94]: (k3_xboole_0(A_93, B_94)=A_93 | ~v1_xboole_0(A_93))), inference(resolution, [status(thm)], [c_200, c_18])).
% 8.06/2.99  tff(c_215, plain, (![B_94]: (k3_xboole_0(k1_xboole_0, B_94)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_212])).
% 8.06/2.99  tff(c_930, plain, (![A_176, B_177]: (r1_tarski('#skF_4'(A_176, B_177), B_177) | v2_tex_2(B_177, A_176) | ~m1_subset_1(B_177, k1_zfmisc_1(u1_struct_0(A_176))) | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176) | v2_struct_0(A_176))), inference(cnfTransformation, [status(thm)], [f_210])).
% 8.06/2.99  tff(c_935, plain, (r1_tarski('#skF_4'('#skF_5', '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_72, c_930])).
% 8.06/2.99  tff(c_939, plain, (r1_tarski('#skF_4'('#skF_5', '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_935])).
% 8.06/2.99  tff(c_940, plain, (r1_tarski('#skF_4'('#skF_5', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_82, c_101, c_939])).
% 8.06/2.99  tff(c_52, plain, (![B_44, A_42]: (B_44=A_42 | ~r1_tarski(A_42, B_44) | ~v1_zfmisc_1(B_44) | v1_xboole_0(B_44) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_162])).
% 8.06/2.99  tff(c_954, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6' | ~v1_zfmisc_1('#skF_6') | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_940, c_52])).
% 8.06/2.99  tff(c_965, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6' | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_954])).
% 8.06/2.99  tff(c_966, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6' | v1_xboole_0('#skF_4'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_74, c_965])).
% 8.06/2.99  tff(c_968, plain, (v1_xboole_0('#skF_4'('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_966])).
% 8.06/2.99  tff(c_16, plain, (![A_12]: (k1_xboole_0=A_12 | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.06/2.99  tff(c_981, plain, ('#skF_4'('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_968, c_16])).
% 8.06/2.99  tff(c_178, plain, (![A_81, B_82]: (~v1_xboole_0(A_81) | r1_tarski(A_81, B_82))), inference(resolution, [status(thm)], [c_169, c_4])).
% 8.06/2.99  tff(c_26, plain, (![A_21, B_22]: (m1_subset_1(A_21, k1_zfmisc_1(B_22)) | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.06/2.99  tff(c_753, plain, (![B_151, A_152]: (v4_pre_topc(B_151, A_152) | ~v1_xboole_0(B_151) | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_pre_topc(A_152) | ~v2_pre_topc(A_152))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.06/2.99  tff(c_896, plain, (![A_172, A_173]: (v4_pre_topc(A_172, A_173) | ~v1_xboole_0(A_172) | ~l1_pre_topc(A_173) | ~v2_pre_topc(A_173) | ~r1_tarski(A_172, u1_struct_0(A_173)))), inference(resolution, [status(thm)], [c_26, c_753])).
% 8.06/2.99  tff(c_914, plain, (![A_174, A_175]: (v4_pre_topc(A_174, A_175) | ~l1_pre_topc(A_175) | ~v2_pre_topc(A_175) | ~v1_xboole_0(A_174))), inference(resolution, [status(thm)], [c_178, c_896])).
% 8.06/2.99  tff(c_701, plain, (![A_143, B_144]: (k2_pre_topc(A_143, B_144)=B_144 | ~v4_pre_topc(B_144, A_143) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_pre_topc(A_143))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.06/2.99  tff(c_851, plain, (![A_164, A_165]: (k2_pre_topc(A_164, A_165)=A_165 | ~v4_pre_topc(A_165, A_164) | ~l1_pre_topc(A_164) | ~r1_tarski(A_165, u1_struct_0(A_164)))), inference(resolution, [status(thm)], [c_26, c_701])).
% 8.06/2.99  tff(c_863, plain, (![A_164, A_81]: (k2_pre_topc(A_164, A_81)=A_81 | ~v4_pre_topc(A_81, A_164) | ~l1_pre_topc(A_164) | ~v1_xboole_0(A_81))), inference(resolution, [status(thm)], [c_178, c_851])).
% 8.06/2.99  tff(c_1065, plain, (![A_181, A_182]: (k2_pre_topc(A_181, A_182)=A_182 | ~l1_pre_topc(A_181) | ~v2_pre_topc(A_181) | ~v1_xboole_0(A_182))), inference(resolution, [status(thm)], [c_914, c_863])).
% 8.06/2.99  tff(c_1067, plain, (![A_182]: (k2_pre_topc('#skF_5', A_182)=A_182 | ~l1_pre_topc('#skF_5') | ~v1_xboole_0(A_182))), inference(resolution, [status(thm)], [c_80, c_1065])).
% 8.06/2.99  tff(c_1071, plain, (![A_183]: (k2_pre_topc('#skF_5', A_183)=A_183 | ~v1_xboole_0(A_183))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1067])).
% 8.06/2.99  tff(c_1075, plain, (k2_pre_topc('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_1071])).
% 8.06/2.99  tff(c_2058, plain, (![A_236, B_237]: (k9_subset_1(u1_struct_0(A_236), B_237, k2_pre_topc(A_236, '#skF_4'(A_236, B_237)))!='#skF_4'(A_236, B_237) | v2_tex_2(B_237, A_236) | ~m1_subset_1(B_237, k1_zfmisc_1(u1_struct_0(A_236))) | ~l1_pre_topc(A_236) | ~v2_pre_topc(A_236) | v2_struct_0(A_236))), inference(cnfTransformation, [status(thm)], [f_210])).
% 8.06/2.99  tff(c_2061, plain, (k9_subset_1(u1_struct_0('#skF_5'), '#skF_6', k2_pre_topc('#skF_5', k1_xboole_0))!='#skF_4'('#skF_5', '#skF_6') | v2_tex_2('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_981, c_2058])).
% 8.06/2.99  tff(c_2075, plain, (v2_tex_2('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_72, c_215, c_423, c_981, c_1075, c_2061])).
% 8.06/2.99  tff(c_2077, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_101, c_2075])).
% 8.06/2.99  tff(c_2078, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_966])).
% 8.06/2.99  tff(c_3350, plain, (![A_308, B_309]: (k9_subset_1(u1_struct_0(A_308), B_309, k2_pre_topc(A_308, '#skF_4'(A_308, B_309)))!='#skF_4'(A_308, B_309) | v2_tex_2(B_309, A_308) | ~m1_subset_1(B_309, k1_zfmisc_1(u1_struct_0(A_308))) | ~l1_pre_topc(A_308) | ~v2_pre_topc(A_308) | v2_struct_0(A_308))), inference(cnfTransformation, [status(thm)], [f_210])).
% 8.06/2.99  tff(c_3357, plain, (k9_subset_1(u1_struct_0('#skF_5'), '#skF_6', k2_pre_topc('#skF_5', '#skF_6'))!='#skF_4'('#skF_5', '#skF_6') | v2_tex_2('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2078, c_3350])).
% 8.06/2.99  tff(c_3374, plain, (v2_tex_2('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_72, c_372, c_2, c_423, c_2078, c_3357])).
% 8.06/2.99  tff(c_3376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_101, c_3374])).
% 8.06/2.99  tff(c_3377, plain, (v2_tex_2('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_90])).
% 8.06/2.99  tff(c_5092, plain, (![A_478, B_479]: (m1_pre_topc('#skF_3'(A_478, B_479), A_478) | ~v2_tex_2(B_479, A_478) | ~m1_subset_1(B_479, k1_zfmisc_1(u1_struct_0(A_478))) | v1_xboole_0(B_479) | ~l1_pre_topc(A_478) | ~v2_pre_topc(A_478) | v2_struct_0(A_478))), inference(cnfTransformation, [status(thm)], [f_191])).
% 8.06/2.99  tff(c_5097, plain, (m1_pre_topc('#skF_3'('#skF_5', '#skF_6'), '#skF_5') | ~v2_tex_2('#skF_6', '#skF_5') | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_72, c_5092])).
% 8.06/2.99  tff(c_5101, plain, (m1_pre_topc('#skF_3'('#skF_5', '#skF_6'), '#skF_5') | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_3377, c_5097])).
% 8.06/2.99  tff(c_5102, plain, (m1_pre_topc('#skF_3'('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_82, c_74, c_5101])).
% 8.06/2.99  tff(c_32, plain, (![B_29, A_27]: (l1_pre_topc(B_29) | ~m1_pre_topc(B_29, A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.06/2.99  tff(c_5108, plain, (l1_pre_topc('#skF_3'('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_5102, c_32])).
% 8.06/2.99  tff(c_5115, plain, (l1_pre_topc('#skF_3'('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_5108])).
% 8.06/2.99  tff(c_30, plain, (![A_26]: (l1_struct_0(A_26) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.06/2.99  tff(c_4853, plain, (![A_459, B_460]: (~v2_struct_0('#skF_3'(A_459, B_460)) | ~v2_tex_2(B_460, A_459) | ~m1_subset_1(B_460, k1_zfmisc_1(u1_struct_0(A_459))) | v1_xboole_0(B_460) | ~l1_pre_topc(A_459) | ~v2_pre_topc(A_459) | v2_struct_0(A_459))), inference(cnfTransformation, [status(thm)], [f_191])).
% 8.06/2.99  tff(c_4860, plain, (~v2_struct_0('#skF_3'('#skF_5', '#skF_6')) | ~v2_tex_2('#skF_6', '#skF_5') | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_72, c_4853])).
% 8.06/2.99  tff(c_4864, plain, (~v2_struct_0('#skF_3'('#skF_5', '#skF_6')) | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_3377, c_4860])).
% 8.06/2.99  tff(c_4865, plain, (~v2_struct_0('#skF_3'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_82, c_74, c_4864])).
% 8.06/2.99  tff(c_78, plain, (v2_tdlat_3('#skF_5')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.06/2.99  tff(c_50, plain, (![B_41, A_39]: (v2_tdlat_3(B_41) | ~m1_pre_topc(B_41, A_39) | ~l1_pre_topc(A_39) | ~v2_tdlat_3(A_39) | ~v2_pre_topc(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.06/2.99  tff(c_5105, plain, (v2_tdlat_3('#skF_3'('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | ~v2_tdlat_3('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_5102, c_50])).
% 8.06/2.99  tff(c_5111, plain, (v2_tdlat_3('#skF_3'('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_5105])).
% 8.06/2.99  tff(c_5112, plain, (v2_tdlat_3('#skF_3'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_82, c_5111])).
% 8.06/2.99  tff(c_42, plain, (![A_37]: (v2_pre_topc(A_37) | ~v2_tdlat_3(A_37) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.06/2.99  tff(c_5119, plain, (v2_pre_topc('#skF_3'('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_3'('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_5112, c_42])).
% 8.06/2.99  tff(c_5121, plain, (v2_pre_topc('#skF_3'('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_5115, c_5119])).
% 8.06/2.99  tff(c_4754, plain, (![A_451, B_452]: (v1_tdlat_3('#skF_3'(A_451, B_452)) | ~v2_tex_2(B_452, A_451) | ~m1_subset_1(B_452, k1_zfmisc_1(u1_struct_0(A_451))) | v1_xboole_0(B_452) | ~l1_pre_topc(A_451) | ~v2_pre_topc(A_451) | v2_struct_0(A_451))), inference(cnfTransformation, [status(thm)], [f_191])).
% 8.06/2.99  tff(c_4761, plain, (v1_tdlat_3('#skF_3'('#skF_5', '#skF_6')) | ~v2_tex_2('#skF_6', '#skF_5') | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_72, c_4754])).
% 8.06/2.99  tff(c_4765, plain, (v1_tdlat_3('#skF_3'('#skF_5', '#skF_6')) | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_3377, c_4761])).
% 8.06/2.99  tff(c_4766, plain, (v1_tdlat_3('#skF_3'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_82, c_74, c_4765])).
% 8.06/2.99  tff(c_46, plain, (![A_38]: (v7_struct_0(A_38) | ~v2_tdlat_3(A_38) | ~v1_tdlat_3(A_38) | ~v2_pre_topc(A_38) | v2_struct_0(A_38) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.06/2.99  tff(c_3378, plain, (~v1_zfmisc_1('#skF_6')), inference(splitRight, [status(thm)], [c_90])).
% 8.06/2.99  tff(c_5267, plain, (![A_485, B_486]: (u1_struct_0('#skF_3'(A_485, B_486))=B_486 | ~v2_tex_2(B_486, A_485) | ~m1_subset_1(B_486, k1_zfmisc_1(u1_struct_0(A_485))) | v1_xboole_0(B_486) | ~l1_pre_topc(A_485) | ~v2_pre_topc(A_485) | v2_struct_0(A_485))), inference(cnfTransformation, [status(thm)], [f_191])).
% 8.06/2.99  tff(c_5274, plain, (u1_struct_0('#skF_3'('#skF_5', '#skF_6'))='#skF_6' | ~v2_tex_2('#skF_6', '#skF_5') | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_72, c_5267])).
% 8.06/2.99  tff(c_5278, plain, (u1_struct_0('#skF_3'('#skF_5', '#skF_6'))='#skF_6' | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_3377, c_5274])).
% 8.06/2.99  tff(c_5279, plain, (u1_struct_0('#skF_3'('#skF_5', '#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_82, c_74, c_5278])).
% 8.06/2.99  tff(c_34, plain, (![A_30]: (v1_zfmisc_1(u1_struct_0(A_30)) | ~l1_struct_0(A_30) | ~v7_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.06/2.99  tff(c_5334, plain, (v1_zfmisc_1('#skF_6') | ~l1_struct_0('#skF_3'('#skF_5', '#skF_6')) | ~v7_struct_0('#skF_3'('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_5279, c_34])).
% 8.06/2.99  tff(c_5382, plain, (~l1_struct_0('#skF_3'('#skF_5', '#skF_6')) | ~v7_struct_0('#skF_3'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_3378, c_5334])).
% 8.06/2.99  tff(c_5387, plain, (~v7_struct_0('#skF_3'('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_5382])).
% 8.06/2.99  tff(c_5452, plain, (~v2_tdlat_3('#skF_3'('#skF_5', '#skF_6')) | ~v1_tdlat_3('#skF_3'('#skF_5', '#skF_6')) | ~v2_pre_topc('#skF_3'('#skF_5', '#skF_6')) | v2_struct_0('#skF_3'('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_3'('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_46, c_5387])).
% 8.06/2.99  tff(c_5455, plain, (v2_struct_0('#skF_3'('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_5115, c_5121, c_4766, c_5112, c_5452])).
% 8.06/2.99  tff(c_5457, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4865, c_5455])).
% 8.06/2.99  tff(c_5458, plain, (~l1_struct_0('#skF_3'('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_5382])).
% 8.06/2.99  tff(c_5462, plain, (~l1_pre_topc('#skF_3'('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_30, c_5458])).
% 8.06/2.99  tff(c_5466, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5115, c_5462])).
% 8.06/2.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.06/2.99  
% 8.06/2.99  Inference rules
% 8.06/2.99  ----------------------
% 8.06/2.99  #Ref     : 0
% 8.06/2.99  #Sup     : 1133
% 8.06/2.99  #Fact    : 0
% 8.06/2.99  #Define  : 0
% 8.06/2.99  #Split   : 29
% 8.06/2.99  #Chain   : 0
% 8.06/2.99  #Close   : 0
% 8.06/2.99  
% 8.06/2.99  Ordering : KBO
% 8.06/2.99  
% 8.06/2.99  Simplification rules
% 8.06/2.99  ----------------------
% 8.06/2.99  #Subsume      : 343
% 8.06/2.99  #Demod        : 594
% 8.06/2.99  #Tautology    : 502
% 8.06/2.99  #SimpNegUnit  : 127
% 8.06/2.99  #BackRed      : 47
% 8.06/2.99  
% 8.06/2.99  #Partial instantiations: 0
% 8.06/2.99  #Strategies tried      : 1
% 8.06/2.99  
% 8.06/2.99  Timing (in seconds)
% 8.06/2.99  ----------------------
% 8.06/3.00  Preprocessing        : 0.61
% 8.06/3.00  Parsing              : 0.32
% 8.06/3.00  CNF conversion       : 0.05
% 8.06/3.00  Main loop            : 1.46
% 8.06/3.00  Inferencing          : 0.49
% 8.06/3.00  Reduction            : 0.50
% 8.06/3.00  Demodulation         : 0.35
% 8.06/3.00  BG Simplification    : 0.06
% 8.06/3.00  Subsumption          : 0.30
% 8.06/3.00  Abstraction          : 0.06
% 8.06/3.00  MUC search           : 0.00
% 8.06/3.00  Cooper               : 0.00
% 8.06/3.00  Total                : 2.13
% 8.06/3.00  Index Insertion      : 0.00
% 8.06/3.00  Index Deletion       : 0.00
% 8.06/3.00  Index Matching       : 0.00
% 8.06/3.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
