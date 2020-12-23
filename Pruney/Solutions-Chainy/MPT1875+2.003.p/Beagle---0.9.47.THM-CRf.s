%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:46 EST 2020

% Result     : Theorem 7.06s
% Output     : CNFRefutation 7.22s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 329 expanded)
%              Number of leaves         :   53 ( 129 expanded)
%              Depth                    :   14
%              Number of atoms          :  250 ( 805 expanded)
%              Number of equality atoms :   35 ( 100 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v2_tex_2 > v1_tsep_1 > v1_borsuk_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k3_subset_1 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v1_borsuk_1,type,(
    v1_borsuk_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_198,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v2_struct_0(A)
        & l1_struct_0(A) )
     => v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).

tff(f_131,axiom,(
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

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_183,axiom,(
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

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_152,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r1_tarski(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_163,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_53,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_78,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_74,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_76,plain,(
    v1_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_72,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_393,plain,(
    ! [A_126,B_127] :
      ( m1_pre_topc(k1_pre_topc(A_126,B_127),A_126)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_402,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_4','#skF_5'),'#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_393])).

tff(c_411,plain,(
    m1_pre_topc(k1_pre_topc('#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_402])).

tff(c_28,plain,(
    ! [B_26,A_24] :
      ( l1_pre_topc(B_26)
      | ~ m1_pre_topc(B_26,A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_415,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_411,c_28])).

tff(c_418,plain,(
    l1_pre_topc(k1_pre_topc('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_415])).

tff(c_26,plain,(
    ! [A_23] :
      ( l1_struct_0(A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_70,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_501,plain,(
    ! [A_140,B_141] :
      ( u1_struct_0(k1_pre_topc(A_140,B_141)) = B_141
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_pre_topc(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_514,plain,
    ( u1_struct_0(k1_pre_topc('#skF_4','#skF_5')) = '#skF_5'
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_501])).

tff(c_524,plain,(
    u1_struct_0(k1_pre_topc('#skF_4','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_514])).

tff(c_30,plain,(
    ! [A_27] :
      ( v1_xboole_0(u1_struct_0(A_27))
      | ~ l1_struct_0(A_27)
      | ~ v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_555,plain,
    ( v1_xboole_0('#skF_5')
    | ~ l1_struct_0(k1_pre_topc('#skF_4','#skF_5'))
    | ~ v2_struct_0(k1_pre_topc('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_30])).

tff(c_625,plain,(
    ~ v2_struct_0(k1_pre_topc('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_555])).

tff(c_690,plain,(
    ! [B_147,A_148] :
      ( v1_tdlat_3(B_147)
      | ~ m1_pre_topc(B_147,A_148)
      | ~ l1_pre_topc(A_148)
      | ~ v1_tdlat_3(A_148)
      | ~ v2_pre_topc(A_148)
      | v2_struct_0(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_699,plain,
    ( v1_tdlat_3(k1_pre_topc('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v1_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_411,c_690])).

tff(c_704,plain,
    ( v1_tdlat_3(k1_pre_topc('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_699])).

tff(c_705,plain,(
    v1_tdlat_3(k1_pre_topc('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_704])).

tff(c_38,plain,(
    ! [B_36,A_34] :
      ( m1_subset_1(u1_struct_0(B_36),k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ m1_pre_topc(B_36,A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1924,plain,(
    ! [B_250,A_251] :
      ( v2_tex_2(u1_struct_0(B_250),A_251)
      | ~ v1_tdlat_3(B_250)
      | ~ m1_subset_1(u1_struct_0(B_250),k1_zfmisc_1(u1_struct_0(A_251)))
      | ~ m1_pre_topc(B_250,A_251)
      | v2_struct_0(B_250)
      | ~ l1_pre_topc(A_251)
      | v2_struct_0(A_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_1967,plain,(
    ! [B_252,A_253] :
      ( v2_tex_2(u1_struct_0(B_252),A_253)
      | ~ v1_tdlat_3(B_252)
      | v2_struct_0(B_252)
      | v2_struct_0(A_253)
      | ~ m1_pre_topc(B_252,A_253)
      | ~ l1_pre_topc(A_253) ) ),
    inference(resolution,[status(thm)],[c_38,c_1924])).

tff(c_1985,plain,(
    ! [A_253] :
      ( v2_tex_2('#skF_5',A_253)
      | ~ v1_tdlat_3(k1_pre_topc('#skF_4','#skF_5'))
      | v2_struct_0(k1_pre_topc('#skF_4','#skF_5'))
      | v2_struct_0(A_253)
      | ~ m1_pre_topc(k1_pre_topc('#skF_4','#skF_5'),A_253)
      | ~ l1_pre_topc(A_253) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_1967])).

tff(c_1988,plain,(
    ! [A_253] :
      ( v2_tex_2('#skF_5',A_253)
      | v2_struct_0(k1_pre_topc('#skF_4','#skF_5'))
      | v2_struct_0(A_253)
      | ~ m1_pre_topc(k1_pre_topc('#skF_4','#skF_5'),A_253)
      | ~ l1_pre_topc(A_253) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_705,c_1985])).

tff(c_1990,plain,(
    ! [A_254] :
      ( v2_tex_2('#skF_5',A_254)
      | v2_struct_0(A_254)
      | ~ m1_pre_topc(k1_pre_topc('#skF_4','#skF_5'),A_254)
      | ~ l1_pre_topc(A_254) ) ),
    inference(negUnitSimplification,[status(thm)],[c_625,c_1988])).

tff(c_1993,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_411,c_1990])).

tff(c_1996,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1993])).

tff(c_1998,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_70,c_1996])).

tff(c_1999,plain,
    ( ~ l1_struct_0(k1_pre_topc('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_555])).

tff(c_2013,plain,(
    ~ l1_struct_0(k1_pre_topc('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1999])).

tff(c_2016,plain,(
    ~ l1_pre_topc(k1_pre_topc('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_26,c_2013])).

tff(c_2020,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_2016])).

tff(c_2021,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1999])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2026,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2021,c_2])).

tff(c_16,plain,(
    ! [A_15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2040,plain,(
    ! [A_15] : m1_subset_1('#skF_5',k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2026,c_16])).

tff(c_2390,plain,(
    ! [A_285,B_286] :
      ( r1_tarski('#skF_2'(A_285,B_286),B_286)
      | v2_tex_2(B_286,A_285)
      | ~ m1_subset_1(B_286,k1_zfmisc_1(u1_struct_0(A_285)))
      | ~ l1_pre_topc(A_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_2413,plain,(
    ! [A_287] :
      ( r1_tarski('#skF_2'(A_287,'#skF_5'),'#skF_5')
      | v2_tex_2('#skF_5',A_287)
      | ~ l1_pre_topc(A_287) ) ),
    inference(resolution,[status(thm)],[c_2040,c_2390])).

tff(c_6,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2038,plain,(
    ! [A_4] :
      ( A_4 = '#skF_5'
      | ~ r1_tarski(A_4,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2026,c_2026,c_6])).

tff(c_2418,plain,(
    ! [A_288] :
      ( '#skF_2'(A_288,'#skF_5') = '#skF_5'
      | v2_tex_2('#skF_5',A_288)
      | ~ l1_pre_topc(A_288) ) ),
    inference(resolution,[status(thm)],[c_2413,c_2038])).

tff(c_2421,plain,
    ( '#skF_2'('#skF_4','#skF_5') = '#skF_5'
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_2418,c_70])).

tff(c_2424,plain,(
    '#skF_2'('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2421])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(k3_subset_1(A_10,B_11),k1_zfmisc_1(A_10))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2168,plain,(
    ! [B_263,A_264] :
      ( v3_pre_topc(B_263,A_264)
      | ~ m1_subset_1(B_263,k1_zfmisc_1(u1_struct_0(A_264)))
      | ~ v1_tdlat_3(A_264)
      | ~ l1_pre_topc(A_264)
      | ~ v2_pre_topc(A_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_3933,plain,(
    ! [A_398,B_399] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_398),B_399),A_398)
      | ~ v1_tdlat_3(A_398)
      | ~ l1_pre_topc(A_398)
      | ~ v2_pre_topc(A_398)
      | ~ m1_subset_1(B_399,k1_zfmisc_1(u1_struct_0(A_398))) ) ),
    inference(resolution,[status(thm)],[c_12,c_2168])).

tff(c_34,plain,(
    ! [B_33,A_31] :
      ( v4_pre_topc(B_33,A_31)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_31),B_33),A_31)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_3957,plain,(
    ! [B_402,A_403] :
      ( v4_pre_topc(B_402,A_403)
      | ~ v1_tdlat_3(A_403)
      | ~ l1_pre_topc(A_403)
      | ~ v2_pre_topc(A_403)
      | ~ m1_subset_1(B_402,k1_zfmisc_1(u1_struct_0(A_403))) ) ),
    inference(resolution,[status(thm)],[c_3933,c_34])).

tff(c_3995,plain,(
    ! [A_403] :
      ( v4_pre_topc('#skF_5',A_403)
      | ~ v1_tdlat_3(A_403)
      | ~ l1_pre_topc(A_403)
      | ~ v2_pre_topc(A_403) ) ),
    inference(resolution,[status(thm)],[c_2040,c_3957])).

tff(c_8,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_140,plain,(
    ! [A_88,B_89] : k1_setfam_1(k2_tarski(A_88,B_89)) = k3_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_161,plain,(
    ! [B_93,A_94] : k1_setfam_1(k2_tarski(B_93,A_94)) = k3_xboole_0(A_94,B_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_140])).

tff(c_18,plain,(
    ! [A_16,B_17] : k1_setfam_1(k2_tarski(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_185,plain,(
    ! [B_97,A_98] : k3_xboole_0(B_97,A_98) = k3_xboole_0(A_98,B_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_18])).

tff(c_85,plain,(
    ! [A_82,B_83] : r1_tarski(k3_xboole_0(A_82,B_83),A_82) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_90,plain,(
    ! [B_83] : k3_xboole_0(k1_xboole_0,B_83) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_85,c_6])).

tff(c_201,plain,(
    ! [B_97] : k3_xboole_0(B_97,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_90])).

tff(c_324,plain,(
    ! [A_111,B_112,C_113] :
      ( k9_subset_1(A_111,B_112,C_113) = k3_xboole_0(B_112,C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(A_111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_330,plain,(
    ! [A_15,B_112] : k9_subset_1(A_15,B_112,k1_xboole_0) = k3_xboole_0(B_112,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_324])).

tff(c_334,plain,(
    ! [A_15,B_112] : k9_subset_1(A_15,B_112,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_330])).

tff(c_2032,plain,(
    ! [A_15,B_112] : k9_subset_1(A_15,B_112,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2026,c_2026,c_334])).

tff(c_3883,plain,(
    ! [A_393,B_394,D_395] :
      ( k9_subset_1(u1_struct_0(A_393),B_394,D_395) != '#skF_2'(A_393,B_394)
      | ~ v4_pre_topc(D_395,A_393)
      | ~ m1_subset_1(D_395,k1_zfmisc_1(u1_struct_0(A_393)))
      | v2_tex_2(B_394,A_393)
      | ~ m1_subset_1(B_394,k1_zfmisc_1(u1_struct_0(A_393)))
      | ~ l1_pre_topc(A_393) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_3907,plain,(
    ! [A_393,B_112] :
      ( '#skF_2'(A_393,B_112) != '#skF_5'
      | ~ v4_pre_topc('#skF_5',A_393)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_393)))
      | v2_tex_2(B_112,A_393)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_393)))
      | ~ l1_pre_topc(A_393) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2032,c_3883])).

tff(c_4925,plain,(
    ! [A_438,B_439] :
      ( '#skF_2'(A_438,B_439) != '#skF_5'
      | ~ v4_pre_topc('#skF_5',A_438)
      | v2_tex_2(B_439,A_438)
      | ~ m1_subset_1(B_439,k1_zfmisc_1(u1_struct_0(A_438)))
      | ~ l1_pre_topc(A_438) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2040,c_3907])).

tff(c_4972,plain,(
    ! [A_440] :
      ( '#skF_2'(A_440,'#skF_5') != '#skF_5'
      | ~ v4_pre_topc('#skF_5',A_440)
      | v2_tex_2('#skF_5',A_440)
      | ~ l1_pre_topc(A_440) ) ),
    inference(resolution,[status(thm)],[c_2040,c_4925])).

tff(c_5203,plain,(
    ! [A_443] :
      ( '#skF_2'(A_443,'#skF_5') != '#skF_5'
      | v2_tex_2('#skF_5',A_443)
      | ~ v1_tdlat_3(A_443)
      | ~ l1_pre_topc(A_443)
      | ~ v2_pre_topc(A_443) ) ),
    inference(resolution,[status(thm)],[c_3995,c_4972])).

tff(c_5206,plain,
    ( '#skF_2'('#skF_4','#skF_5') != '#skF_5'
    | ~ v1_tdlat_3('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_5203,c_70])).

tff(c_5210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_76,c_2424,c_5206])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:00:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.06/2.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.06/2.42  
% 7.06/2.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.06/2.42  %$ v4_pre_topc > v3_pre_topc > v2_tex_2 > v1_tsep_1 > v1_borsuk_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k3_subset_1 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2
% 7.06/2.42  
% 7.06/2.42  %Foreground sorts:
% 7.06/2.42  
% 7.06/2.42  
% 7.06/2.42  %Background operators:
% 7.06/2.42  
% 7.06/2.42  
% 7.06/2.42  %Foreground operators:
% 7.06/2.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.06/2.42  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 7.06/2.42  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.06/2.42  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.06/2.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.06/2.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.06/2.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.06/2.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.06/2.42  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 7.06/2.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.06/2.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.06/2.42  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 7.06/2.42  tff('#skF_5', type, '#skF_5': $i).
% 7.06/2.42  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 7.06/2.42  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 7.06/2.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.06/2.42  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.06/2.42  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 7.06/2.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.06/2.42  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 7.06/2.42  tff('#skF_4', type, '#skF_4': $i).
% 7.06/2.42  tff('#skF_3', type, '#skF_3': $i > $i).
% 7.06/2.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.06/2.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.06/2.42  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.06/2.42  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.06/2.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.06/2.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.06/2.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.06/2.42  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.06/2.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.06/2.42  tff(v1_borsuk_1, type, v1_borsuk_1: ($i * $i) > $o).
% 7.06/2.42  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.06/2.42  
% 7.22/2.44  tff(f_198, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 7.22/2.44  tff(f_67, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 7.22/2.44  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 7.22/2.44  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.22/2.44  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_pre_topc)).
% 7.22/2.44  tff(f_84, axiom, (![A]: ((v2_struct_0(A) & l1_struct_0(A)) => v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_struct_0)).
% 7.22/2.44  tff(f_131, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((v1_borsuk_1(B, A) & v1_tsep_1(B, A)) & v1_tdlat_3(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_tdlat_3)).
% 7.22/2.44  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 7.22/2.44  tff(f_183, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_tex_2)).
% 7.22/2.44  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 7.22/2.44  tff(f_51, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 7.22/2.44  tff(f_152, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tex_2)).
% 7.22/2.44  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 7.22/2.44  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 7.22/2.44  tff(f_163, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_tdlat_3)).
% 7.22/2.44  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 7.22/2.44  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.22/2.44  tff(f_53, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 7.22/2.44  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 7.22/2.44  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 7.22/2.44  tff(c_78, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_198])).
% 7.22/2.44  tff(c_74, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_198])).
% 7.22/2.44  tff(c_76, plain, (v1_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_198])).
% 7.22/2.44  tff(c_72, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_198])).
% 7.22/2.44  tff(c_393, plain, (![A_126, B_127]: (m1_pre_topc(k1_pre_topc(A_126, B_127), A_126) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_pre_topc(A_126))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.22/2.44  tff(c_402, plain, (m1_pre_topc(k1_pre_topc('#skF_4', '#skF_5'), '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_72, c_393])).
% 7.22/2.44  tff(c_411, plain, (m1_pre_topc(k1_pre_topc('#skF_4', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_402])).
% 7.22/2.44  tff(c_28, plain, (![B_26, A_24]: (l1_pre_topc(B_26) | ~m1_pre_topc(B_26, A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.22/2.44  tff(c_415, plain, (l1_pre_topc(k1_pre_topc('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_411, c_28])).
% 7.22/2.44  tff(c_418, plain, (l1_pre_topc(k1_pre_topc('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_415])).
% 7.22/2.44  tff(c_26, plain, (![A_23]: (l1_struct_0(A_23) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.22/2.44  tff(c_80, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_198])).
% 7.22/2.44  tff(c_70, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_198])).
% 7.22/2.44  tff(c_501, plain, (![A_140, B_141]: (u1_struct_0(k1_pre_topc(A_140, B_141))=B_141 | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_pre_topc(A_140))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.22/2.44  tff(c_514, plain, (u1_struct_0(k1_pre_topc('#skF_4', '#skF_5'))='#skF_5' | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_72, c_501])).
% 7.22/2.44  tff(c_524, plain, (u1_struct_0(k1_pre_topc('#skF_4', '#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_514])).
% 7.22/2.44  tff(c_30, plain, (![A_27]: (v1_xboole_0(u1_struct_0(A_27)) | ~l1_struct_0(A_27) | ~v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.22/2.44  tff(c_555, plain, (v1_xboole_0('#skF_5') | ~l1_struct_0(k1_pre_topc('#skF_4', '#skF_5')) | ~v2_struct_0(k1_pre_topc('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_524, c_30])).
% 7.22/2.44  tff(c_625, plain, (~v2_struct_0(k1_pre_topc('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_555])).
% 7.22/2.44  tff(c_690, plain, (![B_147, A_148]: (v1_tdlat_3(B_147) | ~m1_pre_topc(B_147, A_148) | ~l1_pre_topc(A_148) | ~v1_tdlat_3(A_148) | ~v2_pre_topc(A_148) | v2_struct_0(A_148))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.22/2.44  tff(c_699, plain, (v1_tdlat_3(k1_pre_topc('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v1_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_411, c_690])).
% 7.22/2.44  tff(c_704, plain, (v1_tdlat_3(k1_pre_topc('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_699])).
% 7.22/2.44  tff(c_705, plain, (v1_tdlat_3(k1_pre_topc('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80, c_704])).
% 7.22/2.44  tff(c_38, plain, (![B_36, A_34]: (m1_subset_1(u1_struct_0(B_36), k1_zfmisc_1(u1_struct_0(A_34))) | ~m1_pre_topc(B_36, A_34) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.22/2.44  tff(c_1924, plain, (![B_250, A_251]: (v2_tex_2(u1_struct_0(B_250), A_251) | ~v1_tdlat_3(B_250) | ~m1_subset_1(u1_struct_0(B_250), k1_zfmisc_1(u1_struct_0(A_251))) | ~m1_pre_topc(B_250, A_251) | v2_struct_0(B_250) | ~l1_pre_topc(A_251) | v2_struct_0(A_251))), inference(cnfTransformation, [status(thm)], [f_183])).
% 7.22/2.44  tff(c_1967, plain, (![B_252, A_253]: (v2_tex_2(u1_struct_0(B_252), A_253) | ~v1_tdlat_3(B_252) | v2_struct_0(B_252) | v2_struct_0(A_253) | ~m1_pre_topc(B_252, A_253) | ~l1_pre_topc(A_253))), inference(resolution, [status(thm)], [c_38, c_1924])).
% 7.22/2.44  tff(c_1985, plain, (![A_253]: (v2_tex_2('#skF_5', A_253) | ~v1_tdlat_3(k1_pre_topc('#skF_4', '#skF_5')) | v2_struct_0(k1_pre_topc('#skF_4', '#skF_5')) | v2_struct_0(A_253) | ~m1_pre_topc(k1_pre_topc('#skF_4', '#skF_5'), A_253) | ~l1_pre_topc(A_253))), inference(superposition, [status(thm), theory('equality')], [c_524, c_1967])).
% 7.22/2.44  tff(c_1988, plain, (![A_253]: (v2_tex_2('#skF_5', A_253) | v2_struct_0(k1_pre_topc('#skF_4', '#skF_5')) | v2_struct_0(A_253) | ~m1_pre_topc(k1_pre_topc('#skF_4', '#skF_5'), A_253) | ~l1_pre_topc(A_253))), inference(demodulation, [status(thm), theory('equality')], [c_705, c_1985])).
% 7.22/2.44  tff(c_1990, plain, (![A_254]: (v2_tex_2('#skF_5', A_254) | v2_struct_0(A_254) | ~m1_pre_topc(k1_pre_topc('#skF_4', '#skF_5'), A_254) | ~l1_pre_topc(A_254))), inference(negUnitSimplification, [status(thm)], [c_625, c_1988])).
% 7.22/2.44  tff(c_1993, plain, (v2_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_411, c_1990])).
% 7.22/2.44  tff(c_1996, plain, (v2_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1993])).
% 7.22/2.44  tff(c_1998, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_70, c_1996])).
% 7.22/2.44  tff(c_1999, plain, (~l1_struct_0(k1_pre_topc('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_555])).
% 7.22/2.44  tff(c_2013, plain, (~l1_struct_0(k1_pre_topc('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_1999])).
% 7.22/2.44  tff(c_2016, plain, (~l1_pre_topc(k1_pre_topc('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_26, c_2013])).
% 7.22/2.44  tff(c_2020, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_418, c_2016])).
% 7.22/2.44  tff(c_2021, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_1999])).
% 7.22/2.44  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.22/2.44  tff(c_2026, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_2021, c_2])).
% 7.22/2.44  tff(c_16, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.22/2.44  tff(c_2040, plain, (![A_15]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_2026, c_16])).
% 7.22/2.44  tff(c_2390, plain, (![A_285, B_286]: (r1_tarski('#skF_2'(A_285, B_286), B_286) | v2_tex_2(B_286, A_285) | ~m1_subset_1(B_286, k1_zfmisc_1(u1_struct_0(A_285))) | ~l1_pre_topc(A_285))), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.22/2.44  tff(c_2413, plain, (![A_287]: (r1_tarski('#skF_2'(A_287, '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', A_287) | ~l1_pre_topc(A_287))), inference(resolution, [status(thm)], [c_2040, c_2390])).
% 7.22/2.44  tff(c_6, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.22/2.44  tff(c_2038, plain, (![A_4]: (A_4='#skF_5' | ~r1_tarski(A_4, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2026, c_2026, c_6])).
% 7.22/2.44  tff(c_2418, plain, (![A_288]: ('#skF_2'(A_288, '#skF_5')='#skF_5' | v2_tex_2('#skF_5', A_288) | ~l1_pre_topc(A_288))), inference(resolution, [status(thm)], [c_2413, c_2038])).
% 7.22/2.44  tff(c_2421, plain, ('#skF_2'('#skF_4', '#skF_5')='#skF_5' | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_2418, c_70])).
% 7.22/2.44  tff(c_2424, plain, ('#skF_2'('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2421])).
% 7.22/2.44  tff(c_12, plain, (![A_10, B_11]: (m1_subset_1(k3_subset_1(A_10, B_11), k1_zfmisc_1(A_10)) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.22/2.44  tff(c_2168, plain, (![B_263, A_264]: (v3_pre_topc(B_263, A_264) | ~m1_subset_1(B_263, k1_zfmisc_1(u1_struct_0(A_264))) | ~v1_tdlat_3(A_264) | ~l1_pre_topc(A_264) | ~v2_pre_topc(A_264))), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.22/2.44  tff(c_3933, plain, (![A_398, B_399]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_398), B_399), A_398) | ~v1_tdlat_3(A_398) | ~l1_pre_topc(A_398) | ~v2_pre_topc(A_398) | ~m1_subset_1(B_399, k1_zfmisc_1(u1_struct_0(A_398))))), inference(resolution, [status(thm)], [c_12, c_2168])).
% 7.22/2.44  tff(c_34, plain, (![B_33, A_31]: (v4_pre_topc(B_33, A_31) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_31), B_33), A_31) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.22/2.44  tff(c_3957, plain, (![B_402, A_403]: (v4_pre_topc(B_402, A_403) | ~v1_tdlat_3(A_403) | ~l1_pre_topc(A_403) | ~v2_pre_topc(A_403) | ~m1_subset_1(B_402, k1_zfmisc_1(u1_struct_0(A_403))))), inference(resolution, [status(thm)], [c_3933, c_34])).
% 7.22/2.44  tff(c_3995, plain, (![A_403]: (v4_pre_topc('#skF_5', A_403) | ~v1_tdlat_3(A_403) | ~l1_pre_topc(A_403) | ~v2_pre_topc(A_403))), inference(resolution, [status(thm)], [c_2040, c_3957])).
% 7.22/2.44  tff(c_8, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.22/2.44  tff(c_140, plain, (![A_88, B_89]: (k1_setfam_1(k2_tarski(A_88, B_89))=k3_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.22/2.44  tff(c_161, plain, (![B_93, A_94]: (k1_setfam_1(k2_tarski(B_93, A_94))=k3_xboole_0(A_94, B_93))), inference(superposition, [status(thm), theory('equality')], [c_8, c_140])).
% 7.22/2.44  tff(c_18, plain, (![A_16, B_17]: (k1_setfam_1(k2_tarski(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.22/2.44  tff(c_185, plain, (![B_97, A_98]: (k3_xboole_0(B_97, A_98)=k3_xboole_0(A_98, B_97))), inference(superposition, [status(thm), theory('equality')], [c_161, c_18])).
% 7.22/2.44  tff(c_85, plain, (![A_82, B_83]: (r1_tarski(k3_xboole_0(A_82, B_83), A_82))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.22/2.44  tff(c_90, plain, (![B_83]: (k3_xboole_0(k1_xboole_0, B_83)=k1_xboole_0)), inference(resolution, [status(thm)], [c_85, c_6])).
% 7.22/2.44  tff(c_201, plain, (![B_97]: (k3_xboole_0(B_97, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_185, c_90])).
% 7.22/2.44  tff(c_324, plain, (![A_111, B_112, C_113]: (k9_subset_1(A_111, B_112, C_113)=k3_xboole_0(B_112, C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(A_111)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.22/2.44  tff(c_330, plain, (![A_15, B_112]: (k9_subset_1(A_15, B_112, k1_xboole_0)=k3_xboole_0(B_112, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_324])).
% 7.22/2.44  tff(c_334, plain, (![A_15, B_112]: (k9_subset_1(A_15, B_112, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_201, c_330])).
% 7.22/2.44  tff(c_2032, plain, (![A_15, B_112]: (k9_subset_1(A_15, B_112, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2026, c_2026, c_334])).
% 7.22/2.44  tff(c_3883, plain, (![A_393, B_394, D_395]: (k9_subset_1(u1_struct_0(A_393), B_394, D_395)!='#skF_2'(A_393, B_394) | ~v4_pre_topc(D_395, A_393) | ~m1_subset_1(D_395, k1_zfmisc_1(u1_struct_0(A_393))) | v2_tex_2(B_394, A_393) | ~m1_subset_1(B_394, k1_zfmisc_1(u1_struct_0(A_393))) | ~l1_pre_topc(A_393))), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.22/2.44  tff(c_3907, plain, (![A_393, B_112]: ('#skF_2'(A_393, B_112)!='#skF_5' | ~v4_pre_topc('#skF_5', A_393) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_393))) | v2_tex_2(B_112, A_393) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_393))) | ~l1_pre_topc(A_393))), inference(superposition, [status(thm), theory('equality')], [c_2032, c_3883])).
% 7.22/2.44  tff(c_4925, plain, (![A_438, B_439]: ('#skF_2'(A_438, B_439)!='#skF_5' | ~v4_pre_topc('#skF_5', A_438) | v2_tex_2(B_439, A_438) | ~m1_subset_1(B_439, k1_zfmisc_1(u1_struct_0(A_438))) | ~l1_pre_topc(A_438))), inference(demodulation, [status(thm), theory('equality')], [c_2040, c_3907])).
% 7.22/2.44  tff(c_4972, plain, (![A_440]: ('#skF_2'(A_440, '#skF_5')!='#skF_5' | ~v4_pre_topc('#skF_5', A_440) | v2_tex_2('#skF_5', A_440) | ~l1_pre_topc(A_440))), inference(resolution, [status(thm)], [c_2040, c_4925])).
% 7.22/2.44  tff(c_5203, plain, (![A_443]: ('#skF_2'(A_443, '#skF_5')!='#skF_5' | v2_tex_2('#skF_5', A_443) | ~v1_tdlat_3(A_443) | ~l1_pre_topc(A_443) | ~v2_pre_topc(A_443))), inference(resolution, [status(thm)], [c_3995, c_4972])).
% 7.22/2.44  tff(c_5206, plain, ('#skF_2'('#skF_4', '#skF_5')!='#skF_5' | ~v1_tdlat_3('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_5203, c_70])).
% 7.22/2.44  tff(c_5210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_76, c_2424, c_5206])).
% 7.22/2.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.22/2.44  
% 7.22/2.44  Inference rules
% 7.22/2.44  ----------------------
% 7.22/2.44  #Ref     : 0
% 7.22/2.44  #Sup     : 1284
% 7.22/2.44  #Fact    : 0
% 7.22/2.44  #Define  : 0
% 7.22/2.44  #Split   : 8
% 7.22/2.44  #Chain   : 0
% 7.22/2.44  #Close   : 0
% 7.22/2.44  
% 7.22/2.44  Ordering : KBO
% 7.22/2.44  
% 7.22/2.44  Simplification rules
% 7.22/2.45  ----------------------
% 7.22/2.45  #Subsume      : 122
% 7.22/2.45  #Demod        : 627
% 7.22/2.45  #Tautology    : 370
% 7.22/2.45  #SimpNegUnit  : 18
% 7.22/2.45  #BackRed      : 16
% 7.22/2.45  
% 7.22/2.45  #Partial instantiations: 0
% 7.22/2.45  #Strategies tried      : 1
% 7.22/2.45  
% 7.22/2.45  Timing (in seconds)
% 7.22/2.45  ----------------------
% 7.22/2.45  Preprocessing        : 0.37
% 7.22/2.45  Parsing              : 0.20
% 7.22/2.45  CNF conversion       : 0.03
% 7.22/2.45  Main loop            : 1.29
% 7.22/2.45  Inferencing          : 0.46
% 7.22/2.45  Reduction            : 0.43
% 7.22/2.45  Demodulation         : 0.31
% 7.22/2.45  BG Simplification    : 0.06
% 7.22/2.45  Subsumption          : 0.25
% 7.22/2.45  Abstraction          : 0.07
% 7.22/2.45  MUC search           : 0.00
% 7.22/2.45  Cooper               : 0.00
% 7.22/2.45  Total                : 1.71
% 7.22/2.45  Index Insertion      : 0.00
% 7.22/2.45  Index Deletion       : 0.00
% 7.22/2.45  Index Matching       : 0.00
% 7.22/2.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
