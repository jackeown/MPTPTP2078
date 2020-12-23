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
% DateTime   : Thu Dec  3 10:30:37 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 360 expanded)
%              Number of leaves         :   45 ( 146 expanded)
%              Depth                    :    9
%              Number of atoms          :  303 (1740 expanded)
%              Number of equality atoms :   55 ( 264 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_borsuk_1,type,(
    v3_borsuk_1: ( $i * $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v4_tex_2,type,(
    v4_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_191,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_tex_2(B,A)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & v5_pre_topc(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( v3_borsuk_1(C,A,B)
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(B))
                     => ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( D = E
                           => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,k6_domain_1(u1_struct_0(B),D)) = k2_pre_topc(A,k6_domain_1(u1_struct_0(A),E)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tex_2)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_114,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_97,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_152,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_tex_2(B,A)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & v5_pre_topc(C,A,B)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v3_borsuk_1(C,A,B)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(A)))
                       => ( D = E
                         => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,D) = k2_pre_topc(A,E) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tex_2)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & ~ v1_xboole_0(C)
              & v1_funct_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_funct_2)).

tff(c_64,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_28,plain,(
    ! [A_18] :
      ( l1_struct_0(A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_681,plain,(
    ! [A_184,B_185] :
      ( k6_domain_1(A_184,B_185) = k1_tarski(B_185)
      | ~ m1_subset_1(B_185,A_184)
      | v1_xboole_0(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_697,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_681])).

tff(c_722,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_697])).

tff(c_32,plain,(
    ! [A_22] :
      ( ~ v1_xboole_0(u1_struct_0(A_22))
      | ~ l1_struct_0(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_725,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_722,c_32])).

tff(c_731,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_725])).

tff(c_735,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_731])).

tff(c_739,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_735])).

tff(c_741,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_697])).

tff(c_58,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_121,plain,(
    ! [B_98,A_99] :
      ( l1_pre_topc(B_98)
      | ~ m1_pre_topc(B_98,A_99)
      | ~ l1_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_124,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_121])).

tff(c_127,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_124])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_42,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_71,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46])).

tff(c_696,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_71,c_681])).

tff(c_698,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_696])).

tff(c_701,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_698,c_32])).

tff(c_707,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_701])).

tff(c_711,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_707])).

tff(c_715,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_711])).

tff(c_717,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_696])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_54,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [B_7] : k2_zfmisc_1(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( m1_subset_1(k1_tarski(B_9),k1_zfmisc_1(A_8))
      | k1_xboole_0 = A_8
      | ~ m1_subset_1(B_9,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_219,plain,(
    ! [C_112,A_113,B_114] :
      ( m1_subset_1(C_112,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ m1_subset_1(C_112,k1_zfmisc_1(u1_struct_0(B_114)))
      | ~ m1_pre_topc(B_114,A_113)
      | ~ l1_pre_topc(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_285,plain,(
    ! [B_124,A_125,B_126] :
      ( m1_subset_1(k1_tarski(B_124),k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ m1_pre_topc(B_126,A_125)
      | ~ l1_pre_topc(A_125)
      | u1_struct_0(B_126) = k1_xboole_0
      | ~ m1_subset_1(B_124,u1_struct_0(B_126)) ) ),
    inference(resolution,[status(thm)],[c_16,c_219])).

tff(c_287,plain,(
    ! [B_124] :
      ( m1_subset_1(k1_tarski(B_124),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | u1_struct_0('#skF_3') = k1_xboole_0
      | ~ m1_subset_1(B_124,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_58,c_285])).

tff(c_290,plain,(
    ! [B_124] :
      ( m1_subset_1(k1_tarski(B_124),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | u1_struct_0('#skF_3') = k1_xboole_0
      | ~ m1_subset_1(B_124,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_287])).

tff(c_291,plain,(
    u1_struct_0('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_290])).

tff(c_144,plain,(
    ! [A_105,B_106] :
      ( k6_domain_1(A_105,B_106) = k1_tarski(B_106)
      | ~ m1_subset_1(B_106,A_105)
      | v1_xboole_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_155,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_71,c_144])).

tff(c_157,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_155])).

tff(c_160,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_157,c_32])).

tff(c_166,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_160])).

tff(c_170,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_166])).

tff(c_174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_170])).

tff(c_176,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_296,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_176])).

tff(c_305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_296])).

tff(c_307,plain,(
    u1_struct_0('#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_290])).

tff(c_68,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_66,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_60,plain,(
    v4_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_52,plain,(
    v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_48,plain,(
    v3_borsuk_1('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_337,plain,(
    ! [A_130,B_131,C_132,E_133] :
      ( k8_relset_1(u1_struct_0(A_130),u1_struct_0(B_131),C_132,E_133) = k2_pre_topc(A_130,E_133)
      | ~ m1_subset_1(E_133,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ m1_subset_1(E_133,k1_zfmisc_1(u1_struct_0(B_131)))
      | ~ v3_borsuk_1(C_132,A_130,B_131)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_130),u1_struct_0(B_131))))
      | ~ v5_pre_topc(C_132,A_130,B_131)
      | ~ v1_funct_2(C_132,u1_struct_0(A_130),u1_struct_0(B_131))
      | ~ v1_funct_1(C_132)
      | ~ m1_pre_topc(B_131,A_130)
      | ~ v4_tex_2(B_131,A_130)
      | v2_struct_0(B_131)
      | ~ l1_pre_topc(A_130)
      | ~ v3_tdlat_3(A_130)
      | ~ v2_pre_topc(A_130)
      | v2_struct_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_459,plain,(
    ! [A_151,B_152,C_153,B_154] :
      ( k8_relset_1(u1_struct_0(A_151),u1_struct_0(B_152),C_153,k1_tarski(B_154)) = k2_pre_topc(A_151,k1_tarski(B_154))
      | ~ m1_subset_1(k1_tarski(B_154),k1_zfmisc_1(u1_struct_0(B_152)))
      | ~ v3_borsuk_1(C_153,A_151,B_152)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_151),u1_struct_0(B_152))))
      | ~ v5_pre_topc(C_153,A_151,B_152)
      | ~ v1_funct_2(C_153,u1_struct_0(A_151),u1_struct_0(B_152))
      | ~ v1_funct_1(C_153)
      | ~ m1_pre_topc(B_152,A_151)
      | ~ v4_tex_2(B_152,A_151)
      | v2_struct_0(B_152)
      | ~ l1_pre_topc(A_151)
      | ~ v3_tdlat_3(A_151)
      | ~ v2_pre_topc(A_151)
      | v2_struct_0(A_151)
      | u1_struct_0(A_151) = k1_xboole_0
      | ~ m1_subset_1(B_154,u1_struct_0(A_151)) ) ),
    inference(resolution,[status(thm)],[c_16,c_337])).

tff(c_603,plain,(
    ! [A_173,B_174,C_175,B_176] :
      ( k8_relset_1(u1_struct_0(A_173),u1_struct_0(B_174),C_175,k1_tarski(B_176)) = k2_pre_topc(A_173,k1_tarski(B_176))
      | ~ v3_borsuk_1(C_175,A_173,B_174)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_173),u1_struct_0(B_174))))
      | ~ v5_pre_topc(C_175,A_173,B_174)
      | ~ v1_funct_2(C_175,u1_struct_0(A_173),u1_struct_0(B_174))
      | ~ v1_funct_1(C_175)
      | ~ m1_pre_topc(B_174,A_173)
      | ~ v4_tex_2(B_174,A_173)
      | v2_struct_0(B_174)
      | ~ l1_pre_topc(A_173)
      | ~ v3_tdlat_3(A_173)
      | ~ v2_pre_topc(A_173)
      | v2_struct_0(A_173)
      | u1_struct_0(A_173) = k1_xboole_0
      | ~ m1_subset_1(B_176,u1_struct_0(A_173))
      | u1_struct_0(B_174) = k1_xboole_0
      | ~ m1_subset_1(B_176,u1_struct_0(B_174)) ) ),
    inference(resolution,[status(thm)],[c_16,c_459])).

tff(c_608,plain,(
    ! [B_176] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski(B_176)) = k2_pre_topc('#skF_2',k1_tarski(B_176))
      | ~ v3_borsuk_1('#skF_4','#skF_2','#skF_3')
      | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | ~ v4_tex_2('#skF_3','#skF_2')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | u1_struct_0('#skF_2') = k1_xboole_0
      | ~ m1_subset_1(B_176,u1_struct_0('#skF_2'))
      | u1_struct_0('#skF_3') = k1_xboole_0
      | ~ m1_subset_1(B_176,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_50,c_603])).

tff(c_612,plain,(
    ! [B_176] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski(B_176)) = k2_pre_topc('#skF_2',k1_tarski(B_176))
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | u1_struct_0('#skF_2') = k1_xboole_0
      | ~ m1_subset_1(B_176,u1_struct_0('#skF_2'))
      | u1_struct_0('#skF_3') = k1_xboole_0
      | ~ m1_subset_1(B_176,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_60,c_58,c_56,c_54,c_52,c_48,c_608])).

tff(c_613,plain,(
    ! [B_176] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski(B_176)) = k2_pre_topc('#skF_2',k1_tarski(B_176))
      | u1_struct_0('#skF_2') = k1_xboole_0
      | ~ m1_subset_1(B_176,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_176,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_307,c_70,c_62,c_612])).

tff(c_614,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_613])).

tff(c_154,plain,
    ( k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(resolution,[status(thm)],[c_50,c_144])).

tff(c_239,plain,(
    v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_177,plain,(
    ! [B_107,A_108] :
      ( m1_subset_1(k1_tarski(B_107),k1_zfmisc_1(A_108))
      | k1_xboole_0 = A_108
      | ~ m1_subset_1(B_107,A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ! [C_12,B_11,A_10] :
      ( ~ v1_xboole_0(C_12)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(C_12))
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_214,plain,(
    ! [A_109,A_110,B_111] :
      ( ~ v1_xboole_0(A_109)
      | ~ r2_hidden(A_110,k1_tarski(B_111))
      | k1_xboole_0 = A_109
      | ~ m1_subset_1(B_111,A_109) ) ),
    inference(resolution,[status(thm)],[c_177,c_18])).

tff(c_224,plain,(
    ! [A_115,B_116] :
      ( ~ v1_xboole_0(A_115)
      | k1_xboole_0 = A_115
      | ~ m1_subset_1(B_116,A_115)
      | v1_xboole_0(k1_tarski(B_116)) ) ),
    inference(resolution,[status(thm)],[c_4,c_214])).

tff(c_233,plain,(
    ! [A_8,B_9] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_8))
      | k1_zfmisc_1(A_8) = k1_xboole_0
      | v1_xboole_0(k1_tarski(k1_tarski(B_9)))
      | k1_xboole_0 = A_8
      | ~ m1_subset_1(B_9,A_8) ) ),
    inference(resolution,[status(thm)],[c_16,c_224])).

tff(c_245,plain,(
    ! [B_9] :
      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))) = k1_xboole_0
      | v1_xboole_0(k1_tarski(k1_tarski(B_9)))
      | k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) = k1_xboole_0
      | ~ m1_subset_1(B_9,k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_239,c_233])).

tff(c_449,plain,(
    k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_245])).

tff(c_139,plain,(
    ! [C_102,B_103,A_104] :
      ( ~ v1_xboole_0(C_102)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(C_102))
      | ~ r2_hidden(A_104,B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_142,plain,(
    ! [A_104] :
      ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))
      | ~ r2_hidden(A_104,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_139])).

tff(c_143,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_452,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_449,c_143])).

tff(c_456,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_452])).

tff(c_458,plain,(
    k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_245])).

tff(c_618,plain,(
    k2_zfmisc_1(k1_xboole_0,u1_struct_0('#skF_3')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_614,c_458])).

tff(c_637,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_618])).

tff(c_645,plain,(
    ! [B_180] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski(B_180)) = k2_pre_topc('#skF_2',k1_tarski(B_180))
      | ~ m1_subset_1(B_180,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_180,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_613])).

tff(c_156,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_144])).

tff(c_189,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_193,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_189,c_32])).

tff(c_199,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_193])).

tff(c_203,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_199])).

tff(c_207,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_203])).

tff(c_208,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_175,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_40,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_72,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_6')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40])).

tff(c_238,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) != k2_pre_topc('#skF_2',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_175,c_72])).

tff(c_651,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_645,c_238])).

tff(c_659,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_44,c_651])).

tff(c_662,plain,(
    ! [A_181] : ~ r2_hidden(A_181,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_667,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_662])).

tff(c_789,plain,(
    ! [C_198,A_199,B_200] :
      ( ~ v1_xboole_0(C_198)
      | ~ v1_funct_2(C_198,A_199,B_200)
      | ~ v1_funct_1(C_198)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(A_199,B_200)))
      | v1_xboole_0(B_200)
      | v1_xboole_0(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_796,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_789])).

tff(c_806,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_667,c_796])).

tff(c_808,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_741,c_717,c_806])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:20:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.50/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.54  
% 3.55/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.54  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 3.55/1.54  
% 3.55/1.54  %Foreground sorts:
% 3.55/1.54  
% 3.55/1.54  
% 3.55/1.54  %Background operators:
% 3.55/1.54  
% 3.55/1.54  
% 3.55/1.54  %Foreground operators:
% 3.55/1.54  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.55/1.54  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 3.55/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.55/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.55/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.55/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.55/1.54  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.55/1.54  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.55/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.55/1.54  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 3.55/1.54  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.55/1.54  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.55/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.55/1.54  tff('#skF_5', type, '#skF_5': $i).
% 3.55/1.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.55/1.54  tff('#skF_6', type, '#skF_6': $i).
% 3.55/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.55/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.55/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.55/1.54  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.55/1.54  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.55/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.55/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.55/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.55/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.55/1.54  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.55/1.54  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.55/1.54  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.55/1.54  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.55/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.55/1.54  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.55/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.55/1.54  
% 3.55/1.56  tff(f_191, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tex_2)).
% 3.55/1.56  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.55/1.56  tff(f_114, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.55/1.56  tff(f_97, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.55/1.56  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.55/1.56  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.55/1.56  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.55/1.56  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.55/1.56  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 3.55/1.56  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 3.55/1.56  tff(f_152, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tex_2)).
% 3.55/1.56  tff(f_54, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.55/1.56  tff(f_78, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => ((v1_funct_1(C) & ~v1_xboole_0(C)) & v1_funct_2(C, A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_funct_2)).
% 3.55/1.56  tff(c_64, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_191])).
% 3.55/1.56  tff(c_28, plain, (![A_18]: (l1_struct_0(A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.55/1.56  tff(c_70, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_191])).
% 3.55/1.56  tff(c_44, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_191])).
% 3.55/1.56  tff(c_681, plain, (![A_184, B_185]: (k6_domain_1(A_184, B_185)=k1_tarski(B_185) | ~m1_subset_1(B_185, A_184) | v1_xboole_0(A_184))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.55/1.56  tff(c_697, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_681])).
% 3.55/1.56  tff(c_722, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_697])).
% 3.55/1.56  tff(c_32, plain, (![A_22]: (~v1_xboole_0(u1_struct_0(A_22)) | ~l1_struct_0(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.55/1.56  tff(c_725, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_722, c_32])).
% 3.55/1.56  tff(c_731, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_70, c_725])).
% 3.55/1.56  tff(c_735, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_731])).
% 3.55/1.56  tff(c_739, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_735])).
% 3.55/1.56  tff(c_741, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_697])).
% 3.55/1.56  tff(c_58, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_191])).
% 3.55/1.56  tff(c_121, plain, (![B_98, A_99]: (l1_pre_topc(B_98) | ~m1_pre_topc(B_98, A_99) | ~l1_pre_topc(A_99))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.55/1.56  tff(c_124, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_58, c_121])).
% 3.55/1.56  tff(c_127, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_124])).
% 3.55/1.56  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_191])).
% 3.55/1.56  tff(c_42, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_191])).
% 3.55/1.56  tff(c_46, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_191])).
% 3.55/1.56  tff(c_71, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46])).
% 3.55/1.56  tff(c_696, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_71, c_681])).
% 3.55/1.56  tff(c_698, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_696])).
% 3.55/1.56  tff(c_701, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_698, c_32])).
% 3.55/1.56  tff(c_707, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_701])).
% 3.55/1.56  tff(c_711, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_28, c_707])).
% 3.55/1.56  tff(c_715, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_127, c_711])).
% 3.55/1.56  tff(c_717, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_696])).
% 3.55/1.56  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_191])).
% 3.55/1.56  tff(c_54, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_191])).
% 3.55/1.56  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.55/1.56  tff(c_14, plain, (![B_7]: (k2_zfmisc_1(k1_xboole_0, B_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.55/1.56  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.55/1.56  tff(c_16, plain, (![B_9, A_8]: (m1_subset_1(k1_tarski(B_9), k1_zfmisc_1(A_8)) | k1_xboole_0=A_8 | ~m1_subset_1(B_9, A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.55/1.56  tff(c_219, plain, (![C_112, A_113, B_114]: (m1_subset_1(C_112, k1_zfmisc_1(u1_struct_0(A_113))) | ~m1_subset_1(C_112, k1_zfmisc_1(u1_struct_0(B_114))) | ~m1_pre_topc(B_114, A_113) | ~l1_pre_topc(A_113))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.55/1.56  tff(c_285, plain, (![B_124, A_125, B_126]: (m1_subset_1(k1_tarski(B_124), k1_zfmisc_1(u1_struct_0(A_125))) | ~m1_pre_topc(B_126, A_125) | ~l1_pre_topc(A_125) | u1_struct_0(B_126)=k1_xboole_0 | ~m1_subset_1(B_124, u1_struct_0(B_126)))), inference(resolution, [status(thm)], [c_16, c_219])).
% 3.55/1.56  tff(c_287, plain, (![B_124]: (m1_subset_1(k1_tarski(B_124), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | u1_struct_0('#skF_3')=k1_xboole_0 | ~m1_subset_1(B_124, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_58, c_285])).
% 3.55/1.56  tff(c_290, plain, (![B_124]: (m1_subset_1(k1_tarski(B_124), k1_zfmisc_1(u1_struct_0('#skF_2'))) | u1_struct_0('#skF_3')=k1_xboole_0 | ~m1_subset_1(B_124, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_287])).
% 3.55/1.56  tff(c_291, plain, (u1_struct_0('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_290])).
% 3.55/1.56  tff(c_144, plain, (![A_105, B_106]: (k6_domain_1(A_105, B_106)=k1_tarski(B_106) | ~m1_subset_1(B_106, A_105) | v1_xboole_0(A_105))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.55/1.56  tff(c_155, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_71, c_144])).
% 3.55/1.56  tff(c_157, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_155])).
% 3.55/1.56  tff(c_160, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_157, c_32])).
% 3.55/1.56  tff(c_166, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_160])).
% 3.55/1.56  tff(c_170, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_28, c_166])).
% 3.55/1.56  tff(c_174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_127, c_170])).
% 3.55/1.56  tff(c_176, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_155])).
% 3.55/1.56  tff(c_296, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_291, c_176])).
% 3.55/1.56  tff(c_305, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_296])).
% 3.55/1.56  tff(c_307, plain, (u1_struct_0('#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_290])).
% 3.55/1.56  tff(c_68, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_191])).
% 3.55/1.56  tff(c_66, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_191])).
% 3.55/1.56  tff(c_60, plain, (v4_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_191])).
% 3.55/1.56  tff(c_52, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_191])).
% 3.55/1.56  tff(c_48, plain, (v3_borsuk_1('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_191])).
% 3.55/1.56  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_191])).
% 3.55/1.56  tff(c_337, plain, (![A_130, B_131, C_132, E_133]: (k8_relset_1(u1_struct_0(A_130), u1_struct_0(B_131), C_132, E_133)=k2_pre_topc(A_130, E_133) | ~m1_subset_1(E_133, k1_zfmisc_1(u1_struct_0(A_130))) | ~m1_subset_1(E_133, k1_zfmisc_1(u1_struct_0(B_131))) | ~v3_borsuk_1(C_132, A_130, B_131) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_130), u1_struct_0(B_131)))) | ~v5_pre_topc(C_132, A_130, B_131) | ~v1_funct_2(C_132, u1_struct_0(A_130), u1_struct_0(B_131)) | ~v1_funct_1(C_132) | ~m1_pre_topc(B_131, A_130) | ~v4_tex_2(B_131, A_130) | v2_struct_0(B_131) | ~l1_pre_topc(A_130) | ~v3_tdlat_3(A_130) | ~v2_pre_topc(A_130) | v2_struct_0(A_130))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.55/1.56  tff(c_459, plain, (![A_151, B_152, C_153, B_154]: (k8_relset_1(u1_struct_0(A_151), u1_struct_0(B_152), C_153, k1_tarski(B_154))=k2_pre_topc(A_151, k1_tarski(B_154)) | ~m1_subset_1(k1_tarski(B_154), k1_zfmisc_1(u1_struct_0(B_152))) | ~v3_borsuk_1(C_153, A_151, B_152) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_151), u1_struct_0(B_152)))) | ~v5_pre_topc(C_153, A_151, B_152) | ~v1_funct_2(C_153, u1_struct_0(A_151), u1_struct_0(B_152)) | ~v1_funct_1(C_153) | ~m1_pre_topc(B_152, A_151) | ~v4_tex_2(B_152, A_151) | v2_struct_0(B_152) | ~l1_pre_topc(A_151) | ~v3_tdlat_3(A_151) | ~v2_pre_topc(A_151) | v2_struct_0(A_151) | u1_struct_0(A_151)=k1_xboole_0 | ~m1_subset_1(B_154, u1_struct_0(A_151)))), inference(resolution, [status(thm)], [c_16, c_337])).
% 3.55/1.56  tff(c_603, plain, (![A_173, B_174, C_175, B_176]: (k8_relset_1(u1_struct_0(A_173), u1_struct_0(B_174), C_175, k1_tarski(B_176))=k2_pre_topc(A_173, k1_tarski(B_176)) | ~v3_borsuk_1(C_175, A_173, B_174) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_173), u1_struct_0(B_174)))) | ~v5_pre_topc(C_175, A_173, B_174) | ~v1_funct_2(C_175, u1_struct_0(A_173), u1_struct_0(B_174)) | ~v1_funct_1(C_175) | ~m1_pre_topc(B_174, A_173) | ~v4_tex_2(B_174, A_173) | v2_struct_0(B_174) | ~l1_pre_topc(A_173) | ~v3_tdlat_3(A_173) | ~v2_pre_topc(A_173) | v2_struct_0(A_173) | u1_struct_0(A_173)=k1_xboole_0 | ~m1_subset_1(B_176, u1_struct_0(A_173)) | u1_struct_0(B_174)=k1_xboole_0 | ~m1_subset_1(B_176, u1_struct_0(B_174)))), inference(resolution, [status(thm)], [c_16, c_459])).
% 3.55/1.56  tff(c_608, plain, (![B_176]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski(B_176))=k2_pre_topc('#skF_2', k1_tarski(B_176)) | ~v3_borsuk_1('#skF_4', '#skF_2', '#skF_3') | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | ~v4_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | u1_struct_0('#skF_2')=k1_xboole_0 | ~m1_subset_1(B_176, u1_struct_0('#skF_2')) | u1_struct_0('#skF_3')=k1_xboole_0 | ~m1_subset_1(B_176, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_50, c_603])).
% 3.55/1.56  tff(c_612, plain, (![B_176]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski(B_176))=k2_pre_topc('#skF_2', k1_tarski(B_176)) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | u1_struct_0('#skF_2')=k1_xboole_0 | ~m1_subset_1(B_176, u1_struct_0('#skF_2')) | u1_struct_0('#skF_3')=k1_xboole_0 | ~m1_subset_1(B_176, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_60, c_58, c_56, c_54, c_52, c_48, c_608])).
% 3.55/1.56  tff(c_613, plain, (![B_176]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski(B_176))=k2_pre_topc('#skF_2', k1_tarski(B_176)) | u1_struct_0('#skF_2')=k1_xboole_0 | ~m1_subset_1(B_176, u1_struct_0('#skF_2')) | ~m1_subset_1(B_176, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_307, c_70, c_62, c_612])).
% 3.55/1.56  tff(c_614, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_613])).
% 3.55/1.56  tff(c_154, plain, (k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_50, c_144])).
% 3.55/1.56  tff(c_239, plain, (v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(splitLeft, [status(thm)], [c_154])).
% 3.55/1.56  tff(c_177, plain, (![B_107, A_108]: (m1_subset_1(k1_tarski(B_107), k1_zfmisc_1(A_108)) | k1_xboole_0=A_108 | ~m1_subset_1(B_107, A_108))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.55/1.56  tff(c_18, plain, (![C_12, B_11, A_10]: (~v1_xboole_0(C_12) | ~m1_subset_1(B_11, k1_zfmisc_1(C_12)) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.55/1.56  tff(c_214, plain, (![A_109, A_110, B_111]: (~v1_xboole_0(A_109) | ~r2_hidden(A_110, k1_tarski(B_111)) | k1_xboole_0=A_109 | ~m1_subset_1(B_111, A_109))), inference(resolution, [status(thm)], [c_177, c_18])).
% 3.55/1.56  tff(c_224, plain, (![A_115, B_116]: (~v1_xboole_0(A_115) | k1_xboole_0=A_115 | ~m1_subset_1(B_116, A_115) | v1_xboole_0(k1_tarski(B_116)))), inference(resolution, [status(thm)], [c_4, c_214])).
% 3.55/1.56  tff(c_233, plain, (![A_8, B_9]: (~v1_xboole_0(k1_zfmisc_1(A_8)) | k1_zfmisc_1(A_8)=k1_xboole_0 | v1_xboole_0(k1_tarski(k1_tarski(B_9))) | k1_xboole_0=A_8 | ~m1_subset_1(B_9, A_8))), inference(resolution, [status(thm)], [c_16, c_224])).
% 3.55/1.56  tff(c_245, plain, (![B_9]: (k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))=k1_xboole_0 | v1_xboole_0(k1_tarski(k1_tarski(B_9))) | k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))=k1_xboole_0 | ~m1_subset_1(B_9, k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_239, c_233])).
% 3.55/1.56  tff(c_449, plain, (k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_245])).
% 3.55/1.56  tff(c_139, plain, (![C_102, B_103, A_104]: (~v1_xboole_0(C_102) | ~m1_subset_1(B_103, k1_zfmisc_1(C_102)) | ~r2_hidden(A_104, B_103))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.55/1.56  tff(c_142, plain, (![A_104]: (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))) | ~r2_hidden(A_104, '#skF_4'))), inference(resolution, [status(thm)], [c_50, c_139])).
% 3.55/1.56  tff(c_143, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_142])).
% 3.55/1.56  tff(c_452, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_449, c_143])).
% 3.55/1.56  tff(c_456, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_452])).
% 3.55/1.56  tff(c_458, plain, (k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_245])).
% 3.55/1.56  tff(c_618, plain, (k2_zfmisc_1(k1_xboole_0, u1_struct_0('#skF_3'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_614, c_458])).
% 3.55/1.56  tff(c_637, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_618])).
% 3.55/1.56  tff(c_645, plain, (![B_180]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski(B_180))=k2_pre_topc('#skF_2', k1_tarski(B_180)) | ~m1_subset_1(B_180, u1_struct_0('#skF_2')) | ~m1_subset_1(B_180, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_613])).
% 3.55/1.56  tff(c_156, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_144])).
% 3.55/1.56  tff(c_189, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_156])).
% 3.55/1.56  tff(c_193, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_189, c_32])).
% 3.55/1.56  tff(c_199, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_70, c_193])).
% 3.55/1.56  tff(c_203, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_199])).
% 3.55/1.56  tff(c_207, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_203])).
% 3.55/1.56  tff(c_208, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_156])).
% 3.55/1.56  tff(c_175, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_155])).
% 3.55/1.56  tff(c_40, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_191])).
% 3.55/1.56  tff(c_72, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_6'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40])).
% 3.55/1.56  tff(c_238, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_175, c_72])).
% 3.55/1.56  tff(c_651, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_645, c_238])).
% 3.55/1.56  tff(c_659, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_44, c_651])).
% 3.55/1.56  tff(c_662, plain, (![A_181]: (~r2_hidden(A_181, '#skF_4'))), inference(splitRight, [status(thm)], [c_142])).
% 3.55/1.56  tff(c_667, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_662])).
% 3.55/1.56  tff(c_789, plain, (![C_198, A_199, B_200]: (~v1_xboole_0(C_198) | ~v1_funct_2(C_198, A_199, B_200) | ~v1_funct_1(C_198) | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(A_199, B_200))) | v1_xboole_0(B_200) | v1_xboole_0(A_199))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.55/1.56  tff(c_796, plain, (~v1_xboole_0('#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_789])).
% 3.55/1.56  tff(c_806, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_667, c_796])).
% 3.55/1.56  tff(c_808, plain, $false, inference(negUnitSimplification, [status(thm)], [c_741, c_717, c_806])).
% 3.55/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.56  
% 3.55/1.56  Inference rules
% 3.55/1.56  ----------------------
% 3.55/1.56  #Ref     : 0
% 3.55/1.56  #Sup     : 137
% 3.55/1.56  #Fact    : 0
% 3.55/1.56  #Define  : 0
% 3.55/1.56  #Split   : 19
% 3.55/1.56  #Chain   : 0
% 3.55/1.56  #Close   : 0
% 3.55/1.56  
% 3.55/1.56  Ordering : KBO
% 3.55/1.57  
% 3.55/1.57  Simplification rules
% 3.55/1.57  ----------------------
% 3.55/1.57  #Subsume      : 8
% 3.55/1.57  #Demod        : 145
% 3.55/1.57  #Tautology    : 50
% 3.55/1.57  #SimpNegUnit  : 22
% 3.55/1.57  #BackRed      : 49
% 3.55/1.57  
% 3.55/1.57  #Partial instantiations: 0
% 3.55/1.57  #Strategies tried      : 1
% 3.55/1.57  
% 3.55/1.57  Timing (in seconds)
% 3.55/1.57  ----------------------
% 3.55/1.57  Preprocessing        : 0.35
% 3.55/1.57  Parsing              : 0.19
% 3.55/1.57  CNF conversion       : 0.03
% 3.55/1.57  Main loop            : 0.43
% 3.55/1.57  Inferencing          : 0.14
% 3.55/1.57  Reduction            : 0.14
% 3.55/1.57  Demodulation         : 0.09
% 3.55/1.57  BG Simplification    : 0.02
% 3.55/1.57  Subsumption          : 0.09
% 3.55/1.57  Abstraction          : 0.02
% 3.55/1.57  MUC search           : 0.00
% 3.55/1.57  Cooper               : 0.00
% 3.55/1.57  Total                : 0.83
% 3.55/1.57  Index Insertion      : 0.00
% 3.55/1.57  Index Deletion       : 0.00
% 3.55/1.57  Index Matching       : 0.00
% 3.55/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
