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
% DateTime   : Thu Dec  3 10:30:32 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 296 expanded)
%              Number of leaves         :   31 ( 120 expanded)
%              Depth                    :   22
%              Number of atoms          :  202 ( 999 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_131,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ? [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
            & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_34,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
          & ~ v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_subset_1)).

tff(f_116,axiom,(
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

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ~ ( r2_hidden(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = k6_domain_1(u1_struct_0(A),C) ) ) ) )
           => v2_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tex_2)).

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_28,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_6,plain,(
    ! [A_3] :
      ( l1_struct_0(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_32,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_30,plain,(
    v3_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_4,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),k1_zfmisc_1(A_1))
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_83,plain,(
    ! [A_50,B_51] :
      ( m1_subset_1('#skF_3'(A_50,B_51),k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ v2_tex_2(B_51,A_50)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50)
      | ~ v3_tdlat_3(A_50)
      | ~ v2_pre_topc(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_26,plain,(
    ! [B_31] :
      ( ~ v3_tex_2(B_31,'#skF_4')
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_93,plain,(
    ! [B_51] :
      ( ~ v3_tex_2('#skF_3'('#skF_4',B_51),'#skF_4')
      | ~ v2_tex_2(B_51,'#skF_4')
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v3_tdlat_3('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_83,c_26])).

tff(c_99,plain,(
    ! [B_51] :
      ( ~ v3_tex_2('#skF_3'('#skF_4',B_51),'#skF_4')
      | ~ v2_tex_2(B_51,'#skF_4')
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_93])).

tff(c_101,plain,(
    ! [B_52] :
      ( ~ v3_tex_2('#skF_3'('#skF_4',B_52),'#skF_4')
      | ~ v2_tex_2(B_52,'#skF_4')
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_99])).

tff(c_119,plain,
    ( ~ v3_tex_2('#skF_3'('#skF_4','#skF_1'(u1_struct_0('#skF_4'))),'#skF_4')
    | ~ v2_tex_2('#skF_1'(u1_struct_0('#skF_4')),'#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_101])).

tff(c_120,plain,(
    ~ v2_tex_2('#skF_1'(u1_struct_0('#skF_4')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_119])).

tff(c_18,plain,(
    ! [A_10,B_18] :
      ( m1_subset_1('#skF_2'(A_10,B_18),u1_struct_0(A_10))
      | v2_tex_2(B_18,A_10)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10)
      | ~ v3_tdlat_3(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_12,plain,(
    ! [A_7,B_9] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_7),B_9),A_7)
      | ~ m1_subset_1(B_9,u1_struct_0(A_7))
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k6_domain_1(A_5,B_6),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_55,plain,(
    ! [A_42,B_43] :
      ( v3_tex_2('#skF_3'(A_42,B_43),A_42)
      | ~ v2_tex_2(B_43,A_42)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42)
      | ~ v3_tdlat_3(A_42)
      | ~ v2_pre_topc(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_158,plain,(
    ! [A_65,B_66] :
      ( v3_tex_2('#skF_3'(A_65,k6_domain_1(u1_struct_0(A_65),B_66)),A_65)
      | ~ v2_tex_2(k6_domain_1(u1_struct_0(A_65),B_66),A_65)
      | ~ l1_pre_topc(A_65)
      | ~ v3_tdlat_3(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65)
      | ~ m1_subset_1(B_66,u1_struct_0(A_65))
      | v1_xboole_0(u1_struct_0(A_65)) ) ),
    inference(resolution,[status(thm)],[c_10,c_55])).

tff(c_118,plain,(
    ! [B_6] :
      ( ~ v3_tex_2('#skF_3'('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),B_6)),'#skF_4')
      | ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_4'),B_6),'#skF_4')
      | ~ m1_subset_1(B_6,u1_struct_0('#skF_4'))
      | v1_xboole_0(u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_10,c_101])).

tff(c_122,plain,(
    ! [B_6] :
      ( ~ v3_tex_2('#skF_3'('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),B_6)),'#skF_4')
      | ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_4'),B_6),'#skF_4')
      | ~ m1_subset_1(B_6,u1_struct_0('#skF_4')) ) ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_162,plain,(
    ! [B_66] :
      ( ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_4'),B_66),'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v3_tdlat_3('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(B_66,u1_struct_0('#skF_4'))
      | v1_xboole_0(u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_158,c_122])).

tff(c_165,plain,(
    ! [B_66] :
      ( ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_4'),B_66),'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(B_66,u1_struct_0('#skF_4'))
      | v1_xboole_0(u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_162])).

tff(c_166,plain,(
    ! [B_66] :
      ( ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_4'),B_66),'#skF_4')
      | ~ m1_subset_1(B_66,u1_struct_0('#skF_4'))
      | v1_xboole_0(u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_165])).

tff(c_169,plain,(
    ! [B_69] :
      ( ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_4'),B_69),'#skF_4')
      | ~ m1_subset_1(B_69,u1_struct_0('#skF_4')) ) ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_173,plain,(
    ! [B_9] :
      ( ~ m1_subset_1(B_9,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_169])).

tff(c_176,plain,(
    ! [B_9] :
      ( ~ m1_subset_1(B_9,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_173])).

tff(c_178,plain,(
    ! [B_70] : ~ m1_subset_1(B_70,u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_176])).

tff(c_182,plain,(
    ! [B_18] :
      ( v2_tex_2(B_18,'#skF_4')
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v3_tdlat_3('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_178])).

tff(c_185,plain,(
    ! [B_18] :
      ( v2_tex_2(B_18,'#skF_4')
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_182])).

tff(c_187,plain,(
    ! [B_71] :
      ( v2_tex_2(B_71,'#skF_4')
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_185])).

tff(c_199,plain,
    ( v2_tex_2('#skF_1'(u1_struct_0('#skF_4')),'#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_187])).

tff(c_207,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_199])).

tff(c_8,plain,(
    ! [A_4] :
      ( ~ v1_xboole_0(u1_struct_0(A_4))
      | ~ l1_struct_0(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_210,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_207,c_8])).

tff(c_213,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_210])).

tff(c_216,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_213])).

tff(c_220,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_216])).

tff(c_221,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_224,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_221,c_8])).

tff(c_227,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_224])).

tff(c_230,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_227])).

tff(c_234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_230])).

tff(c_235,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_238,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_235,c_8])).

tff(c_241,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_238])).

tff(c_245,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_241])).

tff(c_249,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_245])).

tff(c_251,plain,(
    v2_tex_2('#skF_1'(u1_struct_0('#skF_4')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_256,plain,(
    ! [A_77] :
      ( v3_tex_2('#skF_3'(A_77,'#skF_1'(u1_struct_0(A_77))),A_77)
      | ~ v2_tex_2('#skF_1'(u1_struct_0(A_77)),A_77)
      | ~ l1_pre_topc(A_77)
      | ~ v3_tdlat_3(A_77)
      | ~ v2_pre_topc(A_77)
      | v2_struct_0(A_77)
      | v1_xboole_0(u1_struct_0(A_77)) ) ),
    inference(resolution,[status(thm)],[c_4,c_55])).

tff(c_250,plain,
    ( ~ v3_tex_2('#skF_3'('#skF_4','#skF_1'(u1_struct_0('#skF_4'))),'#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_252,plain,(
    ~ v3_tex_2('#skF_3'('#skF_4','#skF_1'(u1_struct_0('#skF_4'))),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_250])).

tff(c_259,plain,
    ( ~ v2_tex_2('#skF_1'(u1_struct_0('#skF_4')),'#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v3_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_256,c_252])).

tff(c_262,plain,
    ( v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_251,c_259])).

tff(c_263,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_262])).

tff(c_266,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_263,c_8])).

tff(c_269,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_266])).

tff(c_273,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_269])).

tff(c_277,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_273])).

tff(c_278,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_250])).

tff(c_282,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_278,c_8])).

tff(c_285,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_282])).

tff(c_288,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_285])).

tff(c_292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_288])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:12:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.30  
% 2.21/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.30  %$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.21/1.30  
% 2.21/1.30  %Foreground sorts:
% 2.21/1.30  
% 2.21/1.30  
% 2.21/1.30  %Background operators:
% 2.21/1.30  
% 2.21/1.30  
% 2.21/1.30  %Foreground operators:
% 2.21/1.30  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.21/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.21/1.30  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.21/1.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.21/1.30  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.21/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.30  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.21/1.30  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.21/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.21/1.30  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.21/1.30  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.21/1.30  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.21/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.21/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.21/1.30  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.21/1.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.21/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.21/1.30  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.21/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.21/1.30  
% 2.53/1.32  tff(f_131, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tex_2)).
% 2.53/1.32  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.53/1.32  tff(f_34, axiom, (![A]: (~v1_xboole_0(A) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_subset_1)).
% 2.53/1.32  tff(f_116, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tex_2)).
% 2.53/1.32  tff(f_93, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k6_domain_1(u1_struct_0(A), C)))))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_tex_2)).
% 2.53/1.32  tff(f_65, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 2.53/1.32  tff(f_53, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.53/1.32  tff(f_46, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.53/1.32  tff(c_28, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.53/1.32  tff(c_6, plain, (![A_3]: (l1_struct_0(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.53/1.32  tff(c_34, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.53/1.32  tff(c_32, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.53/1.32  tff(c_30, plain, (v3_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.53/1.32  tff(c_4, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), k1_zfmisc_1(A_1)) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.53/1.32  tff(c_83, plain, (![A_50, B_51]: (m1_subset_1('#skF_3'(A_50, B_51), k1_zfmisc_1(u1_struct_0(A_50))) | ~v2_tex_2(B_51, A_50) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50) | ~v3_tdlat_3(A_50) | ~v2_pre_topc(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.53/1.32  tff(c_26, plain, (![B_31]: (~v3_tex_2(B_31, '#skF_4') | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.53/1.32  tff(c_93, plain, (![B_51]: (~v3_tex_2('#skF_3'('#skF_4', B_51), '#skF_4') | ~v2_tex_2(B_51, '#skF_4') | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v3_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_83, c_26])).
% 2.53/1.32  tff(c_99, plain, (![B_51]: (~v3_tex_2('#skF_3'('#skF_4', B_51), '#skF_4') | ~v2_tex_2(B_51, '#skF_4') | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_93])).
% 2.53/1.32  tff(c_101, plain, (![B_52]: (~v3_tex_2('#skF_3'('#skF_4', B_52), '#skF_4') | ~v2_tex_2(B_52, '#skF_4') | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_34, c_99])).
% 2.53/1.32  tff(c_119, plain, (~v3_tex_2('#skF_3'('#skF_4', '#skF_1'(u1_struct_0('#skF_4'))), '#skF_4') | ~v2_tex_2('#skF_1'(u1_struct_0('#skF_4')), '#skF_4') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_4, c_101])).
% 2.53/1.32  tff(c_120, plain, (~v2_tex_2('#skF_1'(u1_struct_0('#skF_4')), '#skF_4')), inference(splitLeft, [status(thm)], [c_119])).
% 2.53/1.32  tff(c_18, plain, (![A_10, B_18]: (m1_subset_1('#skF_2'(A_10, B_18), u1_struct_0(A_10)) | v2_tex_2(B_18, A_10) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_pre_topc(A_10) | ~v3_tdlat_3(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.53/1.32  tff(c_12, plain, (![A_7, B_9]: (v2_tex_2(k6_domain_1(u1_struct_0(A_7), B_9), A_7) | ~m1_subset_1(B_9, u1_struct_0(A_7)) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.53/1.32  tff(c_10, plain, (![A_5, B_6]: (m1_subset_1(k6_domain_1(A_5, B_6), k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.53/1.32  tff(c_55, plain, (![A_42, B_43]: (v3_tex_2('#skF_3'(A_42, B_43), A_42) | ~v2_tex_2(B_43, A_42) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42) | ~v3_tdlat_3(A_42) | ~v2_pre_topc(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.53/1.32  tff(c_158, plain, (![A_65, B_66]: (v3_tex_2('#skF_3'(A_65, k6_domain_1(u1_struct_0(A_65), B_66)), A_65) | ~v2_tex_2(k6_domain_1(u1_struct_0(A_65), B_66), A_65) | ~l1_pre_topc(A_65) | ~v3_tdlat_3(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65) | ~m1_subset_1(B_66, u1_struct_0(A_65)) | v1_xboole_0(u1_struct_0(A_65)))), inference(resolution, [status(thm)], [c_10, c_55])).
% 2.53/1.32  tff(c_118, plain, (![B_6]: (~v3_tex_2('#skF_3'('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), B_6)), '#skF_4') | ~v2_tex_2(k6_domain_1(u1_struct_0('#skF_4'), B_6), '#skF_4') | ~m1_subset_1(B_6, u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_10, c_101])).
% 2.53/1.32  tff(c_122, plain, (![B_6]: (~v3_tex_2('#skF_3'('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), B_6)), '#skF_4') | ~v2_tex_2(k6_domain_1(u1_struct_0('#skF_4'), B_6), '#skF_4') | ~m1_subset_1(B_6, u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_118])).
% 2.53/1.32  tff(c_162, plain, (![B_66]: (~v2_tex_2(k6_domain_1(u1_struct_0('#skF_4'), B_66), '#skF_4') | ~l1_pre_topc('#skF_4') | ~v3_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_subset_1(B_66, u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_158, c_122])).
% 2.53/1.32  tff(c_165, plain, (![B_66]: (~v2_tex_2(k6_domain_1(u1_struct_0('#skF_4'), B_66), '#skF_4') | v2_struct_0('#skF_4') | ~m1_subset_1(B_66, u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_162])).
% 2.53/1.32  tff(c_166, plain, (![B_66]: (~v2_tex_2(k6_domain_1(u1_struct_0('#skF_4'), B_66), '#skF_4') | ~m1_subset_1(B_66, u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_34, c_165])).
% 2.53/1.32  tff(c_169, plain, (![B_69]: (~v2_tex_2(k6_domain_1(u1_struct_0('#skF_4'), B_69), '#skF_4') | ~m1_subset_1(B_69, u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_166])).
% 2.53/1.32  tff(c_173, plain, (![B_9]: (~m1_subset_1(B_9, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_12, c_169])).
% 2.53/1.32  tff(c_176, plain, (![B_9]: (~m1_subset_1(B_9, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_173])).
% 2.53/1.32  tff(c_178, plain, (![B_70]: (~m1_subset_1(B_70, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_34, c_176])).
% 2.53/1.32  tff(c_182, plain, (![B_18]: (v2_tex_2(B_18, '#skF_4') | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v3_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_178])).
% 2.53/1.32  tff(c_185, plain, (![B_18]: (v2_tex_2(B_18, '#skF_4') | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_182])).
% 2.53/1.32  tff(c_187, plain, (![B_71]: (v2_tex_2(B_71, '#skF_4') | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_34, c_185])).
% 2.53/1.32  tff(c_199, plain, (v2_tex_2('#skF_1'(u1_struct_0('#skF_4')), '#skF_4') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_4, c_187])).
% 2.53/1.32  tff(c_207, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_120, c_199])).
% 2.53/1.32  tff(c_8, plain, (![A_4]: (~v1_xboole_0(u1_struct_0(A_4)) | ~l1_struct_0(A_4) | v2_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.53/1.32  tff(c_210, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_207, c_8])).
% 2.53/1.32  tff(c_213, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_34, c_210])).
% 2.53/1.32  tff(c_216, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6, c_213])).
% 2.53/1.32  tff(c_220, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_216])).
% 2.53/1.32  tff(c_221, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_166])).
% 2.53/1.32  tff(c_224, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_221, c_8])).
% 2.53/1.32  tff(c_227, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_34, c_224])).
% 2.53/1.32  tff(c_230, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6, c_227])).
% 2.53/1.32  tff(c_234, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_230])).
% 2.53/1.32  tff(c_235, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_118])).
% 2.53/1.32  tff(c_238, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_235, c_8])).
% 2.53/1.32  tff(c_241, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_34, c_238])).
% 2.53/1.32  tff(c_245, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6, c_241])).
% 2.53/1.32  tff(c_249, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_245])).
% 2.53/1.32  tff(c_251, plain, (v2_tex_2('#skF_1'(u1_struct_0('#skF_4')), '#skF_4')), inference(splitRight, [status(thm)], [c_119])).
% 2.53/1.32  tff(c_256, plain, (![A_77]: (v3_tex_2('#skF_3'(A_77, '#skF_1'(u1_struct_0(A_77))), A_77) | ~v2_tex_2('#skF_1'(u1_struct_0(A_77)), A_77) | ~l1_pre_topc(A_77) | ~v3_tdlat_3(A_77) | ~v2_pre_topc(A_77) | v2_struct_0(A_77) | v1_xboole_0(u1_struct_0(A_77)))), inference(resolution, [status(thm)], [c_4, c_55])).
% 2.53/1.32  tff(c_250, plain, (~v3_tex_2('#skF_3'('#skF_4', '#skF_1'(u1_struct_0('#skF_4'))), '#skF_4') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_119])).
% 2.53/1.32  tff(c_252, plain, (~v3_tex_2('#skF_3'('#skF_4', '#skF_1'(u1_struct_0('#skF_4'))), '#skF_4')), inference(splitLeft, [status(thm)], [c_250])).
% 2.53/1.32  tff(c_259, plain, (~v2_tex_2('#skF_1'(u1_struct_0('#skF_4')), '#skF_4') | ~l1_pre_topc('#skF_4') | ~v3_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_256, c_252])).
% 2.53/1.32  tff(c_262, plain, (v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_251, c_259])).
% 2.53/1.32  tff(c_263, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_34, c_262])).
% 2.53/1.32  tff(c_266, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_263, c_8])).
% 2.53/1.32  tff(c_269, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_34, c_266])).
% 2.53/1.32  tff(c_273, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6, c_269])).
% 2.53/1.32  tff(c_277, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_273])).
% 2.53/1.32  tff(c_278, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_250])).
% 2.53/1.32  tff(c_282, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_278, c_8])).
% 2.53/1.32  tff(c_285, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_34, c_282])).
% 2.53/1.32  tff(c_288, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6, c_285])).
% 2.53/1.32  tff(c_292, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_288])).
% 2.53/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.32  
% 2.53/1.32  Inference rules
% 2.53/1.32  ----------------------
% 2.53/1.32  #Ref     : 0
% 2.53/1.32  #Sup     : 36
% 2.53/1.32  #Fact    : 0
% 2.53/1.32  #Define  : 0
% 2.53/1.32  #Split   : 8
% 2.53/1.32  #Chain   : 0
% 2.53/1.32  #Close   : 0
% 2.53/1.32  
% 2.53/1.32  Ordering : KBO
% 2.53/1.32  
% 2.53/1.32  Simplification rules
% 2.53/1.32  ----------------------
% 2.53/1.32  #Subsume      : 9
% 2.53/1.32  #Demod        : 32
% 2.53/1.32  #Tautology    : 0
% 2.53/1.32  #SimpNegUnit  : 15
% 2.53/1.32  #BackRed      : 0
% 2.53/1.32  
% 2.53/1.32  #Partial instantiations: 0
% 2.53/1.32  #Strategies tried      : 1
% 2.53/1.32  
% 2.53/1.32  Timing (in seconds)
% 2.53/1.32  ----------------------
% 2.53/1.32  Preprocessing        : 0.31
% 2.53/1.32  Parsing              : 0.17
% 2.53/1.32  CNF conversion       : 0.02
% 2.53/1.32  Main loop            : 0.24
% 2.53/1.32  Inferencing          : 0.11
% 2.53/1.32  Reduction            : 0.06
% 2.53/1.32  Demodulation         : 0.04
% 2.53/1.33  BG Simplification    : 0.01
% 2.53/1.33  Subsumption          : 0.05
% 2.53/1.33  Abstraction          : 0.01
% 2.53/1.33  MUC search           : 0.00
% 2.53/1.33  Cooper               : 0.00
% 2.53/1.33  Total                : 0.59
% 2.53/1.33  Index Insertion      : 0.00
% 2.53/1.33  Index Deletion       : 0.00
% 2.53/1.33  Index Matching       : 0.00
% 2.53/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
