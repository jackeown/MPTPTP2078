%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:40 EST 2020

% Result     : Theorem 5.49s
% Output     : CNFRefutation 5.67s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 219 expanded)
%              Number of leaves         :   46 (  98 expanded)
%              Depth                    :   16
%              Number of atoms          :  297 (1000 expanded)
%              Number of equality atoms :   24 ( 119 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_4 > #skF_2

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

tff(v4_tex_2,type,(
    v4_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff(f_187,negated_conjecture,(
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

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_95,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v4_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v3_tex_2(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tex_2)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_110,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_148,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_64,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_58,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_60,plain,(
    v4_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_26,plain,(
    ! [B_28,A_26] :
      ( m1_subset_1(u1_struct_0(B_28),k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_pre_topc(B_28,A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1387,plain,(
    ! [B_297,A_298] :
      ( v3_tex_2(u1_struct_0(B_297),A_298)
      | ~ m1_subset_1(u1_struct_0(B_297),k1_zfmisc_1(u1_struct_0(A_298)))
      | ~ v4_tex_2(B_297,A_298)
      | ~ m1_pre_topc(B_297,A_298)
      | ~ l1_pre_topc(A_298)
      | v2_struct_0(A_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1409,plain,(
    ! [B_299,A_300] :
      ( v3_tex_2(u1_struct_0(B_299),A_300)
      | ~ v4_tex_2(B_299,A_300)
      | v2_struct_0(A_300)
      | ~ m1_pre_topc(B_299,A_300)
      | ~ l1_pre_topc(A_300) ) ),
    inference(resolution,[status(thm)],[c_26,c_1387])).

tff(c_42,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_71,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46])).

tff(c_167,plain,(
    ! [A_127,B_128] :
      ( k6_domain_1(A_127,B_128) = k1_tarski(B_128)
      | ~ m1_subset_1(B_128,A_127)
      | v1_xboole_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_186,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_8') = k1_tarski('#skF_8')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_71,c_167])).

tff(c_197,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_119,plain,(
    ! [A_115,B_116] :
      ( r2_hidden('#skF_2'(A_115,B_116),A_115)
      | r1_tarski(A_115,B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_127,plain,(
    ! [A_115] : r1_tarski(A_115,A_115) ),
    inference(resolution,[status(thm)],[c_119,c_8])).

tff(c_68,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_871,plain,(
    ! [C_222,A_223,B_224] :
      ( m1_subset_1(C_222,k1_zfmisc_1(u1_struct_0(A_223)))
      | ~ m1_subset_1(C_222,k1_zfmisc_1(u1_struct_0(B_224)))
      | ~ m1_pre_topc(B_224,A_223)
      | ~ l1_pre_topc(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_987,plain,(
    ! [A_258,A_259,B_260] :
      ( m1_subset_1(A_258,k1_zfmisc_1(u1_struct_0(A_259)))
      | ~ m1_pre_topc(B_260,A_259)
      | ~ l1_pre_topc(A_259)
      | ~ r1_tarski(A_258,u1_struct_0(B_260)) ) ),
    inference(resolution,[status(thm)],[c_20,c_871])).

tff(c_989,plain,(
    ! [A_258] :
      ( m1_subset_1(A_258,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_258,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_58,c_987])).

tff(c_992,plain,(
    ! [A_258] :
      ( m1_subset_1(A_258,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_258,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_989])).

tff(c_1108,plain,(
    ! [B_271,A_272] :
      ( ~ v3_tex_2(B_271,A_272)
      | ~ m1_subset_1(B_271,k1_zfmisc_1(u1_struct_0(A_272)))
      | ~ v1_xboole_0(B_271)
      | ~ l1_pre_topc(A_272)
      | ~ v2_pre_topc(A_272)
      | v2_struct_0(A_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1111,plain,(
    ! [A_258] :
      ( ~ v3_tex_2(A_258,'#skF_4')
      | ~ v1_xboole_0(A_258)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_258,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_992,c_1108])).

tff(c_1125,plain,(
    ! [A_258] :
      ( ~ v3_tex_2(A_258,'#skF_4')
      | ~ v1_xboole_0(A_258)
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_258,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_1111])).

tff(c_1130,plain,(
    ! [A_273] :
      ( ~ v3_tex_2(A_273,'#skF_4')
      | ~ v1_xboole_0(A_273)
      | ~ r1_tarski(A_273,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1125])).

tff(c_1142,plain,
    ( ~ v3_tex_2(u1_struct_0('#skF_5'),'#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_127,c_1130])).

tff(c_1151,plain,(
    ~ v3_tex_2(u1_struct_0('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_1142])).

tff(c_1416,plain,
    ( ~ v4_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1409,c_1151])).

tff(c_1423,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_58,c_60,c_1416])).

tff(c_1425,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1423])).

tff(c_1427,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | v1_xboole_0(B_14)
      | ~ m1_subset_1(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_103,plain,(
    ! [A_109,B_110] :
      ( m1_subset_1(k1_tarski(A_109),k1_zfmisc_1(B_110))
      | ~ r2_hidden(A_109,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_107,plain,(
    ! [A_109,B_110] :
      ( r1_tarski(k1_tarski(A_109),B_110)
      | ~ r2_hidden(A_109,B_110) ) ),
    inference(resolution,[status(thm)],[c_103,c_18])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_54,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_52,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_48,plain,(
    v3_borsuk_1('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_66,plain,(
    v3_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_1673,plain,(
    ! [C_365,A_366,B_367] :
      ( m1_subset_1(C_365,k1_zfmisc_1(u1_struct_0(A_366)))
      | ~ m1_subset_1(C_365,k1_zfmisc_1(u1_struct_0(B_367)))
      | ~ m1_pre_topc(B_367,A_366)
      | ~ l1_pre_topc(A_366) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1685,plain,(
    ! [A_368,A_369,B_370] :
      ( m1_subset_1(A_368,k1_zfmisc_1(u1_struct_0(A_369)))
      | ~ m1_pre_topc(B_370,A_369)
      | ~ l1_pre_topc(A_369)
      | ~ r1_tarski(A_368,u1_struct_0(B_370)) ) ),
    inference(resolution,[status(thm)],[c_20,c_1673])).

tff(c_1687,plain,(
    ! [A_368] :
      ( m1_subset_1(A_368,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_368,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_58,c_1685])).

tff(c_1690,plain,(
    ! [A_368] :
      ( m1_subset_1(A_368,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_368,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1687])).

tff(c_2194,plain,(
    ! [A_415,B_416,C_417,E_418] :
      ( k8_relset_1(u1_struct_0(A_415),u1_struct_0(B_416),C_417,E_418) = k2_pre_topc(A_415,E_418)
      | ~ m1_subset_1(E_418,k1_zfmisc_1(u1_struct_0(A_415)))
      | ~ m1_subset_1(E_418,k1_zfmisc_1(u1_struct_0(B_416)))
      | ~ v3_borsuk_1(C_417,A_415,B_416)
      | ~ m1_subset_1(C_417,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_415),u1_struct_0(B_416))))
      | ~ v5_pre_topc(C_417,A_415,B_416)
      | ~ v1_funct_2(C_417,u1_struct_0(A_415),u1_struct_0(B_416))
      | ~ v1_funct_1(C_417)
      | ~ m1_pre_topc(B_416,A_415)
      | ~ v4_tex_2(B_416,A_415)
      | v2_struct_0(B_416)
      | ~ l1_pre_topc(A_415)
      | ~ v3_tdlat_3(A_415)
      | ~ v2_pre_topc(A_415)
      | v2_struct_0(A_415) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_2200,plain,(
    ! [B_416,C_417,A_368] :
      ( k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0(B_416),C_417,A_368) = k2_pre_topc('#skF_4',A_368)
      | ~ m1_subset_1(A_368,k1_zfmisc_1(u1_struct_0(B_416)))
      | ~ v3_borsuk_1(C_417,'#skF_4',B_416)
      | ~ m1_subset_1(C_417,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_416))))
      | ~ v5_pre_topc(C_417,'#skF_4',B_416)
      | ~ v1_funct_2(C_417,u1_struct_0('#skF_4'),u1_struct_0(B_416))
      | ~ v1_funct_1(C_417)
      | ~ m1_pre_topc(B_416,'#skF_4')
      | ~ v4_tex_2(B_416,'#skF_4')
      | v2_struct_0(B_416)
      | ~ l1_pre_topc('#skF_4')
      | ~ v3_tdlat_3('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_368,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1690,c_2194])).

tff(c_2213,plain,(
    ! [B_416,C_417,A_368] :
      ( k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0(B_416),C_417,A_368) = k2_pre_topc('#skF_4',A_368)
      | ~ m1_subset_1(A_368,k1_zfmisc_1(u1_struct_0(B_416)))
      | ~ v3_borsuk_1(C_417,'#skF_4',B_416)
      | ~ m1_subset_1(C_417,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_416))))
      | ~ v5_pre_topc(C_417,'#skF_4',B_416)
      | ~ v1_funct_2(C_417,u1_struct_0('#skF_4'),u1_struct_0(B_416))
      | ~ v1_funct_1(C_417)
      | ~ m1_pre_topc(B_416,'#skF_4')
      | ~ v4_tex_2(B_416,'#skF_4')
      | v2_struct_0(B_416)
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_368,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_2200])).

tff(c_2236,plain,(
    ! [B_424,C_425,A_426] :
      ( k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0(B_424),C_425,A_426) = k2_pre_topc('#skF_4',A_426)
      | ~ m1_subset_1(A_426,k1_zfmisc_1(u1_struct_0(B_424)))
      | ~ v3_borsuk_1(C_425,'#skF_4',B_424)
      | ~ m1_subset_1(C_425,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_424))))
      | ~ v5_pre_topc(C_425,'#skF_4',B_424)
      | ~ v1_funct_2(C_425,u1_struct_0('#skF_4'),u1_struct_0(B_424))
      | ~ v1_funct_1(C_425)
      | ~ m1_pre_topc(B_424,'#skF_4')
      | ~ v4_tex_2(B_424,'#skF_4')
      | v2_struct_0(B_424)
      | ~ r1_tarski(A_426,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2213])).

tff(c_2692,plain,(
    ! [B_479,C_480,A_481] :
      ( k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0(B_479),C_480,A_481) = k2_pre_topc('#skF_4',A_481)
      | ~ v3_borsuk_1(C_480,'#skF_4',B_479)
      | ~ m1_subset_1(C_480,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_479))))
      | ~ v5_pre_topc(C_480,'#skF_4',B_479)
      | ~ v1_funct_2(C_480,u1_struct_0('#skF_4'),u1_struct_0(B_479))
      | ~ v1_funct_1(C_480)
      | ~ m1_pre_topc(B_479,'#skF_4')
      | ~ v4_tex_2(B_479,'#skF_4')
      | v2_struct_0(B_479)
      | ~ r1_tarski(A_481,u1_struct_0('#skF_5'))
      | ~ r1_tarski(A_481,u1_struct_0(B_479)) ) ),
    inference(resolution,[status(thm)],[c_20,c_2236])).

tff(c_2697,plain,(
    ! [A_481] :
      ( k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',A_481) = k2_pre_topc('#skF_4',A_481)
      | ~ v3_borsuk_1('#skF_6','#skF_4','#skF_5')
      | ~ v5_pre_topc('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc('#skF_5','#skF_4')
      | ~ v4_tex_2('#skF_5','#skF_4')
      | v2_struct_0('#skF_5')
      | ~ r1_tarski(A_481,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_50,c_2692])).

tff(c_2704,plain,(
    ! [A_481] :
      ( k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',A_481) = k2_pre_topc('#skF_4',A_481)
      | v2_struct_0('#skF_5')
      | ~ r1_tarski(A_481,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_52,c_48,c_2697])).

tff(c_2718,plain,(
    ! [A_484] :
      ( k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',A_484) = k2_pre_topc('#skF_4',A_484)
      | ~ r1_tarski(A_484,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2704])).

tff(c_44,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_187,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_8') = k1_tarski('#skF_8')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_167])).

tff(c_1433,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_188,plain,(
    ! [B_129,A_130] :
      ( m1_subset_1(u1_struct_0(B_129),k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ m1_pre_topc(B_129,A_130)
      | ~ l1_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1440,plain,(
    ! [B_303,A_304] :
      ( r1_tarski(u1_struct_0(B_303),u1_struct_0(A_304))
      | ~ m1_pre_topc(B_303,A_304)
      | ~ l1_pre_topc(A_304) ) ),
    inference(resolution,[status(thm)],[c_188,c_18])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_131,plain,(
    ! [C_120,B_121,A_122] :
      ( r2_hidden(C_120,B_121)
      | ~ r2_hidden(C_120,A_122)
      | ~ r1_tarski(A_122,B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_141,plain,(
    ! [A_123,B_124] :
      ( r2_hidden('#skF_1'(A_123),B_124)
      | ~ r1_tarski(A_123,B_124)
      | v1_xboole_0(A_123) ) ),
    inference(resolution,[status(thm)],[c_4,c_131])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_148,plain,(
    ! [B_124,A_123] :
      ( ~ v1_xboole_0(B_124)
      | ~ r1_tarski(A_123,B_124)
      | v1_xboole_0(A_123) ) ),
    inference(resolution,[status(thm)],[c_141,c_2])).

tff(c_1491,plain,(
    ! [A_316,B_317] :
      ( ~ v1_xboole_0(u1_struct_0(A_316))
      | v1_xboole_0(u1_struct_0(B_317))
      | ~ m1_pre_topc(B_317,A_316)
      | ~ l1_pre_topc(A_316) ) ),
    inference(resolution,[status(thm)],[c_1440,c_148])).

tff(c_1493,plain,(
    ! [B_317] :
      ( v1_xboole_0(u1_struct_0(B_317))
      | ~ m1_pre_topc(B_317,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1433,c_1491])).

tff(c_1497,plain,(
    ! [B_318] :
      ( v1_xboole_0(u1_struct_0(B_318))
      | ~ m1_pre_topc(B_318,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1493])).

tff(c_1502,plain,(
    ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1497,c_1427])).

tff(c_1507,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1502])).

tff(c_1508,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_8') = k1_tarski('#skF_8') ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_1426,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_8') = k1_tarski('#skF_8') ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_40,plain,(
    k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7')) != k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_72,plain,(
    k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k6_domain_1(u1_struct_0('#skF_5'),'#skF_8')) != k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40])).

tff(c_1428,plain,(
    k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k1_tarski('#skF_8')) != k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1426,c_72])).

tff(c_1656,plain,(
    k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k1_tarski('#skF_8')) != k2_pre_topc('#skF_4',k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1508,c_1428])).

tff(c_2729,plain,(
    ~ r1_tarski(k1_tarski('#skF_8'),u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2718,c_1656])).

tff(c_2742,plain,(
    ~ r2_hidden('#skF_8',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_107,c_2729])).

tff(c_2754,plain,
    ( v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_16,c_2742])).

tff(c_2762,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_2754])).

tff(c_2764,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1427,c_2762])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:44:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.49/2.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.55/2.09  
% 5.55/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.55/2.09  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_4 > #skF_2
% 5.55/2.09  
% 5.55/2.09  %Foreground sorts:
% 5.55/2.09  
% 5.55/2.09  
% 5.55/2.09  %Background operators:
% 5.55/2.09  
% 5.55/2.09  
% 5.55/2.09  %Foreground operators:
% 5.55/2.09  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.55/2.09  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 5.55/2.09  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.55/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.55/2.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.55/2.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.55/2.09  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 5.55/2.09  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.55/2.09  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 5.55/2.09  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.55/2.09  tff('#skF_7', type, '#skF_7': $i).
% 5.55/2.09  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.55/2.09  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 5.55/2.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.55/2.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.55/2.09  tff('#skF_5', type, '#skF_5': $i).
% 5.55/2.09  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 5.55/2.09  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.55/2.09  tff('#skF_6', type, '#skF_6': $i).
% 5.55/2.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.55/2.09  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 5.55/2.09  tff('#skF_8', type, '#skF_8': $i).
% 5.55/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.55/2.09  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.55/2.09  tff('#skF_4', type, '#skF_4': $i).
% 5.55/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.55/2.09  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.55/2.09  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 5.55/2.09  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.55/2.09  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.55/2.09  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.55/2.09  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.55/2.09  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.55/2.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.55/2.09  
% 5.67/2.12  tff(f_187, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tex_2)).
% 5.67/2.12  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 5.67/2.12  tff(f_95, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (v4_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v3_tex_2(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_tex_2)).
% 5.67/2.12  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 5.67/2.12  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.67/2.12  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.67/2.12  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 5.67/2.12  tff(f_110, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 5.67/2.12  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 5.67/2.12  tff(f_44, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 5.67/2.12  tff(f_148, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tex_2)).
% 5.67/2.12  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.67/2.12  tff(c_70, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.67/2.12  tff(c_64, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.67/2.12  tff(c_58, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.67/2.12  tff(c_60, plain, (v4_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.67/2.12  tff(c_26, plain, (![B_28, A_26]: (m1_subset_1(u1_struct_0(B_28), k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_pre_topc(B_28, A_26) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.67/2.12  tff(c_1387, plain, (![B_297, A_298]: (v3_tex_2(u1_struct_0(B_297), A_298) | ~m1_subset_1(u1_struct_0(B_297), k1_zfmisc_1(u1_struct_0(A_298))) | ~v4_tex_2(B_297, A_298) | ~m1_pre_topc(B_297, A_298) | ~l1_pre_topc(A_298) | v2_struct_0(A_298))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.67/2.12  tff(c_1409, plain, (![B_299, A_300]: (v3_tex_2(u1_struct_0(B_299), A_300) | ~v4_tex_2(B_299, A_300) | v2_struct_0(A_300) | ~m1_pre_topc(B_299, A_300) | ~l1_pre_topc(A_300))), inference(resolution, [status(thm)], [c_26, c_1387])).
% 5.67/2.12  tff(c_42, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.67/2.12  tff(c_46, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.67/2.12  tff(c_71, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46])).
% 5.67/2.12  tff(c_167, plain, (![A_127, B_128]: (k6_domain_1(A_127, B_128)=k1_tarski(B_128) | ~m1_subset_1(B_128, A_127) | v1_xboole_0(A_127))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.67/2.12  tff(c_186, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_8')=k1_tarski('#skF_8') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_71, c_167])).
% 5.67/2.12  tff(c_197, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_186])).
% 5.67/2.12  tff(c_119, plain, (![A_115, B_116]: (r2_hidden('#skF_2'(A_115, B_116), A_115) | r1_tarski(A_115, B_116))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.67/2.12  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.67/2.12  tff(c_127, plain, (![A_115]: (r1_tarski(A_115, A_115))), inference(resolution, [status(thm)], [c_119, c_8])).
% 5.67/2.12  tff(c_68, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.67/2.12  tff(c_20, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.67/2.12  tff(c_871, plain, (![C_222, A_223, B_224]: (m1_subset_1(C_222, k1_zfmisc_1(u1_struct_0(A_223))) | ~m1_subset_1(C_222, k1_zfmisc_1(u1_struct_0(B_224))) | ~m1_pre_topc(B_224, A_223) | ~l1_pre_topc(A_223))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.67/2.12  tff(c_987, plain, (![A_258, A_259, B_260]: (m1_subset_1(A_258, k1_zfmisc_1(u1_struct_0(A_259))) | ~m1_pre_topc(B_260, A_259) | ~l1_pre_topc(A_259) | ~r1_tarski(A_258, u1_struct_0(B_260)))), inference(resolution, [status(thm)], [c_20, c_871])).
% 5.67/2.12  tff(c_989, plain, (![A_258]: (m1_subset_1(A_258, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_258, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_58, c_987])).
% 5.67/2.12  tff(c_992, plain, (![A_258]: (m1_subset_1(A_258, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_258, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_989])).
% 5.67/2.12  tff(c_1108, plain, (![B_271, A_272]: (~v3_tex_2(B_271, A_272) | ~m1_subset_1(B_271, k1_zfmisc_1(u1_struct_0(A_272))) | ~v1_xboole_0(B_271) | ~l1_pre_topc(A_272) | ~v2_pre_topc(A_272) | v2_struct_0(A_272))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.67/2.12  tff(c_1111, plain, (![A_258]: (~v3_tex_2(A_258, '#skF_4') | ~v1_xboole_0(A_258) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(A_258, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_992, c_1108])).
% 5.67/2.12  tff(c_1125, plain, (![A_258]: (~v3_tex_2(A_258, '#skF_4') | ~v1_xboole_0(A_258) | v2_struct_0('#skF_4') | ~r1_tarski(A_258, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_1111])).
% 5.67/2.12  tff(c_1130, plain, (![A_273]: (~v3_tex_2(A_273, '#skF_4') | ~v1_xboole_0(A_273) | ~r1_tarski(A_273, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_70, c_1125])).
% 5.67/2.12  tff(c_1142, plain, (~v3_tex_2(u1_struct_0('#skF_5'), '#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_127, c_1130])).
% 5.67/2.12  tff(c_1151, plain, (~v3_tex_2(u1_struct_0('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_197, c_1142])).
% 5.67/2.12  tff(c_1416, plain, (~v4_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_1409, c_1151])).
% 5.67/2.12  tff(c_1423, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_58, c_60, c_1416])).
% 5.67/2.12  tff(c_1425, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_1423])).
% 5.67/2.12  tff(c_1427, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_186])).
% 5.67/2.12  tff(c_16, plain, (![A_13, B_14]: (r2_hidden(A_13, B_14) | v1_xboole_0(B_14) | ~m1_subset_1(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.67/2.12  tff(c_103, plain, (![A_109, B_110]: (m1_subset_1(k1_tarski(A_109), k1_zfmisc_1(B_110)) | ~r2_hidden(A_109, B_110))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.67/2.12  tff(c_18, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.67/2.12  tff(c_107, plain, (![A_109, B_110]: (r1_tarski(k1_tarski(A_109), B_110) | ~r2_hidden(A_109, B_110))), inference(resolution, [status(thm)], [c_103, c_18])).
% 5.67/2.12  tff(c_62, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.67/2.12  tff(c_56, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.67/2.12  tff(c_54, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.67/2.12  tff(c_52, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.67/2.12  tff(c_48, plain, (v3_borsuk_1('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.67/2.12  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.67/2.12  tff(c_66, plain, (v3_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.67/2.12  tff(c_1673, plain, (![C_365, A_366, B_367]: (m1_subset_1(C_365, k1_zfmisc_1(u1_struct_0(A_366))) | ~m1_subset_1(C_365, k1_zfmisc_1(u1_struct_0(B_367))) | ~m1_pre_topc(B_367, A_366) | ~l1_pre_topc(A_366))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.67/2.12  tff(c_1685, plain, (![A_368, A_369, B_370]: (m1_subset_1(A_368, k1_zfmisc_1(u1_struct_0(A_369))) | ~m1_pre_topc(B_370, A_369) | ~l1_pre_topc(A_369) | ~r1_tarski(A_368, u1_struct_0(B_370)))), inference(resolution, [status(thm)], [c_20, c_1673])).
% 5.67/2.12  tff(c_1687, plain, (![A_368]: (m1_subset_1(A_368, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_368, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_58, c_1685])).
% 5.67/2.12  tff(c_1690, plain, (![A_368]: (m1_subset_1(A_368, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_368, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1687])).
% 5.67/2.12  tff(c_2194, plain, (![A_415, B_416, C_417, E_418]: (k8_relset_1(u1_struct_0(A_415), u1_struct_0(B_416), C_417, E_418)=k2_pre_topc(A_415, E_418) | ~m1_subset_1(E_418, k1_zfmisc_1(u1_struct_0(A_415))) | ~m1_subset_1(E_418, k1_zfmisc_1(u1_struct_0(B_416))) | ~v3_borsuk_1(C_417, A_415, B_416) | ~m1_subset_1(C_417, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_415), u1_struct_0(B_416)))) | ~v5_pre_topc(C_417, A_415, B_416) | ~v1_funct_2(C_417, u1_struct_0(A_415), u1_struct_0(B_416)) | ~v1_funct_1(C_417) | ~m1_pre_topc(B_416, A_415) | ~v4_tex_2(B_416, A_415) | v2_struct_0(B_416) | ~l1_pre_topc(A_415) | ~v3_tdlat_3(A_415) | ~v2_pre_topc(A_415) | v2_struct_0(A_415))), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.67/2.12  tff(c_2200, plain, (![B_416, C_417, A_368]: (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0(B_416), C_417, A_368)=k2_pre_topc('#skF_4', A_368) | ~m1_subset_1(A_368, k1_zfmisc_1(u1_struct_0(B_416))) | ~v3_borsuk_1(C_417, '#skF_4', B_416) | ~m1_subset_1(C_417, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_416)))) | ~v5_pre_topc(C_417, '#skF_4', B_416) | ~v1_funct_2(C_417, u1_struct_0('#skF_4'), u1_struct_0(B_416)) | ~v1_funct_1(C_417) | ~m1_pre_topc(B_416, '#skF_4') | ~v4_tex_2(B_416, '#skF_4') | v2_struct_0(B_416) | ~l1_pre_topc('#skF_4') | ~v3_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(A_368, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_1690, c_2194])).
% 5.67/2.12  tff(c_2213, plain, (![B_416, C_417, A_368]: (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0(B_416), C_417, A_368)=k2_pre_topc('#skF_4', A_368) | ~m1_subset_1(A_368, k1_zfmisc_1(u1_struct_0(B_416))) | ~v3_borsuk_1(C_417, '#skF_4', B_416) | ~m1_subset_1(C_417, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_416)))) | ~v5_pre_topc(C_417, '#skF_4', B_416) | ~v1_funct_2(C_417, u1_struct_0('#skF_4'), u1_struct_0(B_416)) | ~v1_funct_1(C_417) | ~m1_pre_topc(B_416, '#skF_4') | ~v4_tex_2(B_416, '#skF_4') | v2_struct_0(B_416) | v2_struct_0('#skF_4') | ~r1_tarski(A_368, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_2200])).
% 5.67/2.12  tff(c_2236, plain, (![B_424, C_425, A_426]: (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0(B_424), C_425, A_426)=k2_pre_topc('#skF_4', A_426) | ~m1_subset_1(A_426, k1_zfmisc_1(u1_struct_0(B_424))) | ~v3_borsuk_1(C_425, '#skF_4', B_424) | ~m1_subset_1(C_425, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_424)))) | ~v5_pre_topc(C_425, '#skF_4', B_424) | ~v1_funct_2(C_425, u1_struct_0('#skF_4'), u1_struct_0(B_424)) | ~v1_funct_1(C_425) | ~m1_pre_topc(B_424, '#skF_4') | ~v4_tex_2(B_424, '#skF_4') | v2_struct_0(B_424) | ~r1_tarski(A_426, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_70, c_2213])).
% 5.67/2.12  tff(c_2692, plain, (![B_479, C_480, A_481]: (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0(B_479), C_480, A_481)=k2_pre_topc('#skF_4', A_481) | ~v3_borsuk_1(C_480, '#skF_4', B_479) | ~m1_subset_1(C_480, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_479)))) | ~v5_pre_topc(C_480, '#skF_4', B_479) | ~v1_funct_2(C_480, u1_struct_0('#skF_4'), u1_struct_0(B_479)) | ~v1_funct_1(C_480) | ~m1_pre_topc(B_479, '#skF_4') | ~v4_tex_2(B_479, '#skF_4') | v2_struct_0(B_479) | ~r1_tarski(A_481, u1_struct_0('#skF_5')) | ~r1_tarski(A_481, u1_struct_0(B_479)))), inference(resolution, [status(thm)], [c_20, c_2236])).
% 5.67/2.12  tff(c_2697, plain, (![A_481]: (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', A_481)=k2_pre_topc('#skF_4', A_481) | ~v3_borsuk_1('#skF_6', '#skF_4', '#skF_5') | ~v5_pre_topc('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_4') | ~v4_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_5') | ~r1_tarski(A_481, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_50, c_2692])).
% 5.67/2.12  tff(c_2704, plain, (![A_481]: (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', A_481)=k2_pre_topc('#skF_4', A_481) | v2_struct_0('#skF_5') | ~r1_tarski(A_481, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_52, c_48, c_2697])).
% 5.67/2.12  tff(c_2718, plain, (![A_484]: (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', A_484)=k2_pre_topc('#skF_4', A_484) | ~r1_tarski(A_484, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_62, c_2704])).
% 5.67/2.12  tff(c_44, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.67/2.12  tff(c_187, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_8')=k1_tarski('#skF_8') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_167])).
% 5.67/2.12  tff(c_1433, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_187])).
% 5.67/2.12  tff(c_188, plain, (![B_129, A_130]: (m1_subset_1(u1_struct_0(B_129), k1_zfmisc_1(u1_struct_0(A_130))) | ~m1_pre_topc(B_129, A_130) | ~l1_pre_topc(A_130))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.67/2.12  tff(c_1440, plain, (![B_303, A_304]: (r1_tarski(u1_struct_0(B_303), u1_struct_0(A_304)) | ~m1_pre_topc(B_303, A_304) | ~l1_pre_topc(A_304))), inference(resolution, [status(thm)], [c_188, c_18])).
% 5.67/2.12  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.67/2.12  tff(c_131, plain, (![C_120, B_121, A_122]: (r2_hidden(C_120, B_121) | ~r2_hidden(C_120, A_122) | ~r1_tarski(A_122, B_121))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.67/2.12  tff(c_141, plain, (![A_123, B_124]: (r2_hidden('#skF_1'(A_123), B_124) | ~r1_tarski(A_123, B_124) | v1_xboole_0(A_123))), inference(resolution, [status(thm)], [c_4, c_131])).
% 5.67/2.12  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.67/2.12  tff(c_148, plain, (![B_124, A_123]: (~v1_xboole_0(B_124) | ~r1_tarski(A_123, B_124) | v1_xboole_0(A_123))), inference(resolution, [status(thm)], [c_141, c_2])).
% 5.67/2.12  tff(c_1491, plain, (![A_316, B_317]: (~v1_xboole_0(u1_struct_0(A_316)) | v1_xboole_0(u1_struct_0(B_317)) | ~m1_pre_topc(B_317, A_316) | ~l1_pre_topc(A_316))), inference(resolution, [status(thm)], [c_1440, c_148])).
% 5.67/2.12  tff(c_1493, plain, (![B_317]: (v1_xboole_0(u1_struct_0(B_317)) | ~m1_pre_topc(B_317, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_1433, c_1491])).
% 5.67/2.12  tff(c_1497, plain, (![B_318]: (v1_xboole_0(u1_struct_0(B_318)) | ~m1_pre_topc(B_318, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1493])).
% 5.67/2.12  tff(c_1502, plain, (~m1_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1497, c_1427])).
% 5.67/2.12  tff(c_1507, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_1502])).
% 5.67/2.12  tff(c_1508, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_8')=k1_tarski('#skF_8')), inference(splitRight, [status(thm)], [c_187])).
% 5.67/2.12  tff(c_1426, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_8')=k1_tarski('#skF_8')), inference(splitRight, [status(thm)], [c_186])).
% 5.67/2.12  tff(c_40, plain, (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'))!=k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.67/2.12  tff(c_72, plain, (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k6_domain_1(u1_struct_0('#skF_5'), '#skF_8'))!=k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40])).
% 5.67/2.12  tff(c_1428, plain, (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k1_tarski('#skF_8'))!=k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1426, c_72])).
% 5.67/2.12  tff(c_1656, plain, (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k1_tarski('#skF_8'))!=k2_pre_topc('#skF_4', k1_tarski('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1508, c_1428])).
% 5.67/2.12  tff(c_2729, plain, (~r1_tarski(k1_tarski('#skF_8'), u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2718, c_1656])).
% 5.67/2.12  tff(c_2742, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_107, c_2729])).
% 5.67/2.12  tff(c_2754, plain, (v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_16, c_2742])).
% 5.67/2.12  tff(c_2762, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_2754])).
% 5.67/2.12  tff(c_2764, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1427, c_2762])).
% 5.67/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.67/2.12  
% 5.67/2.12  Inference rules
% 5.67/2.12  ----------------------
% 5.67/2.12  #Ref     : 0
% 5.67/2.12  #Sup     : 614
% 5.67/2.12  #Fact    : 0
% 5.67/2.12  #Define  : 0
% 5.67/2.12  #Split   : 24
% 5.67/2.12  #Chain   : 0
% 5.67/2.12  #Close   : 0
% 5.67/2.12  
% 5.67/2.12  Ordering : KBO
% 5.67/2.12  
% 5.67/2.12  Simplification rules
% 5.67/2.12  ----------------------
% 5.67/2.12  #Subsume      : 207
% 5.67/2.12  #Demod        : 97
% 5.67/2.12  #Tautology    : 78
% 5.67/2.12  #SimpNegUnit  : 61
% 5.67/2.12  #BackRed      : 26
% 5.67/2.12  
% 5.67/2.12  #Partial instantiations: 0
% 5.67/2.12  #Strategies tried      : 1
% 5.67/2.12  
% 5.67/2.12  Timing (in seconds)
% 5.67/2.12  ----------------------
% 5.72/2.12  Preprocessing        : 0.38
% 5.72/2.12  Parsing              : 0.20
% 5.72/2.12  CNF conversion       : 0.03
% 5.72/2.12  Main loop            : 0.89
% 5.72/2.12  Inferencing          : 0.33
% 5.72/2.12  Reduction            : 0.25
% 5.72/2.12  Demodulation         : 0.17
% 5.72/2.12  BG Simplification    : 0.03
% 5.72/2.12  Subsumption          : 0.20
% 5.72/2.12  Abstraction          : 0.04
% 5.72/2.13  MUC search           : 0.00
% 5.72/2.13  Cooper               : 0.00
% 5.72/2.13  Total                : 1.33
% 5.72/2.13  Index Insertion      : 0.00
% 5.72/2.13  Index Deletion       : 0.00
% 5.72/2.13  Index Matching       : 0.00
% 5.72/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
