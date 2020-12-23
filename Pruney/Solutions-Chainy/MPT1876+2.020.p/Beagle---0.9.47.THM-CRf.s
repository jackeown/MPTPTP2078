%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:53 EST 2020

% Result     : Theorem 11.65s
% Output     : CNFRefutation 11.79s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 362 expanded)
%              Number of leaves         :   50 ( 147 expanded)
%              Depth                    :   16
%              Number of atoms          :  296 (1057 expanded)
%              Number of equality atoms :   35 (  94 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_200,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_139,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_53,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_46,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_48,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_180,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_168,axiom,(
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

tff(f_89,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_126,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ( ~ v2_struct_0(B)
              & ~ v7_struct_0(B) )
           => ( ~ v2_struct_0(B)
              & ~ v1_tdlat_3(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc32_tex_2)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(c_46,plain,(
    ! [A_27] :
      ( l1_struct_0(A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_84,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_76,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_82,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_78,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,
    ( v2_tex_2('#skF_6','#skF_5')
    | v1_zfmisc_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_114,plain,(
    v1_zfmisc_1('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_86,plain,
    ( ~ v1_zfmisc_1('#skF_6')
    | ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_116,plain,(
    ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_86])).

tff(c_166,plain,(
    ! [A_73,B_74] :
      ( m1_subset_1(k1_tarski(A_73),k1_zfmisc_1(B_74))
      | ~ r2_hidden(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_42,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(A_25,B_26)
      | ~ m1_subset_1(A_25,k1_zfmisc_1(B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_171,plain,(
    ! [A_75,B_76] :
      ( r1_tarski(k1_tarski(A_75),B_76)
      | ~ r2_hidden(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_166,c_42])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = k1_xboole_0
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_175,plain,(
    ! [A_75,B_76] :
      ( k4_xboole_0(k1_tarski(A_75),B_76) = k1_xboole_0
      | ~ r2_hidden(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_171,c_26])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | k4_xboole_0(A_11,B_12) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_426,plain,(
    ! [B_103,A_104] :
      ( B_103 = A_104
      | ~ r1_tarski(A_104,B_103)
      | ~ v1_zfmisc_1(B_103)
      | v1_xboole_0(B_103)
      | v1_xboole_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_9272,plain,(
    ! [B_432,A_433] :
      ( B_432 = A_433
      | ~ v1_zfmisc_1(B_432)
      | v1_xboole_0(B_432)
      | v1_xboole_0(A_433)
      | k4_xboole_0(A_433,B_432) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_426])).

tff(c_9276,plain,(
    ! [A_433] :
      ( A_433 = '#skF_6'
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(A_433)
      | k4_xboole_0(A_433,'#skF_6') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_114,c_9272])).

tff(c_9281,plain,(
    ! [A_434] :
      ( A_434 = '#skF_6'
      | v1_xboole_0(A_434)
      | k4_xboole_0(A_434,'#skF_6') != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_9276])).

tff(c_34,plain,(
    ! [A_17] : ~ v1_xboole_0(k1_tarski(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_9334,plain,(
    ! [A_435] :
      ( k1_tarski(A_435) = '#skF_6'
      | k4_xboole_0(k1_tarski(A_435),'#skF_6') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_9281,c_34])).

tff(c_9340,plain,(
    ! [A_436] :
      ( k1_tarski(A_436) = '#skF_6'
      | ~ r2_hidden(A_436,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_9334])).

tff(c_9379,plain,
    ( k1_tarski('#skF_1'('#skF_6')) = '#skF_6'
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_9340])).

tff(c_9390,plain,(
    k1_tarski('#skF_1'('#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_9379])).

tff(c_28,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_74,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_137,plain,(
    ! [A_66,B_67] :
      ( r1_tarski(A_66,B_67)
      | ~ m1_subset_1(A_66,k1_zfmisc_1(B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_146,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_74,c_137])).

tff(c_147,plain,(
    ! [A_68,B_69] :
      ( k4_xboole_0(A_68,B_69) = k1_xboole_0
      | ~ r1_tarski(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_154,plain,(
    k4_xboole_0('#skF_6',u1_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_146,c_147])).

tff(c_176,plain,(
    ! [A_77,B_78] : k4_xboole_0(A_77,k4_xboole_0(A_77,B_78)) = k3_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_191,plain,(
    k3_xboole_0('#skF_6',u1_struct_0('#skF_5')) = k4_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_176])).

tff(c_197,plain,(
    k3_xboole_0('#skF_6',u1_struct_0('#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_191])).

tff(c_227,plain,(
    ! [D_80,B_81,A_82] :
      ( r2_hidden(D_80,B_81)
      | ~ r2_hidden(D_80,k3_xboole_0(A_82,B_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3584,plain,(
    ! [A_270,B_271] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_270,B_271)),B_271)
      | v1_xboole_0(k3_xboole_0(A_270,B_271)) ) ),
    inference(resolution,[status(thm)],[c_4,c_227])).

tff(c_3642,plain,
    ( r2_hidden('#skF_1'('#skF_6'),u1_struct_0('#skF_5'))
    | v1_xboole_0(k3_xboole_0('#skF_6',u1_struct_0('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_3584])).

tff(c_3656,plain,
    ( r2_hidden('#skF_1'('#skF_6'),u1_struct_0('#skF_5'))
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_3642])).

tff(c_3657,plain,(
    r2_hidden('#skF_1'('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_3656])).

tff(c_40,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(A_23,B_24)
      | ~ r2_hidden(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3696,plain,(
    m1_subset_1('#skF_1'('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_3657,c_40])).

tff(c_239,plain,(
    ! [D_83] :
      ( r2_hidden(D_83,u1_struct_0('#skF_5'))
      | ~ r2_hidden(D_83,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_227])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_247,plain,(
    ! [D_83] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ r2_hidden(D_83,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_239,c_2])).

tff(c_260,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_247])).

tff(c_52,plain,(
    ! [A_32,B_33] :
      ( k6_domain_1(A_32,B_33) = k1_tarski(B_33)
      | ~ m1_subset_1(B_33,A_32)
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_3700,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_1'('#skF_6')) = k1_tarski('#skF_1'('#skF_6'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_3696,c_52])).

tff(c_3703,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_1'('#skF_6')) = k1_tarski('#skF_1'('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_260,c_3700])).

tff(c_72,plain,(
    ! [A_47,B_49] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_47),B_49),A_47)
      | ~ m1_subset_1(B_49,u1_struct_0(A_47))
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_3881,plain,
    ( v2_tex_2(k1_tarski('#skF_1'('#skF_6')),'#skF_5')
    | ~ m1_subset_1('#skF_1'('#skF_6'),u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3703,c_72])).

tff(c_3891,plain,
    ( v2_tex_2(k1_tarski('#skF_1'('#skF_6')),'#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_3696,c_3881])).

tff(c_3892,plain,(
    v2_tex_2(k1_tarski('#skF_1'('#skF_6')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_3891])).

tff(c_9392,plain,(
    v2_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9390,c_3892])).

tff(c_9397,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_9392])).

tff(c_9400,plain,(
    ! [D_437] : ~ r2_hidden(D_437,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_9404,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_9400])).

tff(c_9408,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_9404])).

tff(c_9409,plain,(
    v2_tex_2('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_26518,plain,(
    ! [A_1122,B_1123] :
      ( ~ v2_struct_0('#skF_4'(A_1122,B_1123))
      | ~ v2_tex_2(B_1123,A_1122)
      | ~ m1_subset_1(B_1123,k1_zfmisc_1(u1_struct_0(A_1122)))
      | v1_xboole_0(B_1123)
      | ~ l1_pre_topc(A_1122)
      | ~ v2_pre_topc(A_1122)
      | v2_struct_0(A_1122) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_26533,plain,
    ( ~ v2_struct_0('#skF_4'('#skF_5','#skF_6'))
    | ~ v2_tex_2('#skF_6','#skF_5')
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_26518])).

tff(c_26541,plain,
    ( ~ v2_struct_0('#skF_4'('#skF_5','#skF_6'))
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_9409,c_26533])).

tff(c_26542,plain,(
    ~ v2_struct_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_76,c_26541])).

tff(c_9410,plain,(
    ~ v1_zfmisc_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_26971,plain,(
    ! [A_1142,B_1143] :
      ( u1_struct_0('#skF_4'(A_1142,B_1143)) = B_1143
      | ~ v2_tex_2(B_1143,A_1142)
      | ~ m1_subset_1(B_1143,k1_zfmisc_1(u1_struct_0(A_1142)))
      | v1_xboole_0(B_1143)
      | ~ l1_pre_topc(A_1142)
      | ~ v2_pre_topc(A_1142)
      | v2_struct_0(A_1142) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_26986,plain,
    ( u1_struct_0('#skF_4'('#skF_5','#skF_6')) = '#skF_6'
    | ~ v2_tex_2('#skF_6','#skF_5')
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_26971])).

tff(c_26994,plain,
    ( u1_struct_0('#skF_4'('#skF_5','#skF_6')) = '#skF_6'
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_9409,c_26986])).

tff(c_26995,plain,(
    u1_struct_0('#skF_4'('#skF_5','#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_76,c_26994])).

tff(c_50,plain,(
    ! [A_31] :
      ( v1_zfmisc_1(u1_struct_0(A_31))
      | ~ l1_struct_0(A_31)
      | ~ v7_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_27014,plain,
    ( v1_zfmisc_1('#skF_6')
    | ~ l1_struct_0('#skF_4'('#skF_5','#skF_6'))
    | ~ v7_struct_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_26995,c_50])).

tff(c_27023,plain,
    ( ~ l1_struct_0('#skF_4'('#skF_5','#skF_6'))
    | ~ v7_struct_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_9410,c_27014])).

tff(c_27121,plain,(
    ~ v7_struct_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_27023])).

tff(c_80,plain,(
    v2_tdlat_3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_26738,plain,(
    ! [A_1134,B_1135] :
      ( v1_tdlat_3('#skF_4'(A_1134,B_1135))
      | ~ v2_tex_2(B_1135,A_1134)
      | ~ m1_subset_1(B_1135,k1_zfmisc_1(u1_struct_0(A_1134)))
      | v1_xboole_0(B_1135)
      | ~ l1_pre_topc(A_1134)
      | ~ v2_pre_topc(A_1134)
      | v2_struct_0(A_1134) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_26753,plain,
    ( v1_tdlat_3('#skF_4'('#skF_5','#skF_6'))
    | ~ v2_tex_2('#skF_6','#skF_5')
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_26738])).

tff(c_26761,plain,
    ( v1_tdlat_3('#skF_4'('#skF_5','#skF_6'))
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_9409,c_26753])).

tff(c_26762,plain,(
    v1_tdlat_3('#skF_4'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_76,c_26761])).

tff(c_27145,plain,(
    ! [A_1151,B_1152] :
      ( m1_pre_topc('#skF_4'(A_1151,B_1152),A_1151)
      | ~ v2_tex_2(B_1152,A_1151)
      | ~ m1_subset_1(B_1152,k1_zfmisc_1(u1_struct_0(A_1151)))
      | v1_xboole_0(B_1152)
      | ~ l1_pre_topc(A_1151)
      | ~ v2_pre_topc(A_1151)
      | v2_struct_0(A_1151) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_27158,plain,
    ( m1_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5')
    | ~ v2_tex_2('#skF_6','#skF_5')
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_27145])).

tff(c_27167,plain,
    ( m1_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5')
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_9409,c_27158])).

tff(c_27168,plain,(
    m1_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_76,c_27167])).

tff(c_56,plain,(
    ! [B_37,A_35] :
      ( ~ v1_tdlat_3(B_37)
      | v7_struct_0(B_37)
      | v2_struct_0(B_37)
      | ~ m1_pre_topc(B_37,A_35)
      | ~ l1_pre_topc(A_35)
      | ~ v2_tdlat_3(A_35)
      | ~ v2_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_27171,plain,
    ( ~ v1_tdlat_3('#skF_4'('#skF_5','#skF_6'))
    | v7_struct_0('#skF_4'('#skF_5','#skF_6'))
    | v2_struct_0('#skF_4'('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_tdlat_3('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_27168,c_56])).

tff(c_27177,plain,
    ( v7_struct_0('#skF_4'('#skF_5','#skF_6'))
    | v2_struct_0('#skF_4'('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_26762,c_27171])).

tff(c_27179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_26542,c_27121,c_27177])).

tff(c_27180,plain,(
    ~ l1_struct_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_27023])).

tff(c_27185,plain,(
    ~ l1_pre_topc('#skF_4'('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_46,c_27180])).

tff(c_27193,plain,(
    ! [A_1155,B_1156] :
      ( m1_pre_topc('#skF_4'(A_1155,B_1156),A_1155)
      | ~ v2_tex_2(B_1156,A_1155)
      | ~ m1_subset_1(B_1156,k1_zfmisc_1(u1_struct_0(A_1155)))
      | v1_xboole_0(B_1156)
      | ~ l1_pre_topc(A_1155)
      | ~ v2_pre_topc(A_1155)
      | v2_struct_0(A_1155) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_27206,plain,
    ( m1_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5')
    | ~ v2_tex_2('#skF_6','#skF_5')
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_27193])).

tff(c_27215,plain,
    ( m1_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5')
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_9409,c_27206])).

tff(c_27216,plain,(
    m1_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_76,c_27215])).

tff(c_48,plain,(
    ! [B_30,A_28] :
      ( l1_pre_topc(B_30)
      | ~ m1_pre_topc(B_30,A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_27222,plain,
    ( l1_pre_topc('#skF_4'('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_27216,c_48])).

tff(c_27229,plain,(
    l1_pre_topc('#skF_4'('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_27222])).

tff(c_27231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27185,c_27229])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:42:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.65/4.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.65/4.80  
% 11.65/4.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.79/4.80  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 11.79/4.80  
% 11.79/4.80  %Foreground sorts:
% 11.79/4.80  
% 11.79/4.80  
% 11.79/4.80  %Background operators:
% 11.79/4.80  
% 11.79/4.80  
% 11.79/4.80  %Foreground operators:
% 11.79/4.80  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 11.79/4.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.79/4.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.79/4.80  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.79/4.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.79/4.80  tff('#skF_1', type, '#skF_1': $i > $i).
% 11.79/4.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.79/4.80  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 11.79/4.80  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.79/4.80  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 11.79/4.80  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 11.79/4.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.79/4.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.79/4.80  tff('#skF_5', type, '#skF_5': $i).
% 11.79/4.80  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 11.79/4.80  tff('#skF_6', type, '#skF_6': $i).
% 11.79/4.80  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.79/4.80  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 11.79/4.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.79/4.80  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 11.79/4.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.79/4.80  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 11.79/4.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.79/4.80  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 11.79/4.80  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 11.79/4.80  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.79/4.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.79/4.80  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.79/4.80  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.79/4.80  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 11.79/4.80  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 11.79/4.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.79/4.80  
% 11.79/4.82  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 11.79/4.82  tff(f_200, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 11.79/4.82  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 11.79/4.82  tff(f_57, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 11.79/4.82  tff(f_72, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 11.79/4.82  tff(f_44, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 11.79/4.82  tff(f_139, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 11.79/4.82  tff(f_53, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 11.79/4.82  tff(f_46, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 11.79/4.82  tff(f_48, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.79/4.82  tff(f_40, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 11.79/4.82  tff(f_68, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 11.79/4.82  tff(f_96, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 11.79/4.82  tff(f_180, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 11.79/4.82  tff(f_168, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tex_2)).
% 11.79/4.82  tff(f_89, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 11.79/4.82  tff(f_126, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((~v2_struct_0(B) & ~v7_struct_0(B)) => (~v2_struct_0(B) & ~v1_tdlat_3(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc32_tex_2)).
% 11.79/4.82  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 11.79/4.82  tff(c_46, plain, (![A_27]: (l1_struct_0(A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.79/4.82  tff(c_84, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_200])).
% 11.79/4.82  tff(c_76, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_200])).
% 11.79/4.82  tff(c_82, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_200])).
% 11.79/4.82  tff(c_78, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_200])).
% 11.79/4.82  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.79/4.82  tff(c_92, plain, (v2_tex_2('#skF_6', '#skF_5') | v1_zfmisc_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_200])).
% 11.79/4.82  tff(c_114, plain, (v1_zfmisc_1('#skF_6')), inference(splitLeft, [status(thm)], [c_92])).
% 11.79/4.82  tff(c_86, plain, (~v1_zfmisc_1('#skF_6') | ~v2_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_200])).
% 11.79/4.82  tff(c_116, plain, (~v2_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_86])).
% 11.79/4.82  tff(c_166, plain, (![A_73, B_74]: (m1_subset_1(k1_tarski(A_73), k1_zfmisc_1(B_74)) | ~r2_hidden(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.79/4.82  tff(c_42, plain, (![A_25, B_26]: (r1_tarski(A_25, B_26) | ~m1_subset_1(A_25, k1_zfmisc_1(B_26)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.79/4.82  tff(c_171, plain, (![A_75, B_76]: (r1_tarski(k1_tarski(A_75), B_76) | ~r2_hidden(A_75, B_76))), inference(resolution, [status(thm)], [c_166, c_42])).
% 11.79/4.82  tff(c_26, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=k1_xboole_0 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.79/4.82  tff(c_175, plain, (![A_75, B_76]: (k4_xboole_0(k1_tarski(A_75), B_76)=k1_xboole_0 | ~r2_hidden(A_75, B_76))), inference(resolution, [status(thm)], [c_171, c_26])).
% 11.79/4.82  tff(c_24, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | k4_xboole_0(A_11, B_12)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.79/4.82  tff(c_426, plain, (![B_103, A_104]: (B_103=A_104 | ~r1_tarski(A_104, B_103) | ~v1_zfmisc_1(B_103) | v1_xboole_0(B_103) | v1_xboole_0(A_104))), inference(cnfTransformation, [status(thm)], [f_139])).
% 11.79/4.82  tff(c_9272, plain, (![B_432, A_433]: (B_432=A_433 | ~v1_zfmisc_1(B_432) | v1_xboole_0(B_432) | v1_xboole_0(A_433) | k4_xboole_0(A_433, B_432)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_426])).
% 11.79/4.82  tff(c_9276, plain, (![A_433]: (A_433='#skF_6' | v1_xboole_0('#skF_6') | v1_xboole_0(A_433) | k4_xboole_0(A_433, '#skF_6')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_114, c_9272])).
% 11.79/4.82  tff(c_9281, plain, (![A_434]: (A_434='#skF_6' | v1_xboole_0(A_434) | k4_xboole_0(A_434, '#skF_6')!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_76, c_9276])).
% 11.79/4.82  tff(c_34, plain, (![A_17]: (~v1_xboole_0(k1_tarski(A_17)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.79/4.82  tff(c_9334, plain, (![A_435]: (k1_tarski(A_435)='#skF_6' | k4_xboole_0(k1_tarski(A_435), '#skF_6')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_9281, c_34])).
% 11.79/4.82  tff(c_9340, plain, (![A_436]: (k1_tarski(A_436)='#skF_6' | ~r2_hidden(A_436, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_175, c_9334])).
% 11.79/4.82  tff(c_9379, plain, (k1_tarski('#skF_1'('#skF_6'))='#skF_6' | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_4, c_9340])).
% 11.79/4.82  tff(c_9390, plain, (k1_tarski('#skF_1'('#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_76, c_9379])).
% 11.79/4.82  tff(c_28, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.79/4.82  tff(c_74, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_200])).
% 11.79/4.82  tff(c_137, plain, (![A_66, B_67]: (r1_tarski(A_66, B_67) | ~m1_subset_1(A_66, k1_zfmisc_1(B_67)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.79/4.82  tff(c_146, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_74, c_137])).
% 11.79/4.82  tff(c_147, plain, (![A_68, B_69]: (k4_xboole_0(A_68, B_69)=k1_xboole_0 | ~r1_tarski(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.79/4.82  tff(c_154, plain, (k4_xboole_0('#skF_6', u1_struct_0('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_146, c_147])).
% 11.79/4.82  tff(c_176, plain, (![A_77, B_78]: (k4_xboole_0(A_77, k4_xboole_0(A_77, B_78))=k3_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.79/4.82  tff(c_191, plain, (k3_xboole_0('#skF_6', u1_struct_0('#skF_5'))=k4_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_154, c_176])).
% 11.79/4.82  tff(c_197, plain, (k3_xboole_0('#skF_6', u1_struct_0('#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_191])).
% 11.79/4.82  tff(c_227, plain, (![D_80, B_81, A_82]: (r2_hidden(D_80, B_81) | ~r2_hidden(D_80, k3_xboole_0(A_82, B_81)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.79/4.82  tff(c_3584, plain, (![A_270, B_271]: (r2_hidden('#skF_1'(k3_xboole_0(A_270, B_271)), B_271) | v1_xboole_0(k3_xboole_0(A_270, B_271)))), inference(resolution, [status(thm)], [c_4, c_227])).
% 11.79/4.82  tff(c_3642, plain, (r2_hidden('#skF_1'('#skF_6'), u1_struct_0('#skF_5')) | v1_xboole_0(k3_xboole_0('#skF_6', u1_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_197, c_3584])).
% 11.79/4.82  tff(c_3656, plain, (r2_hidden('#skF_1'('#skF_6'), u1_struct_0('#skF_5')) | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_197, c_3642])).
% 11.79/4.82  tff(c_3657, plain, (r2_hidden('#skF_1'('#skF_6'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_76, c_3656])).
% 11.79/4.82  tff(c_40, plain, (![A_23, B_24]: (m1_subset_1(A_23, B_24) | ~r2_hidden(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.79/4.82  tff(c_3696, plain, (m1_subset_1('#skF_1'('#skF_6'), u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_3657, c_40])).
% 11.79/4.82  tff(c_239, plain, (![D_83]: (r2_hidden(D_83, u1_struct_0('#skF_5')) | ~r2_hidden(D_83, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_197, c_227])).
% 11.79/4.82  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.79/4.82  tff(c_247, plain, (![D_83]: (~v1_xboole_0(u1_struct_0('#skF_5')) | ~r2_hidden(D_83, '#skF_6'))), inference(resolution, [status(thm)], [c_239, c_2])).
% 11.79/4.82  tff(c_260, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_247])).
% 11.79/4.82  tff(c_52, plain, (![A_32, B_33]: (k6_domain_1(A_32, B_33)=k1_tarski(B_33) | ~m1_subset_1(B_33, A_32) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.79/4.82  tff(c_3700, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_1'('#skF_6'))=k1_tarski('#skF_1'('#skF_6')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_3696, c_52])).
% 11.79/4.82  tff(c_3703, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_1'('#skF_6'))=k1_tarski('#skF_1'('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_260, c_3700])).
% 11.79/4.82  tff(c_72, plain, (![A_47, B_49]: (v2_tex_2(k6_domain_1(u1_struct_0(A_47), B_49), A_47) | ~m1_subset_1(B_49, u1_struct_0(A_47)) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_180])).
% 11.79/4.82  tff(c_3881, plain, (v2_tex_2(k1_tarski('#skF_1'('#skF_6')), '#skF_5') | ~m1_subset_1('#skF_1'('#skF_6'), u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3703, c_72])).
% 11.79/4.82  tff(c_3891, plain, (v2_tex_2(k1_tarski('#skF_1'('#skF_6')), '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_3696, c_3881])).
% 11.79/4.82  tff(c_3892, plain, (v2_tex_2(k1_tarski('#skF_1'('#skF_6')), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_84, c_3891])).
% 11.79/4.82  tff(c_9392, plain, (v2_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9390, c_3892])).
% 11.79/4.82  tff(c_9397, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116, c_9392])).
% 11.79/4.82  tff(c_9400, plain, (![D_437]: (~r2_hidden(D_437, '#skF_6'))), inference(splitRight, [status(thm)], [c_247])).
% 11.79/4.82  tff(c_9404, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_4, c_9400])).
% 11.79/4.82  tff(c_9408, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_9404])).
% 11.79/4.82  tff(c_9409, plain, (v2_tex_2('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_92])).
% 11.79/4.82  tff(c_26518, plain, (![A_1122, B_1123]: (~v2_struct_0('#skF_4'(A_1122, B_1123)) | ~v2_tex_2(B_1123, A_1122) | ~m1_subset_1(B_1123, k1_zfmisc_1(u1_struct_0(A_1122))) | v1_xboole_0(B_1123) | ~l1_pre_topc(A_1122) | ~v2_pre_topc(A_1122) | v2_struct_0(A_1122))), inference(cnfTransformation, [status(thm)], [f_168])).
% 11.79/4.82  tff(c_26533, plain, (~v2_struct_0('#skF_4'('#skF_5', '#skF_6')) | ~v2_tex_2('#skF_6', '#skF_5') | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_74, c_26518])).
% 11.79/4.82  tff(c_26541, plain, (~v2_struct_0('#skF_4'('#skF_5', '#skF_6')) | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_9409, c_26533])).
% 11.79/4.82  tff(c_26542, plain, (~v2_struct_0('#skF_4'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_84, c_76, c_26541])).
% 11.79/4.82  tff(c_9410, plain, (~v1_zfmisc_1('#skF_6')), inference(splitRight, [status(thm)], [c_92])).
% 11.79/4.82  tff(c_26971, plain, (![A_1142, B_1143]: (u1_struct_0('#skF_4'(A_1142, B_1143))=B_1143 | ~v2_tex_2(B_1143, A_1142) | ~m1_subset_1(B_1143, k1_zfmisc_1(u1_struct_0(A_1142))) | v1_xboole_0(B_1143) | ~l1_pre_topc(A_1142) | ~v2_pre_topc(A_1142) | v2_struct_0(A_1142))), inference(cnfTransformation, [status(thm)], [f_168])).
% 11.79/4.82  tff(c_26986, plain, (u1_struct_0('#skF_4'('#skF_5', '#skF_6'))='#skF_6' | ~v2_tex_2('#skF_6', '#skF_5') | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_74, c_26971])).
% 11.79/4.82  tff(c_26994, plain, (u1_struct_0('#skF_4'('#skF_5', '#skF_6'))='#skF_6' | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_9409, c_26986])).
% 11.79/4.82  tff(c_26995, plain, (u1_struct_0('#skF_4'('#skF_5', '#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_84, c_76, c_26994])).
% 11.79/4.82  tff(c_50, plain, (![A_31]: (v1_zfmisc_1(u1_struct_0(A_31)) | ~l1_struct_0(A_31) | ~v7_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.79/4.82  tff(c_27014, plain, (v1_zfmisc_1('#skF_6') | ~l1_struct_0('#skF_4'('#skF_5', '#skF_6')) | ~v7_struct_0('#skF_4'('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_26995, c_50])).
% 11.79/4.82  tff(c_27023, plain, (~l1_struct_0('#skF_4'('#skF_5', '#skF_6')) | ~v7_struct_0('#skF_4'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_9410, c_27014])).
% 11.79/4.82  tff(c_27121, plain, (~v7_struct_0('#skF_4'('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_27023])).
% 11.79/4.82  tff(c_80, plain, (v2_tdlat_3('#skF_5')), inference(cnfTransformation, [status(thm)], [f_200])).
% 11.79/4.82  tff(c_26738, plain, (![A_1134, B_1135]: (v1_tdlat_3('#skF_4'(A_1134, B_1135)) | ~v2_tex_2(B_1135, A_1134) | ~m1_subset_1(B_1135, k1_zfmisc_1(u1_struct_0(A_1134))) | v1_xboole_0(B_1135) | ~l1_pre_topc(A_1134) | ~v2_pre_topc(A_1134) | v2_struct_0(A_1134))), inference(cnfTransformation, [status(thm)], [f_168])).
% 11.79/4.82  tff(c_26753, plain, (v1_tdlat_3('#skF_4'('#skF_5', '#skF_6')) | ~v2_tex_2('#skF_6', '#skF_5') | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_74, c_26738])).
% 11.79/4.82  tff(c_26761, plain, (v1_tdlat_3('#skF_4'('#skF_5', '#skF_6')) | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_9409, c_26753])).
% 11.79/4.82  tff(c_26762, plain, (v1_tdlat_3('#skF_4'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_84, c_76, c_26761])).
% 11.79/4.82  tff(c_27145, plain, (![A_1151, B_1152]: (m1_pre_topc('#skF_4'(A_1151, B_1152), A_1151) | ~v2_tex_2(B_1152, A_1151) | ~m1_subset_1(B_1152, k1_zfmisc_1(u1_struct_0(A_1151))) | v1_xboole_0(B_1152) | ~l1_pre_topc(A_1151) | ~v2_pre_topc(A_1151) | v2_struct_0(A_1151))), inference(cnfTransformation, [status(thm)], [f_168])).
% 11.79/4.82  tff(c_27158, plain, (m1_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5') | ~v2_tex_2('#skF_6', '#skF_5') | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_74, c_27145])).
% 11.79/4.82  tff(c_27167, plain, (m1_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5') | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_9409, c_27158])).
% 11.79/4.82  tff(c_27168, plain, (m1_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_84, c_76, c_27167])).
% 11.79/4.82  tff(c_56, plain, (![B_37, A_35]: (~v1_tdlat_3(B_37) | v7_struct_0(B_37) | v2_struct_0(B_37) | ~m1_pre_topc(B_37, A_35) | ~l1_pre_topc(A_35) | ~v2_tdlat_3(A_35) | ~v2_pre_topc(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_126])).
% 11.79/4.82  tff(c_27171, plain, (~v1_tdlat_3('#skF_4'('#skF_5', '#skF_6')) | v7_struct_0('#skF_4'('#skF_5', '#skF_6')) | v2_struct_0('#skF_4'('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | ~v2_tdlat_3('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_27168, c_56])).
% 11.79/4.82  tff(c_27177, plain, (v7_struct_0('#skF_4'('#skF_5', '#skF_6')) | v2_struct_0('#skF_4'('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_26762, c_27171])).
% 11.79/4.82  tff(c_27179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_26542, c_27121, c_27177])).
% 11.79/4.82  tff(c_27180, plain, (~l1_struct_0('#skF_4'('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_27023])).
% 11.79/4.82  tff(c_27185, plain, (~l1_pre_topc('#skF_4'('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_46, c_27180])).
% 11.79/4.82  tff(c_27193, plain, (![A_1155, B_1156]: (m1_pre_topc('#skF_4'(A_1155, B_1156), A_1155) | ~v2_tex_2(B_1156, A_1155) | ~m1_subset_1(B_1156, k1_zfmisc_1(u1_struct_0(A_1155))) | v1_xboole_0(B_1156) | ~l1_pre_topc(A_1155) | ~v2_pre_topc(A_1155) | v2_struct_0(A_1155))), inference(cnfTransformation, [status(thm)], [f_168])).
% 11.79/4.82  tff(c_27206, plain, (m1_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5') | ~v2_tex_2('#skF_6', '#skF_5') | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_74, c_27193])).
% 11.79/4.82  tff(c_27215, plain, (m1_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5') | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_9409, c_27206])).
% 11.79/4.82  tff(c_27216, plain, (m1_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_84, c_76, c_27215])).
% 11.79/4.82  tff(c_48, plain, (![B_30, A_28]: (l1_pre_topc(B_30) | ~m1_pre_topc(B_30, A_28) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.79/4.82  tff(c_27222, plain, (l1_pre_topc('#skF_4'('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_27216, c_48])).
% 11.79/4.82  tff(c_27229, plain, (l1_pre_topc('#skF_4'('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_27222])).
% 11.79/4.82  tff(c_27231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27185, c_27229])).
% 11.79/4.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.79/4.82  
% 11.79/4.82  Inference rules
% 11.79/4.82  ----------------------
% 11.79/4.82  #Ref     : 9
% 11.79/4.82  #Sup     : 6688
% 11.79/4.82  #Fact    : 0
% 11.79/4.82  #Define  : 0
% 11.79/4.82  #Split   : 26
% 11.79/4.82  #Chain   : 0
% 11.79/4.82  #Close   : 0
% 11.79/4.82  
% 11.79/4.82  Ordering : KBO
% 11.79/4.82  
% 11.79/4.82  Simplification rules
% 11.79/4.82  ----------------------
% 11.79/4.82  #Subsume      : 2346
% 11.79/4.82  #Demod        : 2543
% 11.79/4.82  #Tautology    : 2042
% 11.79/4.82  #SimpNegUnit  : 480
% 11.79/4.82  #BackRed      : 158
% 11.79/4.82  
% 11.79/4.82  #Partial instantiations: 0
% 11.79/4.82  #Strategies tried      : 1
% 11.79/4.82  
% 11.79/4.82  Timing (in seconds)
% 11.79/4.82  ----------------------
% 11.79/4.82  Preprocessing        : 0.37
% 11.79/4.82  Parsing              : 0.20
% 11.79/4.82  CNF conversion       : 0.03
% 11.79/4.82  Main loop            : 3.61
% 11.79/4.82  Inferencing          : 0.97
% 11.79/4.82  Reduction            : 1.30
% 11.79/4.82  Demodulation         : 0.91
% 11.79/4.82  BG Simplification    : 0.10
% 11.79/4.82  Subsumption          : 0.97
% 11.79/4.82  Abstraction          : 0.14
% 11.79/4.82  MUC search           : 0.00
% 11.79/4.82  Cooper               : 0.00
% 11.79/4.82  Total                : 4.03
% 11.79/4.82  Index Insertion      : 0.00
% 11.79/4.82  Index Deletion       : 0.00
% 11.79/4.82  Index Matching       : 0.00
% 11.79/4.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
