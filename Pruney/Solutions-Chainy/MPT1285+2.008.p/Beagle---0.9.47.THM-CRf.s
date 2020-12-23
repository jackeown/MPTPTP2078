%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:25 EST 2020

% Result     : Theorem 4.15s
% Output     : CNFRefutation 4.44s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 610 expanded)
%              Number of leaves         :   27 ( 214 expanded)
%              Depth                    :   15
%              Number of atoms          :  418 (2528 expanded)
%              Number of equality atoms :   44 ( 108 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_tops_1 > v4_tops_1 > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v6_tops_1,type,(
    v6_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v4_tops_1,type,(
    v4_tops_1: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( ( ( v3_pre_topc(D,B)
                          & v4_tops_1(D,B) )
                       => v6_tops_1(D,B) )
                      & ( v6_tops_1(C,A)
                       => ( v3_pre_topc(C,A)
                          & v4_tops_1(C,A) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_tops_1)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_tops_1(B,A)
          <=> B = k1_tops_1(A,k2_pre_topc(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tops_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k1_tops_1(A,k1_tops_1(A,B)) = k1_tops_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_tops_1(B,A)
          <=> ( r1_tarski(k1_tops_1(A,k2_pre_topc(A,B)),B)
              & r1_tarski(B,k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).

tff(c_40,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1430,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_44,plain,
    ( ~ v6_tops_1('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_51,plain,(
    ~ v6_tops_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_185,plain,(
    ! [B_57,A_58] :
      ( r1_tarski(B_57,k2_pre_topc(A_58,B_57))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_187,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_185])).

tff(c_192,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_187])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_52,plain,(
    v6_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_246,plain,(
    ! [A_67,B_68] :
      ( k1_tops_1(A_67,k2_pre_topc(A_67,B_68)) = B_68
      | ~ v6_tops_1(B_68,A_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_250,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_246])).

tff(c_256,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_52,c_250])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k2_pre_topc(A_3,B_4),k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_223,plain,(
    ! [A_63,B_64] :
      ( k1_tops_1(A_63,k1_tops_1(A_63,B_64)) = k1_tops_1(A_63,B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_354,plain,(
    ! [A_82,B_83] :
      ( k1_tops_1(A_82,k1_tops_1(A_82,k2_pre_topc(A_82,B_83))) = k1_tops_1(A_82,k2_pre_topc(A_82,B_83))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(resolution,[status(thm)],[c_8,c_223])).

tff(c_358,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_354])).

tff(c_364,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_256,c_256,c_358])).

tff(c_42,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_62,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_124,plain,(
    ! [A_49,B_50] :
      ( k1_tops_1(A_49,k2_pre_topc(A_49,B_50)) = B_50
      | ~ v6_tops_1(B_50,A_49)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_128,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_124])).

tff(c_134,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_52,c_128])).

tff(c_93,plain,(
    ! [A_43,B_44] :
      ( m1_subset_1(k2_pre_topc(A_43,B_44),k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( v3_pre_topc(k1_tops_1(A_14,B_15),A_14)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_170,plain,(
    ! [A_55,B_56] :
      ( v3_pre_topc(k1_tops_1(A_55,k2_pre_topc(A_55,B_56)),A_55)
      | ~ v2_pre_topc(A_55)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55) ) ),
    inference(resolution,[status(thm)],[c_93,c_22])).

tff(c_173,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_170])).

tff(c_175,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_36,c_173])).

tff(c_177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_175])).

tff(c_179,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_307,plain,(
    ! [B_77,A_78,C_79] :
      ( r1_tarski(B_77,k1_tops_1(A_78,C_79))
      | ~ r1_tarski(B_77,C_79)
      | ~ v3_pre_topc(B_77,A_78)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_311,plain,(
    ! [B_77] :
      ( r1_tarski(B_77,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(B_77,'#skF_3')
      | ~ v3_pre_topc(B_77,'#skF_1')
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_307])).

tff(c_321,plain,(
    ! [B_80] :
      ( r1_tarski(B_80,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(B_80,'#skF_3')
      | ~ v3_pre_topc(B_80,'#skF_1')
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_311])).

tff(c_328,plain,
    ( r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_321])).

tff(c_334,plain,(
    r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_6,c_328])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_337,plain,
    ( k1_tops_1('#skF_1','#skF_3') = '#skF_3'
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_334,c_2])).

tff(c_338,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_337])).

tff(c_368,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_338])).

tff(c_375,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_368])).

tff(c_376,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_337])).

tff(c_178,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_182,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_378,plain,(
    ! [B_84,A_85] :
      ( v4_tops_1(B_84,A_85)
      | ~ r1_tarski(B_84,k2_pre_topc(A_85,k1_tops_1(A_85,B_84)))
      | ~ r1_tarski(k1_tops_1(A_85,k2_pre_topc(A_85,B_84)),B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_384,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_378])).

tff(c_387,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_6,c_384])).

tff(c_388,plain,(
    ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_387])).

tff(c_406,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_376,c_388])).

tff(c_407,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_417,plain,(
    ! [B_86,A_87] :
      ( r1_tarski(B_86,k2_pre_topc(A_87,B_86))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_421,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_417])).

tff(c_427,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_421])).

tff(c_577,plain,(
    ! [B_108,A_109,C_110] :
      ( r1_tarski(B_108,k1_tops_1(A_109,C_110))
      | ~ r1_tarski(B_108,C_110)
      | ~ v3_pre_topc(B_108,A_109)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_584,plain,(
    ! [B_108,A_3,B_4] :
      ( r1_tarski(B_108,k1_tops_1(A_3,k2_pre_topc(A_3,B_4)))
      | ~ r1_tarski(B_108,k2_pre_topc(A_3,B_4))
      | ~ v3_pre_topc(B_108,A_3)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ l1_pre_topc(A_3) ) ),
    inference(resolution,[status(thm)],[c_8,c_577])).

tff(c_408,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_410,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_40])).

tff(c_411,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_410])).

tff(c_413,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_411])).

tff(c_414,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_410])).

tff(c_16,plain,(
    ! [A_8,B_10] :
      ( r1_tarski(k1_tops_1(A_8,k2_pre_topc(A_8,B_10)),B_10)
      | ~ v4_tops_1(B_10,A_8)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_814,plain,(
    ! [B_131,A_132,B_133] :
      ( r1_tarski(B_131,k1_tops_1(A_132,k2_pre_topc(A_132,B_133)))
      | ~ r1_tarski(B_131,k2_pre_topc(A_132,B_133))
      | ~ v3_pre_topc(B_131,A_132)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132) ) ),
    inference(resolution,[status(thm)],[c_8,c_577])).

tff(c_530,plain,(
    ! [A_104,B_105] :
      ( r1_tarski(k1_tops_1(A_104,k2_pre_topc(A_104,B_105)),B_105)
      | ~ v4_tops_1(B_105,A_104)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_536,plain,(
    ! [A_104,B_105] :
      ( k1_tops_1(A_104,k2_pre_topc(A_104,B_105)) = B_105
      | ~ r1_tarski(B_105,k1_tops_1(A_104,k2_pre_topc(A_104,B_105)))
      | ~ v4_tops_1(B_105,A_104)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(resolution,[status(thm)],[c_530,c_2])).

tff(c_926,plain,(
    ! [A_144,B_145] :
      ( k1_tops_1(A_144,k2_pre_topc(A_144,B_145)) = B_145
      | ~ v4_tops_1(B_145,A_144)
      | ~ r1_tarski(B_145,k2_pre_topc(A_144,B_145))
      | ~ v3_pre_topc(B_145,A_144)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144) ) ),
    inference(resolution,[status(thm)],[c_814,c_536])).

tff(c_932,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_427,c_926])).

tff(c_941,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_407,c_414,c_932])).

tff(c_690,plain,(
    ! [B_125,A_126,B_127] :
      ( r1_tarski(B_125,k1_tops_1(A_126,k2_pre_topc(A_126,B_127)))
      | ~ r1_tarski(B_125,k2_pre_topc(A_126,B_127))
      | ~ v3_pre_topc(B_125,A_126)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126) ) ),
    inference(resolution,[status(thm)],[c_8,c_577])).

tff(c_728,plain,(
    ! [A_129,B_130] :
      ( k1_tops_1(A_129,k2_pre_topc(A_129,B_130)) = B_130
      | ~ v4_tops_1(B_130,A_129)
      | ~ r1_tarski(B_130,k2_pre_topc(A_129,B_130))
      | ~ v3_pre_topc(B_130,A_129)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129) ) ),
    inference(resolution,[status(thm)],[c_690,c_536])).

tff(c_732,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_427,c_728])).

tff(c_738,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_407,c_414,c_732])).

tff(c_455,plain,(
    ! [A_92,B_93] :
      ( k1_tops_1(A_92,k1_tops_1(A_92,B_93)) = k1_tops_1(A_92,B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_540,plain,(
    ! [A_106,B_107] :
      ( k1_tops_1(A_106,k1_tops_1(A_106,k2_pre_topc(A_106,B_107))) = k1_tops_1(A_106,k2_pre_topc(A_106,B_107))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(resolution,[status(thm)],[c_8,c_455])).

tff(c_546,plain,
    ( k1_tops_1('#skF_2',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) = k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_540])).

tff(c_553,plain,(
    k1_tops_1('#skF_2',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) = k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_546])).

tff(c_14,plain,(
    ! [B_10,A_8] :
      ( r1_tarski(B_10,k2_pre_topc(A_8,k1_tops_1(A_8,B_10)))
      | ~ v4_tops_1(B_10,A_8)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_569,plain,
    ( r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k2_pre_topc('#skF_2',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))))
    | ~ v4_tops_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_2')
    | ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_14])).

tff(c_573,plain,
    ( r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k2_pre_topc('#skF_2',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))))
    | ~ v4_tops_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_2')
    | ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_569])).

tff(c_673,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_573])).

tff(c_742,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_673])).

tff(c_746,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_742])).

tff(c_748,plain,(
    m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_573])).

tff(c_583,plain,(
    ! [B_108] :
      ( r1_tarski(B_108,k1_tops_1('#skF_2','#skF_4'))
      | ~ r1_tarski(B_108,'#skF_4')
      | ~ v3_pre_topc(B_108,'#skF_2')
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_577])).

tff(c_590,plain,(
    ! [B_108] :
      ( r1_tarski(B_108,k1_tops_1('#skF_2','#skF_4'))
      | ~ r1_tarski(B_108,'#skF_4')
      | ~ v3_pre_topc(B_108,'#skF_2')
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_583])).

tff(c_769,plain,
    ( r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_748,c_590])).

tff(c_791,plain,(
    ~ v3_pre_topc(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_769])).

tff(c_948,plain,(
    ~ v3_pre_topc('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_941,c_791])).

tff(c_955,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_948])).

tff(c_956,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_4')
    | r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_769])).

tff(c_958,plain,(
    ~ r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_956])).

tff(c_961,plain,
    ( ~ v4_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_958])).

tff(c_965,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_414,c_961])).

tff(c_967,plain,(
    r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_956])).

tff(c_976,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_967,c_2])).

tff(c_980,plain,(
    ~ r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_976])).

tff(c_1007,plain,
    ( ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_584,c_980])).

tff(c_1011,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_407,c_427,c_1007])).

tff(c_1012,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_976])).

tff(c_18,plain,(
    ! [B_13,A_11] :
      ( v6_tops_1(B_13,A_11)
      | k1_tops_1(A_11,k2_pre_topc(A_11,B_13)) != B_13
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1045,plain,
    ( v6_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1012,c_18])).

tff(c_1062,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_1045])).

tff(c_1064,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_1062])).

tff(c_1065,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1066,plain,(
    ~ v6_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1067,plain,(
    v6_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_1068,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1066,c_1067])).

tff(c_1069,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1080,plain,(
    ! [B_151,A_152] :
      ( r1_tarski(B_151,k2_pre_topc(A_152,B_151))
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_pre_topc(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1084,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_1080])).

tff(c_1090,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1084])).

tff(c_1211,plain,(
    ! [B_173,A_174,C_175] :
      ( r1_tarski(B_173,k1_tops_1(A_174,C_175))
      | ~ r1_tarski(B_173,C_175)
      | ~ v3_pre_topc(B_173,A_174)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(u1_struct_0(A_174)))
      | ~ m1_subset_1(B_173,k1_zfmisc_1(u1_struct_0(A_174)))
      | ~ l1_pre_topc(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1324,plain,(
    ! [B_188,A_189,B_190] :
      ( r1_tarski(B_188,k1_tops_1(A_189,k2_pre_topc(A_189,B_190)))
      | ~ r1_tarski(B_188,k2_pre_topc(A_189,B_190))
      | ~ v3_pre_topc(B_188,A_189)
      | ~ m1_subset_1(B_188,k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ m1_subset_1(B_190,k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ l1_pre_topc(A_189) ) ),
    inference(resolution,[status(thm)],[c_8,c_1211])).

tff(c_1160,plain,(
    ! [A_167,B_168] :
      ( r1_tarski(k1_tops_1(A_167,k2_pre_topc(A_167,B_168)),B_168)
      | ~ v4_tops_1(B_168,A_167)
      | ~ m1_subset_1(B_168,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ l1_pre_topc(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1163,plain,(
    ! [A_167,B_168] :
      ( k1_tops_1(A_167,k2_pre_topc(A_167,B_168)) = B_168
      | ~ r1_tarski(B_168,k1_tops_1(A_167,k2_pre_topc(A_167,B_168)))
      | ~ v4_tops_1(B_168,A_167)
      | ~ m1_subset_1(B_168,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ l1_pre_topc(A_167) ) ),
    inference(resolution,[status(thm)],[c_1160,c_2])).

tff(c_1359,plain,(
    ! [A_195,B_196] :
      ( k1_tops_1(A_195,k2_pre_topc(A_195,B_196)) = B_196
      | ~ v4_tops_1(B_196,A_195)
      | ~ r1_tarski(B_196,k2_pre_topc(A_195,B_196))
      | ~ v3_pre_topc(B_196,A_195)
      | ~ m1_subset_1(B_196,k1_zfmisc_1(u1_struct_0(A_195)))
      | ~ l1_pre_topc(A_195) ) ),
    inference(resolution,[status(thm)],[c_1324,c_1163])).

tff(c_1363,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1090,c_1359])).

tff(c_1369,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_1065,c_1069,c_1363])).

tff(c_1397,plain,
    ( v6_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1369,c_18])).

tff(c_1416,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_1397])).

tff(c_1418,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_1416])).

tff(c_1419,plain,(
    v6_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1493,plain,(
    ! [A_207,B_208] :
      ( k1_tops_1(A_207,k2_pre_topc(A_207,B_208)) = B_208
      | ~ v6_tops_1(B_208,A_207)
      | ~ m1_subset_1(B_208,k1_zfmisc_1(u1_struct_0(A_207)))
      | ~ l1_pre_topc(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1497,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1493])).

tff(c_1503,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1419,c_1497])).

tff(c_1464,plain,(
    ! [A_203,B_204] :
      ( m1_subset_1(k2_pre_topc(A_203,B_204),k1_zfmisc_1(u1_struct_0(A_203)))
      | ~ m1_subset_1(B_204,k1_zfmisc_1(u1_struct_0(A_203)))
      | ~ l1_pre_topc(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1526,plain,(
    ! [A_211,B_212] :
      ( v3_pre_topc(k1_tops_1(A_211,k2_pre_topc(A_211,B_212)),A_211)
      | ~ v2_pre_topc(A_211)
      | ~ m1_subset_1(B_212,k1_zfmisc_1(u1_struct_0(A_211)))
      | ~ l1_pre_topc(A_211) ) ),
    inference(resolution,[status(thm)],[c_1464,c_22])).

tff(c_1532,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1503,c_1526])).

tff(c_1536,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_36,c_1532])).

tff(c_1538,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1430,c_1536])).

tff(c_1540,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1541,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_1543,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1540,c_1541])).

tff(c_1544,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1547,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1544])).

tff(c_1550,plain,(
    ! [B_213,A_214] :
      ( r1_tarski(B_213,k2_pre_topc(A_214,B_213))
      | ~ m1_subset_1(B_213,k1_zfmisc_1(u1_struct_0(A_214)))
      | ~ l1_pre_topc(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1552,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1550])).

tff(c_1557,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1552])).

tff(c_1611,plain,(
    ! [A_223,B_224] :
      ( k1_tops_1(A_223,k2_pre_topc(A_223,B_224)) = B_224
      | ~ v6_tops_1(B_224,A_223)
      | ~ m1_subset_1(B_224,k1_zfmisc_1(u1_struct_0(A_223)))
      | ~ l1_pre_topc(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1615,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1611])).

tff(c_1621,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1419,c_1615])).

tff(c_1588,plain,(
    ! [A_219,B_220] :
      ( k1_tops_1(A_219,k1_tops_1(A_219,B_220)) = k1_tops_1(A_219,B_220)
      | ~ m1_subset_1(B_220,k1_zfmisc_1(u1_struct_0(A_219)))
      | ~ l1_pre_topc(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1696,plain,(
    ! [A_233,B_234] :
      ( k1_tops_1(A_233,k1_tops_1(A_233,k2_pre_topc(A_233,B_234))) = k1_tops_1(A_233,k2_pre_topc(A_233,B_234))
      | ~ m1_subset_1(B_234,k1_zfmisc_1(u1_struct_0(A_233)))
      | ~ l1_pre_topc(A_233) ) ),
    inference(resolution,[status(thm)],[c_8,c_1588])).

tff(c_1700,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1696])).

tff(c_1706,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1621,c_1621,c_1700])).

tff(c_1813,plain,(
    ! [B_246,A_247] :
      ( v4_tops_1(B_246,A_247)
      | ~ r1_tarski(B_246,k2_pre_topc(A_247,k1_tops_1(A_247,B_246)))
      | ~ r1_tarski(k1_tops_1(A_247,k2_pre_topc(A_247,B_246)),B_246)
      | ~ m1_subset_1(B_246,k1_zfmisc_1(u1_struct_0(A_247)))
      | ~ l1_pre_topc(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1819,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1621,c_1813])).

tff(c_1826,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_6,c_1557,c_1706,c_1819])).

tff(c_1828,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1547,c_1826])).

tff(c_1830,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_1544])).

tff(c_1420,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_38,plain,
    ( ~ v6_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1834,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1540,c_1830,c_1420,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:05:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.15/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/1.71  
% 4.15/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/1.71  %$ v6_tops_1 > v4_tops_1 > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.15/1.71  
% 4.15/1.71  %Foreground sorts:
% 4.15/1.71  
% 4.15/1.71  
% 4.15/1.71  %Background operators:
% 4.15/1.71  
% 4.15/1.71  
% 4.15/1.71  %Foreground operators:
% 4.15/1.71  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.15/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.15/1.71  tff(v6_tops_1, type, v6_tops_1: ($i * $i) > $o).
% 4.15/1.71  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.15/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.15/1.71  tff(v4_tops_1, type, v4_tops_1: ($i * $i) > $o).
% 4.15/1.71  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.15/1.71  tff('#skF_2', type, '#skF_2': $i).
% 4.15/1.71  tff('#skF_3', type, '#skF_3': $i).
% 4.15/1.71  tff('#skF_1', type, '#skF_1': $i).
% 4.15/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.15/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.15/1.71  tff('#skF_4', type, '#skF_4': $i).
% 4.15/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.15/1.71  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.15/1.71  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.15/1.71  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.15/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.15/1.71  
% 4.44/1.75  tff(f_118, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (((v3_pre_topc(D, B) & v4_tops_1(D, B)) => v6_tops_1(D, B)) & (v6_tops_1(C, A) => (v3_pre_topc(C, A) & v4_tops_1(C, A)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_tops_1)).
% 4.44/1.75  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 4.44/1.75  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.44/1.75  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_tops_1(B, A) <=> (B = k1_tops_1(A, k2_pre_topc(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_tops_1)).
% 4.44/1.75  tff(f_37, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 4.44/1.75  tff(f_78, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k1_tops_1(A, k1_tops_1(A, B)) = k1_tops_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 4.44/1.75  tff(f_72, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 4.44/1.75  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 4.44/1.75  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) <=> (r1_tarski(k1_tops_1(A, k2_pre_topc(A, B)), B) & r1_tarski(B, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tops_1)).
% 4.44/1.75  tff(c_40, plain, (v4_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.44/1.75  tff(c_1430, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_40])).
% 4.44/1.75  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.44/1.75  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.44/1.75  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.44/1.75  tff(c_44, plain, (~v6_tops_1('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.44/1.75  tff(c_51, plain, (~v6_tops_1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_44])).
% 4.44/1.75  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.44/1.75  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.44/1.75  tff(c_185, plain, (![B_57, A_58]: (r1_tarski(B_57, k2_pre_topc(A_58, B_57)) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.44/1.75  tff(c_187, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_185])).
% 4.44/1.75  tff(c_192, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_187])).
% 4.44/1.75  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.44/1.75  tff(c_48, plain, (v3_pre_topc('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.44/1.75  tff(c_52, plain, (v6_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_48])).
% 4.44/1.75  tff(c_246, plain, (![A_67, B_68]: (k1_tops_1(A_67, k2_pre_topc(A_67, B_68))=B_68 | ~v6_tops_1(B_68, A_67) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.44/1.75  tff(c_250, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_246])).
% 4.44/1.75  tff(c_256, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_52, c_250])).
% 4.44/1.75  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k2_pre_topc(A_3, B_4), k1_zfmisc_1(u1_struct_0(A_3))) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0(A_3))) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.44/1.75  tff(c_223, plain, (![A_63, B_64]: (k1_tops_1(A_63, k1_tops_1(A_63, B_64))=k1_tops_1(A_63, B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.44/1.75  tff(c_354, plain, (![A_82, B_83]: (k1_tops_1(A_82, k1_tops_1(A_82, k2_pre_topc(A_82, B_83)))=k1_tops_1(A_82, k2_pre_topc(A_82, B_83)) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82))), inference(resolution, [status(thm)], [c_8, c_223])).
% 4.44/1.75  tff(c_358, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_354])).
% 4.44/1.75  tff(c_364, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_256, c_256, c_358])).
% 4.44/1.75  tff(c_42, plain, (v3_pre_topc('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.44/1.75  tff(c_62, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_42])).
% 4.44/1.75  tff(c_124, plain, (![A_49, B_50]: (k1_tops_1(A_49, k2_pre_topc(A_49, B_50))=B_50 | ~v6_tops_1(B_50, A_49) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.44/1.75  tff(c_128, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_124])).
% 4.44/1.75  tff(c_134, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_52, c_128])).
% 4.44/1.75  tff(c_93, plain, (![A_43, B_44]: (m1_subset_1(k2_pre_topc(A_43, B_44), k1_zfmisc_1(u1_struct_0(A_43))) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.44/1.75  tff(c_22, plain, (![A_14, B_15]: (v3_pre_topc(k1_tops_1(A_14, B_15), A_14) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.44/1.75  tff(c_170, plain, (![A_55, B_56]: (v3_pre_topc(k1_tops_1(A_55, k2_pre_topc(A_55, B_56)), A_55) | ~v2_pre_topc(A_55) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_pre_topc(A_55))), inference(resolution, [status(thm)], [c_93, c_22])).
% 4.44/1.75  tff(c_173, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_134, c_170])).
% 4.44/1.75  tff(c_175, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_36, c_173])).
% 4.44/1.75  tff(c_177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_175])).
% 4.44/1.75  tff(c_179, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_42])).
% 4.44/1.75  tff(c_307, plain, (![B_77, A_78, C_79]: (r1_tarski(B_77, k1_tops_1(A_78, C_79)) | ~r1_tarski(B_77, C_79) | ~v3_pre_topc(B_77, A_78) | ~m1_subset_1(C_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.44/1.75  tff(c_311, plain, (![B_77]: (r1_tarski(B_77, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(B_77, '#skF_3') | ~v3_pre_topc(B_77, '#skF_1') | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_307])).
% 4.44/1.75  tff(c_321, plain, (![B_80]: (r1_tarski(B_80, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(B_80, '#skF_3') | ~v3_pre_topc(B_80, '#skF_1') | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_311])).
% 4.44/1.75  tff(c_328, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski('#skF_3', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_321])).
% 4.44/1.75  tff(c_334, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_6, c_328])).
% 4.44/1.75  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.44/1.75  tff(c_337, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3' | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_334, c_2])).
% 4.44/1.75  tff(c_338, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_337])).
% 4.44/1.75  tff(c_368, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_364, c_338])).
% 4.44/1.75  tff(c_375, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_368])).
% 4.44/1.75  tff(c_376, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_337])).
% 4.44/1.75  tff(c_178, plain, (~v4_tops_1('#skF_3', '#skF_1') | v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 4.44/1.75  tff(c_182, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_178])).
% 4.44/1.75  tff(c_378, plain, (![B_84, A_85]: (v4_tops_1(B_84, A_85) | ~r1_tarski(B_84, k2_pre_topc(A_85, k1_tops_1(A_85, B_84))) | ~r1_tarski(k1_tops_1(A_85, k2_pre_topc(A_85, B_84)), B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.44/1.75  tff(c_384, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_256, c_378])).
% 4.44/1.75  tff(c_387, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_6, c_384])).
% 4.44/1.75  tff(c_388, plain, (~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_182, c_387])).
% 4.44/1.75  tff(c_406, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_192, c_376, c_388])).
% 4.44/1.75  tff(c_407, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_178])).
% 4.44/1.75  tff(c_417, plain, (![B_86, A_87]: (r1_tarski(B_86, k2_pre_topc(A_87, B_86)) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.44/1.75  tff(c_421, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_417])).
% 4.44/1.75  tff(c_427, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_421])).
% 4.44/1.75  tff(c_577, plain, (![B_108, A_109, C_110]: (r1_tarski(B_108, k1_tops_1(A_109, C_110)) | ~r1_tarski(B_108, C_110) | ~v3_pre_topc(B_108, A_109) | ~m1_subset_1(C_110, k1_zfmisc_1(u1_struct_0(A_109))) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.44/1.75  tff(c_584, plain, (![B_108, A_3, B_4]: (r1_tarski(B_108, k1_tops_1(A_3, k2_pre_topc(A_3, B_4))) | ~r1_tarski(B_108, k2_pre_topc(A_3, B_4)) | ~v3_pre_topc(B_108, A_3) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_3))) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0(A_3))) | ~l1_pre_topc(A_3))), inference(resolution, [status(thm)], [c_8, c_577])).
% 4.44/1.75  tff(c_408, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_178])).
% 4.44/1.75  tff(c_410, plain, (v4_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_40])).
% 4.44/1.75  tff(c_411, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_410])).
% 4.44/1.75  tff(c_413, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_408, c_411])).
% 4.44/1.75  tff(c_414, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_410])).
% 4.44/1.75  tff(c_16, plain, (![A_8, B_10]: (r1_tarski(k1_tops_1(A_8, k2_pre_topc(A_8, B_10)), B_10) | ~v4_tops_1(B_10, A_8) | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.44/1.75  tff(c_814, plain, (![B_131, A_132, B_133]: (r1_tarski(B_131, k1_tops_1(A_132, k2_pre_topc(A_132, B_133))) | ~r1_tarski(B_131, k2_pre_topc(A_132, B_133)) | ~v3_pre_topc(B_131, A_132) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_132))) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132))), inference(resolution, [status(thm)], [c_8, c_577])).
% 4.44/1.75  tff(c_530, plain, (![A_104, B_105]: (r1_tarski(k1_tops_1(A_104, k2_pre_topc(A_104, B_105)), B_105) | ~v4_tops_1(B_105, A_104) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.44/1.75  tff(c_536, plain, (![A_104, B_105]: (k1_tops_1(A_104, k2_pre_topc(A_104, B_105))=B_105 | ~r1_tarski(B_105, k1_tops_1(A_104, k2_pre_topc(A_104, B_105))) | ~v4_tops_1(B_105, A_104) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(resolution, [status(thm)], [c_530, c_2])).
% 4.44/1.75  tff(c_926, plain, (![A_144, B_145]: (k1_tops_1(A_144, k2_pre_topc(A_144, B_145))=B_145 | ~v4_tops_1(B_145, A_144) | ~r1_tarski(B_145, k2_pre_topc(A_144, B_145)) | ~v3_pre_topc(B_145, A_144) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_144))) | ~l1_pre_topc(A_144))), inference(resolution, [status(thm)], [c_814, c_536])).
% 4.44/1.75  tff(c_932, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_427, c_926])).
% 4.44/1.75  tff(c_941, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_407, c_414, c_932])).
% 4.44/1.75  tff(c_690, plain, (![B_125, A_126, B_127]: (r1_tarski(B_125, k1_tops_1(A_126, k2_pre_topc(A_126, B_127))) | ~r1_tarski(B_125, k2_pre_topc(A_126, B_127)) | ~v3_pre_topc(B_125, A_126) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_126))) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_pre_topc(A_126))), inference(resolution, [status(thm)], [c_8, c_577])).
% 4.44/1.75  tff(c_728, plain, (![A_129, B_130]: (k1_tops_1(A_129, k2_pre_topc(A_129, B_130))=B_130 | ~v4_tops_1(B_130, A_129) | ~r1_tarski(B_130, k2_pre_topc(A_129, B_130)) | ~v3_pre_topc(B_130, A_129) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129))), inference(resolution, [status(thm)], [c_690, c_536])).
% 4.44/1.75  tff(c_732, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_427, c_728])).
% 4.44/1.75  tff(c_738, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_407, c_414, c_732])).
% 4.44/1.75  tff(c_455, plain, (![A_92, B_93]: (k1_tops_1(A_92, k1_tops_1(A_92, B_93))=k1_tops_1(A_92, B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.44/1.75  tff(c_540, plain, (![A_106, B_107]: (k1_tops_1(A_106, k1_tops_1(A_106, k2_pre_topc(A_106, B_107)))=k1_tops_1(A_106, k2_pre_topc(A_106, B_107)) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106))), inference(resolution, [status(thm)], [c_8, c_455])).
% 4.44/1.75  tff(c_546, plain, (k1_tops_1('#skF_2', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))=k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_540])).
% 4.44/1.75  tff(c_553, plain, (k1_tops_1('#skF_2', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))=k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_546])).
% 4.44/1.75  tff(c_14, plain, (![B_10, A_8]: (r1_tarski(B_10, k2_pre_topc(A_8, k1_tops_1(A_8, B_10))) | ~v4_tops_1(B_10, A_8) | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.44/1.75  tff(c_569, plain, (r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k2_pre_topc('#skF_2', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))) | ~v4_tops_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_2') | ~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_553, c_14])).
% 4.44/1.75  tff(c_573, plain, (r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k2_pre_topc('#skF_2', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))) | ~v4_tops_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_2') | ~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_569])).
% 4.44/1.75  tff(c_673, plain, (~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_573])).
% 4.44/1.75  tff(c_742, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_738, c_673])).
% 4.44/1.75  tff(c_746, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_742])).
% 4.44/1.75  tff(c_748, plain, (m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_573])).
% 4.44/1.75  tff(c_583, plain, (![B_108]: (r1_tarski(B_108, k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(B_108, '#skF_4') | ~v3_pre_topc(B_108, '#skF_2') | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_577])).
% 4.44/1.75  tff(c_590, plain, (![B_108]: (r1_tarski(B_108, k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(B_108, '#skF_4') | ~v3_pre_topc(B_108, '#skF_2') | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_583])).
% 4.44/1.75  tff(c_769, plain, (r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_2')), inference(resolution, [status(thm)], [c_748, c_590])).
% 4.44/1.75  tff(c_791, plain, (~v3_pre_topc(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_2')), inference(splitLeft, [status(thm)], [c_769])).
% 4.44/1.75  tff(c_948, plain, (~v3_pre_topc('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_941, c_791])).
% 4.44/1.75  tff(c_955, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_407, c_948])).
% 4.44/1.75  tff(c_956, plain, (~r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_4') | r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_769])).
% 4.44/1.75  tff(c_958, plain, (~r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_4')), inference(splitLeft, [status(thm)], [c_956])).
% 4.44/1.75  tff(c_961, plain, (~v4_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_958])).
% 4.44/1.75  tff(c_965, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_414, c_961])).
% 4.44/1.75  tff(c_967, plain, (r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_4')), inference(splitRight, [status(thm)], [c_956])).
% 4.44/1.75  tff(c_976, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4' | ~r1_tarski('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_967, c_2])).
% 4.44/1.75  tff(c_980, plain, (~r1_tarski('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))), inference(splitLeft, [status(thm)], [c_976])).
% 4.44/1.75  tff(c_1007, plain, (~r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_584, c_980])).
% 4.44/1.75  tff(c_1011, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_407, c_427, c_1007])).
% 4.44/1.75  tff(c_1012, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_976])).
% 4.44/1.75  tff(c_18, plain, (![B_13, A_11]: (v6_tops_1(B_13, A_11) | k1_tops_1(A_11, k2_pre_topc(A_11, B_13))!=B_13 | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.44/1.75  tff(c_1045, plain, (v6_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1012, c_18])).
% 4.44/1.75  tff(c_1062, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_1045])).
% 4.44/1.75  tff(c_1064, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_1062])).
% 4.44/1.75  tff(c_1065, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 4.44/1.75  tff(c_1066, plain, (~v6_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 4.44/1.75  tff(c_46, plain, (v4_tops_1('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.44/1.75  tff(c_1067, plain, (v6_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 4.44/1.75  tff(c_1068, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1066, c_1067])).
% 4.44/1.75  tff(c_1069, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 4.44/1.75  tff(c_1080, plain, (![B_151, A_152]: (r1_tarski(B_151, k2_pre_topc(A_152, B_151)) | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_pre_topc(A_152))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.44/1.75  tff(c_1084, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_1080])).
% 4.44/1.75  tff(c_1090, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1084])).
% 4.44/1.75  tff(c_1211, plain, (![B_173, A_174, C_175]: (r1_tarski(B_173, k1_tops_1(A_174, C_175)) | ~r1_tarski(B_173, C_175) | ~v3_pre_topc(B_173, A_174) | ~m1_subset_1(C_175, k1_zfmisc_1(u1_struct_0(A_174))) | ~m1_subset_1(B_173, k1_zfmisc_1(u1_struct_0(A_174))) | ~l1_pre_topc(A_174))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.44/1.75  tff(c_1324, plain, (![B_188, A_189, B_190]: (r1_tarski(B_188, k1_tops_1(A_189, k2_pre_topc(A_189, B_190))) | ~r1_tarski(B_188, k2_pre_topc(A_189, B_190)) | ~v3_pre_topc(B_188, A_189) | ~m1_subset_1(B_188, k1_zfmisc_1(u1_struct_0(A_189))) | ~m1_subset_1(B_190, k1_zfmisc_1(u1_struct_0(A_189))) | ~l1_pre_topc(A_189))), inference(resolution, [status(thm)], [c_8, c_1211])).
% 4.44/1.75  tff(c_1160, plain, (![A_167, B_168]: (r1_tarski(k1_tops_1(A_167, k2_pre_topc(A_167, B_168)), B_168) | ~v4_tops_1(B_168, A_167) | ~m1_subset_1(B_168, k1_zfmisc_1(u1_struct_0(A_167))) | ~l1_pre_topc(A_167))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.44/1.75  tff(c_1163, plain, (![A_167, B_168]: (k1_tops_1(A_167, k2_pre_topc(A_167, B_168))=B_168 | ~r1_tarski(B_168, k1_tops_1(A_167, k2_pre_topc(A_167, B_168))) | ~v4_tops_1(B_168, A_167) | ~m1_subset_1(B_168, k1_zfmisc_1(u1_struct_0(A_167))) | ~l1_pre_topc(A_167))), inference(resolution, [status(thm)], [c_1160, c_2])).
% 4.44/1.75  tff(c_1359, plain, (![A_195, B_196]: (k1_tops_1(A_195, k2_pre_topc(A_195, B_196))=B_196 | ~v4_tops_1(B_196, A_195) | ~r1_tarski(B_196, k2_pre_topc(A_195, B_196)) | ~v3_pre_topc(B_196, A_195) | ~m1_subset_1(B_196, k1_zfmisc_1(u1_struct_0(A_195))) | ~l1_pre_topc(A_195))), inference(resolution, [status(thm)], [c_1324, c_1163])).
% 4.44/1.75  tff(c_1363, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1090, c_1359])).
% 4.44/1.75  tff(c_1369, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_1065, c_1069, c_1363])).
% 4.44/1.75  tff(c_1397, plain, (v6_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1369, c_18])).
% 4.44/1.75  tff(c_1416, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_1397])).
% 4.44/1.75  tff(c_1418, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_1416])).
% 4.44/1.75  tff(c_1419, plain, (v6_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 4.44/1.75  tff(c_1493, plain, (![A_207, B_208]: (k1_tops_1(A_207, k2_pre_topc(A_207, B_208))=B_208 | ~v6_tops_1(B_208, A_207) | ~m1_subset_1(B_208, k1_zfmisc_1(u1_struct_0(A_207))) | ~l1_pre_topc(A_207))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.44/1.75  tff(c_1497, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1493])).
% 4.44/1.75  tff(c_1503, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1419, c_1497])).
% 4.44/1.75  tff(c_1464, plain, (![A_203, B_204]: (m1_subset_1(k2_pre_topc(A_203, B_204), k1_zfmisc_1(u1_struct_0(A_203))) | ~m1_subset_1(B_204, k1_zfmisc_1(u1_struct_0(A_203))) | ~l1_pre_topc(A_203))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.44/1.75  tff(c_1526, plain, (![A_211, B_212]: (v3_pre_topc(k1_tops_1(A_211, k2_pre_topc(A_211, B_212)), A_211) | ~v2_pre_topc(A_211) | ~m1_subset_1(B_212, k1_zfmisc_1(u1_struct_0(A_211))) | ~l1_pre_topc(A_211))), inference(resolution, [status(thm)], [c_1464, c_22])).
% 4.44/1.75  tff(c_1532, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1503, c_1526])).
% 4.44/1.75  tff(c_1536, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_36, c_1532])).
% 4.44/1.75  tff(c_1538, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1430, c_1536])).
% 4.44/1.75  tff(c_1540, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_40])).
% 4.44/1.75  tff(c_1541, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_42])).
% 4.44/1.75  tff(c_1543, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1540, c_1541])).
% 4.44/1.75  tff(c_1544, plain, (~v4_tops_1('#skF_3', '#skF_1') | v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 4.44/1.75  tff(c_1547, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_1544])).
% 4.44/1.75  tff(c_1550, plain, (![B_213, A_214]: (r1_tarski(B_213, k2_pre_topc(A_214, B_213)) | ~m1_subset_1(B_213, k1_zfmisc_1(u1_struct_0(A_214))) | ~l1_pre_topc(A_214))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.44/1.75  tff(c_1552, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1550])).
% 4.44/1.75  tff(c_1557, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1552])).
% 4.44/1.75  tff(c_1611, plain, (![A_223, B_224]: (k1_tops_1(A_223, k2_pre_topc(A_223, B_224))=B_224 | ~v6_tops_1(B_224, A_223) | ~m1_subset_1(B_224, k1_zfmisc_1(u1_struct_0(A_223))) | ~l1_pre_topc(A_223))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.44/1.75  tff(c_1615, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1611])).
% 4.44/1.75  tff(c_1621, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1419, c_1615])).
% 4.44/1.75  tff(c_1588, plain, (![A_219, B_220]: (k1_tops_1(A_219, k1_tops_1(A_219, B_220))=k1_tops_1(A_219, B_220) | ~m1_subset_1(B_220, k1_zfmisc_1(u1_struct_0(A_219))) | ~l1_pre_topc(A_219))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.44/1.75  tff(c_1696, plain, (![A_233, B_234]: (k1_tops_1(A_233, k1_tops_1(A_233, k2_pre_topc(A_233, B_234)))=k1_tops_1(A_233, k2_pre_topc(A_233, B_234)) | ~m1_subset_1(B_234, k1_zfmisc_1(u1_struct_0(A_233))) | ~l1_pre_topc(A_233))), inference(resolution, [status(thm)], [c_8, c_1588])).
% 4.44/1.75  tff(c_1700, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1696])).
% 4.44/1.75  tff(c_1706, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1621, c_1621, c_1700])).
% 4.44/1.75  tff(c_1813, plain, (![B_246, A_247]: (v4_tops_1(B_246, A_247) | ~r1_tarski(B_246, k2_pre_topc(A_247, k1_tops_1(A_247, B_246))) | ~r1_tarski(k1_tops_1(A_247, k2_pre_topc(A_247, B_246)), B_246) | ~m1_subset_1(B_246, k1_zfmisc_1(u1_struct_0(A_247))) | ~l1_pre_topc(A_247))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.44/1.75  tff(c_1819, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1621, c_1813])).
% 4.44/1.75  tff(c_1826, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_6, c_1557, c_1706, c_1819])).
% 4.44/1.75  tff(c_1828, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1547, c_1826])).
% 4.44/1.75  tff(c_1830, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_1544])).
% 4.44/1.75  tff(c_1420, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 4.44/1.75  tff(c_38, plain, (~v6_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.44/1.75  tff(c_1834, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1540, c_1830, c_1420, c_38])).
% 4.44/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.44/1.75  
% 4.44/1.75  Inference rules
% 4.44/1.75  ----------------------
% 4.44/1.75  #Ref     : 0
% 4.44/1.75  #Sup     : 364
% 4.44/1.75  #Fact    : 0
% 4.44/1.75  #Define  : 0
% 4.44/1.75  #Split   : 48
% 4.44/1.75  #Chain   : 0
% 4.44/1.75  #Close   : 0
% 4.44/1.75  
% 4.44/1.75  Ordering : KBO
% 4.44/1.75  
% 4.44/1.75  Simplification rules
% 4.44/1.75  ----------------------
% 4.44/1.75  #Subsume      : 45
% 4.44/1.75  #Demod        : 516
% 4.44/1.75  #Tautology    : 147
% 4.44/1.75  #SimpNegUnit  : 8
% 4.44/1.75  #BackRed      : 30
% 4.44/1.75  
% 4.44/1.75  #Partial instantiations: 0
% 4.44/1.75  #Strategies tried      : 1
% 4.44/1.75  
% 4.44/1.75  Timing (in seconds)
% 4.44/1.75  ----------------------
% 4.44/1.75  Preprocessing        : 0.31
% 4.44/1.75  Parsing              : 0.17
% 4.44/1.75  CNF conversion       : 0.02
% 4.44/1.75  Main loop            : 0.64
% 4.44/1.75  Inferencing          : 0.22
% 4.44/1.75  Reduction            : 0.21
% 4.44/1.75  Demodulation         : 0.15
% 4.44/1.75  BG Simplification    : 0.03
% 4.44/1.75  Subsumption          : 0.13
% 4.44/1.75  Abstraction          : 0.03
% 4.44/1.75  MUC search           : 0.00
% 4.44/1.75  Cooper               : 0.00
% 4.44/1.75  Total                : 1.02
% 4.44/1.75  Index Insertion      : 0.00
% 4.44/1.75  Index Deletion       : 0.00
% 4.44/1.75  Index Matching       : 0.00
% 4.44/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
