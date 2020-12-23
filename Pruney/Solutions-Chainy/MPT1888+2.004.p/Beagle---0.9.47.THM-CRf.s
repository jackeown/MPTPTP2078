%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:21 EST 2020

% Result     : Theorem 22.24s
% Output     : CNFRefutation 22.38s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 812 expanded)
%              Number of leaves         :   41 ( 285 expanded)
%              Depth                    :   18
%              Number of atoms          :  232 (2605 expanded)
%              Number of equality atoms :   32 ( 442 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_8 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_185,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r1_xboole_0(k2_pre_topc(A,k6_domain_1(u1_struct_0(A),B)),k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C)))
                  | k2_pre_topc(A,k6_domain_1(u1_struct_0(A),B)) = k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tex_2)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_117,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_110,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_103,axiom,(
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
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(f_146,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_xboole_0(B,C)
                  & v3_pre_topc(B,A) )
               => r1_xboole_0(B,k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_tsep_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_165,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(B,k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C)))
               => k2_pre_topc(A,k6_domain_1(u1_struct_0(A),B)) = k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tex_2)).

tff(c_64,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_30,plain,(
    ! [A_20] :
      ( l1_struct_0(A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_60,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_179,plain,(
    ! [A_83,B_84] :
      ( k6_domain_1(A_83,B_84) = k1_tarski(B_84)
      | ~ m1_subset_1(B_84,A_83)
      | v1_xboole_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_186,plain,
    ( k6_domain_1(u1_struct_0('#skF_6'),'#skF_8') = k1_tarski('#skF_8')
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_60,c_179])).

tff(c_188,plain,(
    v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_32,plain,(
    ! [A_21] :
      ( ~ v1_xboole_0(u1_struct_0(A_21))
      | ~ l1_struct_0(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_191,plain,
    ( ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_188,c_32])).

tff(c_194,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_191])).

tff(c_197,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_194])).

tff(c_201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_197])).

tff(c_203,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_62,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_187,plain,
    ( k6_domain_1(u1_struct_0('#skF_6'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_62,c_179])).

tff(c_212,plain,(
    k6_domain_1(u1_struct_0('#skF_6'),'#skF_7') = k1_tarski('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_203,c_187])).

tff(c_587,plain,(
    ! [A_745,B_746] :
      ( m1_subset_1(k6_domain_1(A_745,B_746),k1_zfmisc_1(A_745))
      | ~ m1_subset_1(B_746,A_745)
      | v1_xboole_0(A_745) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_595,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_587])).

tff(c_601,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_595])).

tff(c_602,plain,(
    m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_203,c_601])).

tff(c_28,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k2_pre_topc(A_18,B_19),k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_68,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_66,plain,(
    v3_tdlat_3('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_3306,plain,(
    ! [A_7254,B_7255] :
      ( k2_pre_topc(A_7254,k2_pre_topc(A_7254,B_7255)) = k2_pre_topc(A_7254,B_7255)
      | ~ m1_subset_1(B_7255,k1_zfmisc_1(u1_struct_0(A_7254)))
      | ~ l1_pre_topc(A_7254) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_3322,plain,
    ( k2_pre_topc('#skF_6',k2_pre_topc('#skF_6',k1_tarski('#skF_7'))) = k2_pre_topc('#skF_6',k1_tarski('#skF_7'))
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_602,c_3306])).

tff(c_3335,plain,(
    k2_pre_topc('#skF_6',k2_pre_topc('#skF_6',k1_tarski('#skF_7'))) = k2_pre_topc('#skF_6',k1_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3322])).

tff(c_3554,plain,(
    ! [B_7852,A_7853] :
      ( v4_pre_topc(B_7852,A_7853)
      | k2_pre_topc(A_7853,B_7852) != B_7852
      | ~ v2_pre_topc(A_7853)
      | ~ m1_subset_1(B_7852,k1_zfmisc_1(u1_struct_0(A_7853)))
      | ~ l1_pre_topc(A_7853) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_60899,plain,(
    ! [A_53906,B_53907] :
      ( v4_pre_topc(k2_pre_topc(A_53906,B_53907),A_53906)
      | k2_pre_topc(A_53906,k2_pre_topc(A_53906,B_53907)) != k2_pre_topc(A_53906,B_53907)
      | ~ v2_pre_topc(A_53906)
      | ~ m1_subset_1(B_53907,k1_zfmisc_1(u1_struct_0(A_53906)))
      | ~ l1_pre_topc(A_53906) ) ),
    inference(resolution,[status(thm)],[c_28,c_3554])).

tff(c_60953,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_6',k1_tarski('#skF_7')),'#skF_6')
    | k2_pre_topc('#skF_6',k2_pre_topc('#skF_6',k1_tarski('#skF_7'))) != k2_pre_topc('#skF_6',k1_tarski('#skF_7'))
    | ~ v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_602,c_60899])).

tff(c_60966,plain,(
    v4_pre_topc(k2_pre_topc('#skF_6',k1_tarski('#skF_7')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68,c_3335,c_60953])).

tff(c_3830,plain,(
    ! [B_8537,A_8538] :
      ( v3_pre_topc(B_8537,A_8538)
      | ~ v4_pre_topc(B_8537,A_8538)
      | ~ m1_subset_1(B_8537,k1_zfmisc_1(u1_struct_0(A_8538)))
      | ~ v3_tdlat_3(A_8538)
      | ~ l1_pre_topc(A_8538)
      | ~ v2_pre_topc(A_8538) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_3857,plain,(
    ! [A_18,B_19] :
      ( v3_pre_topc(k2_pre_topc(A_18,B_19),A_18)
      | ~ v4_pre_topc(k2_pre_topc(A_18,B_19),A_18)
      | ~ v3_tdlat_3(A_18)
      | ~ v2_pre_topc(A_18)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(resolution,[status(thm)],[c_28,c_3830])).

tff(c_61049,plain,
    ( v3_pre_topc(k2_pre_topc('#skF_6',k1_tarski('#skF_7')),'#skF_6')
    | ~ v3_tdlat_3('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | ~ m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_60966,c_3857])).

tff(c_61125,plain,(
    v3_pre_topc(k2_pre_topc('#skF_6',k1_tarski('#skF_7')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_602,c_68,c_66,c_61049])).

tff(c_202,plain,(
    k6_domain_1(u1_struct_0('#skF_6'),'#skF_8') = k1_tarski('#skF_8') ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_40,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(k6_domain_1(A_27,B_28),k1_zfmisc_1(A_27))
      | ~ m1_subset_1(B_28,A_27)
      | v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_4255,plain,(
    ! [B_9312,A_9313,C_9314] :
      ( r1_xboole_0(B_9312,k2_pre_topc(A_9313,C_9314))
      | ~ v3_pre_topc(B_9312,A_9313)
      | ~ r1_xboole_0(B_9312,C_9314)
      | ~ m1_subset_1(C_9314,k1_zfmisc_1(u1_struct_0(A_9313)))
      | ~ m1_subset_1(B_9312,k1_zfmisc_1(u1_struct_0(A_9313)))
      | ~ l1_pre_topc(A_9313)
      | ~ v2_pre_topc(A_9313) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_66137,plain,(
    ! [B_65203,A_65204,B_65205] :
      ( r1_xboole_0(B_65203,k2_pre_topc(A_65204,k6_domain_1(u1_struct_0(A_65204),B_65205)))
      | ~ v3_pre_topc(B_65203,A_65204)
      | ~ r1_xboole_0(B_65203,k6_domain_1(u1_struct_0(A_65204),B_65205))
      | ~ m1_subset_1(B_65203,k1_zfmisc_1(u1_struct_0(A_65204)))
      | ~ l1_pre_topc(A_65204)
      | ~ v2_pre_topc(A_65204)
      | ~ m1_subset_1(B_65205,u1_struct_0(A_65204))
      | v1_xboole_0(u1_struct_0(A_65204)) ) ),
    inference(resolution,[status(thm)],[c_40,c_4255])).

tff(c_66239,plain,(
    ! [B_65203] :
      ( r1_xboole_0(B_65203,k2_pre_topc('#skF_6',k1_tarski('#skF_8')))
      | ~ v3_pre_topc(B_65203,'#skF_6')
      | ~ r1_xboole_0(B_65203,k6_domain_1(u1_struct_0('#skF_6'),'#skF_8'))
      | ~ m1_subset_1(B_65203,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
      | v1_xboole_0(u1_struct_0('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_66137])).

tff(c_66267,plain,(
    ! [B_65203] :
      ( r1_xboole_0(B_65203,k2_pre_topc('#skF_6',k1_tarski('#skF_8')))
      | ~ v3_pre_topc(B_65203,'#skF_6')
      | ~ r1_xboole_0(B_65203,k1_tarski('#skF_8'))
      | ~ m1_subset_1(B_65203,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | v1_xboole_0(u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_68,c_64,c_202,c_66239])).

tff(c_72086,plain,(
    ! [B_74655] :
      ( r1_xboole_0(B_74655,k2_pre_topc('#skF_6',k1_tarski('#skF_8')))
      | ~ v3_pre_topc(B_74655,'#skF_6')
      | ~ r1_xboole_0(B_74655,k1_tarski('#skF_8'))
      | ~ m1_subset_1(B_74655,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_203,c_66267])).

tff(c_58,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_6',k6_domain_1(u1_struct_0('#skF_6'),'#skF_7')),k2_pre_topc('#skF_6',k6_domain_1(u1_struct_0('#skF_6'),'#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_205,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_6',k6_domain_1(u1_struct_0('#skF_6'),'#skF_7')),k2_pre_topc('#skF_6',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_58])).

tff(c_718,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_6',k1_tarski('#skF_7')),k2_pre_topc('#skF_6',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_205])).

tff(c_72096,plain,
    ( ~ v3_pre_topc(k2_pre_topc('#skF_6',k1_tarski('#skF_7')),'#skF_6')
    | ~ r1_xboole_0(k2_pre_topc('#skF_6',k1_tarski('#skF_7')),k1_tarski('#skF_8'))
    | ~ m1_subset_1(k2_pre_topc('#skF_6',k1_tarski('#skF_7')),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_72086,c_718])).

tff(c_72172,plain,
    ( ~ r1_xboole_0(k2_pre_topc('#skF_6',k1_tarski('#skF_7')),k1_tarski('#skF_8'))
    | ~ m1_subset_1(k2_pre_topc('#skF_6',k1_tarski('#skF_7')),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61125,c_72096])).

tff(c_72174,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_6',k1_tarski('#skF_7')),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_72172])).

tff(c_72231,plain,
    ( ~ m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_28,c_72174])).

tff(c_72254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_602,c_72231])).

tff(c_72255,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_6',k1_tarski('#skF_7')),k1_tarski('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_72172])).

tff(c_56,plain,(
    k2_pre_topc('#skF_6',k6_domain_1(u1_struct_0('#skF_6'),'#skF_7')) != k2_pre_topc('#skF_6',k6_domain_1(u1_struct_0('#skF_6'),'#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_206,plain,(
    k2_pre_topc('#skF_6',k6_domain_1(u1_struct_0('#skF_6'),'#skF_7')) != k2_pre_topc('#skF_6',k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_56])).

tff(c_219,plain,(
    k2_pre_topc('#skF_6',k1_tarski('#skF_7')) != k2_pre_topc('#skF_6',k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_206])).

tff(c_149,plain,(
    ! [A_72,B_73] :
      ( r2_hidden('#skF_2'(A_72,B_73),B_73)
      | r1_xboole_0(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [C_14,A_10] :
      ( C_14 = A_10
      | ~ r2_hidden(C_14,k1_tarski(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_157,plain,(
    ! [A_72,A_10] :
      ( '#skF_2'(A_72,k1_tarski(A_10)) = A_10
      | r1_xboole_0(A_72,k1_tarski(A_10)) ) ),
    inference(resolution,[status(thm)],[c_149,c_12])).

tff(c_72344,plain,(
    '#skF_2'(k2_pre_topc('#skF_6',k1_tarski('#skF_7')),k1_tarski('#skF_8')) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_157,c_72255])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_5494,plain,(
    ! [A_12169,C_12170,B_12171] :
      ( k2_pre_topc(A_12169,k6_domain_1(u1_struct_0(A_12169),C_12170)) = k2_pre_topc(A_12169,k6_domain_1(u1_struct_0(A_12169),B_12171))
      | ~ r2_hidden(B_12171,k2_pre_topc(A_12169,k6_domain_1(u1_struct_0(A_12169),C_12170)))
      | ~ m1_subset_1(C_12170,u1_struct_0(A_12169))
      | ~ m1_subset_1(B_12171,u1_struct_0(A_12169))
      | ~ l1_pre_topc(A_12169)
      | ~ v3_tdlat_3(A_12169)
      | ~ v2_pre_topc(A_12169)
      | v2_struct_0(A_12169) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_5519,plain,(
    ! [B_12171] :
      ( k2_pre_topc('#skF_6',k6_domain_1(u1_struct_0('#skF_6'),B_12171)) = k2_pre_topc('#skF_6',k6_domain_1(u1_struct_0('#skF_6'),'#skF_7'))
      | ~ r2_hidden(B_12171,k2_pre_topc('#skF_6',k1_tarski('#skF_7')))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_12171,u1_struct_0('#skF_6'))
      | ~ l1_pre_topc('#skF_6')
      | ~ v3_tdlat_3('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_5494])).

tff(c_5541,plain,(
    ! [B_12171] :
      ( k2_pre_topc('#skF_6',k6_domain_1(u1_struct_0('#skF_6'),B_12171)) = k2_pre_topc('#skF_6',k1_tarski('#skF_7'))
      | ~ r2_hidden(B_12171,k2_pre_topc('#skF_6',k1_tarski('#skF_7')))
      | ~ m1_subset_1(B_12171,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_62,c_212,c_5519])).

tff(c_5898,plain,(
    ! [B_12587] :
      ( k2_pre_topc('#skF_6',k6_domain_1(u1_struct_0('#skF_6'),B_12587)) = k2_pre_topc('#skF_6',k1_tarski('#skF_7'))
      | ~ r2_hidden(B_12587,k2_pre_topc('#skF_6',k1_tarski('#skF_7')))
      | ~ m1_subset_1(B_12587,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_5541])).

tff(c_5952,plain,(
    ! [B_6] :
      ( k2_pre_topc('#skF_6',k6_domain_1(u1_struct_0('#skF_6'),'#skF_2'(k2_pre_topc('#skF_6',k1_tarski('#skF_7')),B_6))) = k2_pre_topc('#skF_6',k1_tarski('#skF_7'))
      | ~ m1_subset_1('#skF_2'(k2_pre_topc('#skF_6',k1_tarski('#skF_7')),B_6),u1_struct_0('#skF_6'))
      | r1_xboole_0(k2_pre_topc('#skF_6',k1_tarski('#skF_7')),B_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_5898])).

tff(c_72781,plain,
    ( k2_pre_topc('#skF_6',k6_domain_1(u1_struct_0('#skF_6'),'#skF_8')) = k2_pre_topc('#skF_6',k1_tarski('#skF_7'))
    | ~ m1_subset_1('#skF_2'(k2_pre_topc('#skF_6',k1_tarski('#skF_7')),k1_tarski('#skF_8')),u1_struct_0('#skF_6'))
    | r1_xboole_0(k2_pre_topc('#skF_6',k1_tarski('#skF_7')),k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_72344,c_5952])).

tff(c_73205,plain,
    ( k2_pre_topc('#skF_6',k1_tarski('#skF_7')) = k2_pre_topc('#skF_6',k1_tarski('#skF_8'))
    | r1_xboole_0(k2_pre_topc('#skF_6',k1_tarski('#skF_7')),k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_72344,c_202,c_72781])).

tff(c_73207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72255,c_219,c_73205])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:07:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.24/11.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.24/11.63  
% 22.24/11.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.24/11.64  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_8 > #skF_2 > #skF_4
% 22.24/11.64  
% 22.24/11.64  %Foreground sorts:
% 22.24/11.64  
% 22.24/11.64  
% 22.24/11.64  %Background operators:
% 22.24/11.64  
% 22.24/11.64  
% 22.24/11.64  %Foreground operators:
% 22.24/11.64  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 22.24/11.64  tff('#skF_5', type, '#skF_5': $i > $i).
% 22.24/11.64  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 22.24/11.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.24/11.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 22.24/11.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 22.24/11.64  tff('#skF_1', type, '#skF_1': $i > $i).
% 22.24/11.64  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 22.24/11.64  tff('#skF_7', type, '#skF_7': $i).
% 22.24/11.64  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 22.24/11.64  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 22.24/11.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 22.24/11.64  tff('#skF_6', type, '#skF_6': $i).
% 22.24/11.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 22.24/11.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 22.24/11.64  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 22.24/11.64  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 22.24/11.64  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 22.24/11.64  tff('#skF_8', type, '#skF_8': $i).
% 22.24/11.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.24/11.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.24/11.64  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 22.24/11.64  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 22.24/11.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 22.24/11.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 22.24/11.64  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 22.24/11.64  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 22.24/11.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 22.24/11.64  
% 22.38/11.65  tff(f_185, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_xboole_0(k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)), k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) | (k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tex_2)).
% 22.38/11.65  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 22.38/11.65  tff(f_117, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 22.38/11.65  tff(f_82, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 22.38/11.65  tff(f_110, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 22.38/11.65  tff(f_70, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 22.38/11.65  tff(f_88, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 22.38/11.65  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 22.38/11.65  tff(f_130, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tdlat_3)).
% 22.38/11.65  tff(f_146, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_xboole_0(B, C) & v3_pre_topc(B, A)) => r1_xboole_0(B, k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_tsep_1)).
% 22.38/11.65  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 22.38/11.65  tff(f_56, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 22.38/11.65  tff(f_165, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) => (k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tex_2)).
% 22.38/11.65  tff(c_64, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_185])).
% 22.38/11.65  tff(c_30, plain, (![A_20]: (l1_struct_0(A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_74])).
% 22.38/11.65  tff(c_70, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_185])).
% 22.38/11.65  tff(c_60, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_185])).
% 22.38/11.65  tff(c_179, plain, (![A_83, B_84]: (k6_domain_1(A_83, B_84)=k1_tarski(B_84) | ~m1_subset_1(B_84, A_83) | v1_xboole_0(A_83))), inference(cnfTransformation, [status(thm)], [f_117])).
% 22.38/11.65  tff(c_186, plain, (k6_domain_1(u1_struct_0('#skF_6'), '#skF_8')=k1_tarski('#skF_8') | v1_xboole_0(u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_60, c_179])).
% 22.38/11.65  tff(c_188, plain, (v1_xboole_0(u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_186])).
% 22.38/11.65  tff(c_32, plain, (![A_21]: (~v1_xboole_0(u1_struct_0(A_21)) | ~l1_struct_0(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_82])).
% 22.38/11.65  tff(c_191, plain, (~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_188, c_32])).
% 22.38/11.65  tff(c_194, plain, (~l1_struct_0('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_70, c_191])).
% 22.38/11.65  tff(c_197, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_30, c_194])).
% 22.38/11.65  tff(c_201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_197])).
% 22.38/11.65  tff(c_203, plain, (~v1_xboole_0(u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_186])).
% 22.38/11.65  tff(c_62, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_185])).
% 22.38/11.65  tff(c_187, plain, (k6_domain_1(u1_struct_0('#skF_6'), '#skF_7')=k1_tarski('#skF_7') | v1_xboole_0(u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_62, c_179])).
% 22.38/11.65  tff(c_212, plain, (k6_domain_1(u1_struct_0('#skF_6'), '#skF_7')=k1_tarski('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_203, c_187])).
% 22.38/11.65  tff(c_587, plain, (![A_745, B_746]: (m1_subset_1(k6_domain_1(A_745, B_746), k1_zfmisc_1(A_745)) | ~m1_subset_1(B_746, A_745) | v1_xboole_0(A_745))), inference(cnfTransformation, [status(thm)], [f_110])).
% 22.38/11.65  tff(c_595, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | v1_xboole_0(u1_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_212, c_587])).
% 22.38/11.65  tff(c_601, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | v1_xboole_0(u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_595])).
% 22.38/11.65  tff(c_602, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_203, c_601])).
% 22.38/11.65  tff(c_28, plain, (![A_18, B_19]: (m1_subset_1(k2_pre_topc(A_18, B_19), k1_zfmisc_1(u1_struct_0(A_18))) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_70])).
% 22.38/11.65  tff(c_68, plain, (v2_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_185])).
% 22.38/11.65  tff(c_66, plain, (v3_tdlat_3('#skF_6')), inference(cnfTransformation, [status(thm)], [f_185])).
% 22.38/11.65  tff(c_3306, plain, (![A_7254, B_7255]: (k2_pre_topc(A_7254, k2_pre_topc(A_7254, B_7255))=k2_pre_topc(A_7254, B_7255) | ~m1_subset_1(B_7255, k1_zfmisc_1(u1_struct_0(A_7254))) | ~l1_pre_topc(A_7254))), inference(cnfTransformation, [status(thm)], [f_88])).
% 22.38/11.65  tff(c_3322, plain, (k2_pre_topc('#skF_6', k2_pre_topc('#skF_6', k1_tarski('#skF_7')))=k2_pre_topc('#skF_6', k1_tarski('#skF_7')) | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_602, c_3306])).
% 22.38/11.65  tff(c_3335, plain, (k2_pre_topc('#skF_6', k2_pre_topc('#skF_6', k1_tarski('#skF_7')))=k2_pre_topc('#skF_6', k1_tarski('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_3322])).
% 22.38/11.65  tff(c_3554, plain, (![B_7852, A_7853]: (v4_pre_topc(B_7852, A_7853) | k2_pre_topc(A_7853, B_7852)!=B_7852 | ~v2_pre_topc(A_7853) | ~m1_subset_1(B_7852, k1_zfmisc_1(u1_struct_0(A_7853))) | ~l1_pre_topc(A_7853))), inference(cnfTransformation, [status(thm)], [f_103])).
% 22.38/11.65  tff(c_60899, plain, (![A_53906, B_53907]: (v4_pre_topc(k2_pre_topc(A_53906, B_53907), A_53906) | k2_pre_topc(A_53906, k2_pre_topc(A_53906, B_53907))!=k2_pre_topc(A_53906, B_53907) | ~v2_pre_topc(A_53906) | ~m1_subset_1(B_53907, k1_zfmisc_1(u1_struct_0(A_53906))) | ~l1_pre_topc(A_53906))), inference(resolution, [status(thm)], [c_28, c_3554])).
% 22.38/11.65  tff(c_60953, plain, (v4_pre_topc(k2_pre_topc('#skF_6', k1_tarski('#skF_7')), '#skF_6') | k2_pre_topc('#skF_6', k2_pre_topc('#skF_6', k1_tarski('#skF_7')))!=k2_pre_topc('#skF_6', k1_tarski('#skF_7')) | ~v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_602, c_60899])).
% 22.38/11.65  tff(c_60966, plain, (v4_pre_topc(k2_pre_topc('#skF_6', k1_tarski('#skF_7')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_68, c_3335, c_60953])).
% 22.38/11.65  tff(c_3830, plain, (![B_8537, A_8538]: (v3_pre_topc(B_8537, A_8538) | ~v4_pre_topc(B_8537, A_8538) | ~m1_subset_1(B_8537, k1_zfmisc_1(u1_struct_0(A_8538))) | ~v3_tdlat_3(A_8538) | ~l1_pre_topc(A_8538) | ~v2_pre_topc(A_8538))), inference(cnfTransformation, [status(thm)], [f_130])).
% 22.38/11.65  tff(c_3857, plain, (![A_18, B_19]: (v3_pre_topc(k2_pre_topc(A_18, B_19), A_18) | ~v4_pre_topc(k2_pre_topc(A_18, B_19), A_18) | ~v3_tdlat_3(A_18) | ~v2_pre_topc(A_18) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(resolution, [status(thm)], [c_28, c_3830])).
% 22.38/11.65  tff(c_61049, plain, (v3_pre_topc(k2_pre_topc('#skF_6', k1_tarski('#skF_7')), '#skF_6') | ~v3_tdlat_3('#skF_6') | ~v2_pre_topc('#skF_6') | ~m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_60966, c_3857])).
% 22.38/11.65  tff(c_61125, plain, (v3_pre_topc(k2_pre_topc('#skF_6', k1_tarski('#skF_7')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_602, c_68, c_66, c_61049])).
% 22.38/11.65  tff(c_202, plain, (k6_domain_1(u1_struct_0('#skF_6'), '#skF_8')=k1_tarski('#skF_8')), inference(splitRight, [status(thm)], [c_186])).
% 22.38/11.65  tff(c_40, plain, (![A_27, B_28]: (m1_subset_1(k6_domain_1(A_27, B_28), k1_zfmisc_1(A_27)) | ~m1_subset_1(B_28, A_27) | v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_110])).
% 22.38/11.65  tff(c_4255, plain, (![B_9312, A_9313, C_9314]: (r1_xboole_0(B_9312, k2_pre_topc(A_9313, C_9314)) | ~v3_pre_topc(B_9312, A_9313) | ~r1_xboole_0(B_9312, C_9314) | ~m1_subset_1(C_9314, k1_zfmisc_1(u1_struct_0(A_9313))) | ~m1_subset_1(B_9312, k1_zfmisc_1(u1_struct_0(A_9313))) | ~l1_pre_topc(A_9313) | ~v2_pre_topc(A_9313))), inference(cnfTransformation, [status(thm)], [f_146])).
% 22.38/11.65  tff(c_66137, plain, (![B_65203, A_65204, B_65205]: (r1_xboole_0(B_65203, k2_pre_topc(A_65204, k6_domain_1(u1_struct_0(A_65204), B_65205))) | ~v3_pre_topc(B_65203, A_65204) | ~r1_xboole_0(B_65203, k6_domain_1(u1_struct_0(A_65204), B_65205)) | ~m1_subset_1(B_65203, k1_zfmisc_1(u1_struct_0(A_65204))) | ~l1_pre_topc(A_65204) | ~v2_pre_topc(A_65204) | ~m1_subset_1(B_65205, u1_struct_0(A_65204)) | v1_xboole_0(u1_struct_0(A_65204)))), inference(resolution, [status(thm)], [c_40, c_4255])).
% 22.38/11.65  tff(c_66239, plain, (![B_65203]: (r1_xboole_0(B_65203, k2_pre_topc('#skF_6', k1_tarski('#skF_8'))) | ~v3_pre_topc(B_65203, '#skF_6') | ~r1_xboole_0(B_65203, k6_domain_1(u1_struct_0('#skF_6'), '#skF_8')) | ~m1_subset_1(B_65203, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | v1_xboole_0(u1_struct_0('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_202, c_66137])).
% 22.38/11.65  tff(c_66267, plain, (![B_65203]: (r1_xboole_0(B_65203, k2_pre_topc('#skF_6', k1_tarski('#skF_8'))) | ~v3_pre_topc(B_65203, '#skF_6') | ~r1_xboole_0(B_65203, k1_tarski('#skF_8')) | ~m1_subset_1(B_65203, k1_zfmisc_1(u1_struct_0('#skF_6'))) | v1_xboole_0(u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_68, c_64, c_202, c_66239])).
% 22.38/11.65  tff(c_72086, plain, (![B_74655]: (r1_xboole_0(B_74655, k2_pre_topc('#skF_6', k1_tarski('#skF_8'))) | ~v3_pre_topc(B_74655, '#skF_6') | ~r1_xboole_0(B_74655, k1_tarski('#skF_8')) | ~m1_subset_1(B_74655, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_203, c_66267])).
% 22.38/11.65  tff(c_58, plain, (~r1_xboole_0(k2_pre_topc('#skF_6', k6_domain_1(u1_struct_0('#skF_6'), '#skF_7')), k2_pre_topc('#skF_6', k6_domain_1(u1_struct_0('#skF_6'), '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_185])).
% 22.38/11.65  tff(c_205, plain, (~r1_xboole_0(k2_pre_topc('#skF_6', k6_domain_1(u1_struct_0('#skF_6'), '#skF_7')), k2_pre_topc('#skF_6', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_202, c_58])).
% 22.38/11.65  tff(c_718, plain, (~r1_xboole_0(k2_pre_topc('#skF_6', k1_tarski('#skF_7')), k2_pre_topc('#skF_6', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_205])).
% 22.38/11.65  tff(c_72096, plain, (~v3_pre_topc(k2_pre_topc('#skF_6', k1_tarski('#skF_7')), '#skF_6') | ~r1_xboole_0(k2_pre_topc('#skF_6', k1_tarski('#skF_7')), k1_tarski('#skF_8')) | ~m1_subset_1(k2_pre_topc('#skF_6', k1_tarski('#skF_7')), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_72086, c_718])).
% 22.38/11.65  tff(c_72172, plain, (~r1_xboole_0(k2_pre_topc('#skF_6', k1_tarski('#skF_7')), k1_tarski('#skF_8')) | ~m1_subset_1(k2_pre_topc('#skF_6', k1_tarski('#skF_7')), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_61125, c_72096])).
% 22.38/11.65  tff(c_72174, plain, (~m1_subset_1(k2_pre_topc('#skF_6', k1_tarski('#skF_7')), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(splitLeft, [status(thm)], [c_72172])).
% 22.38/11.65  tff(c_72231, plain, (~m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_28, c_72174])).
% 22.38/11.65  tff(c_72254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_602, c_72231])).
% 22.38/11.65  tff(c_72255, plain, (~r1_xboole_0(k2_pre_topc('#skF_6', k1_tarski('#skF_7')), k1_tarski('#skF_8'))), inference(splitRight, [status(thm)], [c_72172])).
% 22.38/11.65  tff(c_56, plain, (k2_pre_topc('#skF_6', k6_domain_1(u1_struct_0('#skF_6'), '#skF_7'))!=k2_pre_topc('#skF_6', k6_domain_1(u1_struct_0('#skF_6'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_185])).
% 22.38/11.65  tff(c_206, plain, (k2_pre_topc('#skF_6', k6_domain_1(u1_struct_0('#skF_6'), '#skF_7'))!=k2_pre_topc('#skF_6', k1_tarski('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_202, c_56])).
% 22.38/11.65  tff(c_219, plain, (k2_pre_topc('#skF_6', k1_tarski('#skF_7'))!=k2_pre_topc('#skF_6', k1_tarski('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_206])).
% 22.38/11.65  tff(c_149, plain, (![A_72, B_73]: (r2_hidden('#skF_2'(A_72, B_73), B_73) | r1_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_49])).
% 22.38/11.65  tff(c_12, plain, (![C_14, A_10]: (C_14=A_10 | ~r2_hidden(C_14, k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 22.38/11.65  tff(c_157, plain, (![A_72, A_10]: ('#skF_2'(A_72, k1_tarski(A_10))=A_10 | r1_xboole_0(A_72, k1_tarski(A_10)))), inference(resolution, [status(thm)], [c_149, c_12])).
% 22.38/11.65  tff(c_72344, plain, ('#skF_2'(k2_pre_topc('#skF_6', k1_tarski('#skF_7')), k1_tarski('#skF_8'))='#skF_8'), inference(resolution, [status(thm)], [c_157, c_72255])).
% 22.38/11.65  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 22.38/11.65  tff(c_5494, plain, (![A_12169, C_12170, B_12171]: (k2_pre_topc(A_12169, k6_domain_1(u1_struct_0(A_12169), C_12170))=k2_pre_topc(A_12169, k6_domain_1(u1_struct_0(A_12169), B_12171)) | ~r2_hidden(B_12171, k2_pre_topc(A_12169, k6_domain_1(u1_struct_0(A_12169), C_12170))) | ~m1_subset_1(C_12170, u1_struct_0(A_12169)) | ~m1_subset_1(B_12171, u1_struct_0(A_12169)) | ~l1_pre_topc(A_12169) | ~v3_tdlat_3(A_12169) | ~v2_pre_topc(A_12169) | v2_struct_0(A_12169))), inference(cnfTransformation, [status(thm)], [f_165])).
% 22.38/11.65  tff(c_5519, plain, (![B_12171]: (k2_pre_topc('#skF_6', k6_domain_1(u1_struct_0('#skF_6'), B_12171))=k2_pre_topc('#skF_6', k6_domain_1(u1_struct_0('#skF_6'), '#skF_7')) | ~r2_hidden(B_12171, k2_pre_topc('#skF_6', k1_tarski('#skF_7'))) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~m1_subset_1(B_12171, u1_struct_0('#skF_6')) | ~l1_pre_topc('#skF_6') | ~v3_tdlat_3('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_212, c_5494])).
% 22.38/11.65  tff(c_5541, plain, (![B_12171]: (k2_pre_topc('#skF_6', k6_domain_1(u1_struct_0('#skF_6'), B_12171))=k2_pre_topc('#skF_6', k1_tarski('#skF_7')) | ~r2_hidden(B_12171, k2_pre_topc('#skF_6', k1_tarski('#skF_7'))) | ~m1_subset_1(B_12171, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_62, c_212, c_5519])).
% 22.38/11.65  tff(c_5898, plain, (![B_12587]: (k2_pre_topc('#skF_6', k6_domain_1(u1_struct_0('#skF_6'), B_12587))=k2_pre_topc('#skF_6', k1_tarski('#skF_7')) | ~r2_hidden(B_12587, k2_pre_topc('#skF_6', k1_tarski('#skF_7'))) | ~m1_subset_1(B_12587, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_70, c_5541])).
% 22.38/11.65  tff(c_5952, plain, (![B_6]: (k2_pre_topc('#skF_6', k6_domain_1(u1_struct_0('#skF_6'), '#skF_2'(k2_pre_topc('#skF_6', k1_tarski('#skF_7')), B_6)))=k2_pre_topc('#skF_6', k1_tarski('#skF_7')) | ~m1_subset_1('#skF_2'(k2_pre_topc('#skF_6', k1_tarski('#skF_7')), B_6), u1_struct_0('#skF_6')) | r1_xboole_0(k2_pre_topc('#skF_6', k1_tarski('#skF_7')), B_6))), inference(resolution, [status(thm)], [c_10, c_5898])).
% 22.38/11.65  tff(c_72781, plain, (k2_pre_topc('#skF_6', k6_domain_1(u1_struct_0('#skF_6'), '#skF_8'))=k2_pre_topc('#skF_6', k1_tarski('#skF_7')) | ~m1_subset_1('#skF_2'(k2_pre_topc('#skF_6', k1_tarski('#skF_7')), k1_tarski('#skF_8')), u1_struct_0('#skF_6')) | r1_xboole_0(k2_pre_topc('#skF_6', k1_tarski('#skF_7')), k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_72344, c_5952])).
% 22.38/11.65  tff(c_73205, plain, (k2_pre_topc('#skF_6', k1_tarski('#skF_7'))=k2_pre_topc('#skF_6', k1_tarski('#skF_8')) | r1_xboole_0(k2_pre_topc('#skF_6', k1_tarski('#skF_7')), k1_tarski('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_72344, c_202, c_72781])).
% 22.38/11.65  tff(c_73207, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72255, c_219, c_73205])).
% 22.38/11.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.38/11.65  
% 22.38/11.65  Inference rules
% 22.38/11.65  ----------------------
% 22.38/11.65  #Ref     : 1
% 22.38/11.65  #Sup     : 12486
% 22.38/11.65  #Fact    : 10
% 22.38/11.65  #Define  : 0
% 22.38/11.65  #Split   : 28
% 22.38/11.65  #Chain   : 0
% 22.38/11.65  #Close   : 0
% 22.38/11.65  
% 22.38/11.65  Ordering : KBO
% 22.38/11.65  
% 22.38/11.65  Simplification rules
% 22.38/11.65  ----------------------
% 22.38/11.65  #Subsume      : 1854
% 22.38/11.65  #Demod        : 1383
% 22.38/11.65  #Tautology    : 1549
% 22.38/11.65  #SimpNegUnit  : 519
% 22.38/11.65  #BackRed      : 4
% 22.38/11.65  
% 22.38/11.65  #Partial instantiations: 54145
% 22.38/11.65  #Strategies tried      : 1
% 22.38/11.65  
% 22.38/11.65  Timing (in seconds)
% 22.38/11.65  ----------------------
% 22.38/11.66  Preprocessing        : 0.35
% 22.38/11.66  Parsing              : 0.19
% 22.38/11.66  CNF conversion       : 0.03
% 22.38/11.66  Main loop            : 10.53
% 22.38/11.66  Inferencing          : 2.81
% 22.38/11.66  Reduction            : 1.93
% 22.38/11.66  Demodulation         : 1.20
% 22.38/11.66  BG Simplification    : 0.42
% 22.38/11.66  Subsumption          : 4.91
% 22.38/11.66  Abstraction          : 0.55
% 22.38/11.66  MUC search           : 0.00
% 22.38/11.66  Cooper               : 0.00
% 22.38/11.66  Total                : 10.92
% 22.38/11.66  Index Insertion      : 0.00
% 22.38/11.66  Index Deletion       : 0.00
% 22.38/11.66  Index Matching       : 0.00
% 22.38/11.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
