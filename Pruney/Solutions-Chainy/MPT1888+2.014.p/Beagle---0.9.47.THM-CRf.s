%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:22 EST 2020

% Result     : Theorem 3.99s
% Output     : CNFRefutation 4.42s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 404 expanded)
%              Number of leaves         :   37 ( 149 expanded)
%              Depth                    :   17
%              Number of atoms          :  204 (1240 expanded)
%              Number of equality atoms :   17 ( 195 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_158,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tex_2)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(f_119,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_tsep_1)).

tff(f_138,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tex_2)).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_14,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_70,plain,(
    ! [A_54,B_55] :
      ( k6_domain_1(A_54,B_55) = k1_tarski(B_55)
      | ~ m1_subset_1(B_55,A_54)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_77,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_70])).

tff(c_79,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_16,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_82,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_79,c_16])).

tff(c_85,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_82])).

tff(c_88,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_85])).

tff(c_92,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_88])).

tff(c_94,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_78,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_42,c_70])).

tff(c_101,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_78])).

tff(c_93,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_36,plain,(
    k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5')) != k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_96,plain,(
    k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')) != k2_pre_topc('#skF_3',k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_36])).

tff(c_139,plain,(
    k2_pre_topc('#skF_3',k1_tarski('#skF_5')) != k2_pre_topc('#skF_3',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_96])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r1_xboole_0(k1_tarski(A_7),B_8)
      | r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_65,plain,(
    ! [A_50,B_51,C_52] :
      ( ~ r1_xboole_0(A_50,B_51)
      | ~ r2_hidden(C_52,B_51)
      | ~ r2_hidden(C_52,A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_107,plain,(
    ! [C_57,B_58,A_59] :
      ( ~ r2_hidden(C_57,B_58)
      | ~ r2_hidden(C_57,k1_tarski(A_59))
      | r2_hidden(A_59,B_58) ) ),
    inference(resolution,[status(thm)],[c_10,c_65])).

tff(c_181,plain,(
    ! [A_71,B_72,A_73] :
      ( ~ r2_hidden('#skF_1'(A_71,B_72),k1_tarski(A_73))
      | r2_hidden(A_73,A_71)
      | r1_xboole_0(A_71,B_72) ) ),
    inference(resolution,[status(thm)],[c_6,c_107])).

tff(c_195,plain,(
    ! [A_73,A_1] :
      ( r2_hidden(A_73,A_1)
      | r1_xboole_0(A_1,k1_tarski(A_73)) ) ),
    inference(resolution,[status(thm)],[c_4,c_181])).

tff(c_114,plain,(
    ! [A_60,B_61] :
      ( m1_subset_1(k6_domain_1(A_60,B_61),k1_zfmisc_1(A_60))
      | ~ m1_subset_1(B_61,A_60)
      | v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_120,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_114])).

tff(c_126,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_120])).

tff(c_127,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_126])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k2_pre_topc(A_9,B_10),k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_48,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_46,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_294,plain,(
    ! [A_92,B_93] :
      ( v4_pre_topc(k2_pre_topc(A_92,B_93),A_92)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92)
      | ~ v2_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_302,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_127,c_294])).

tff(c_313,plain,(
    v4_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_302])).

tff(c_316,plain,(
    ! [B_95,A_96] :
      ( v3_pre_topc(B_95,A_96)
      | ~ v4_pre_topc(B_95,A_96)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ v3_tdlat_3(A_96)
      | ~ l1_pre_topc(A_96)
      | ~ v2_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_700,plain,(
    ! [A_133,B_134] :
      ( v3_pre_topc(k2_pre_topc(A_133,B_134),A_133)
      | ~ v4_pre_topc(k2_pre_topc(A_133,B_134),A_133)
      | ~ v3_tdlat_3(A_133)
      | ~ v2_pre_topc(A_133)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133) ) ),
    inference(resolution,[status(thm)],[c_12,c_316])).

tff(c_708,plain,
    ( v3_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),'#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_313,c_700])).

tff(c_716,plain,(
    v3_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_127,c_48,c_46,c_708])).

tff(c_123,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_114])).

tff(c_129,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_123])).

tff(c_130,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_129])).

tff(c_365,plain,(
    ! [B_100,A_101,C_102] :
      ( r1_xboole_0(B_100,k2_pre_topc(A_101,C_102))
      | ~ v3_pre_topc(B_100,A_101)
      | ~ r1_xboole_0(B_100,C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101)
      | ~ v2_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_371,plain,(
    ! [B_100] :
      ( r1_xboole_0(B_100,k2_pre_topc('#skF_3',k1_tarski('#skF_5')))
      | ~ v3_pre_topc(B_100,'#skF_3')
      | ~ r1_xboole_0(B_100,k1_tarski('#skF_5'))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_130,c_365])).

tff(c_417,plain,(
    ! [B_107] :
      ( r1_xboole_0(B_107,k2_pre_topc('#skF_3',k1_tarski('#skF_5')))
      | ~ v3_pre_topc(B_107,'#skF_3')
      | ~ r1_xboole_0(B_107,k1_tarski('#skF_5'))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_371])).

tff(c_38,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')),k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_95,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')),k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_38])).

tff(c_140,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_95])).

tff(c_423,plain,
    ( ~ v3_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),'#skF_3')
    | ~ r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_tarski('#skF_5'))
    | ~ m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_417,c_140])).

tff(c_1283,plain,
    ( ~ r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_tarski('#skF_5'))
    | ~ m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_716,c_423])).

tff(c_1284,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1283])).

tff(c_1287,plain,
    ( ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_1284])).

tff(c_1291,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_127,c_1287])).

tff(c_1292,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_tarski('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1283])).

tff(c_1300,plain,(
    r2_hidden('#skF_5',k2_pre_topc('#skF_3',k1_tarski('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_195,c_1292])).

tff(c_573,plain,(
    ! [A_121,C_122,B_123] :
      ( k2_pre_topc(A_121,k6_domain_1(u1_struct_0(A_121),C_122)) = k2_pre_topc(A_121,k6_domain_1(u1_struct_0(A_121),B_123))
      | ~ r2_hidden(B_123,k2_pre_topc(A_121,k6_domain_1(u1_struct_0(A_121),C_122)))
      | ~ m1_subset_1(C_122,u1_struct_0(A_121))
      | ~ m1_subset_1(B_123,u1_struct_0(A_121))
      | ~ l1_pre_topc(A_121)
      | ~ v3_tdlat_3(A_121)
      | ~ v2_pre_topc(A_121)
      | v2_struct_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_576,plain,(
    ! [B_123] :
      ( k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),B_123)) = k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))
      | ~ r2_hidden(B_123,k2_pre_topc('#skF_3',k1_tarski('#skF_4')))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_123,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_573])).

tff(c_589,plain,(
    ! [B_123] :
      ( k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),B_123)) = k2_pre_topc('#skF_3',k1_tarski('#skF_4'))
      | ~ r2_hidden(B_123,k2_pre_topc('#skF_3',k1_tarski('#skF_4')))
      | ~ m1_subset_1(B_123,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_101,c_576])).

tff(c_590,plain,(
    ! [B_123] :
      ( k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),B_123)) = k2_pre_topc('#skF_3',k1_tarski('#skF_4'))
      | ~ r2_hidden(B_123,k2_pre_topc('#skF_3',k1_tarski('#skF_4')))
      | ~ m1_subset_1(B_123,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_589])).

tff(c_1357,plain,
    ( k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5')) = k2_pre_topc('#skF_3',k1_tarski('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1300,c_590])).

tff(c_1367,plain,(
    k2_pre_topc('#skF_3',k1_tarski('#skF_5')) = k2_pre_topc('#skF_3',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_93,c_1357])).

tff(c_1369,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_1367])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n016.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 15:49:19 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.99/1.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.99/1.76  
% 3.99/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.99/1.77  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 3.99/1.77  
% 3.99/1.77  %Foreground sorts:
% 3.99/1.77  
% 3.99/1.77  
% 3.99/1.77  %Background operators:
% 3.99/1.77  
% 3.99/1.77  
% 3.99/1.77  %Foreground operators:
% 3.99/1.77  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.99/1.77  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.99/1.77  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.99/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.99/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.99/1.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.99/1.77  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.99/1.77  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.99/1.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.99/1.77  tff('#skF_5', type, '#skF_5': $i).
% 3.99/1.77  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.99/1.77  tff('#skF_3', type, '#skF_3': $i).
% 3.99/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.99/1.77  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.99/1.77  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.99/1.77  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.99/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.99/1.77  tff('#skF_4', type, '#skF_4': $i).
% 3.99/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.99/1.77  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.99/1.77  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.99/1.77  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.99/1.77  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.99/1.77  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.99/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.99/1.77  
% 4.42/1.79  tff(f_158, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_xboole_0(k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)), k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) | (k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tex_2)).
% 4.42/1.79  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.42/1.79  tff(f_82, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.42/1.79  tff(f_68, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.42/1.79  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.42/1.79  tff(f_50, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 4.42/1.79  tff(f_75, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 4.42/1.79  tff(f_56, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 4.42/1.79  tff(f_90, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 4.42/1.79  tff(f_103, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tdlat_3)).
% 4.42/1.79  tff(f_119, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_xboole_0(B, C) & v3_pre_topc(B, A)) => r1_xboole_0(B, k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_tsep_1)).
% 4.42/1.79  tff(f_138, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) => (k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tex_2)).
% 4.42/1.79  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.42/1.79  tff(c_14, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.42/1.79  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.42/1.79  tff(c_40, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.42/1.79  tff(c_70, plain, (![A_54, B_55]: (k6_domain_1(A_54, B_55)=k1_tarski(B_55) | ~m1_subset_1(B_55, A_54) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.42/1.79  tff(c_77, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_40, c_70])).
% 4.42/1.79  tff(c_79, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_77])).
% 4.42/1.79  tff(c_16, plain, (![A_12]: (~v1_xboole_0(u1_struct_0(A_12)) | ~l1_struct_0(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.42/1.79  tff(c_82, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_79, c_16])).
% 4.42/1.79  tff(c_85, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_50, c_82])).
% 4.42/1.79  tff(c_88, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_85])).
% 4.42/1.79  tff(c_92, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_88])).
% 4.42/1.79  tff(c_94, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_77])).
% 4.42/1.79  tff(c_42, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.42/1.79  tff(c_78, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_70])).
% 4.42/1.79  tff(c_101, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_94, c_78])).
% 4.42/1.79  tff(c_93, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_77])).
% 4.42/1.79  tff(c_36, plain, (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5'))!=k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.42/1.79  tff(c_96, plain, (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'))!=k2_pre_topc('#skF_3', k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_36])).
% 4.42/1.79  tff(c_139, plain, (k2_pre_topc('#skF_3', k1_tarski('#skF_5'))!=k2_pre_topc('#skF_3', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_96])).
% 4.42/1.79  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.42/1.79  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.42/1.79  tff(c_10, plain, (![A_7, B_8]: (r1_xboole_0(k1_tarski(A_7), B_8) | r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.42/1.79  tff(c_65, plain, (![A_50, B_51, C_52]: (~r1_xboole_0(A_50, B_51) | ~r2_hidden(C_52, B_51) | ~r2_hidden(C_52, A_50))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.42/1.79  tff(c_107, plain, (![C_57, B_58, A_59]: (~r2_hidden(C_57, B_58) | ~r2_hidden(C_57, k1_tarski(A_59)) | r2_hidden(A_59, B_58))), inference(resolution, [status(thm)], [c_10, c_65])).
% 4.42/1.79  tff(c_181, plain, (![A_71, B_72, A_73]: (~r2_hidden('#skF_1'(A_71, B_72), k1_tarski(A_73)) | r2_hidden(A_73, A_71) | r1_xboole_0(A_71, B_72))), inference(resolution, [status(thm)], [c_6, c_107])).
% 4.42/1.79  tff(c_195, plain, (![A_73, A_1]: (r2_hidden(A_73, A_1) | r1_xboole_0(A_1, k1_tarski(A_73)))), inference(resolution, [status(thm)], [c_4, c_181])).
% 4.42/1.79  tff(c_114, plain, (![A_60, B_61]: (m1_subset_1(k6_domain_1(A_60, B_61), k1_zfmisc_1(A_60)) | ~m1_subset_1(B_61, A_60) | v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.42/1.79  tff(c_120, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_114])).
% 4.42/1.79  tff(c_126, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_120])).
% 4.42/1.79  tff(c_127, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_94, c_126])).
% 4.42/1.79  tff(c_12, plain, (![A_9, B_10]: (m1_subset_1(k2_pre_topc(A_9, B_10), k1_zfmisc_1(u1_struct_0(A_9))) | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.42/1.79  tff(c_48, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.42/1.79  tff(c_46, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.42/1.79  tff(c_294, plain, (![A_92, B_93]: (v4_pre_topc(k2_pre_topc(A_92, B_93), A_92) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92) | ~v2_pre_topc(A_92))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.42/1.79  tff(c_302, plain, (v4_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_127, c_294])).
% 4.42/1.79  tff(c_313, plain, (v4_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_302])).
% 4.42/1.79  tff(c_316, plain, (![B_95, A_96]: (v3_pre_topc(B_95, A_96) | ~v4_pre_topc(B_95, A_96) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_96))) | ~v3_tdlat_3(A_96) | ~l1_pre_topc(A_96) | ~v2_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.42/1.79  tff(c_700, plain, (![A_133, B_134]: (v3_pre_topc(k2_pre_topc(A_133, B_134), A_133) | ~v4_pre_topc(k2_pre_topc(A_133, B_134), A_133) | ~v3_tdlat_3(A_133) | ~v2_pre_topc(A_133) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133))), inference(resolution, [status(thm)], [c_12, c_316])).
% 4.42/1.79  tff(c_708, plain, (v3_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), '#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_313, c_700])).
% 4.42/1.79  tff(c_716, plain, (v3_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_127, c_48, c_46, c_708])).
% 4.42/1.79  tff(c_123, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_93, c_114])).
% 4.42/1.79  tff(c_129, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_123])).
% 4.42/1.79  tff(c_130, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_94, c_129])).
% 4.42/1.79  tff(c_365, plain, (![B_100, A_101, C_102]: (r1_xboole_0(B_100, k2_pre_topc(A_101, C_102)) | ~v3_pre_topc(B_100, A_101) | ~r1_xboole_0(B_100, C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(u1_struct_0(A_101))) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101) | ~v2_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.42/1.79  tff(c_371, plain, (![B_100]: (r1_xboole_0(B_100, k2_pre_topc('#skF_3', k1_tarski('#skF_5'))) | ~v3_pre_topc(B_100, '#skF_3') | ~r1_xboole_0(B_100, k1_tarski('#skF_5')) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_130, c_365])).
% 4.42/1.79  tff(c_417, plain, (![B_107]: (r1_xboole_0(B_107, k2_pre_topc('#skF_3', k1_tarski('#skF_5'))) | ~v3_pre_topc(B_107, '#skF_3') | ~r1_xboole_0(B_107, k1_tarski('#skF_5')) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_371])).
% 4.42/1.79  tff(c_38, plain, (~r1_xboole_0(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')), k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.42/1.79  tff(c_95, plain, (~r1_xboole_0(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')), k2_pre_topc('#skF_3', k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_38])).
% 4.42/1.79  tff(c_140, plain, (~r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k2_pre_topc('#skF_3', k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_95])).
% 4.42/1.79  tff(c_423, plain, (~v3_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), '#skF_3') | ~r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_tarski('#skF_5')) | ~m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_417, c_140])).
% 4.42/1.79  tff(c_1283, plain, (~r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_tarski('#skF_5')) | ~m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_716, c_423])).
% 4.42/1.79  tff(c_1284, plain, (~m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_1283])).
% 4.42/1.79  tff(c_1287, plain, (~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_12, c_1284])).
% 4.42/1.79  tff(c_1291, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_127, c_1287])).
% 4.42/1.79  tff(c_1292, plain, (~r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_tarski('#skF_5'))), inference(splitRight, [status(thm)], [c_1283])).
% 4.42/1.79  tff(c_1300, plain, (r2_hidden('#skF_5', k2_pre_topc('#skF_3', k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_195, c_1292])).
% 4.42/1.79  tff(c_573, plain, (![A_121, C_122, B_123]: (k2_pre_topc(A_121, k6_domain_1(u1_struct_0(A_121), C_122))=k2_pre_topc(A_121, k6_domain_1(u1_struct_0(A_121), B_123)) | ~r2_hidden(B_123, k2_pre_topc(A_121, k6_domain_1(u1_struct_0(A_121), C_122))) | ~m1_subset_1(C_122, u1_struct_0(A_121)) | ~m1_subset_1(B_123, u1_struct_0(A_121)) | ~l1_pre_topc(A_121) | ~v3_tdlat_3(A_121) | ~v2_pre_topc(A_121) | v2_struct_0(A_121))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.42/1.79  tff(c_576, plain, (![B_123]: (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), B_123))=k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')) | ~r2_hidden(B_123, k2_pre_topc('#skF_3', k1_tarski('#skF_4'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1(B_123, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_573])).
% 4.42/1.79  tff(c_589, plain, (![B_123]: (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), B_123))=k2_pre_topc('#skF_3', k1_tarski('#skF_4')) | ~r2_hidden(B_123, k2_pre_topc('#skF_3', k1_tarski('#skF_4'))) | ~m1_subset_1(B_123, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_101, c_576])).
% 4.42/1.79  tff(c_590, plain, (![B_123]: (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), B_123))=k2_pre_topc('#skF_3', k1_tarski('#skF_4')) | ~r2_hidden(B_123, k2_pre_topc('#skF_3', k1_tarski('#skF_4'))) | ~m1_subset_1(B_123, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_50, c_589])).
% 4.42/1.79  tff(c_1357, plain, (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5'))=k2_pre_topc('#skF_3', k1_tarski('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1300, c_590])).
% 4.42/1.79  tff(c_1367, plain, (k2_pre_topc('#skF_3', k1_tarski('#skF_5'))=k2_pre_topc('#skF_3', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_93, c_1357])).
% 4.42/1.79  tff(c_1369, plain, $false, inference(negUnitSimplification, [status(thm)], [c_139, c_1367])).
% 4.42/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.42/1.79  
% 4.42/1.79  Inference rules
% 4.42/1.79  ----------------------
% 4.42/1.79  #Ref     : 0
% 4.42/1.79  #Sup     : 321
% 4.42/1.79  #Fact    : 0
% 4.42/1.79  #Define  : 0
% 4.42/1.79  #Split   : 5
% 4.42/1.79  #Chain   : 0
% 4.42/1.79  #Close   : 0
% 4.42/1.79  
% 4.42/1.79  Ordering : KBO
% 4.42/1.79  
% 4.42/1.79  Simplification rules
% 4.42/1.79  ----------------------
% 4.42/1.79  #Subsume      : 63
% 4.42/1.79  #Demod        : 79
% 4.42/1.79  #Tautology    : 33
% 4.42/1.79  #SimpNegUnit  : 13
% 4.42/1.79  #BackRed      : 2
% 4.42/1.79  
% 4.42/1.79  #Partial instantiations: 0
% 4.42/1.79  #Strategies tried      : 1
% 4.42/1.79  
% 4.42/1.79  Timing (in seconds)
% 4.42/1.79  ----------------------
% 4.42/1.80  Preprocessing        : 0.37
% 4.42/1.80  Parsing              : 0.20
% 4.42/1.80  CNF conversion       : 0.03
% 4.42/1.80  Main loop            : 0.61
% 4.42/1.80  Inferencing          : 0.20
% 4.42/1.80  Reduction            : 0.15
% 4.42/1.80  Demodulation         : 0.10
% 4.42/1.80  BG Simplification    : 0.03
% 4.42/1.80  Subsumption          : 0.18
% 4.42/1.80  Abstraction          : 0.03
% 4.42/1.80  MUC search           : 0.00
% 4.42/1.80  Cooper               : 0.00
% 4.42/1.80  Total                : 1.03
% 4.42/1.80  Index Insertion      : 0.00
% 4.42/1.80  Index Deletion       : 0.00
% 4.42/1.80  Index Matching       : 0.00
% 4.42/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
