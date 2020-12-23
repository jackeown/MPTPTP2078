%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:22 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 326 expanded)
%              Number of leaves         :   38 ( 122 expanded)
%              Depth                    :   16
%              Number of atoms          :  213 ( 998 expanded)
%              Number of equality atoms :   17 ( 143 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

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

tff(f_67,axiom,(
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

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

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

tff(f_63,axiom,(
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

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_20,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_101,plain,(
    ! [A_66,B_67] :
      ( k6_domain_1(A_66,B_67) = k1_tarski(B_67)
      | ~ m1_subset_1(B_67,A_66)
      | v1_xboole_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_115,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_101])).

tff(c_118,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_22,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(u1_struct_0(A_18))
      | ~ l1_struct_0(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_121,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_118,c_22])).

tff(c_124,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_121])).

tff(c_128,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_124])).

tff(c_132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_128])).

tff(c_134,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_116,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_101])).

tff(c_141,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_116])).

tff(c_133,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_40,plain,(
    k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_136,plain,(
    k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_2',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_40])).

tff(c_156,plain,(
    k2_pre_topc('#skF_2',k1_tarski('#skF_3')) != k2_pre_topc('#skF_2',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_136])).

tff(c_78,plain,(
    ! [A_52,B_53] :
      ( r1_xboole_0(k1_tarski(A_52),B_53)
      | r2_hidden(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_81,plain,(
    ! [B_53,A_52] :
      ( r1_xboole_0(B_53,k1_tarski(A_52))
      | r2_hidden(A_52,B_53) ) ),
    inference(resolution,[status(thm)],[c_78,c_2])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r2_hidden(A_10,B_11)
      | v1_xboole_0(B_11)
      | ~ m1_subset_1(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k1_tarski(A_8),k1_zfmisc_1(B_9))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k2_pre_topc(A_15,B_16),k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_50,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_166,plain,(
    ! [A_72,B_73] :
      ( v4_pre_topc(k2_pre_topc(A_72,B_73),A_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_176,plain,(
    ! [A_72,A_8] :
      ( v4_pre_topc(k2_pre_topc(A_72,k1_tarski(A_8)),A_72)
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72)
      | ~ r2_hidden(A_8,u1_struct_0(A_72)) ) ),
    inference(resolution,[status(thm)],[c_12,c_166])).

tff(c_224,plain,(
    ! [B_91,A_92] :
      ( v3_pre_topc(B_91,A_92)
      | ~ v4_pre_topc(B_91,A_92)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ v3_tdlat_3(A_92)
      | ~ l1_pre_topc(A_92)
      | ~ v2_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_286,plain,(
    ! [A_107,B_108] :
      ( v3_pre_topc(k2_pre_topc(A_107,B_108),A_107)
      | ~ v4_pre_topc(k2_pre_topc(A_107,B_108),A_107)
      | ~ v3_tdlat_3(A_107)
      | ~ v2_pre_topc(A_107)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(resolution,[status(thm)],[c_18,c_224])).

tff(c_346,plain,(
    ! [A_119,A_120] :
      ( v3_pre_topc(k2_pre_topc(A_119,k1_tarski(A_120)),A_119)
      | ~ v3_tdlat_3(A_119)
      | ~ m1_subset_1(k1_tarski(A_120),k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119)
      | ~ r2_hidden(A_120,u1_struct_0(A_119)) ) ),
    inference(resolution,[status(thm)],[c_176,c_286])).

tff(c_350,plain,(
    ! [A_119,A_8] :
      ( v3_pre_topc(k2_pre_topc(A_119,k1_tarski(A_8)),A_119)
      | ~ v3_tdlat_3(A_119)
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119)
      | ~ r2_hidden(A_8,u1_struct_0(A_119)) ) ),
    inference(resolution,[status(thm)],[c_12,c_346])).

tff(c_254,plain,(
    ! [B_97,A_98,C_99] :
      ( r1_xboole_0(B_97,k2_pre_topc(A_98,C_99))
      | ~ v3_pre_topc(B_97,A_98)
      | ~ r1_xboole_0(B_97,C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98)
      | ~ v2_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_371,plain,(
    ! [B_136,A_137,A_138] :
      ( r1_xboole_0(B_136,k2_pre_topc(A_137,k1_tarski(A_138)))
      | ~ v3_pre_topc(B_136,A_137)
      | ~ r1_xboole_0(B_136,k1_tarski(A_138))
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137)
      | ~ r2_hidden(A_138,u1_struct_0(A_137)) ) ),
    inference(resolution,[status(thm)],[c_12,c_254])).

tff(c_42,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')),k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_135,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_42])).

tff(c_157,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_135])).

tff(c_374,plain,
    ( ~ v3_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),'#skF_2')
    | ~ r1_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_tarski('#skF_4'))
    | ~ m1_subset_1(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_371,c_157])).

tff(c_379,plain,
    ( ~ v3_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),'#skF_2')
    | ~ r1_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_tarski('#skF_4'))
    | ~ m1_subset_1(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_374])).

tff(c_381,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_379])).

tff(c_384,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_14,c_381])).

tff(c_387,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_384])).

tff(c_389,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_387])).

tff(c_390,plain,
    ( ~ m1_subset_1(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ r1_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_tarski('#skF_4'))
    | ~ v3_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_379])).

tff(c_400,plain,(
    ~ v3_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_390])).

tff(c_403,plain,
    ( ~ v3_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ r2_hidden('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_350,c_400])).

tff(c_406,plain,(
    ~ r2_hidden('#skF_3',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_50,c_403])).

tff(c_409,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_14,c_406])).

tff(c_412,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_409])).

tff(c_414,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_412])).

tff(c_415,plain,
    ( ~ r1_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_tarski('#skF_4'))
    | ~ m1_subset_1(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_390])).

tff(c_417,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_415])).

tff(c_420,plain,
    ( ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_417])).

tff(c_423,plain,(
    ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_420])).

tff(c_427,plain,(
    ~ r2_hidden('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_12,c_423])).

tff(c_430,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_14,c_427])).

tff(c_433,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_430])).

tff(c_435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_433])).

tff(c_436,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_415])).

tff(c_454,plain,(
    r2_hidden('#skF_4',k2_pre_topc('#skF_2',k1_tarski('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_81,c_436])).

tff(c_302,plain,(
    ! [A_110,C_111,B_112] :
      ( k2_pre_topc(A_110,k6_domain_1(u1_struct_0(A_110),C_111)) = k2_pre_topc(A_110,k6_domain_1(u1_struct_0(A_110),B_112))
      | ~ r2_hidden(B_112,k2_pre_topc(A_110,k6_domain_1(u1_struct_0(A_110),C_111)))
      | ~ m1_subset_1(C_111,u1_struct_0(A_110))
      | ~ m1_subset_1(B_112,u1_struct_0(A_110))
      | ~ l1_pre_topc(A_110)
      | ~ v3_tdlat_3(A_110)
      | ~ v2_pre_topc(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_308,plain,(
    ! [B_112] :
      ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),B_112)) = k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'))
      | ~ r2_hidden(B_112,k2_pre_topc('#skF_2',k1_tarski('#skF_3')))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_112,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_302])).

tff(c_317,plain,(
    ! [B_112] :
      ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),B_112)) = k2_pre_topc('#skF_2',k1_tarski('#skF_3'))
      | ~ r2_hidden(B_112,k2_pre_topc('#skF_2',k1_tarski('#skF_3')))
      | ~ m1_subset_1(B_112,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_133,c_308])).

tff(c_318,plain,(
    ! [B_112] :
      ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),B_112)) = k2_pre_topc('#skF_2',k1_tarski('#skF_3'))
      | ~ r2_hidden(B_112,k2_pre_topc('#skF_2',k1_tarski('#skF_3')))
      | ~ m1_subset_1(B_112,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_317])).

tff(c_457,plain,
    ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) = k2_pre_topc('#skF_2',k1_tarski('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_454,c_318])).

tff(c_465,plain,(
    k2_pre_topc('#skF_2',k1_tarski('#skF_3')) = k2_pre_topc('#skF_2',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_141,c_457])).

tff(c_467,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_465])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:45:27 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.44  
% 3.14/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.45  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.14/1.45  
% 3.14/1.45  %Foreground sorts:
% 3.14/1.45  
% 3.14/1.45  
% 3.14/1.45  %Background operators:
% 3.14/1.45  
% 3.14/1.45  
% 3.14/1.45  %Foreground operators:
% 3.14/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.14/1.45  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.14/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.14/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.14/1.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.14/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.14/1.45  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.14/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.14/1.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.14/1.45  tff('#skF_2', type, '#skF_2': $i).
% 3.14/1.45  tff('#skF_3', type, '#skF_3': $i).
% 3.14/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.14/1.45  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.14/1.45  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.14/1.45  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.14/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.45  tff('#skF_4', type, '#skF_4': $i).
% 3.14/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.14/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.14/1.45  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.14/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.14/1.45  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.14/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.14/1.45  
% 3.14/1.47  tff(f_158, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_xboole_0(k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)), k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) | (k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tex_2)).
% 3.14/1.47  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.14/1.47  tff(f_82, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.14/1.47  tff(f_75, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.14/1.47  tff(f_36, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.14/1.47  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.14/1.47  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.14/1.47  tff(f_44, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 3.14/1.47  tff(f_63, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 3.14/1.47  tff(f_90, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 3.14/1.47  tff(f_103, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tdlat_3)).
% 3.14/1.47  tff(f_119, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_xboole_0(B, C) & v3_pre_topc(B, A)) => r1_xboole_0(B, k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_tsep_1)).
% 3.14/1.47  tff(f_138, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) => (k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tex_2)).
% 3.14/1.47  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.14/1.47  tff(c_20, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.14/1.47  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.14/1.47  tff(c_46, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.14/1.47  tff(c_101, plain, (![A_66, B_67]: (k6_domain_1(A_66, B_67)=k1_tarski(B_67) | ~m1_subset_1(B_67, A_66) | v1_xboole_0(A_66))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.14/1.47  tff(c_115, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_46, c_101])).
% 3.14/1.47  tff(c_118, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_115])).
% 3.14/1.47  tff(c_22, plain, (![A_18]: (~v1_xboole_0(u1_struct_0(A_18)) | ~l1_struct_0(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.14/1.47  tff(c_121, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_118, c_22])).
% 3.14/1.47  tff(c_124, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_121])).
% 3.14/1.47  tff(c_128, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_124])).
% 3.14/1.47  tff(c_132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_128])).
% 3.14/1.47  tff(c_134, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_115])).
% 3.14/1.47  tff(c_44, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.14/1.47  tff(c_116, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_101])).
% 3.14/1.47  tff(c_141, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_134, c_116])).
% 3.14/1.47  tff(c_133, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_115])).
% 3.14/1.47  tff(c_40, plain, (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.14/1.47  tff(c_136, plain, (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_40])).
% 3.14/1.47  tff(c_156, plain, (k2_pre_topc('#skF_2', k1_tarski('#skF_3'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_136])).
% 3.14/1.47  tff(c_78, plain, (![A_52, B_53]: (r1_xboole_0(k1_tarski(A_52), B_53) | r2_hidden(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.14/1.47  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.14/1.47  tff(c_81, plain, (![B_53, A_52]: (r1_xboole_0(B_53, k1_tarski(A_52)) | r2_hidden(A_52, B_53))), inference(resolution, [status(thm)], [c_78, c_2])).
% 3.14/1.47  tff(c_14, plain, (![A_10, B_11]: (r2_hidden(A_10, B_11) | v1_xboole_0(B_11) | ~m1_subset_1(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.14/1.47  tff(c_12, plain, (![A_8, B_9]: (m1_subset_1(k1_tarski(A_8), k1_zfmisc_1(B_9)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.14/1.47  tff(c_18, plain, (![A_15, B_16]: (m1_subset_1(k2_pre_topc(A_15, B_16), k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.14/1.47  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.14/1.47  tff(c_50, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.14/1.47  tff(c_166, plain, (![A_72, B_73]: (v4_pre_topc(k2_pre_topc(A_72, B_73), A_72) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72) | ~v2_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.14/1.47  tff(c_176, plain, (![A_72, A_8]: (v4_pre_topc(k2_pre_topc(A_72, k1_tarski(A_8)), A_72) | ~l1_pre_topc(A_72) | ~v2_pre_topc(A_72) | ~r2_hidden(A_8, u1_struct_0(A_72)))), inference(resolution, [status(thm)], [c_12, c_166])).
% 3.14/1.47  tff(c_224, plain, (![B_91, A_92]: (v3_pre_topc(B_91, A_92) | ~v4_pre_topc(B_91, A_92) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_92))) | ~v3_tdlat_3(A_92) | ~l1_pre_topc(A_92) | ~v2_pre_topc(A_92))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.14/1.47  tff(c_286, plain, (![A_107, B_108]: (v3_pre_topc(k2_pre_topc(A_107, B_108), A_107) | ~v4_pre_topc(k2_pre_topc(A_107, B_108), A_107) | ~v3_tdlat_3(A_107) | ~v2_pre_topc(A_107) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(resolution, [status(thm)], [c_18, c_224])).
% 3.14/1.47  tff(c_346, plain, (![A_119, A_120]: (v3_pre_topc(k2_pre_topc(A_119, k1_tarski(A_120)), A_119) | ~v3_tdlat_3(A_119) | ~m1_subset_1(k1_tarski(A_120), k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119) | ~v2_pre_topc(A_119) | ~r2_hidden(A_120, u1_struct_0(A_119)))), inference(resolution, [status(thm)], [c_176, c_286])).
% 3.14/1.47  tff(c_350, plain, (![A_119, A_8]: (v3_pre_topc(k2_pre_topc(A_119, k1_tarski(A_8)), A_119) | ~v3_tdlat_3(A_119) | ~l1_pre_topc(A_119) | ~v2_pre_topc(A_119) | ~r2_hidden(A_8, u1_struct_0(A_119)))), inference(resolution, [status(thm)], [c_12, c_346])).
% 3.14/1.47  tff(c_254, plain, (![B_97, A_98, C_99]: (r1_xboole_0(B_97, k2_pre_topc(A_98, C_99)) | ~v3_pre_topc(B_97, A_98) | ~r1_xboole_0(B_97, C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(u1_struct_0(A_98))) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98) | ~v2_pre_topc(A_98))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.14/1.47  tff(c_371, plain, (![B_136, A_137, A_138]: (r1_xboole_0(B_136, k2_pre_topc(A_137, k1_tarski(A_138))) | ~v3_pre_topc(B_136, A_137) | ~r1_xboole_0(B_136, k1_tarski(A_138)) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_137))) | ~l1_pre_topc(A_137) | ~v2_pre_topc(A_137) | ~r2_hidden(A_138, u1_struct_0(A_137)))), inference(resolution, [status(thm)], [c_12, c_254])).
% 3.14/1.47  tff(c_42, plain, (~r1_xboole_0(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')), k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.14/1.47  tff(c_135, plain, (~r1_xboole_0(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_42])).
% 3.14/1.47  tff(c_157, plain, (~r1_xboole_0(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k2_pre_topc('#skF_2', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_135])).
% 3.14/1.47  tff(c_374, plain, (~v3_pre_topc(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), '#skF_2') | ~r1_xboole_0(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_tarski('#skF_4')) | ~m1_subset_1(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r2_hidden('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_371, c_157])).
% 3.14/1.47  tff(c_379, plain, (~v3_pre_topc(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), '#skF_2') | ~r1_xboole_0(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_tarski('#skF_4')) | ~m1_subset_1(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden('#skF_4', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_374])).
% 3.14/1.47  tff(c_381, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_379])).
% 3.14/1.47  tff(c_384, plain, (v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_14, c_381])).
% 3.14/1.47  tff(c_387, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_384])).
% 3.14/1.47  tff(c_389, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134, c_387])).
% 3.14/1.47  tff(c_390, plain, (~m1_subset_1(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_xboole_0(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_tarski('#skF_4')) | ~v3_pre_topc(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), '#skF_2')), inference(splitRight, [status(thm)], [c_379])).
% 3.14/1.47  tff(c_400, plain, (~v3_pre_topc(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), '#skF_2')), inference(splitLeft, [status(thm)], [c_390])).
% 3.14/1.47  tff(c_403, plain, (~v3_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r2_hidden('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_350, c_400])).
% 3.14/1.47  tff(c_406, plain, (~r2_hidden('#skF_3', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_50, c_403])).
% 3.14/1.47  tff(c_409, plain, (v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_14, c_406])).
% 3.14/1.47  tff(c_412, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_409])).
% 3.14/1.47  tff(c_414, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134, c_412])).
% 3.14/1.47  tff(c_415, plain, (~r1_xboole_0(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_tarski('#skF_4')) | ~m1_subset_1(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_390])).
% 3.14/1.47  tff(c_417, plain, (~m1_subset_1(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_415])).
% 3.14/1.47  tff(c_420, plain, (~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_18, c_417])).
% 3.14/1.47  tff(c_423, plain, (~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_420])).
% 3.14/1.47  tff(c_427, plain, (~r2_hidden('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_12, c_423])).
% 3.14/1.47  tff(c_430, plain, (v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_14, c_427])).
% 3.14/1.47  tff(c_433, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_430])).
% 3.14/1.47  tff(c_435, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134, c_433])).
% 3.14/1.47  tff(c_436, plain, (~r1_xboole_0(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_415])).
% 3.14/1.47  tff(c_454, plain, (r2_hidden('#skF_4', k2_pre_topc('#skF_2', k1_tarski('#skF_3')))), inference(resolution, [status(thm)], [c_81, c_436])).
% 3.14/1.47  tff(c_302, plain, (![A_110, C_111, B_112]: (k2_pre_topc(A_110, k6_domain_1(u1_struct_0(A_110), C_111))=k2_pre_topc(A_110, k6_domain_1(u1_struct_0(A_110), B_112)) | ~r2_hidden(B_112, k2_pre_topc(A_110, k6_domain_1(u1_struct_0(A_110), C_111))) | ~m1_subset_1(C_111, u1_struct_0(A_110)) | ~m1_subset_1(B_112, u1_struct_0(A_110)) | ~l1_pre_topc(A_110) | ~v3_tdlat_3(A_110) | ~v2_pre_topc(A_110) | v2_struct_0(A_110))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.14/1.47  tff(c_308, plain, (![B_112]: (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), B_112))=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')) | ~r2_hidden(B_112, k2_pre_topc('#skF_2', k1_tarski('#skF_3'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_112, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_133, c_302])).
% 3.14/1.47  tff(c_317, plain, (![B_112]: (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), B_112))=k2_pre_topc('#skF_2', k1_tarski('#skF_3')) | ~r2_hidden(B_112, k2_pre_topc('#skF_2', k1_tarski('#skF_3'))) | ~m1_subset_1(B_112, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_133, c_308])).
% 3.14/1.47  tff(c_318, plain, (![B_112]: (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), B_112))=k2_pre_topc('#skF_2', k1_tarski('#skF_3')) | ~r2_hidden(B_112, k2_pre_topc('#skF_2', k1_tarski('#skF_3'))) | ~m1_subset_1(B_112, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_54, c_317])).
% 3.14/1.47  tff(c_457, plain, (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))=k2_pre_topc('#skF_2', k1_tarski('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_454, c_318])).
% 3.14/1.47  tff(c_465, plain, (k2_pre_topc('#skF_2', k1_tarski('#skF_3'))=k2_pre_topc('#skF_2', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_141, c_457])).
% 3.14/1.47  tff(c_467, plain, $false, inference(negUnitSimplification, [status(thm)], [c_156, c_465])).
% 3.14/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.47  
% 3.14/1.47  Inference rules
% 3.14/1.47  ----------------------
% 3.14/1.47  #Ref     : 0
% 3.14/1.47  #Sup     : 82
% 3.14/1.47  #Fact    : 0
% 3.14/1.47  #Define  : 0
% 3.14/1.47  #Split   : 6
% 3.14/1.47  #Chain   : 0
% 3.14/1.47  #Close   : 0
% 3.14/1.47  
% 3.14/1.47  Ordering : KBO
% 3.14/1.47  
% 3.14/1.47  Simplification rules
% 3.14/1.47  ----------------------
% 3.14/1.47  #Subsume      : 8
% 3.14/1.47  #Demod        : 42
% 3.14/1.47  #Tautology    : 23
% 3.14/1.47  #SimpNegUnit  : 10
% 3.14/1.47  #BackRed      : 2
% 3.14/1.47  
% 3.14/1.47  #Partial instantiations: 0
% 3.14/1.47  #Strategies tried      : 1
% 3.14/1.47  
% 3.14/1.47  Timing (in seconds)
% 3.14/1.47  ----------------------
% 3.14/1.47  Preprocessing        : 0.34
% 3.14/1.47  Parsing              : 0.18
% 3.14/1.47  CNF conversion       : 0.02
% 3.14/1.47  Main loop            : 0.35
% 3.14/1.47  Inferencing          : 0.14
% 3.14/1.47  Reduction            : 0.10
% 3.14/1.47  Demodulation         : 0.06
% 3.14/1.47  BG Simplification    : 0.02
% 3.14/1.47  Subsumption          : 0.06
% 3.14/1.47  Abstraction          : 0.01
% 3.14/1.47  MUC search           : 0.00
% 3.14/1.47  Cooper               : 0.00
% 3.14/1.47  Total                : 0.73
% 3.14/1.47  Index Insertion      : 0.00
% 3.14/1.47  Index Deletion       : 0.00
% 3.14/1.47  Index Matching       : 0.00
% 3.14/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
