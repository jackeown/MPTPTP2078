%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:22 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 589 expanded)
%              Number of leaves         :   37 ( 208 expanded)
%              Depth                    :   18
%              Number of atoms          :  226 (1827 expanded)
%              Number of equality atoms :   26 ( 309 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_157,negated_conjecture,(
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

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_75,axiom,(
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

tff(f_102,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

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

tff(f_118,axiom,(
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

tff(f_137,axiom,(
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
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_10,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_73,plain,(
    ! [A_52,B_53] :
      ( k6_domain_1(A_52,B_53) = k1_tarski(B_53)
      | ~ m1_subset_1(B_53,A_52)
      | v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_80,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_73])).

tff(c_82,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_12,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(u1_struct_0(A_9))
      | ~ l1_struct_0(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_85,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_12])).

tff(c_88,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_85])).

tff(c_91,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_88])).

tff(c_95,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_91])).

tff(c_97,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_81,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_73])).

tff(c_104,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_81])).

tff(c_110,plain,(
    ! [A_54,B_55] :
      ( m1_subset_1(k6_domain_1(A_54,B_55),k1_zfmisc_1(A_54))
      | ~ m1_subset_1(B_55,A_54)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_116,plain,
    ( m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_110])).

tff(c_122,plain,
    ( m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_116])).

tff(c_123,plain,(
    m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_122])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_46,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_175,plain,(
    ! [A_61,B_62] :
      ( k2_pre_topc(A_61,k2_pre_topc(A_61,B_62)) = k2_pre_topc(A_61,B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_181,plain,
    ( k2_pre_topc('#skF_2',k2_pre_topc('#skF_2',k1_tarski('#skF_3'))) = k2_pre_topc('#skF_2',k1_tarski('#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_123,c_175])).

tff(c_193,plain,(
    k2_pre_topc('#skF_2',k2_pre_topc('#skF_2',k1_tarski('#skF_3'))) = k2_pre_topc('#skF_2',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_181])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k2_pre_topc(A_6,B_7),k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_215,plain,(
    ! [B_63,A_64] :
      ( v4_pre_topc(B_63,A_64)
      | k2_pre_topc(A_64,B_63) != B_63
      | ~ v2_pre_topc(A_64)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_511,plain,(
    ! [A_90,B_91] :
      ( v4_pre_topc(k2_pre_topc(A_90,B_91),A_90)
      | k2_pre_topc(A_90,k2_pre_topc(A_90,B_91)) != k2_pre_topc(A_90,B_91)
      | ~ v2_pre_topc(A_90)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90) ) ),
    inference(resolution,[status(thm)],[c_8,c_215])).

tff(c_519,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),'#skF_2')
    | k2_pre_topc('#skF_2',k2_pre_topc('#skF_2',k1_tarski('#skF_3'))) != k2_pre_topc('#skF_2',k1_tarski('#skF_3'))
    | ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_123,c_511])).

tff(c_534,plain,(
    v4_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48,c_193,c_519])).

tff(c_255,plain,(
    ! [B_66,A_67] :
      ( v3_pre_topc(B_66,A_67)
      | ~ v4_pre_topc(B_66,A_67)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ v3_tdlat_3(A_67)
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_272,plain,(
    ! [A_6,B_7] :
      ( v3_pre_topc(k2_pre_topc(A_6,B_7),A_6)
      | ~ v4_pre_topc(k2_pre_topc(A_6,B_7),A_6)
      | ~ v3_tdlat_3(A_6)
      | ~ v2_pre_topc(A_6)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_255])).

tff(c_543,plain,
    ( v3_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),'#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_534,c_272])).

tff(c_546,plain,(
    v3_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_123,c_48,c_46,c_543])).

tff(c_96,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_36,plain,(
    k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_99,plain,(
    k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')) != k2_pre_topc('#skF_2',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_36])).

tff(c_109,plain,(
    k2_pre_topc('#skF_2',k1_tarski('#skF_3')) != k2_pre_topc('#skF_2',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_99])).

tff(c_63,plain,(
    ! [A_46,B_47] :
      ( r1_xboole_0(k1_tarski(A_46),B_47)
      | r2_hidden(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_66,plain,(
    ! [B_47,A_46] :
      ( r1_xboole_0(B_47,k1_tarski(A_46))
      | r2_hidden(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_63,c_2])).

tff(c_448,plain,(
    ! [A_88,B_89] :
      ( v3_pre_topc(k2_pre_topc(A_88,B_89),A_88)
      | ~ v4_pre_topc(k2_pre_topc(A_88,B_89),A_88)
      | ~ v3_tdlat_3(A_88)
      | ~ v2_pre_topc(A_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(resolution,[status(thm)],[c_8,c_255])).

tff(c_456,plain,
    ( v3_pre_topc(k2_pre_topc('#skF_2',k2_pre_topc('#skF_2',k1_tarski('#skF_3'))),'#skF_2')
    | ~ v4_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),'#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ m1_subset_1(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_448])).

tff(c_460,plain,
    ( v3_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),'#skF_2')
    | ~ v4_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),'#skF_2')
    | ~ m1_subset_1(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48,c_46,c_193,c_456])).

tff(c_463,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_460])).

tff(c_466,plain,
    ( ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_463])).

tff(c_470,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_123,c_466])).

tff(c_472,plain,(
    m1_subset_1(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_460])).

tff(c_119,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_110])).

tff(c_125,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_119])).

tff(c_126,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_125])).

tff(c_332,plain,(
    ! [B_72,A_73,C_74] :
      ( r1_xboole_0(B_72,k2_pre_topc(A_73,C_74))
      | ~ v3_pre_topc(B_72,A_73)
      | ~ r1_xboole_0(B_72,C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_336,plain,(
    ! [B_72] :
      ( r1_xboole_0(B_72,k2_pre_topc('#skF_2',k1_tarski('#skF_4')))
      | ~ v3_pre_topc(B_72,'#skF_2')
      | ~ r1_xboole_0(B_72,k1_tarski('#skF_4'))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_126,c_332])).

tff(c_353,plain,(
    ! [B_75] :
      ( r1_xboole_0(B_75,k2_pre_topc('#skF_2',k1_tarski('#skF_4')))
      | ~ v3_pre_topc(B_75,'#skF_2')
      | ~ r1_xboole_0(B_75,k1_tarski('#skF_4'))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_336])).

tff(c_38,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')),k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_98,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')),k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_38])).

tff(c_140,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_98])).

tff(c_359,plain,
    ( ~ v3_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),'#skF_2')
    | ~ r1_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_tarski('#skF_4'))
    | ~ m1_subset_1(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_353,c_140])).

tff(c_548,plain,
    ( ~ v3_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),'#skF_2')
    | ~ r1_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_472,c_359])).

tff(c_549,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_548])).

tff(c_561,plain,(
    r2_hidden('#skF_4',k2_pre_topc('#skF_2',k1_tarski('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_66,c_549])).

tff(c_398,plain,(
    ! [A_81,C_82,B_83] :
      ( k2_pre_topc(A_81,k6_domain_1(u1_struct_0(A_81),C_82)) = k2_pre_topc(A_81,k6_domain_1(u1_struct_0(A_81),B_83))
      | ~ r2_hidden(B_83,k2_pre_topc(A_81,k6_domain_1(u1_struct_0(A_81),C_82)))
      | ~ m1_subset_1(C_82,u1_struct_0(A_81))
      | ~ m1_subset_1(B_83,u1_struct_0(A_81))
      | ~ l1_pre_topc(A_81)
      | ~ v3_tdlat_3(A_81)
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_401,plain,(
    ! [B_83] :
      ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),B_83)) = k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'))
      | ~ r2_hidden(B_83,k2_pre_topc('#skF_2',k1_tarski('#skF_3')))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_398])).

tff(c_406,plain,(
    ! [B_83] :
      ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),B_83)) = k2_pre_topc('#skF_2',k1_tarski('#skF_3'))
      | ~ r2_hidden(B_83,k2_pre_topc('#skF_2',k1_tarski('#skF_3')))
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_104,c_401])).

tff(c_407,plain,(
    ! [B_83] :
      ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),B_83)) = k2_pre_topc('#skF_2',k1_tarski('#skF_3'))
      | ~ r2_hidden(B_83,k2_pre_topc('#skF_2',k1_tarski('#skF_3')))
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_406])).

tff(c_564,plain,
    ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) = k2_pre_topc('#skF_2',k1_tarski('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_561,c_407])).

tff(c_567,plain,(
    k2_pre_topc('#skF_2',k1_tarski('#skF_3')) = k2_pre_topc('#skF_2',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_96,c_564])).

tff(c_569,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_567])).

tff(c_570,plain,(
    ~ v3_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_548])).

tff(c_607,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_570])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:56:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.46  
% 2.77/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.47  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.77/1.47  
% 2.77/1.47  %Foreground sorts:
% 2.77/1.47  
% 2.77/1.47  
% 2.77/1.47  %Background operators:
% 2.77/1.47  
% 2.77/1.47  
% 2.77/1.47  %Foreground operators:
% 2.77/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.77/1.47  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.77/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.77/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.77/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.77/1.47  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.77/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.77/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.77/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.77/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.77/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.77/1.47  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.77/1.47  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.77/1.47  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.77/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.77/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.77/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.77/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.77/1.47  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.77/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.77/1.47  
% 3.17/1.49  tff(f_157, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_xboole_0(k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)), k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) | (k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tex_2)).
% 3.17/1.49  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.17/1.49  tff(f_89, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.17/1.49  tff(f_54, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.17/1.49  tff(f_82, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.17/1.49  tff(f_60, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 3.17/1.49  tff(f_42, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 3.17/1.49  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.17/1.49  tff(f_102, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tdlat_3)).
% 3.17/1.49  tff(f_36, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.17/1.49  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.17/1.49  tff(f_118, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_xboole_0(B, C) & v3_pre_topc(B, A)) => r1_xboole_0(B, k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_tsep_1)).
% 3.17/1.49  tff(f_137, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) => (k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tex_2)).
% 3.17/1.49  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.17/1.49  tff(c_10, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.17/1.49  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.17/1.49  tff(c_40, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.17/1.49  tff(c_73, plain, (![A_52, B_53]: (k6_domain_1(A_52, B_53)=k1_tarski(B_53) | ~m1_subset_1(B_53, A_52) | v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.17/1.49  tff(c_80, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_73])).
% 3.17/1.49  tff(c_82, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_80])).
% 3.17/1.49  tff(c_12, plain, (![A_9]: (~v1_xboole_0(u1_struct_0(A_9)) | ~l1_struct_0(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.17/1.49  tff(c_85, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_82, c_12])).
% 3.17/1.49  tff(c_88, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_85])).
% 3.17/1.49  tff(c_91, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_10, c_88])).
% 3.17/1.49  tff(c_95, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_91])).
% 3.17/1.49  tff(c_97, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_80])).
% 3.17/1.49  tff(c_42, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.17/1.49  tff(c_81, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_73])).
% 3.17/1.49  tff(c_104, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_97, c_81])).
% 3.17/1.49  tff(c_110, plain, (![A_54, B_55]: (m1_subset_1(k6_domain_1(A_54, B_55), k1_zfmisc_1(A_54)) | ~m1_subset_1(B_55, A_54) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.17/1.49  tff(c_116, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_104, c_110])).
% 3.17/1.49  tff(c_122, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_116])).
% 3.17/1.49  tff(c_123, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_97, c_122])).
% 3.17/1.49  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.17/1.49  tff(c_46, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.17/1.49  tff(c_175, plain, (![A_61, B_62]: (k2_pre_topc(A_61, k2_pre_topc(A_61, B_62))=k2_pre_topc(A_61, B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.17/1.49  tff(c_181, plain, (k2_pre_topc('#skF_2', k2_pre_topc('#skF_2', k1_tarski('#skF_3')))=k2_pre_topc('#skF_2', k1_tarski('#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_123, c_175])).
% 3.17/1.49  tff(c_193, plain, (k2_pre_topc('#skF_2', k2_pre_topc('#skF_2', k1_tarski('#skF_3')))=k2_pre_topc('#skF_2', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_181])).
% 3.17/1.49  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(k2_pre_topc(A_6, B_7), k1_zfmisc_1(u1_struct_0(A_6))) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.17/1.49  tff(c_215, plain, (![B_63, A_64]: (v4_pre_topc(B_63, A_64) | k2_pre_topc(A_64, B_63)!=B_63 | ~v2_pre_topc(A_64) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.17/1.49  tff(c_511, plain, (![A_90, B_91]: (v4_pre_topc(k2_pre_topc(A_90, B_91), A_90) | k2_pre_topc(A_90, k2_pre_topc(A_90, B_91))!=k2_pre_topc(A_90, B_91) | ~v2_pre_topc(A_90) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90))), inference(resolution, [status(thm)], [c_8, c_215])).
% 3.17/1.49  tff(c_519, plain, (v4_pre_topc(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), '#skF_2') | k2_pre_topc('#skF_2', k2_pre_topc('#skF_2', k1_tarski('#skF_3')))!=k2_pre_topc('#skF_2', k1_tarski('#skF_3')) | ~v2_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_123, c_511])).
% 3.17/1.49  tff(c_534, plain, (v4_pre_topc(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_48, c_193, c_519])).
% 3.17/1.49  tff(c_255, plain, (![B_66, A_67]: (v3_pre_topc(B_66, A_67) | ~v4_pre_topc(B_66, A_67) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_67))) | ~v3_tdlat_3(A_67) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.17/1.49  tff(c_272, plain, (![A_6, B_7]: (v3_pre_topc(k2_pre_topc(A_6, B_7), A_6) | ~v4_pre_topc(k2_pre_topc(A_6, B_7), A_6) | ~v3_tdlat_3(A_6) | ~v2_pre_topc(A_6) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_pre_topc(A_6))), inference(resolution, [status(thm)], [c_8, c_255])).
% 3.17/1.49  tff(c_543, plain, (v3_pre_topc(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), '#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | ~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_534, c_272])).
% 3.17/1.49  tff(c_546, plain, (v3_pre_topc(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_123, c_48, c_46, c_543])).
% 3.17/1.49  tff(c_96, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_80])).
% 3.17/1.49  tff(c_36, plain, (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.17/1.49  tff(c_99, plain, (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_36])).
% 3.17/1.49  tff(c_109, plain, (k2_pre_topc('#skF_2', k1_tarski('#skF_3'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_99])).
% 3.17/1.49  tff(c_63, plain, (![A_46, B_47]: (r1_xboole_0(k1_tarski(A_46), B_47) | r2_hidden(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.17/1.49  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.17/1.49  tff(c_66, plain, (![B_47, A_46]: (r1_xboole_0(B_47, k1_tarski(A_46)) | r2_hidden(A_46, B_47))), inference(resolution, [status(thm)], [c_63, c_2])).
% 3.17/1.49  tff(c_448, plain, (![A_88, B_89]: (v3_pre_topc(k2_pre_topc(A_88, B_89), A_88) | ~v4_pre_topc(k2_pre_topc(A_88, B_89), A_88) | ~v3_tdlat_3(A_88) | ~v2_pre_topc(A_88) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(resolution, [status(thm)], [c_8, c_255])).
% 3.17/1.49  tff(c_456, plain, (v3_pre_topc(k2_pre_topc('#skF_2', k2_pre_topc('#skF_2', k1_tarski('#skF_3'))), '#skF_2') | ~v4_pre_topc(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), '#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | ~m1_subset_1(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_193, c_448])).
% 3.17/1.49  tff(c_460, plain, (v3_pre_topc(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), '#skF_2') | ~v4_pre_topc(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), '#skF_2') | ~m1_subset_1(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_48, c_46, c_193, c_456])).
% 3.17/1.49  tff(c_463, plain, (~m1_subset_1(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_460])).
% 3.17/1.49  tff(c_466, plain, (~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_8, c_463])).
% 3.17/1.49  tff(c_470, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_123, c_466])).
% 3.17/1.49  tff(c_472, plain, (m1_subset_1(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_460])).
% 3.17/1.49  tff(c_119, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_110])).
% 3.17/1.49  tff(c_125, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_119])).
% 3.17/1.49  tff(c_126, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_97, c_125])).
% 3.17/1.49  tff(c_332, plain, (![B_72, A_73, C_74]: (r1_xboole_0(B_72, k2_pre_topc(A_73, C_74)) | ~v3_pre_topc(B_72, A_73) | ~r1_xboole_0(B_72, C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.17/1.49  tff(c_336, plain, (![B_72]: (r1_xboole_0(B_72, k2_pre_topc('#skF_2', k1_tarski('#skF_4'))) | ~v3_pre_topc(B_72, '#skF_2') | ~r1_xboole_0(B_72, k1_tarski('#skF_4')) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_126, c_332])).
% 3.17/1.49  tff(c_353, plain, (![B_75]: (r1_xboole_0(B_75, k2_pre_topc('#skF_2', k1_tarski('#skF_4'))) | ~v3_pre_topc(B_75, '#skF_2') | ~r1_xboole_0(B_75, k1_tarski('#skF_4')) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_336])).
% 3.17/1.49  tff(c_38, plain, (~r1_xboole_0(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')), k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.17/1.49  tff(c_98, plain, (~r1_xboole_0(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')), k2_pre_topc('#skF_2', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_38])).
% 3.17/1.49  tff(c_140, plain, (~r1_xboole_0(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k2_pre_topc('#skF_2', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_98])).
% 3.17/1.49  tff(c_359, plain, (~v3_pre_topc(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), '#skF_2') | ~r1_xboole_0(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_tarski('#skF_4')) | ~m1_subset_1(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_353, c_140])).
% 3.17/1.49  tff(c_548, plain, (~v3_pre_topc(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), '#skF_2') | ~r1_xboole_0(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_472, c_359])).
% 3.17/1.49  tff(c_549, plain, (~r1_xboole_0(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_548])).
% 3.17/1.49  tff(c_561, plain, (r2_hidden('#skF_4', k2_pre_topc('#skF_2', k1_tarski('#skF_3')))), inference(resolution, [status(thm)], [c_66, c_549])).
% 3.17/1.49  tff(c_398, plain, (![A_81, C_82, B_83]: (k2_pre_topc(A_81, k6_domain_1(u1_struct_0(A_81), C_82))=k2_pre_topc(A_81, k6_domain_1(u1_struct_0(A_81), B_83)) | ~r2_hidden(B_83, k2_pre_topc(A_81, k6_domain_1(u1_struct_0(A_81), C_82))) | ~m1_subset_1(C_82, u1_struct_0(A_81)) | ~m1_subset_1(B_83, u1_struct_0(A_81)) | ~l1_pre_topc(A_81) | ~v3_tdlat_3(A_81) | ~v2_pre_topc(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.17/1.49  tff(c_401, plain, (![B_83]: (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), B_83))=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')) | ~r2_hidden(B_83, k2_pre_topc('#skF_2', k1_tarski('#skF_3'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_83, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_104, c_398])).
% 3.17/1.49  tff(c_406, plain, (![B_83]: (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), B_83))=k2_pre_topc('#skF_2', k1_tarski('#skF_3')) | ~r2_hidden(B_83, k2_pre_topc('#skF_2', k1_tarski('#skF_3'))) | ~m1_subset_1(B_83, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_104, c_401])).
% 3.17/1.49  tff(c_407, plain, (![B_83]: (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), B_83))=k2_pre_topc('#skF_2', k1_tarski('#skF_3')) | ~r2_hidden(B_83, k2_pre_topc('#skF_2', k1_tarski('#skF_3'))) | ~m1_subset_1(B_83, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_406])).
% 3.17/1.49  tff(c_564, plain, (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))=k2_pre_topc('#skF_2', k1_tarski('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_561, c_407])).
% 3.17/1.49  tff(c_567, plain, (k2_pre_topc('#skF_2', k1_tarski('#skF_3'))=k2_pre_topc('#skF_2', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_96, c_564])).
% 3.17/1.49  tff(c_569, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_567])).
% 3.17/1.49  tff(c_570, plain, (~v3_pre_topc(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), '#skF_2')), inference(splitRight, [status(thm)], [c_548])).
% 3.17/1.49  tff(c_607, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_546, c_570])).
% 3.17/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.49  
% 3.17/1.49  Inference rules
% 3.17/1.49  ----------------------
% 3.17/1.49  #Ref     : 0
% 3.17/1.49  #Sup     : 120
% 3.17/1.49  #Fact    : 0
% 3.17/1.49  #Define  : 0
% 3.17/1.49  #Split   : 6
% 3.17/1.49  #Chain   : 0
% 3.17/1.49  #Close   : 0
% 3.17/1.49  
% 3.17/1.49  Ordering : KBO
% 3.17/1.49  
% 3.17/1.49  Simplification rules
% 3.17/1.49  ----------------------
% 3.17/1.49  #Subsume      : 9
% 3.17/1.49  #Demod        : 106
% 3.17/1.49  #Tautology    : 47
% 3.17/1.49  #SimpNegUnit  : 11
% 3.17/1.49  #BackRed      : 2
% 3.17/1.49  
% 3.17/1.49  #Partial instantiations: 0
% 3.17/1.49  #Strategies tried      : 1
% 3.17/1.49  
% 3.17/1.49  Timing (in seconds)
% 3.17/1.49  ----------------------
% 3.17/1.49  Preprocessing        : 0.36
% 3.17/1.49  Parsing              : 0.20
% 3.17/1.49  CNF conversion       : 0.02
% 3.17/1.49  Main loop            : 0.34
% 3.17/1.49  Inferencing          : 0.13
% 3.17/1.49  Reduction            : 0.10
% 3.17/1.49  Demodulation         : 0.07
% 3.17/1.49  BG Simplification    : 0.02
% 3.17/1.49  Subsumption          : 0.06
% 3.17/1.49  Abstraction          : 0.02
% 3.17/1.49  MUC search           : 0.00
% 3.17/1.49  Cooper               : 0.00
% 3.17/1.49  Total                : 0.74
% 3.17/1.49  Index Insertion      : 0.00
% 3.17/1.49  Index Deletion       : 0.00
% 3.17/1.49  Index Matching       : 0.00
% 3.17/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
