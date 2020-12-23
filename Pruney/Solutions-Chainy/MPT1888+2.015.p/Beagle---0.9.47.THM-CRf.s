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

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 349 expanded)
%              Number of leaves         :   37 ( 130 expanded)
%              Depth                    :   18
%              Number of atoms          :  183 (1054 expanded)
%              Number of equality atoms :   22 ( 180 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k4_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_144,negated_conjecture,(
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

tff(f_68,axiom,(
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

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_105,axiom,(
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

tff(f_89,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(f_124,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_14,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_83,plain,(
    ! [A_50,B_51] :
      ( k6_domain_1(A_50,B_51) = k1_tarski(B_51)
      | ~ m1_subset_1(B_51,A_50)
      | v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_90,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_83])).

tff(c_92,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_16,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(u1_struct_0(A_9))
      | ~ l1_struct_0(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_95,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_92,c_16])).

tff(c_98,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_95])).

tff(c_101,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_98])).

tff(c_105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_101])).

tff(c_107,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_91,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_83])).

tff(c_118,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_91])).

tff(c_106,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_36,plain,(
    k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_113,plain,(
    k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')) != k2_pre_topc('#skF_2',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_36])).

tff(c_124,plain,(
    k2_pre_topc('#skF_2',k1_tarski('#skF_3')) != k2_pre_topc('#skF_2',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_113])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( k4_xboole_0(A_4,k1_tarski(B_5)) = A_4
      | r2_hidden(B_5,A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_46,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_125,plain,(
    ! [A_53,B_54] :
      ( m1_subset_1(k6_domain_1(A_53,B_54),k1_zfmisc_1(A_53))
      | ~ m1_subset_1(B_54,A_53)
      | v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_131,plain,
    ( m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_125])).

tff(c_137,plain,
    ( m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_131])).

tff(c_138,plain,(
    m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_137])).

tff(c_163,plain,(
    ! [A_56,B_57] :
      ( v4_pre_topc(k2_pre_topc(A_56,B_57),A_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_169,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_138,c_163])).

tff(c_179,plain,(
    v4_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_169])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k2_pre_topc(A_6,B_7),k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_134,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_125])).

tff(c_140,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_134])).

tff(c_141,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_140])).

tff(c_219,plain,(
    ! [B_65,A_66,C_67] :
      ( r1_xboole_0(B_65,k2_pre_topc(A_66,C_67))
      | ~ v3_pre_topc(B_65,A_66)
      | ~ r1_xboole_0(B_65,C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_225,plain,(
    ! [B_65] :
      ( r1_xboole_0(B_65,k2_pre_topc('#skF_2',k1_tarski('#skF_4')))
      | ~ v3_pre_topc(B_65,'#skF_2')
      | ~ r1_xboole_0(B_65,k1_tarski('#skF_4'))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_141,c_219])).

tff(c_270,plain,(
    ! [B_70] :
      ( r1_xboole_0(B_70,k2_pre_topc('#skF_2',k1_tarski('#skF_4')))
      | ~ v3_pre_topc(B_70,'#skF_2')
      | ~ r1_xboole_0(B_70,k1_tarski('#skF_4'))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_225])).

tff(c_38,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')),k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_112,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')),k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_38])).

tff(c_150,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_112])).

tff(c_277,plain,
    ( ~ v3_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),'#skF_2')
    | ~ r1_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_tarski('#skF_4'))
    | ~ m1_subset_1(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_270,c_150])).

tff(c_279,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_277])).

tff(c_282,plain,
    ( ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_279])).

tff(c_286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_138,c_282])).

tff(c_288,plain,(
    m1_subset_1(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_277])).

tff(c_24,plain,(
    ! [B_19,A_16] :
      ( v3_pre_topc(B_19,A_16)
      | ~ v4_pre_topc(B_19,A_16)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ v3_tdlat_3(A_16)
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_293,plain,
    ( v3_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),'#skF_2')
    | ~ v4_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),'#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_288,c_24])).

tff(c_304,plain,(
    v3_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_46,c_179,c_293])).

tff(c_287,plain,
    ( ~ r1_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_tarski('#skF_4'))
    | ~ v3_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_277])).

tff(c_311,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_287])).

tff(c_315,plain,(
    k4_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_tarski('#skF_4')) != k2_pre_topc('#skF_2',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_311])).

tff(c_332,plain,(
    r2_hidden('#skF_4',k2_pre_topc('#skF_2',k1_tarski('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_315])).

tff(c_316,plain,(
    ! [A_71,C_72,B_73] :
      ( k2_pre_topc(A_71,k6_domain_1(u1_struct_0(A_71),C_72)) = k2_pre_topc(A_71,k6_domain_1(u1_struct_0(A_71),B_73))
      | ~ r2_hidden(B_73,k2_pre_topc(A_71,k6_domain_1(u1_struct_0(A_71),C_72)))
      | ~ m1_subset_1(C_72,u1_struct_0(A_71))
      | ~ m1_subset_1(B_73,u1_struct_0(A_71))
      | ~ l1_pre_topc(A_71)
      | ~ v3_tdlat_3(A_71)
      | ~ v2_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_319,plain,(
    ! [B_73] :
      ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),B_73)) = k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'))
      | ~ r2_hidden(B_73,k2_pre_topc('#skF_2',k1_tarski('#skF_3')))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_73,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_316])).

tff(c_324,plain,(
    ! [B_73] :
      ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),B_73)) = k2_pre_topc('#skF_2',k1_tarski('#skF_3'))
      | ~ r2_hidden(B_73,k2_pre_topc('#skF_2',k1_tarski('#skF_3')))
      | ~ m1_subset_1(B_73,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_118,c_319])).

tff(c_338,plain,(
    ! [B_75] :
      ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),B_75)) = k2_pre_topc('#skF_2',k1_tarski('#skF_3'))
      | ~ r2_hidden(B_75,k2_pre_topc('#skF_2',k1_tarski('#skF_3')))
      | ~ m1_subset_1(B_75,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_324])).

tff(c_341,plain,
    ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) = k2_pre_topc('#skF_2',k1_tarski('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_332,c_338])).

tff(c_344,plain,(
    k2_pre_topc('#skF_2',k1_tarski('#skF_3')) = k2_pre_topc('#skF_2',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_106,c_341])).

tff(c_346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_344])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:51:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.44  
% 2.83/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.44  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k4_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.83/1.44  
% 2.83/1.44  %Foreground sorts:
% 2.83/1.44  
% 2.83/1.44  
% 2.83/1.44  %Background operators:
% 2.83/1.44  
% 2.83/1.44  
% 2.83/1.44  %Foreground operators:
% 2.83/1.44  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.83/1.44  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.83/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.83/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.83/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.83/1.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.83/1.44  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.83/1.44  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.83/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.83/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.83/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.83/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.83/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.44  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.83/1.44  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.83/1.44  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.83/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.83/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.44  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.83/1.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.83/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.83/1.44  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.83/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.44  
% 2.83/1.46  tff(f_144, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_xboole_0(k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)), k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) | (k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tex_2)).
% 2.83/1.46  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.83/1.46  tff(f_68, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.83/1.46  tff(f_54, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.83/1.46  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.83/1.46  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.83/1.46  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.83/1.46  tff(f_76, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 2.83/1.46  tff(f_42, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.83/1.46  tff(f_105, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_xboole_0(B, C) & v3_pre_topc(B, A)) => r1_xboole_0(B, k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_tsep_1)).
% 2.83/1.46  tff(f_89, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tdlat_3)).
% 2.83/1.46  tff(f_124, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) => (k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tex_2)).
% 2.83/1.46  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.83/1.46  tff(c_14, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.83/1.46  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.83/1.46  tff(c_40, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.83/1.46  tff(c_83, plain, (![A_50, B_51]: (k6_domain_1(A_50, B_51)=k1_tarski(B_51) | ~m1_subset_1(B_51, A_50) | v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.83/1.46  tff(c_90, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_83])).
% 2.83/1.46  tff(c_92, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_90])).
% 2.83/1.46  tff(c_16, plain, (![A_9]: (~v1_xboole_0(u1_struct_0(A_9)) | ~l1_struct_0(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.83/1.46  tff(c_95, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_92, c_16])).
% 2.83/1.46  tff(c_98, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_95])).
% 2.83/1.46  tff(c_101, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_98])).
% 2.83/1.46  tff(c_105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_101])).
% 2.83/1.46  tff(c_107, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_90])).
% 2.83/1.46  tff(c_42, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.83/1.46  tff(c_91, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_83])).
% 2.83/1.46  tff(c_118, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_107, c_91])).
% 2.83/1.46  tff(c_106, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_90])).
% 2.83/1.46  tff(c_36, plain, (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.83/1.46  tff(c_113, plain, (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_36])).
% 2.83/1.46  tff(c_124, plain, (k2_pre_topc('#skF_2', k1_tarski('#skF_3'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_113])).
% 2.83/1.46  tff(c_10, plain, (![A_4, B_5]: (k4_xboole_0(A_4, k1_tarski(B_5))=A_4 | r2_hidden(B_5, A_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.83/1.46  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k4_xboole_0(A_1, B_2)!=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.83/1.46  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.83/1.46  tff(c_46, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.83/1.46  tff(c_125, plain, (![A_53, B_54]: (m1_subset_1(k6_domain_1(A_53, B_54), k1_zfmisc_1(A_53)) | ~m1_subset_1(B_54, A_53) | v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.83/1.46  tff(c_131, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_118, c_125])).
% 2.83/1.46  tff(c_137, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_131])).
% 2.83/1.46  tff(c_138, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_107, c_137])).
% 2.83/1.46  tff(c_163, plain, (![A_56, B_57]: (v4_pre_topc(k2_pre_topc(A_56, B_57), A_56) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.83/1.46  tff(c_169, plain, (v4_pre_topc(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_138, c_163])).
% 2.83/1.46  tff(c_179, plain, (v4_pre_topc(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_169])).
% 2.83/1.46  tff(c_12, plain, (![A_6, B_7]: (m1_subset_1(k2_pre_topc(A_6, B_7), k1_zfmisc_1(u1_struct_0(A_6))) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.83/1.46  tff(c_134, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_106, c_125])).
% 2.83/1.46  tff(c_140, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_134])).
% 2.83/1.46  tff(c_141, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_107, c_140])).
% 2.83/1.46  tff(c_219, plain, (![B_65, A_66, C_67]: (r1_xboole_0(B_65, k2_pre_topc(A_66, C_67)) | ~v3_pre_topc(B_65, A_66) | ~r1_xboole_0(B_65, C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.83/1.46  tff(c_225, plain, (![B_65]: (r1_xboole_0(B_65, k2_pre_topc('#skF_2', k1_tarski('#skF_4'))) | ~v3_pre_topc(B_65, '#skF_2') | ~r1_xboole_0(B_65, k1_tarski('#skF_4')) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_141, c_219])).
% 2.83/1.46  tff(c_270, plain, (![B_70]: (r1_xboole_0(B_70, k2_pre_topc('#skF_2', k1_tarski('#skF_4'))) | ~v3_pre_topc(B_70, '#skF_2') | ~r1_xboole_0(B_70, k1_tarski('#skF_4')) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_225])).
% 2.83/1.46  tff(c_38, plain, (~r1_xboole_0(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')), k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.83/1.46  tff(c_112, plain, (~r1_xboole_0(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')), k2_pre_topc('#skF_2', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_38])).
% 2.83/1.46  tff(c_150, plain, (~r1_xboole_0(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k2_pre_topc('#skF_2', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_112])).
% 2.83/1.46  tff(c_277, plain, (~v3_pre_topc(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), '#skF_2') | ~r1_xboole_0(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_tarski('#skF_4')) | ~m1_subset_1(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_270, c_150])).
% 2.83/1.46  tff(c_279, plain, (~m1_subset_1(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_277])).
% 2.83/1.46  tff(c_282, plain, (~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_279])).
% 2.83/1.46  tff(c_286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_138, c_282])).
% 2.83/1.46  tff(c_288, plain, (m1_subset_1(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_277])).
% 2.83/1.46  tff(c_24, plain, (![B_19, A_16]: (v3_pre_topc(B_19, A_16) | ~v4_pre_topc(B_19, A_16) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_16))) | ~v3_tdlat_3(A_16) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.83/1.46  tff(c_293, plain, (v3_pre_topc(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), '#skF_2') | ~v4_pre_topc(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), '#skF_2') | ~v3_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_288, c_24])).
% 2.83/1.46  tff(c_304, plain, (v3_pre_topc(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_46, c_179, c_293])).
% 2.83/1.46  tff(c_287, plain, (~r1_xboole_0(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_tarski('#skF_4')) | ~v3_pre_topc(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), '#skF_2')), inference(splitRight, [status(thm)], [c_277])).
% 2.83/1.46  tff(c_311, plain, (~r1_xboole_0(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_304, c_287])).
% 2.83/1.46  tff(c_315, plain, (k4_xboole_0(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_tarski('#skF_4'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_4, c_311])).
% 2.83/1.46  tff(c_332, plain, (r2_hidden('#skF_4', k2_pre_topc('#skF_2', k1_tarski('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_10, c_315])).
% 2.83/1.46  tff(c_316, plain, (![A_71, C_72, B_73]: (k2_pre_topc(A_71, k6_domain_1(u1_struct_0(A_71), C_72))=k2_pre_topc(A_71, k6_domain_1(u1_struct_0(A_71), B_73)) | ~r2_hidden(B_73, k2_pre_topc(A_71, k6_domain_1(u1_struct_0(A_71), C_72))) | ~m1_subset_1(C_72, u1_struct_0(A_71)) | ~m1_subset_1(B_73, u1_struct_0(A_71)) | ~l1_pre_topc(A_71) | ~v3_tdlat_3(A_71) | ~v2_pre_topc(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.83/1.46  tff(c_319, plain, (![B_73]: (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), B_73))=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')) | ~r2_hidden(B_73, k2_pre_topc('#skF_2', k1_tarski('#skF_3'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_73, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_118, c_316])).
% 2.83/1.46  tff(c_324, plain, (![B_73]: (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), B_73))=k2_pre_topc('#skF_2', k1_tarski('#skF_3')) | ~r2_hidden(B_73, k2_pre_topc('#skF_2', k1_tarski('#skF_3'))) | ~m1_subset_1(B_73, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_118, c_319])).
% 2.83/1.46  tff(c_338, plain, (![B_75]: (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), B_75))=k2_pre_topc('#skF_2', k1_tarski('#skF_3')) | ~r2_hidden(B_75, k2_pre_topc('#skF_2', k1_tarski('#skF_3'))) | ~m1_subset_1(B_75, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_324])).
% 2.83/1.46  tff(c_341, plain, (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))=k2_pre_topc('#skF_2', k1_tarski('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_332, c_338])).
% 2.83/1.46  tff(c_344, plain, (k2_pre_topc('#skF_2', k1_tarski('#skF_3'))=k2_pre_topc('#skF_2', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_106, c_341])).
% 2.83/1.46  tff(c_346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124, c_344])).
% 2.83/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.46  
% 2.83/1.46  Inference rules
% 2.83/1.46  ----------------------
% 2.83/1.46  #Ref     : 0
% 2.83/1.46  #Sup     : 58
% 2.83/1.46  #Fact    : 0
% 2.83/1.46  #Define  : 0
% 2.83/1.46  #Split   : 5
% 2.83/1.46  #Chain   : 0
% 2.83/1.46  #Close   : 0
% 2.83/1.46  
% 2.83/1.46  Ordering : KBO
% 2.83/1.46  
% 2.83/1.46  Simplification rules
% 2.83/1.46  ----------------------
% 2.83/1.46  #Subsume      : 1
% 2.83/1.46  #Demod        : 55
% 2.83/1.46  #Tautology    : 17
% 2.83/1.46  #SimpNegUnit  : 9
% 2.83/1.46  #BackRed      : 2
% 2.83/1.46  
% 2.83/1.46  #Partial instantiations: 0
% 2.83/1.46  #Strategies tried      : 1
% 2.83/1.46  
% 2.83/1.46  Timing (in seconds)
% 2.83/1.46  ----------------------
% 2.83/1.46  Preprocessing        : 0.36
% 2.83/1.46  Parsing              : 0.20
% 2.97/1.46  CNF conversion       : 0.03
% 2.97/1.46  Main loop            : 0.27
% 2.97/1.46  Inferencing          : 0.10
% 2.97/1.46  Reduction            : 0.09
% 2.97/1.46  Demodulation         : 0.06
% 2.97/1.46  BG Simplification    : 0.02
% 2.97/1.46  Subsumption          : 0.04
% 2.97/1.46  Abstraction          : 0.01
% 2.97/1.46  MUC search           : 0.00
% 2.97/1.46  Cooper               : 0.00
% 2.97/1.46  Total                : 0.67
% 2.97/1.46  Index Insertion      : 0.00
% 2.97/1.46  Index Deletion       : 0.00
% 2.97/1.46  Index Matching       : 0.00
% 2.97/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
