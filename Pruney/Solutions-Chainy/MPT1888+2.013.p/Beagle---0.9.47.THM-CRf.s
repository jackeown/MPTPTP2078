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

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 348 expanded)
%              Number of leaves         :   36 ( 129 expanded)
%              Depth                    :   17
%              Number of atoms          :  184 (1055 expanded)
%              Number of equality atoms :   17 ( 175 expanded)
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
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

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

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_10,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_68,plain,(
    ! [A_48,B_49] :
      ( k6_domain_1(A_48,B_49) = k1_tarski(B_49)
      | ~ m1_subset_1(B_49,A_48)
      | v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_75,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_68])).

tff(c_78,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_12,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(u1_struct_0(A_9))
      | ~ l1_struct_0(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_81,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_12])).

tff(c_84,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_81])).

tff(c_87,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_84])).

tff(c_91,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_87])).

tff(c_93,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_76,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_68])).

tff(c_100,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_76])).

tff(c_92,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_32,plain,(
    k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_95,plain,(
    k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')) != k2_pre_topc('#skF_2',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_32])).

tff(c_105,plain,(
    k2_pre_topc('#skF_2',k1_tarski('#skF_3')) != k2_pre_topc('#skF_2',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_95])).

tff(c_58,plain,(
    ! [A_42,B_43] :
      ( r1_xboole_0(k1_tarski(A_42),B_43)
      | r2_hidden(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_61,plain,(
    ! [B_43,A_42] :
      ( r1_xboole_0(B_43,k1_tarski(A_42))
      | r2_hidden(A_42,B_43) ) ),
    inference(resolution,[status(thm)],[c_58,c_2])).

tff(c_44,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_42,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_106,plain,(
    ! [A_51,B_52] :
      ( m1_subset_1(k6_domain_1(A_51,B_52),k1_zfmisc_1(A_51))
      | ~ m1_subset_1(B_52,A_51)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_112,plain,
    ( m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_106])).

tff(c_118,plain,
    ( m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_112])).

tff(c_119,plain,(
    m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_118])).

tff(c_139,plain,(
    ! [A_54,B_55] :
      ( v4_pre_topc(k2_pre_topc(A_54,B_55),A_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54)
      | ~ v2_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_143,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_119,c_139])).

tff(c_154,plain,(
    v4_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_143])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k2_pre_topc(A_6,B_7),k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_115,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_106])).

tff(c_121,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_115])).

tff(c_122,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_121])).

tff(c_240,plain,(
    ! [B_66,A_67,C_68] :
      ( r1_xboole_0(B_66,k2_pre_topc(A_67,C_68))
      | ~ v3_pre_topc(B_66,A_67)
      | ~ r1_xboole_0(B_66,C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_244,plain,(
    ! [B_66] :
      ( r1_xboole_0(B_66,k2_pre_topc('#skF_2',k1_tarski('#skF_4')))
      | ~ v3_pre_topc(B_66,'#skF_2')
      | ~ r1_xboole_0(B_66,k1_tarski('#skF_4'))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_122,c_240])).

tff(c_261,plain,(
    ! [B_69] :
      ( r1_xboole_0(B_69,k2_pre_topc('#skF_2',k1_tarski('#skF_4')))
      | ~ v3_pre_topc(B_69,'#skF_2')
      | ~ r1_xboole_0(B_69,k1_tarski('#skF_4'))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_244])).

tff(c_34,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')),k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_94,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')),k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_34])).

tff(c_136,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_94])).

tff(c_267,plain,
    ( ~ v3_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),'#skF_2')
    | ~ r1_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_tarski('#skF_4'))
    | ~ m1_subset_1(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_261,c_136])).

tff(c_277,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_267])).

tff(c_280,plain,
    ( ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_277])).

tff(c_284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_119,c_280])).

tff(c_286,plain,(
    m1_subset_1(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_267])).

tff(c_20,plain,(
    ! [B_19,A_16] :
      ( v3_pre_topc(B_19,A_16)
      | ~ v4_pre_topc(B_19,A_16)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ v3_tdlat_3(A_16)
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_291,plain,
    ( v3_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),'#skF_2')
    | ~ v4_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),'#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_286,c_20])).

tff(c_302,plain,(
    v3_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_42,c_154,c_291])).

tff(c_285,plain,
    ( ~ r1_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_tarski('#skF_4'))
    | ~ v3_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_267])).

tff(c_309,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_285])).

tff(c_313,plain,(
    r2_hidden('#skF_4',k2_pre_topc('#skF_2',k1_tarski('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_61,c_309])).

tff(c_314,plain,(
    ! [A_72,C_73,B_74] :
      ( k2_pre_topc(A_72,k6_domain_1(u1_struct_0(A_72),C_73)) = k2_pre_topc(A_72,k6_domain_1(u1_struct_0(A_72),B_74))
      | ~ r2_hidden(B_74,k2_pre_topc(A_72,k6_domain_1(u1_struct_0(A_72),C_73)))
      | ~ m1_subset_1(C_73,u1_struct_0(A_72))
      | ~ m1_subset_1(B_74,u1_struct_0(A_72))
      | ~ l1_pre_topc(A_72)
      | ~ v3_tdlat_3(A_72)
      | ~ v2_pre_topc(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_317,plain,(
    ! [B_74] :
      ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),B_74)) = k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'))
      | ~ r2_hidden(B_74,k2_pre_topc('#skF_2',k1_tarski('#skF_3')))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_74,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_314])).

tff(c_322,plain,(
    ! [B_74] :
      ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),B_74)) = k2_pre_topc('#skF_2',k1_tarski('#skF_3'))
      | ~ r2_hidden(B_74,k2_pre_topc('#skF_2',k1_tarski('#skF_3')))
      | ~ m1_subset_1(B_74,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_100,c_317])).

tff(c_342,plain,(
    ! [B_76] :
      ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),B_76)) = k2_pre_topc('#skF_2',k1_tarski('#skF_3'))
      | ~ r2_hidden(B_76,k2_pre_topc('#skF_2',k1_tarski('#skF_3')))
      | ~ m1_subset_1(B_76,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_322])).

tff(c_345,plain,
    ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) = k2_pre_topc('#skF_2',k1_tarski('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_313,c_342])).

tff(c_348,plain,(
    k2_pre_topc('#skF_2',k1_tarski('#skF_3')) = k2_pre_topc('#skF_2',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_92,c_345])).

tff(c_350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_348])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n016.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:55:34 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.38  
% 2.69/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.39  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.69/1.39  
% 2.69/1.39  %Foreground sorts:
% 2.69/1.39  
% 2.69/1.39  
% 2.69/1.39  %Background operators:
% 2.69/1.39  
% 2.69/1.39  
% 2.69/1.39  %Foreground operators:
% 2.69/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.69/1.39  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.69/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.69/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.69/1.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.69/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.69/1.39  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.69/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.69/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.69/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.69/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.69/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.69/1.39  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.69/1.39  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.69/1.39  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.69/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.69/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.69/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.69/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.69/1.39  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.69/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.69/1.39  
% 2.69/1.41  tff(f_144, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_xboole_0(k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)), k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) | (k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tex_2)).
% 2.69/1.41  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.69/1.41  tff(f_68, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.69/1.41  tff(f_54, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.69/1.41  tff(f_36, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.69/1.41  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.69/1.41  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.69/1.41  tff(f_76, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 2.69/1.41  tff(f_42, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.69/1.41  tff(f_105, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_xboole_0(B, C) & v3_pre_topc(B, A)) => r1_xboole_0(B, k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_tsep_1)).
% 2.69/1.41  tff(f_89, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tdlat_3)).
% 2.69/1.41  tff(f_124, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) => (k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tex_2)).
% 2.69/1.41  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.69/1.41  tff(c_10, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.69/1.41  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.69/1.41  tff(c_36, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.69/1.41  tff(c_68, plain, (![A_48, B_49]: (k6_domain_1(A_48, B_49)=k1_tarski(B_49) | ~m1_subset_1(B_49, A_48) | v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.69/1.41  tff(c_75, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_68])).
% 2.69/1.41  tff(c_78, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_75])).
% 2.69/1.41  tff(c_12, plain, (![A_9]: (~v1_xboole_0(u1_struct_0(A_9)) | ~l1_struct_0(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.69/1.41  tff(c_81, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_78, c_12])).
% 2.69/1.41  tff(c_84, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_46, c_81])).
% 2.69/1.41  tff(c_87, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_10, c_84])).
% 2.69/1.41  tff(c_91, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_87])).
% 2.69/1.41  tff(c_93, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_75])).
% 2.69/1.41  tff(c_38, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.69/1.41  tff(c_76, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_68])).
% 2.69/1.41  tff(c_100, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_93, c_76])).
% 2.69/1.41  tff(c_92, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_75])).
% 2.69/1.41  tff(c_32, plain, (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.69/1.41  tff(c_95, plain, (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_32])).
% 2.69/1.41  tff(c_105, plain, (k2_pre_topc('#skF_2', k1_tarski('#skF_3'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_95])).
% 2.69/1.41  tff(c_58, plain, (![A_42, B_43]: (r1_xboole_0(k1_tarski(A_42), B_43) | r2_hidden(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.69/1.41  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.69/1.41  tff(c_61, plain, (![B_43, A_42]: (r1_xboole_0(B_43, k1_tarski(A_42)) | r2_hidden(A_42, B_43))), inference(resolution, [status(thm)], [c_58, c_2])).
% 2.69/1.41  tff(c_44, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.69/1.41  tff(c_42, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.69/1.41  tff(c_106, plain, (![A_51, B_52]: (m1_subset_1(k6_domain_1(A_51, B_52), k1_zfmisc_1(A_51)) | ~m1_subset_1(B_52, A_51) | v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.69/1.41  tff(c_112, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_100, c_106])).
% 2.69/1.41  tff(c_118, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_112])).
% 2.69/1.41  tff(c_119, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_93, c_118])).
% 2.69/1.41  tff(c_139, plain, (![A_54, B_55]: (v4_pre_topc(k2_pre_topc(A_54, B_55), A_54) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54) | ~v2_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.69/1.41  tff(c_143, plain, (v4_pre_topc(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_119, c_139])).
% 2.69/1.41  tff(c_154, plain, (v4_pre_topc(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_143])).
% 2.69/1.41  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(k2_pre_topc(A_6, B_7), k1_zfmisc_1(u1_struct_0(A_6))) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.69/1.41  tff(c_115, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_106])).
% 2.69/1.41  tff(c_121, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_115])).
% 2.69/1.41  tff(c_122, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_93, c_121])).
% 2.69/1.41  tff(c_240, plain, (![B_66, A_67, C_68]: (r1_xboole_0(B_66, k2_pre_topc(A_67, C_68)) | ~v3_pre_topc(B_66, A_67) | ~r1_xboole_0(B_66, C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.69/1.41  tff(c_244, plain, (![B_66]: (r1_xboole_0(B_66, k2_pre_topc('#skF_2', k1_tarski('#skF_4'))) | ~v3_pre_topc(B_66, '#skF_2') | ~r1_xboole_0(B_66, k1_tarski('#skF_4')) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_122, c_240])).
% 2.69/1.41  tff(c_261, plain, (![B_69]: (r1_xboole_0(B_69, k2_pre_topc('#skF_2', k1_tarski('#skF_4'))) | ~v3_pre_topc(B_69, '#skF_2') | ~r1_xboole_0(B_69, k1_tarski('#skF_4')) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_244])).
% 2.69/1.41  tff(c_34, plain, (~r1_xboole_0(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')), k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.69/1.41  tff(c_94, plain, (~r1_xboole_0(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')), k2_pre_topc('#skF_2', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_34])).
% 2.69/1.41  tff(c_136, plain, (~r1_xboole_0(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k2_pre_topc('#skF_2', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_94])).
% 2.69/1.41  tff(c_267, plain, (~v3_pre_topc(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), '#skF_2') | ~r1_xboole_0(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_tarski('#skF_4')) | ~m1_subset_1(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_261, c_136])).
% 2.69/1.41  tff(c_277, plain, (~m1_subset_1(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_267])).
% 2.69/1.41  tff(c_280, plain, (~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_8, c_277])).
% 2.69/1.41  tff(c_284, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_119, c_280])).
% 2.69/1.41  tff(c_286, plain, (m1_subset_1(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_267])).
% 2.69/1.41  tff(c_20, plain, (![B_19, A_16]: (v3_pre_topc(B_19, A_16) | ~v4_pre_topc(B_19, A_16) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_16))) | ~v3_tdlat_3(A_16) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.69/1.41  tff(c_291, plain, (v3_pre_topc(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), '#skF_2') | ~v4_pre_topc(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), '#skF_2') | ~v3_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_286, c_20])).
% 2.69/1.41  tff(c_302, plain, (v3_pre_topc(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_42, c_154, c_291])).
% 2.69/1.41  tff(c_285, plain, (~r1_xboole_0(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_tarski('#skF_4')) | ~v3_pre_topc(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), '#skF_2')), inference(splitRight, [status(thm)], [c_267])).
% 2.69/1.41  tff(c_309, plain, (~r1_xboole_0(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_302, c_285])).
% 2.69/1.41  tff(c_313, plain, (r2_hidden('#skF_4', k2_pre_topc('#skF_2', k1_tarski('#skF_3')))), inference(resolution, [status(thm)], [c_61, c_309])).
% 2.69/1.41  tff(c_314, plain, (![A_72, C_73, B_74]: (k2_pre_topc(A_72, k6_domain_1(u1_struct_0(A_72), C_73))=k2_pre_topc(A_72, k6_domain_1(u1_struct_0(A_72), B_74)) | ~r2_hidden(B_74, k2_pre_topc(A_72, k6_domain_1(u1_struct_0(A_72), C_73))) | ~m1_subset_1(C_73, u1_struct_0(A_72)) | ~m1_subset_1(B_74, u1_struct_0(A_72)) | ~l1_pre_topc(A_72) | ~v3_tdlat_3(A_72) | ~v2_pre_topc(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.69/1.41  tff(c_317, plain, (![B_74]: (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), B_74))=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')) | ~r2_hidden(B_74, k2_pre_topc('#skF_2', k1_tarski('#skF_3'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_74, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_100, c_314])).
% 2.69/1.41  tff(c_322, plain, (![B_74]: (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), B_74))=k2_pre_topc('#skF_2', k1_tarski('#skF_3')) | ~r2_hidden(B_74, k2_pre_topc('#skF_2', k1_tarski('#skF_3'))) | ~m1_subset_1(B_74, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_100, c_317])).
% 2.69/1.41  tff(c_342, plain, (![B_76]: (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), B_76))=k2_pre_topc('#skF_2', k1_tarski('#skF_3')) | ~r2_hidden(B_76, k2_pre_topc('#skF_2', k1_tarski('#skF_3'))) | ~m1_subset_1(B_76, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_46, c_322])).
% 2.69/1.41  tff(c_345, plain, (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))=k2_pre_topc('#skF_2', k1_tarski('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_313, c_342])).
% 2.69/1.41  tff(c_348, plain, (k2_pre_topc('#skF_2', k1_tarski('#skF_3'))=k2_pre_topc('#skF_2', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_92, c_345])).
% 2.69/1.41  tff(c_350, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105, c_348])).
% 2.69/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.41  
% 2.69/1.41  Inference rules
% 2.69/1.41  ----------------------
% 2.69/1.41  #Ref     : 0
% 2.69/1.41  #Sup     : 61
% 2.69/1.41  #Fact    : 0
% 2.69/1.41  #Define  : 0
% 2.69/1.41  #Split   : 6
% 2.69/1.41  #Chain   : 0
% 2.69/1.41  #Close   : 0
% 2.69/1.41  
% 2.69/1.41  Ordering : KBO
% 2.69/1.41  
% 2.69/1.41  Simplification rules
% 2.69/1.41  ----------------------
% 2.69/1.41  #Subsume      : 3
% 2.69/1.41  #Demod        : 53
% 2.69/1.41  #Tautology    : 15
% 2.69/1.41  #SimpNegUnit  : 9
% 2.69/1.41  #BackRed      : 2
% 2.69/1.41  
% 2.69/1.41  #Partial instantiations: 0
% 2.69/1.41  #Strategies tried      : 1
% 2.69/1.41  
% 2.69/1.41  Timing (in seconds)
% 2.69/1.41  ----------------------
% 2.69/1.41  Preprocessing        : 0.35
% 2.69/1.41  Parsing              : 0.18
% 2.69/1.41  CNF conversion       : 0.03
% 2.69/1.41  Main loop            : 0.27
% 2.69/1.41  Inferencing          : 0.10
% 2.69/1.41  Reduction            : 0.08
% 2.69/1.41  Demodulation         : 0.05
% 2.69/1.41  BG Simplification    : 0.02
% 2.69/1.41  Subsumption          : 0.05
% 2.69/1.41  Abstraction          : 0.01
% 2.69/1.41  MUC search           : 0.00
% 2.69/1.41  Cooper               : 0.00
% 2.69/1.41  Total                : 0.67
% 2.69/1.41  Index Insertion      : 0.00
% 2.69/1.41  Index Deletion       : 0.00
% 2.69/1.41  Index Matching       : 0.00
% 2.69/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
