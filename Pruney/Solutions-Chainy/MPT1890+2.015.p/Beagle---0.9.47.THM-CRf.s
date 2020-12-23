%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:25 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 436 expanded)
%              Number of leaves         :   33 ( 173 expanded)
%              Depth                    :   17
%              Number of atoms          :  246 (1853 expanded)
%              Number of equality atoms :   18 ( 185 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v2_tex_2 > r2_hidden > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

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
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( r2_hidden(C,B)
                   => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C))) = k6_domain_1(u1_struct_0(A),C) ) )
             => v2_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_tex_2)).

tff(f_109,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ~ ( r2_hidden(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = k6_domain_1(u1_struct_0(A),C) ) ) ) )
           => v2_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_tex_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_30,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_40,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_36,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_187,plain,(
    ! [A_93,B_94] :
      ( r2_hidden('#skF_2'(A_93,B_94),B_94)
      | v2_tex_2(B_94,A_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_196,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_187])).

tff(c_202,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_196])).

tff(c_203,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_30,c_202])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_206,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_2'('#skF_3','#skF_4'),A_1)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_203,c_2])).

tff(c_38,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_4,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k1_tarski(A_5),k1_zfmisc_1(B_6))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_125,plain,(
    ! [A_71,B_72] :
      ( v4_pre_topc(k2_pre_topc(A_71,B_72),A_71)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_137,plain,(
    ! [A_71,A_5] :
      ( v4_pre_topc(k2_pre_topc(A_71,k1_tarski(A_5)),A_71)
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71)
      | ~ r2_hidden(A_5,u1_struct_0(A_71)) ) ),
    inference(resolution,[status(thm)],[c_4,c_125])).

tff(c_10,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k2_pre_topc(A_13,B_14),k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_165,plain,(
    ! [B_89,A_90] :
      ( v3_pre_topc(B_89,A_90)
      | ~ v4_pre_topc(B_89,A_90)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ v3_tdlat_3(A_90)
      | ~ l1_pre_topc(A_90)
      | ~ v2_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_368,plain,(
    ! [A_125,B_126] :
      ( v3_pre_topc(k2_pre_topc(A_125,B_126),A_125)
      | ~ v4_pre_topc(k2_pre_topc(A_125,B_126),A_125)
      | ~ v3_tdlat_3(A_125)
      | ~ v2_pre_topc(A_125)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125) ) ),
    inference(resolution,[status(thm)],[c_10,c_165])).

tff(c_461,plain,(
    ! [A_147,A_148] :
      ( v3_pre_topc(k2_pre_topc(A_147,k1_tarski(A_148)),A_147)
      | ~ v3_tdlat_3(A_147)
      | ~ m1_subset_1(k1_tarski(A_148),k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ l1_pre_topc(A_147)
      | ~ v2_pre_topc(A_147)
      | ~ r2_hidden(A_148,u1_struct_0(A_147)) ) ),
    inference(resolution,[status(thm)],[c_137,c_368])).

tff(c_465,plain,(
    ! [A_147,A_5] :
      ( v3_pre_topc(k2_pre_topc(A_147,k1_tarski(A_5)),A_147)
      | ~ v3_tdlat_3(A_147)
      | ~ l1_pre_topc(A_147)
      | ~ v2_pre_topc(A_147)
      | ~ r2_hidden(A_5,u1_struct_0(A_147)) ) ),
    inference(resolution,[status(thm)],[c_4,c_461])).

tff(c_28,plain,(
    ! [A_23,B_31] :
      ( m1_subset_1('#skF_2'(A_23,B_31),u1_struct_0(A_23))
      | v2_tex_2(B_31,A_23)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_44,plain,(
    ! [C_44,B_45,A_46] :
      ( ~ v1_xboole_0(C_44)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(C_44))
      | ~ r2_hidden(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_50,plain,(
    ! [A_46] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_46,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_44])).

tff(c_51,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_245,plain,(
    ! [A_98,B_99] :
      ( m1_subset_1('#skF_2'(A_98,B_99),u1_struct_0(A_98))
      | v2_tex_2(B_99,A_98)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98)
      | ~ v2_pre_topc(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_12,plain,(
    ! [A_15,B_16] :
      ( k6_domain_1(A_15,B_16) = k1_tarski(B_16)
      | ~ m1_subset_1(B_16,A_15)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_625,plain,(
    ! [A_172,B_173] :
      ( k6_domain_1(u1_struct_0(A_172),'#skF_2'(A_172,B_173)) = k1_tarski('#skF_2'(A_172,B_173))
      | v1_xboole_0(u1_struct_0(A_172))
      | v2_tex_2(B_173,A_172)
      | ~ m1_subset_1(B_173,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ l1_pre_topc(A_172)
      | ~ v2_pre_topc(A_172)
      | v2_struct_0(A_172) ) ),
    inference(resolution,[status(thm)],[c_245,c_12])).

tff(c_637,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4')) = k1_tarski('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_3'))
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_625])).

tff(c_644,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4')) = k1_tarski('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_3'))
    | v2_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_637])).

tff(c_645,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4')) = k1_tarski('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_30,c_51,c_644])).

tff(c_32,plain,(
    ! [C_41] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_41))) = k6_domain_1(u1_struct_0('#skF_3'),C_41)
      | ~ r2_hidden(C_41,'#skF_4')
      | ~ m1_subset_1(C_41,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_658,plain,
    ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k1_tarski('#skF_2'('#skF_3','#skF_4')))) = k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
    | ~ r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_645,c_32])).

tff(c_673,plain,
    ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k1_tarski('#skF_2'('#skF_3','#skF_4')))) = k1_tarski('#skF_2'('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_645,c_658])).

tff(c_710,plain,(
    ~ m1_subset_1('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_673])).

tff(c_716,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_710])).

tff(c_725,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_34,c_716])).

tff(c_727,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_30,c_725])).

tff(c_728,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k1_tarski('#skF_2'('#skF_3','#skF_4')))) = k1_tarski('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_673])).

tff(c_73,plain,(
    ! [A_57,C_58,B_59] :
      ( m1_subset_1(A_57,C_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(C_58))
      | ~ r2_hidden(A_57,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_80,plain,(
    ! [A_60] :
      ( m1_subset_1(A_60,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_60,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_73])).

tff(c_83,plain,(
    ! [A_60] :
      ( k6_domain_1(u1_struct_0('#skF_3'),A_60) = k1_tarski(A_60)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_60,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_80,c_12])).

tff(c_86,plain,(
    ! [A_60] :
      ( k6_domain_1(u1_struct_0('#skF_3'),A_60) = k1_tarski(A_60)
      | ~ r2_hidden(A_60,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_83])).

tff(c_290,plain,(
    ! [A_110,B_111,D_112] :
      ( k9_subset_1(u1_struct_0(A_110),B_111,D_112) != k6_domain_1(u1_struct_0(A_110),'#skF_2'(A_110,B_111))
      | ~ v3_pre_topc(D_112,A_110)
      | ~ m1_subset_1(D_112,k1_zfmisc_1(u1_struct_0(A_110)))
      | v2_tex_2(B_111,A_110)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110)
      | ~ v2_pre_topc(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_295,plain,(
    ! [B_111,D_112] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_111,D_112) != k1_tarski('#skF_2'('#skF_3',B_111))
      | ~ v3_pre_topc(D_112,'#skF_3')
      | ~ m1_subset_1(D_112,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_tex_2(B_111,'#skF_3')
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_3',B_111),'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_290])).

tff(c_302,plain,(
    ! [B_111,D_112] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_111,D_112) != k1_tarski('#skF_2'('#skF_3',B_111))
      | ~ v3_pre_topc(D_112,'#skF_3')
      | ~ m1_subset_1(D_112,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_tex_2(B_111,'#skF_3')
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_3',B_111),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_295])).

tff(c_303,plain,(
    ! [B_111,D_112] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_111,D_112) != k1_tarski('#skF_2'('#skF_3',B_111))
      | ~ v3_pre_topc(D_112,'#skF_3')
      | ~ m1_subset_1(D_112,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_tex_2(B_111,'#skF_3')
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden('#skF_2'('#skF_3',B_111),'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_302])).

tff(c_780,plain,
    ( ~ v3_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_2'('#skF_3','#skF_4'))),'#skF_3')
    | ~ m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_2'('#skF_3','#skF_4'))),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_728,c_303])).

tff(c_793,plain,
    ( ~ v3_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_2'('#skF_3','#skF_4'))),'#skF_3')
    | ~ m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_2'('#skF_3','#skF_4'))),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_34,c_780])).

tff(c_794,plain,
    ( ~ v3_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_2'('#skF_3','#skF_4'))),'#skF_3')
    | ~ m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_2'('#skF_3','#skF_4'))),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_793])).

tff(c_803,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_2'('#skF_3','#skF_4'))),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_794])).

tff(c_806,plain,
    ( ~ m1_subset_1(k1_tarski('#skF_2'('#skF_3','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_803])).

tff(c_809,plain,(
    ~ m1_subset_1(k1_tarski('#skF_2'('#skF_3','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_806])).

tff(c_813,plain,(
    ~ r2_hidden('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_809])).

tff(c_819,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_206,c_813])).

tff(c_826,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_819])).

tff(c_827,plain,(
    ~ v3_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_2'('#skF_3','#skF_4'))),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_794])).

tff(c_831,plain,
    ( ~ v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ r2_hidden('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_465,c_827])).

tff(c_834,plain,(
    ~ r2_hidden('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_38,c_831])).

tff(c_840,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_206,c_834])).

tff(c_847,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_840])).

tff(c_848,plain,(
    ! [A_46] : ~ r2_hidden(A_46,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_946,plain,(
    ! [A_215,B_216] :
      ( r2_hidden('#skF_2'(A_215,B_216),B_216)
      | v2_tex_2(B_216,A_215)
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0(A_215)))
      | ~ l1_pre_topc(A_215)
      | ~ v2_pre_topc(A_215)
      | v2_struct_0(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_955,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_946])).

tff(c_961,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_955])).

tff(c_963,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_30,c_848,c_961])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:31:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.56  
% 3.60/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.56  %$ v4_pre_topc > v3_pre_topc > v2_tex_2 > r2_hidden > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.60/1.56  
% 3.60/1.56  %Foreground sorts:
% 3.60/1.56  
% 3.60/1.56  
% 3.60/1.56  %Background operators:
% 3.60/1.56  
% 3.60/1.56  
% 3.60/1.56  %Foreground operators:
% 3.60/1.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.60/1.56  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.60/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.60/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.60/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.60/1.56  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.60/1.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.60/1.56  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.60/1.56  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.60/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.60/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.60/1.56  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.60/1.56  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.60/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.60/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.60/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.60/1.56  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.60/1.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.60/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.60/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.60/1.56  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.60/1.56  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.60/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.60/1.56  
% 3.60/1.58  tff(f_131, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_tex_2)).
% 3.60/1.58  tff(f_109, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k6_domain_1(u1_struct_0(A), C)))))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_tex_2)).
% 3.60/1.58  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.60/1.58  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 3.60/1.58  tff(f_70, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 3.60/1.58  tff(f_55, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 3.60/1.58  tff(f_83, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tdlat_3)).
% 3.60/1.58  tff(f_49, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.60/1.58  tff(f_62, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.60/1.58  tff(f_42, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.60/1.58  tff(c_42, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.60/1.58  tff(c_30, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.60/1.58  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.60/1.58  tff(c_40, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.60/1.58  tff(c_36, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.60/1.58  tff(c_187, plain, (![A_93, B_94]: (r2_hidden('#skF_2'(A_93, B_94), B_94) | v2_tex_2(B_94, A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.60/1.58  tff(c_196, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_187])).
% 3.60/1.58  tff(c_202, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_196])).
% 3.60/1.58  tff(c_203, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_42, c_30, c_202])).
% 3.60/1.58  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.60/1.58  tff(c_206, plain, (![A_1]: (r2_hidden('#skF_2'('#skF_3', '#skF_4'), A_1) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_203, c_2])).
% 3.60/1.58  tff(c_38, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.60/1.58  tff(c_4, plain, (![A_5, B_6]: (m1_subset_1(k1_tarski(A_5), k1_zfmisc_1(B_6)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.60/1.58  tff(c_125, plain, (![A_71, B_72]: (v4_pre_topc(k2_pre_topc(A_71, B_72), A_71) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.60/1.58  tff(c_137, plain, (![A_71, A_5]: (v4_pre_topc(k2_pre_topc(A_71, k1_tarski(A_5)), A_71) | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71) | ~r2_hidden(A_5, u1_struct_0(A_71)))), inference(resolution, [status(thm)], [c_4, c_125])).
% 3.60/1.58  tff(c_10, plain, (![A_13, B_14]: (m1_subset_1(k2_pre_topc(A_13, B_14), k1_zfmisc_1(u1_struct_0(A_13))) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.60/1.58  tff(c_165, plain, (![B_89, A_90]: (v3_pre_topc(B_89, A_90) | ~v4_pre_topc(B_89, A_90) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_90))) | ~v3_tdlat_3(A_90) | ~l1_pre_topc(A_90) | ~v2_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.60/1.58  tff(c_368, plain, (![A_125, B_126]: (v3_pre_topc(k2_pre_topc(A_125, B_126), A_125) | ~v4_pre_topc(k2_pre_topc(A_125, B_126), A_125) | ~v3_tdlat_3(A_125) | ~v2_pre_topc(A_125) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125))), inference(resolution, [status(thm)], [c_10, c_165])).
% 3.60/1.58  tff(c_461, plain, (![A_147, A_148]: (v3_pre_topc(k2_pre_topc(A_147, k1_tarski(A_148)), A_147) | ~v3_tdlat_3(A_147) | ~m1_subset_1(k1_tarski(A_148), k1_zfmisc_1(u1_struct_0(A_147))) | ~l1_pre_topc(A_147) | ~v2_pre_topc(A_147) | ~r2_hidden(A_148, u1_struct_0(A_147)))), inference(resolution, [status(thm)], [c_137, c_368])).
% 3.60/1.58  tff(c_465, plain, (![A_147, A_5]: (v3_pre_topc(k2_pre_topc(A_147, k1_tarski(A_5)), A_147) | ~v3_tdlat_3(A_147) | ~l1_pre_topc(A_147) | ~v2_pre_topc(A_147) | ~r2_hidden(A_5, u1_struct_0(A_147)))), inference(resolution, [status(thm)], [c_4, c_461])).
% 3.60/1.58  tff(c_28, plain, (![A_23, B_31]: (m1_subset_1('#skF_2'(A_23, B_31), u1_struct_0(A_23)) | v2_tex_2(B_31, A_23) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.60/1.58  tff(c_44, plain, (![C_44, B_45, A_46]: (~v1_xboole_0(C_44) | ~m1_subset_1(B_45, k1_zfmisc_1(C_44)) | ~r2_hidden(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.60/1.58  tff(c_50, plain, (![A_46]: (~v1_xboole_0(u1_struct_0('#skF_3')) | ~r2_hidden(A_46, '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_44])).
% 3.60/1.58  tff(c_51, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_50])).
% 3.60/1.58  tff(c_245, plain, (![A_98, B_99]: (m1_subset_1('#skF_2'(A_98, B_99), u1_struct_0(A_98)) | v2_tex_2(B_99, A_98) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98) | ~v2_pre_topc(A_98) | v2_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.60/1.58  tff(c_12, plain, (![A_15, B_16]: (k6_domain_1(A_15, B_16)=k1_tarski(B_16) | ~m1_subset_1(B_16, A_15) | v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.60/1.58  tff(c_625, plain, (![A_172, B_173]: (k6_domain_1(u1_struct_0(A_172), '#skF_2'(A_172, B_173))=k1_tarski('#skF_2'(A_172, B_173)) | v1_xboole_0(u1_struct_0(A_172)) | v2_tex_2(B_173, A_172) | ~m1_subset_1(B_173, k1_zfmisc_1(u1_struct_0(A_172))) | ~l1_pre_topc(A_172) | ~v2_pre_topc(A_172) | v2_struct_0(A_172))), inference(resolution, [status(thm)], [c_245, c_12])).
% 3.60/1.58  tff(c_637, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4'))=k1_tarski('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0(u1_struct_0('#skF_3')) | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_625])).
% 3.60/1.58  tff(c_644, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4'))=k1_tarski('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0(u1_struct_0('#skF_3')) | v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_637])).
% 3.60/1.58  tff(c_645, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4'))=k1_tarski('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_42, c_30, c_51, c_644])).
% 3.60/1.58  tff(c_32, plain, (![C_41]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_41)))=k6_domain_1(u1_struct_0('#skF_3'), C_41) | ~r2_hidden(C_41, '#skF_4') | ~m1_subset_1(C_41, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.60/1.58  tff(c_658, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k1_tarski('#skF_2'('#skF_3', '#skF_4'))))=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_645, c_32])).
% 3.60/1.58  tff(c_673, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k1_tarski('#skF_2'('#skF_3', '#skF_4'))))=k1_tarski('#skF_2'('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_203, c_645, c_658])).
% 3.60/1.58  tff(c_710, plain, (~m1_subset_1('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_673])).
% 3.60/1.58  tff(c_716, plain, (v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_28, c_710])).
% 3.60/1.58  tff(c_725, plain, (v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_34, c_716])).
% 3.60/1.58  tff(c_727, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_30, c_725])).
% 3.60/1.58  tff(c_728, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k1_tarski('#skF_2'('#skF_3', '#skF_4'))))=k1_tarski('#skF_2'('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_673])).
% 3.60/1.58  tff(c_73, plain, (![A_57, C_58, B_59]: (m1_subset_1(A_57, C_58) | ~m1_subset_1(B_59, k1_zfmisc_1(C_58)) | ~r2_hidden(A_57, B_59))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.60/1.58  tff(c_80, plain, (![A_60]: (m1_subset_1(A_60, u1_struct_0('#skF_3')) | ~r2_hidden(A_60, '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_73])).
% 3.60/1.58  tff(c_83, plain, (![A_60]: (k6_domain_1(u1_struct_0('#skF_3'), A_60)=k1_tarski(A_60) | v1_xboole_0(u1_struct_0('#skF_3')) | ~r2_hidden(A_60, '#skF_4'))), inference(resolution, [status(thm)], [c_80, c_12])).
% 3.60/1.58  tff(c_86, plain, (![A_60]: (k6_domain_1(u1_struct_0('#skF_3'), A_60)=k1_tarski(A_60) | ~r2_hidden(A_60, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_51, c_83])).
% 3.60/1.58  tff(c_290, plain, (![A_110, B_111, D_112]: (k9_subset_1(u1_struct_0(A_110), B_111, D_112)!=k6_domain_1(u1_struct_0(A_110), '#skF_2'(A_110, B_111)) | ~v3_pre_topc(D_112, A_110) | ~m1_subset_1(D_112, k1_zfmisc_1(u1_struct_0(A_110))) | v2_tex_2(B_111, A_110) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110) | ~v2_pre_topc(A_110) | v2_struct_0(A_110))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.60/1.58  tff(c_295, plain, (![B_111, D_112]: (k9_subset_1(u1_struct_0('#skF_3'), B_111, D_112)!=k1_tarski('#skF_2'('#skF_3', B_111)) | ~v3_pre_topc(D_112, '#skF_3') | ~m1_subset_1(D_112, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_tex_2(B_111, '#skF_3') | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r2_hidden('#skF_2'('#skF_3', B_111), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_86, c_290])).
% 3.60/1.58  tff(c_302, plain, (![B_111, D_112]: (k9_subset_1(u1_struct_0('#skF_3'), B_111, D_112)!=k1_tarski('#skF_2'('#skF_3', B_111)) | ~v3_pre_topc(D_112, '#skF_3') | ~m1_subset_1(D_112, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_tex_2(B_111, '#skF_3') | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3') | ~r2_hidden('#skF_2'('#skF_3', B_111), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_295])).
% 3.60/1.58  tff(c_303, plain, (![B_111, D_112]: (k9_subset_1(u1_struct_0('#skF_3'), B_111, D_112)!=k1_tarski('#skF_2'('#skF_3', B_111)) | ~v3_pre_topc(D_112, '#skF_3') | ~m1_subset_1(D_112, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_tex_2(B_111, '#skF_3') | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden('#skF_2'('#skF_3', B_111), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_42, c_302])).
% 3.60/1.58  tff(c_780, plain, (~v3_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_2'('#skF_3', '#skF_4'))), '#skF_3') | ~m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_2'('#skF_3', '#skF_4'))), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_728, c_303])).
% 3.60/1.58  tff(c_793, plain, (~v3_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_2'('#skF_3', '#skF_4'))), '#skF_3') | ~m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_2'('#skF_3', '#skF_4'))), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_203, c_34, c_780])).
% 3.60/1.58  tff(c_794, plain, (~v3_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_2'('#skF_3', '#skF_4'))), '#skF_3') | ~m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_2'('#skF_3', '#skF_4'))), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_30, c_793])).
% 3.60/1.58  tff(c_803, plain, (~m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_2'('#skF_3', '#skF_4'))), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_794])).
% 3.60/1.58  tff(c_806, plain, (~m1_subset_1(k1_tarski('#skF_2'('#skF_3', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_10, c_803])).
% 3.60/1.58  tff(c_809, plain, (~m1_subset_1(k1_tarski('#skF_2'('#skF_3', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_806])).
% 3.60/1.58  tff(c_813, plain, (~r2_hidden('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_4, c_809])).
% 3.60/1.58  tff(c_819, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_206, c_813])).
% 3.60/1.58  tff(c_826, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_819])).
% 3.60/1.58  tff(c_827, plain, (~v3_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_2'('#skF_3', '#skF_4'))), '#skF_3')), inference(splitRight, [status(thm)], [c_794])).
% 3.60/1.58  tff(c_831, plain, (~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~r2_hidden('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_465, c_827])).
% 3.60/1.58  tff(c_834, plain, (~r2_hidden('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_38, c_831])).
% 3.60/1.58  tff(c_840, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_206, c_834])).
% 3.60/1.58  tff(c_847, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_840])).
% 3.60/1.58  tff(c_848, plain, (![A_46]: (~r2_hidden(A_46, '#skF_4'))), inference(splitRight, [status(thm)], [c_50])).
% 3.60/1.58  tff(c_946, plain, (![A_215, B_216]: (r2_hidden('#skF_2'(A_215, B_216), B_216) | v2_tex_2(B_216, A_215) | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0(A_215))) | ~l1_pre_topc(A_215) | ~v2_pre_topc(A_215) | v2_struct_0(A_215))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.60/1.58  tff(c_955, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_946])).
% 3.60/1.58  tff(c_961, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_955])).
% 3.60/1.58  tff(c_963, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_30, c_848, c_961])).
% 3.60/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.58  
% 3.60/1.58  Inference rules
% 3.60/1.58  ----------------------
% 3.60/1.58  #Ref     : 0
% 3.60/1.58  #Sup     : 204
% 3.60/1.58  #Fact    : 0
% 3.60/1.58  #Define  : 0
% 3.60/1.58  #Split   : 12
% 3.60/1.58  #Chain   : 0
% 3.60/1.58  #Close   : 0
% 3.60/1.58  
% 3.60/1.58  Ordering : KBO
% 3.60/1.58  
% 3.60/1.58  Simplification rules
% 3.60/1.58  ----------------------
% 3.60/1.58  #Subsume      : 16
% 3.60/1.58  #Demod        : 88
% 3.60/1.58  #Tautology    : 30
% 3.60/1.58  #SimpNegUnit  : 15
% 3.60/1.58  #BackRed      : 1
% 3.60/1.58  
% 3.60/1.59  #Partial instantiations: 0
% 3.60/1.59  #Strategies tried      : 1
% 3.60/1.59  
% 3.60/1.59  Timing (in seconds)
% 3.60/1.59  ----------------------
% 3.60/1.59  Preprocessing        : 0.33
% 3.60/1.59  Parsing              : 0.17
% 3.60/1.59  CNF conversion       : 0.02
% 3.60/1.59  Main loop            : 0.49
% 3.60/1.59  Inferencing          : 0.19
% 3.60/1.59  Reduction            : 0.13
% 3.60/1.59  Demodulation         : 0.08
% 3.60/1.59  BG Simplification    : 0.02
% 3.60/1.59  Subsumption          : 0.10
% 3.60/1.59  Abstraction          : 0.03
% 3.60/1.59  MUC search           : 0.00
% 3.60/1.59  Cooper               : 0.00
% 3.60/1.59  Total                : 0.86
% 3.60/1.59  Index Insertion      : 0.00
% 3.60/1.59  Index Deletion       : 0.00
% 3.60/1.59  Index Matching       : 0.00
% 3.60/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
