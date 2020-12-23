%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:20 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 348 expanded)
%              Number of leaves         :   40 ( 132 expanded)
%              Depth                    :   16
%              Number of atoms          :  253 (1107 expanded)
%              Number of equality atoms :   17 ( 153 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k2_pre_topc > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

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

tff(k1_connsp_2,type,(
    k1_connsp_2: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(f_171,negated_conjecture,(
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

tff(f_103,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r2_hidden(B,k1_connsp_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_connsp_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_connsp_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_116,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(f_132,axiom,(
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

tff(f_151,axiom,(
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

tff(c_54,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_52,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_153,plain,(
    ! [B_79,A_80] :
      ( r2_hidden(B_79,k1_connsp_2(A_80,B_79))
      | ~ m1_subset_1(B_79,u1_struct_0(A_80))
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_173,plain,(
    ! [A_85,B_86] :
      ( ~ v1_xboole_0(k1_connsp_2(A_85,B_86))
      | ~ m1_subset_1(B_86,u1_struct_0(A_85))
      | ~ l1_pre_topc(A_85)
      | ~ v2_pre_topc(A_85)
      | v2_struct_0(A_85) ) ),
    inference(resolution,[status(thm)],[c_153,c_2])).

tff(c_176,plain,
    ( ~ v1_xboole_0(k1_connsp_2('#skF_3','#skF_5'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_173])).

tff(c_182,plain,
    ( ~ v1_xboole_0(k1_connsp_2('#skF_3','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_176])).

tff(c_183,plain,(
    ~ v1_xboole_0(k1_connsp_2('#skF_3','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_182])).

tff(c_91,plain,(
    ! [A_67,B_68] :
      ( k6_domain_1(A_67,B_68) = k1_tarski(B_68)
      | ~ m1_subset_1(B_68,A_67)
      | v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_102,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_91])).

tff(c_104,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_188,plain,(
    ! [A_87,B_88] :
      ( m1_subset_1(k1_connsp_2(A_87,B_88),k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ m1_subset_1(B_88,u1_struct_0(A_87))
      | ~ l1_pre_topc(A_87)
      | ~ v2_pre_topc(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_14,plain,(
    ! [B_14,A_12] :
      ( v1_xboole_0(B_14)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_12))
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_239,plain,(
    ! [A_97,B_98] :
      ( v1_xboole_0(k1_connsp_2(A_97,B_98))
      | ~ v1_xboole_0(u1_struct_0(A_97))
      | ~ m1_subset_1(B_98,u1_struct_0(A_97))
      | ~ l1_pre_topc(A_97)
      | ~ v2_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(resolution,[status(thm)],[c_188,c_14])).

tff(c_242,plain,
    ( v1_xboole_0(k1_connsp_2('#skF_3','#skF_5'))
    | ~ v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_239])).

tff(c_248,plain,
    ( v1_xboole_0(k1_connsp_2('#skF_3','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_104,c_242])).

tff(c_250,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_183,c_248])).

tff(c_252,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_103,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_91])).

tff(c_258,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_252,c_103])).

tff(c_251,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_40,plain,(
    k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5')) != k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_253,plain,(
    k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')) != k2_pre_topc('#skF_3',k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_40])).

tff(c_264,plain,(
    k2_pre_topc('#skF_3',k1_tarski('#skF_5')) != k2_pre_topc('#skF_3',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_253])).

tff(c_71,plain,(
    ! [A_56,B_57] :
      ( r1_xboole_0(k1_tarski(A_56),B_57)
      | r2_hidden(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_74,plain,(
    ! [B_57,A_56] :
      ( r1_xboole_0(B_57,k1_tarski(A_56))
      | r2_hidden(A_56,B_57) ) ),
    inference(resolution,[status(thm)],[c_71,c_6])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( r2_hidden(A_15,B_16)
      | v1_xboole_0(B_16)
      | ~ m1_subset_1(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(k1_tarski(A_10),k1_zfmisc_1(B_11))
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k2_pre_topc(A_17,B_18),k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_50,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_276,plain,(
    ! [A_102,B_103] :
      ( v4_pre_topc(k2_pre_topc(A_102,B_103),A_102)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102)
      | ~ v2_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_283,plain,(
    ! [A_102,A_10] :
      ( v4_pre_topc(k2_pre_topc(A_102,k1_tarski(A_10)),A_102)
      | ~ l1_pre_topc(A_102)
      | ~ v2_pre_topc(A_102)
      | ~ r2_hidden(A_10,u1_struct_0(A_102)) ) ),
    inference(resolution,[status(thm)],[c_12,c_276])).

tff(c_355,plain,(
    ! [B_123,A_124] :
      ( v3_pre_topc(B_123,A_124)
      | ~ v4_pre_topc(B_123,A_124)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ v3_tdlat_3(A_124)
      | ~ l1_pre_topc(A_124)
      | ~ v2_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_434,plain,(
    ! [A_141,B_142] :
      ( v3_pre_topc(k2_pre_topc(A_141,B_142),A_141)
      | ~ v4_pre_topc(k2_pre_topc(A_141,B_142),A_141)
      | ~ v3_tdlat_3(A_141)
      | ~ v2_pre_topc(A_141)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141) ) ),
    inference(resolution,[status(thm)],[c_18,c_355])).

tff(c_504,plain,(
    ! [A_154,A_155] :
      ( v3_pre_topc(k2_pre_topc(A_154,k1_tarski(A_155)),A_154)
      | ~ v3_tdlat_3(A_154)
      | ~ m1_subset_1(k1_tarski(A_155),k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_pre_topc(A_154)
      | ~ v2_pre_topc(A_154)
      | ~ r2_hidden(A_155,u1_struct_0(A_154)) ) ),
    inference(resolution,[status(thm)],[c_283,c_434])).

tff(c_508,plain,(
    ! [A_154,A_10] :
      ( v3_pre_topc(k2_pre_topc(A_154,k1_tarski(A_10)),A_154)
      | ~ v3_tdlat_3(A_154)
      | ~ l1_pre_topc(A_154)
      | ~ v2_pre_topc(A_154)
      | ~ r2_hidden(A_10,u1_struct_0(A_154)) ) ),
    inference(resolution,[status(thm)],[c_12,c_504])).

tff(c_409,plain,(
    ! [B_133,A_134,C_135] :
      ( r1_xboole_0(B_133,k2_pre_topc(A_134,C_135))
      | ~ v3_pre_topc(B_133,A_134)
      | ~ r1_xboole_0(B_133,C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_533,plain,(
    ! [B_168,A_169,A_170] :
      ( r1_xboole_0(B_168,k2_pre_topc(A_169,k1_tarski(A_170)))
      | ~ v3_pre_topc(B_168,A_169)
      | ~ r1_xboole_0(B_168,k1_tarski(A_170))
      | ~ m1_subset_1(B_168,k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ l1_pre_topc(A_169)
      | ~ v2_pre_topc(A_169)
      | ~ r2_hidden(A_170,u1_struct_0(A_169)) ) ),
    inference(resolution,[status(thm)],[c_12,c_409])).

tff(c_42,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')),k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_275,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_251,c_42])).

tff(c_536,plain,
    ( ~ v3_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),'#skF_3')
    | ~ r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_tarski('#skF_5'))
    | ~ m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ r2_hidden('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_533,c_275])).

tff(c_541,plain,
    ( ~ v3_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),'#skF_3')
    | ~ r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_tarski('#skF_5'))
    | ~ m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ r2_hidden('#skF_5',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_536])).

tff(c_543,plain,(
    ~ r2_hidden('#skF_5',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_541])).

tff(c_546,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_543])).

tff(c_549,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_546])).

tff(c_551,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_252,c_549])).

tff(c_552,plain,
    ( ~ m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_tarski('#skF_5'))
    | ~ v3_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_541])).

tff(c_562,plain,(
    ~ v3_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_552])).

tff(c_565,plain,
    ( ~ v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ r2_hidden('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_508,c_562])).

tff(c_568,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_50,c_565])).

tff(c_571,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_568])).

tff(c_574,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_571])).

tff(c_576,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_252,c_574])).

tff(c_577,plain,
    ( ~ r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_tarski('#skF_5'))
    | ~ m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_552])).

tff(c_580,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_577])).

tff(c_583,plain,
    ( ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_580])).

tff(c_586,plain,(
    ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_583])).

tff(c_590,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_586])).

tff(c_593,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_590])).

tff(c_596,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_593])).

tff(c_598,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_252,c_596])).

tff(c_599,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_tarski('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_577])).

tff(c_608,plain,(
    r2_hidden('#skF_5',k2_pre_topc('#skF_3',k1_tarski('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_74,c_599])).

tff(c_448,plain,(
    ! [A_145,C_146,B_147] :
      ( k2_pre_topc(A_145,k6_domain_1(u1_struct_0(A_145),C_146)) = k2_pre_topc(A_145,k6_domain_1(u1_struct_0(A_145),B_147))
      | ~ r2_hidden(B_147,k2_pre_topc(A_145,k6_domain_1(u1_struct_0(A_145),C_146)))
      | ~ m1_subset_1(C_146,u1_struct_0(A_145))
      | ~ m1_subset_1(B_147,u1_struct_0(A_145))
      | ~ l1_pre_topc(A_145)
      | ~ v3_tdlat_3(A_145)
      | ~ v2_pre_topc(A_145)
      | v2_struct_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_451,plain,(
    ! [B_147] :
      ( k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),B_147)) = k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))
      | ~ r2_hidden(B_147,k2_pre_topc('#skF_3',k1_tarski('#skF_4')))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_147,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_448])).

tff(c_464,plain,(
    ! [B_147] :
      ( k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),B_147)) = k2_pre_topc('#skF_3',k1_tarski('#skF_4'))
      | ~ r2_hidden(B_147,k2_pre_topc('#skF_3',k1_tarski('#skF_4')))
      | ~ m1_subset_1(B_147,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_258,c_451])).

tff(c_465,plain,(
    ! [B_147] :
      ( k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),B_147)) = k2_pre_topc('#skF_3',k1_tarski('#skF_4'))
      | ~ r2_hidden(B_147,k2_pre_topc('#skF_3',k1_tarski('#skF_4')))
      | ~ m1_subset_1(B_147,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_464])).

tff(c_611,plain,
    ( k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5')) = k2_pre_topc('#skF_3',k1_tarski('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_608,c_465])).

tff(c_617,plain,(
    k2_pre_topc('#skF_3',k1_tarski('#skF_5')) = k2_pre_topc('#skF_3',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_251,c_611])).

tff(c_619,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_264,c_617])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:01:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.67  
% 3.13/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.67  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k2_pre_topc > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 3.13/1.67  
% 3.13/1.67  %Foreground sorts:
% 3.13/1.67  
% 3.13/1.67  
% 3.13/1.67  %Background operators:
% 3.13/1.67  
% 3.13/1.67  
% 3.13/1.67  %Foreground operators:
% 3.13/1.67  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.13/1.67  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.13/1.67  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.13/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.13/1.67  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.13/1.67  tff(k1_connsp_2, type, k1_connsp_2: ($i * $i) > $i).
% 3.13/1.67  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.13/1.67  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.13/1.67  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.13/1.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.13/1.67  tff('#skF_5', type, '#skF_5': $i).
% 3.13/1.67  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.13/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.13/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.13/1.67  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.13/1.67  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.13/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.13/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.67  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.13/1.67  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.13/1.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.13/1.67  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.13/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.13/1.67  
% 3.13/1.69  tff(f_171, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_xboole_0(k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)), k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) | (k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tex_2)).
% 3.13/1.69  tff(f_103, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r2_hidden(B, k1_connsp_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_connsp_2)).
% 3.13/1.69  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.13/1.69  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.13/1.69  tff(f_91, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k1_connsp_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 3.13/1.69  tff(f_53, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.13/1.69  tff(f_42, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.13/1.69  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.13/1.69  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.13/1.69  tff(f_46, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 3.13/1.69  tff(f_65, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 3.13/1.69  tff(f_80, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 3.13/1.69  tff(f_116, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tdlat_3)).
% 3.13/1.69  tff(f_132, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_xboole_0(B, C) & v3_pre_topc(B, A)) => r1_xboole_0(B, k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_tsep_1)).
% 3.13/1.69  tff(f_151, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) => (k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tex_2)).
% 3.13/1.69  tff(c_54, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.13/1.69  tff(c_52, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.13/1.69  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.13/1.69  tff(c_44, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.13/1.69  tff(c_153, plain, (![B_79, A_80]: (r2_hidden(B_79, k1_connsp_2(A_80, B_79)) | ~m1_subset_1(B_79, u1_struct_0(A_80)) | ~l1_pre_topc(A_80) | ~v2_pre_topc(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.13/1.69  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.13/1.69  tff(c_173, plain, (![A_85, B_86]: (~v1_xboole_0(k1_connsp_2(A_85, B_86)) | ~m1_subset_1(B_86, u1_struct_0(A_85)) | ~l1_pre_topc(A_85) | ~v2_pre_topc(A_85) | v2_struct_0(A_85))), inference(resolution, [status(thm)], [c_153, c_2])).
% 3.13/1.69  tff(c_176, plain, (~v1_xboole_0(k1_connsp_2('#skF_3', '#skF_5')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_173])).
% 3.13/1.69  tff(c_182, plain, (~v1_xboole_0(k1_connsp_2('#skF_3', '#skF_5')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_176])).
% 3.13/1.69  tff(c_183, plain, (~v1_xboole_0(k1_connsp_2('#skF_3', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_54, c_182])).
% 3.13/1.69  tff(c_91, plain, (![A_67, B_68]: (k6_domain_1(A_67, B_68)=k1_tarski(B_68) | ~m1_subset_1(B_68, A_67) | v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.13/1.69  tff(c_102, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_91])).
% 3.13/1.69  tff(c_104, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_102])).
% 3.13/1.69  tff(c_188, plain, (![A_87, B_88]: (m1_subset_1(k1_connsp_2(A_87, B_88), k1_zfmisc_1(u1_struct_0(A_87))) | ~m1_subset_1(B_88, u1_struct_0(A_87)) | ~l1_pre_topc(A_87) | ~v2_pre_topc(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.13/1.69  tff(c_14, plain, (![B_14, A_12]: (v1_xboole_0(B_14) | ~m1_subset_1(B_14, k1_zfmisc_1(A_12)) | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.13/1.69  tff(c_239, plain, (![A_97, B_98]: (v1_xboole_0(k1_connsp_2(A_97, B_98)) | ~v1_xboole_0(u1_struct_0(A_97)) | ~m1_subset_1(B_98, u1_struct_0(A_97)) | ~l1_pre_topc(A_97) | ~v2_pre_topc(A_97) | v2_struct_0(A_97))), inference(resolution, [status(thm)], [c_188, c_14])).
% 3.13/1.69  tff(c_242, plain, (v1_xboole_0(k1_connsp_2('#skF_3', '#skF_5')) | ~v1_xboole_0(u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_239])).
% 3.13/1.69  tff(c_248, plain, (v1_xboole_0(k1_connsp_2('#skF_3', '#skF_5')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_104, c_242])).
% 3.13/1.69  tff(c_250, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_183, c_248])).
% 3.13/1.69  tff(c_252, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_102])).
% 3.13/1.69  tff(c_46, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.13/1.69  tff(c_103, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_91])).
% 3.13/1.69  tff(c_258, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_252, c_103])).
% 3.13/1.69  tff(c_251, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_102])).
% 3.13/1.69  tff(c_40, plain, (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5'))!=k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.13/1.69  tff(c_253, plain, (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'))!=k2_pre_topc('#skF_3', k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_251, c_40])).
% 3.13/1.69  tff(c_264, plain, (k2_pre_topc('#skF_3', k1_tarski('#skF_5'))!=k2_pre_topc('#skF_3', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_258, c_253])).
% 3.13/1.69  tff(c_71, plain, (![A_56, B_57]: (r1_xboole_0(k1_tarski(A_56), B_57) | r2_hidden(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.13/1.69  tff(c_6, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.13/1.69  tff(c_74, plain, (![B_57, A_56]: (r1_xboole_0(B_57, k1_tarski(A_56)) | r2_hidden(A_56, B_57))), inference(resolution, [status(thm)], [c_71, c_6])).
% 3.13/1.69  tff(c_16, plain, (![A_15, B_16]: (r2_hidden(A_15, B_16) | v1_xboole_0(B_16) | ~m1_subset_1(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.13/1.69  tff(c_12, plain, (![A_10, B_11]: (m1_subset_1(k1_tarski(A_10), k1_zfmisc_1(B_11)) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.13/1.69  tff(c_18, plain, (![A_17, B_18]: (m1_subset_1(k2_pre_topc(A_17, B_18), k1_zfmisc_1(u1_struct_0(A_17))) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.13/1.69  tff(c_50, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.13/1.69  tff(c_276, plain, (![A_102, B_103]: (v4_pre_topc(k2_pre_topc(A_102, B_103), A_102) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102) | ~v2_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.13/1.69  tff(c_283, plain, (![A_102, A_10]: (v4_pre_topc(k2_pre_topc(A_102, k1_tarski(A_10)), A_102) | ~l1_pre_topc(A_102) | ~v2_pre_topc(A_102) | ~r2_hidden(A_10, u1_struct_0(A_102)))), inference(resolution, [status(thm)], [c_12, c_276])).
% 3.13/1.69  tff(c_355, plain, (![B_123, A_124]: (v3_pre_topc(B_123, A_124) | ~v4_pre_topc(B_123, A_124) | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0(A_124))) | ~v3_tdlat_3(A_124) | ~l1_pre_topc(A_124) | ~v2_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.13/1.69  tff(c_434, plain, (![A_141, B_142]: (v3_pre_topc(k2_pre_topc(A_141, B_142), A_141) | ~v4_pre_topc(k2_pre_topc(A_141, B_142), A_141) | ~v3_tdlat_3(A_141) | ~v2_pre_topc(A_141) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141))), inference(resolution, [status(thm)], [c_18, c_355])).
% 3.13/1.69  tff(c_504, plain, (![A_154, A_155]: (v3_pre_topc(k2_pre_topc(A_154, k1_tarski(A_155)), A_154) | ~v3_tdlat_3(A_154) | ~m1_subset_1(k1_tarski(A_155), k1_zfmisc_1(u1_struct_0(A_154))) | ~l1_pre_topc(A_154) | ~v2_pre_topc(A_154) | ~r2_hidden(A_155, u1_struct_0(A_154)))), inference(resolution, [status(thm)], [c_283, c_434])).
% 3.13/1.69  tff(c_508, plain, (![A_154, A_10]: (v3_pre_topc(k2_pre_topc(A_154, k1_tarski(A_10)), A_154) | ~v3_tdlat_3(A_154) | ~l1_pre_topc(A_154) | ~v2_pre_topc(A_154) | ~r2_hidden(A_10, u1_struct_0(A_154)))), inference(resolution, [status(thm)], [c_12, c_504])).
% 3.13/1.69  tff(c_409, plain, (![B_133, A_134, C_135]: (r1_xboole_0(B_133, k2_pre_topc(A_134, C_135)) | ~v3_pre_topc(B_133, A_134) | ~r1_xboole_0(B_133, C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(u1_struct_0(A_134))) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_134))) | ~l1_pre_topc(A_134) | ~v2_pre_topc(A_134))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.13/1.69  tff(c_533, plain, (![B_168, A_169, A_170]: (r1_xboole_0(B_168, k2_pre_topc(A_169, k1_tarski(A_170))) | ~v3_pre_topc(B_168, A_169) | ~r1_xboole_0(B_168, k1_tarski(A_170)) | ~m1_subset_1(B_168, k1_zfmisc_1(u1_struct_0(A_169))) | ~l1_pre_topc(A_169) | ~v2_pre_topc(A_169) | ~r2_hidden(A_170, u1_struct_0(A_169)))), inference(resolution, [status(thm)], [c_12, c_409])).
% 3.13/1.69  tff(c_42, plain, (~r1_xboole_0(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')), k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.13/1.69  tff(c_275, plain, (~r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k2_pre_topc('#skF_3', k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_258, c_251, c_42])).
% 3.13/1.69  tff(c_536, plain, (~v3_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), '#skF_3') | ~r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_tarski('#skF_5')) | ~m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~r2_hidden('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_533, c_275])).
% 3.13/1.69  tff(c_541, plain, (~v3_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), '#skF_3') | ~r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_tarski('#skF_5')) | ~m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden('#skF_5', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_536])).
% 3.13/1.69  tff(c_543, plain, (~r2_hidden('#skF_5', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_541])).
% 3.13/1.69  tff(c_546, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_16, c_543])).
% 3.13/1.69  tff(c_549, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_546])).
% 3.13/1.69  tff(c_551, plain, $false, inference(negUnitSimplification, [status(thm)], [c_252, c_549])).
% 3.13/1.69  tff(c_552, plain, (~m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_tarski('#skF_5')) | ~v3_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), '#skF_3')), inference(splitRight, [status(thm)], [c_541])).
% 3.13/1.69  tff(c_562, plain, (~v3_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_552])).
% 3.13/1.69  tff(c_565, plain, (~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~r2_hidden('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_508, c_562])).
% 3.13/1.69  tff(c_568, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_50, c_565])).
% 3.13/1.69  tff(c_571, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_16, c_568])).
% 3.13/1.69  tff(c_574, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_571])).
% 3.13/1.69  tff(c_576, plain, $false, inference(negUnitSimplification, [status(thm)], [c_252, c_574])).
% 3.13/1.69  tff(c_577, plain, (~r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_tarski('#skF_5')) | ~m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_552])).
% 3.13/1.69  tff(c_580, plain, (~m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_577])).
% 3.13/1.69  tff(c_583, plain, (~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_18, c_580])).
% 3.13/1.69  tff(c_586, plain, (~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_583])).
% 3.13/1.69  tff(c_590, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_12, c_586])).
% 3.13/1.69  tff(c_593, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_16, c_590])).
% 3.13/1.69  tff(c_596, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_593])).
% 3.13/1.69  tff(c_598, plain, $false, inference(negUnitSimplification, [status(thm)], [c_252, c_596])).
% 3.13/1.69  tff(c_599, plain, (~r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_tarski('#skF_5'))), inference(splitRight, [status(thm)], [c_577])).
% 3.13/1.69  tff(c_608, plain, (r2_hidden('#skF_5', k2_pre_topc('#skF_3', k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_74, c_599])).
% 3.13/1.69  tff(c_448, plain, (![A_145, C_146, B_147]: (k2_pre_topc(A_145, k6_domain_1(u1_struct_0(A_145), C_146))=k2_pre_topc(A_145, k6_domain_1(u1_struct_0(A_145), B_147)) | ~r2_hidden(B_147, k2_pre_topc(A_145, k6_domain_1(u1_struct_0(A_145), C_146))) | ~m1_subset_1(C_146, u1_struct_0(A_145)) | ~m1_subset_1(B_147, u1_struct_0(A_145)) | ~l1_pre_topc(A_145) | ~v3_tdlat_3(A_145) | ~v2_pre_topc(A_145) | v2_struct_0(A_145))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.13/1.69  tff(c_451, plain, (![B_147]: (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), B_147))=k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')) | ~r2_hidden(B_147, k2_pre_topc('#skF_3', k1_tarski('#skF_4'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1(B_147, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_258, c_448])).
% 3.13/1.69  tff(c_464, plain, (![B_147]: (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), B_147))=k2_pre_topc('#skF_3', k1_tarski('#skF_4')) | ~r2_hidden(B_147, k2_pre_topc('#skF_3', k1_tarski('#skF_4'))) | ~m1_subset_1(B_147, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_258, c_451])).
% 3.13/1.69  tff(c_465, plain, (![B_147]: (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), B_147))=k2_pre_topc('#skF_3', k1_tarski('#skF_4')) | ~r2_hidden(B_147, k2_pre_topc('#skF_3', k1_tarski('#skF_4'))) | ~m1_subset_1(B_147, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_54, c_464])).
% 3.13/1.69  tff(c_611, plain, (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5'))=k2_pre_topc('#skF_3', k1_tarski('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_608, c_465])).
% 3.13/1.69  tff(c_617, plain, (k2_pre_topc('#skF_3', k1_tarski('#skF_5'))=k2_pre_topc('#skF_3', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_251, c_611])).
% 3.13/1.69  tff(c_619, plain, $false, inference(negUnitSimplification, [status(thm)], [c_264, c_617])).
% 3.13/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.69  
% 3.13/1.69  Inference rules
% 3.13/1.69  ----------------------
% 3.13/1.69  #Ref     : 0
% 3.13/1.69  #Sup     : 113
% 3.13/1.69  #Fact    : 0
% 3.13/1.69  #Define  : 0
% 3.13/1.69  #Split   : 6
% 3.13/1.69  #Chain   : 0
% 3.13/1.69  #Close   : 0
% 3.13/1.69  
% 3.13/1.69  Ordering : KBO
% 3.13/1.69  
% 3.13/1.69  Simplification rules
% 3.13/1.69  ----------------------
% 3.13/1.69  #Subsume      : 12
% 3.13/1.69  #Demod        : 45
% 3.13/1.69  #Tautology    : 24
% 3.13/1.69  #SimpNegUnit  : 14
% 3.13/1.69  #BackRed      : 1
% 3.13/1.69  
% 3.13/1.69  #Partial instantiations: 0
% 3.13/1.69  #Strategies tried      : 1
% 3.13/1.69  
% 3.13/1.69  Timing (in seconds)
% 3.13/1.69  ----------------------
% 3.13/1.69  Preprocessing        : 0.46
% 3.13/1.69  Parsing              : 0.27
% 3.13/1.69  CNF conversion       : 0.03
% 3.13/1.69  Main loop            : 0.37
% 3.13/1.69  Inferencing          : 0.15
% 3.13/1.69  Reduction            : 0.10
% 3.13/1.69  Demodulation         : 0.07
% 3.13/1.69  BG Simplification    : 0.02
% 3.13/1.69  Subsumption          : 0.06
% 3.13/1.70  Abstraction          : 0.02
% 3.13/1.70  MUC search           : 0.00
% 3.13/1.70  Cooper               : 0.00
% 3.13/1.70  Total                : 0.87
% 3.13/1.70  Index Insertion      : 0.00
% 3.13/1.70  Index Deletion       : 0.00
% 3.13/1.70  Index Matching       : 0.00
% 3.13/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
