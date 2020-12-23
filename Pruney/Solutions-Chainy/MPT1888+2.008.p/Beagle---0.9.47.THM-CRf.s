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
% DateTime   : Thu Dec  3 10:30:21 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 332 expanded)
%              Number of leaves         :   38 ( 124 expanded)
%              Depth                    :   16
%              Number of atoms          :  213 (1016 expanded)
%              Number of equality atoms :   17 ( 147 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

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

tff(f_153,negated_conjecture,(
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

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

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

tff(f_52,axiom,(
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

tff(f_58,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(f_114,axiom,(
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

tff(f_133,axiom,(
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

tff(c_46,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_18,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_86,plain,(
    ! [A_61,B_62] :
      ( k6_domain_1(A_61,B_62) = k1_tarski(B_62)
      | ~ m1_subset_1(B_62,A_61)
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_97,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_42,c_86])).

tff(c_99,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_20,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(u1_struct_0(A_17))
      | ~ l1_struct_0(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_102,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_99,c_20])).

tff(c_105,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_102])).

tff(c_108,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_105])).

tff(c_112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_108])).

tff(c_114,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_98,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_86])).

tff(c_122,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_98])).

tff(c_113,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_38,plain,(
    k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5')) != k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_116,plain,(
    k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')) != k2_pre_topc('#skF_3',k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_38])).

tff(c_127,plain,(
    k2_pre_topc('#skF_3',k1_tarski('#skF_5')) != k2_pre_topc('#skF_3',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_116])).

tff(c_71,plain,(
    ! [A_52,B_53] :
      ( r1_xboole_0(k1_tarski(A_52),B_53)
      | r2_hidden(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_74,plain,(
    ! [B_53,A_52] :
      ( r1_xboole_0(B_53,k1_tarski(A_52))
      | r2_hidden(A_52,B_53) ) ),
    inference(resolution,[status(thm)],[c_71,c_6])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | v1_xboole_0(B_13)
      | ~ m1_subset_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(k1_tarski(A_10),k1_zfmisc_1(B_11))
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k2_pre_topc(A_14,B_15),k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_50,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_48,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_139,plain,(
    ! [A_67,B_68] :
      ( v4_pre_topc(k2_pre_topc(A_67,B_68),A_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_149,plain,(
    ! [A_67,A_10] :
      ( v4_pre_topc(k2_pre_topc(A_67,k1_tarski(A_10)),A_67)
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67)
      | ~ r2_hidden(A_10,u1_struct_0(A_67)) ) ),
    inference(resolution,[status(thm)],[c_12,c_139])).

tff(c_161,plain,(
    ! [B_74,A_75] :
      ( v3_pre_topc(B_74,A_75)
      | ~ v4_pre_topc(B_74,A_75)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ v3_tdlat_3(A_75)
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_197,plain,(
    ! [A_84,B_85] :
      ( v3_pre_topc(k2_pre_topc(A_84,B_85),A_84)
      | ~ v4_pre_topc(k2_pre_topc(A_84,B_85),A_84)
      | ~ v3_tdlat_3(A_84)
      | ~ v2_pre_topc(A_84)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(resolution,[status(thm)],[c_16,c_161])).

tff(c_216,plain,(
    ! [A_88,A_89] :
      ( v3_pre_topc(k2_pre_topc(A_88,k1_tarski(A_89)),A_88)
      | ~ v3_tdlat_3(A_88)
      | ~ m1_subset_1(k1_tarski(A_89),k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88)
      | ~ r2_hidden(A_89,u1_struct_0(A_88)) ) ),
    inference(resolution,[status(thm)],[c_149,c_197])).

tff(c_220,plain,(
    ! [A_88,A_10] :
      ( v3_pre_topc(k2_pre_topc(A_88,k1_tarski(A_10)),A_88)
      | ~ v3_tdlat_3(A_88)
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88)
      | ~ r2_hidden(A_10,u1_struct_0(A_88)) ) ),
    inference(resolution,[status(thm)],[c_12,c_216])).

tff(c_186,plain,(
    ! [B_81,A_82,C_83] :
      ( r1_xboole_0(B_81,k2_pre_topc(A_82,C_83))
      | ~ v3_pre_topc(B_81,A_82)
      | ~ r1_xboole_0(B_81,C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_282,plain,(
    ! [B_105,A_106,A_107] :
      ( r1_xboole_0(B_105,k2_pre_topc(A_106,k1_tarski(A_107)))
      | ~ v3_pre_topc(B_105,A_106)
      | ~ r1_xboole_0(B_105,k1_tarski(A_107))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106)
      | ~ r2_hidden(A_107,u1_struct_0(A_106)) ) ),
    inference(resolution,[status(thm)],[c_12,c_186])).

tff(c_40,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')),k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_115,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')),k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_40])).

tff(c_128,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_115])).

tff(c_285,plain,
    ( ~ v3_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),'#skF_3')
    | ~ r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_tarski('#skF_5'))
    | ~ m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ r2_hidden('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_282,c_128])).

tff(c_290,plain,
    ( ~ v3_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),'#skF_3')
    | ~ r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_tarski('#skF_5'))
    | ~ m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ r2_hidden('#skF_5',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_285])).

tff(c_292,plain,(
    ~ r2_hidden('#skF_5',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_290])).

tff(c_295,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14,c_292])).

tff(c_298,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_295])).

tff(c_300,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_298])).

tff(c_301,plain,
    ( ~ m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_tarski('#skF_5'))
    | ~ v3_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_290])).

tff(c_308,plain,(
    ~ v3_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_301])).

tff(c_311,plain,
    ( ~ v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ r2_hidden('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_220,c_308])).

tff(c_314,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_48,c_311])).

tff(c_317,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14,c_314])).

tff(c_320,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_317])).

tff(c_322,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_320])).

tff(c_323,plain,
    ( ~ r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_tarski('#skF_5'))
    | ~ m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_301])).

tff(c_325,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_323])).

tff(c_332,plain,
    ( ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_325])).

tff(c_335,plain,(
    ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_332])).

tff(c_339,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_335])).

tff(c_342,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14,c_339])).

tff(c_345,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_342])).

tff(c_347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_345])).

tff(c_348,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_tarski('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_323])).

tff(c_354,plain,(
    r2_hidden('#skF_5',k2_pre_topc('#skF_3',k1_tarski('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_74,c_348])).

tff(c_226,plain,(
    ! [A_94,C_95,B_96] :
      ( k2_pre_topc(A_94,k6_domain_1(u1_struct_0(A_94),C_95)) = k2_pre_topc(A_94,k6_domain_1(u1_struct_0(A_94),B_96))
      | ~ r2_hidden(B_96,k2_pre_topc(A_94,k6_domain_1(u1_struct_0(A_94),C_95)))
      | ~ m1_subset_1(C_95,u1_struct_0(A_94))
      | ~ m1_subset_1(B_96,u1_struct_0(A_94))
      | ~ l1_pre_topc(A_94)
      | ~ v3_tdlat_3(A_94)
      | ~ v2_pre_topc(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_229,plain,(
    ! [B_96] :
      ( k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),B_96)) = k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))
      | ~ r2_hidden(B_96,k2_pre_topc('#skF_3',k1_tarski('#skF_4')))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_96,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_226])).

tff(c_242,plain,(
    ! [B_96] :
      ( k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),B_96)) = k2_pre_topc('#skF_3',k1_tarski('#skF_4'))
      | ~ r2_hidden(B_96,k2_pre_topc('#skF_3',k1_tarski('#skF_4')))
      | ~ m1_subset_1(B_96,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_122,c_229])).

tff(c_243,plain,(
    ! [B_96] :
      ( k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),B_96)) = k2_pre_topc('#skF_3',k1_tarski('#skF_4'))
      | ~ r2_hidden(B_96,k2_pre_topc('#skF_3',k1_tarski('#skF_4')))
      | ~ m1_subset_1(B_96,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_242])).

tff(c_357,plain,
    ( k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5')) = k2_pre_topc('#skF_3',k1_tarski('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_354,c_243])).

tff(c_363,plain,(
    k2_pre_topc('#skF_3',k1_tarski('#skF_5')) = k2_pre_topc('#skF_3',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_113,c_357])).

tff(c_365,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_363])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:37:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.37  
% 2.81/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.38  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 2.81/1.38  
% 2.81/1.38  %Foreground sorts:
% 2.81/1.38  
% 2.81/1.38  
% 2.81/1.38  %Background operators:
% 2.81/1.38  
% 2.81/1.38  
% 2.81/1.38  %Foreground operators:
% 2.81/1.38  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.81/1.38  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.81/1.38  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.81/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.81/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.81/1.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.81/1.38  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.81/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.81/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.81/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.81/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.81/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.81/1.38  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.81/1.38  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.81/1.38  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.81/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.81/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.38  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.81/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.81/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.81/1.38  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.81/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.81/1.38  
% 2.81/1.40  tff(f_153, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_xboole_0(k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)), k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) | (k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tex_2)).
% 2.81/1.40  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.81/1.40  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.81/1.40  tff(f_70, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.81/1.40  tff(f_42, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.81/1.40  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.81/1.40  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.81/1.40  tff(f_46, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 2.81/1.40  tff(f_58, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.81/1.40  tff(f_85, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 2.81/1.40  tff(f_98, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tdlat_3)).
% 2.81/1.40  tff(f_114, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_xboole_0(B, C) & v3_pre_topc(B, A)) => r1_xboole_0(B, k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_tsep_1)).
% 2.81/1.40  tff(f_133, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) => (k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tex_2)).
% 2.81/1.40  tff(c_46, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.81/1.40  tff(c_18, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.81/1.40  tff(c_52, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.81/1.40  tff(c_42, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.81/1.40  tff(c_86, plain, (![A_61, B_62]: (k6_domain_1(A_61, B_62)=k1_tarski(B_62) | ~m1_subset_1(B_62, A_61) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.81/1.40  tff(c_97, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_86])).
% 2.81/1.40  tff(c_99, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_97])).
% 2.81/1.40  tff(c_20, plain, (![A_17]: (~v1_xboole_0(u1_struct_0(A_17)) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.81/1.40  tff(c_102, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_99, c_20])).
% 2.81/1.40  tff(c_105, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_52, c_102])).
% 2.81/1.40  tff(c_108, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_18, c_105])).
% 2.81/1.40  tff(c_112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_108])).
% 2.81/1.40  tff(c_114, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_97])).
% 2.81/1.40  tff(c_44, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.81/1.40  tff(c_98, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_86])).
% 2.81/1.40  tff(c_122, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_114, c_98])).
% 2.81/1.40  tff(c_113, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_97])).
% 2.81/1.40  tff(c_38, plain, (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5'))!=k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.81/1.40  tff(c_116, plain, (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'))!=k2_pre_topc('#skF_3', k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_38])).
% 2.81/1.40  tff(c_127, plain, (k2_pre_topc('#skF_3', k1_tarski('#skF_5'))!=k2_pre_topc('#skF_3', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_116])).
% 2.81/1.40  tff(c_71, plain, (![A_52, B_53]: (r1_xboole_0(k1_tarski(A_52), B_53) | r2_hidden(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.81/1.40  tff(c_6, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.81/1.40  tff(c_74, plain, (![B_53, A_52]: (r1_xboole_0(B_53, k1_tarski(A_52)) | r2_hidden(A_52, B_53))), inference(resolution, [status(thm)], [c_71, c_6])).
% 2.81/1.40  tff(c_14, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | v1_xboole_0(B_13) | ~m1_subset_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.81/1.40  tff(c_12, plain, (![A_10, B_11]: (m1_subset_1(k1_tarski(A_10), k1_zfmisc_1(B_11)) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.81/1.40  tff(c_16, plain, (![A_14, B_15]: (m1_subset_1(k2_pre_topc(A_14, B_15), k1_zfmisc_1(u1_struct_0(A_14))) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.81/1.40  tff(c_50, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.81/1.40  tff(c_48, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.81/1.40  tff(c_139, plain, (![A_67, B_68]: (v4_pre_topc(k2_pre_topc(A_67, B_68), A_67) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.81/1.40  tff(c_149, plain, (![A_67, A_10]: (v4_pre_topc(k2_pre_topc(A_67, k1_tarski(A_10)), A_67) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67) | ~r2_hidden(A_10, u1_struct_0(A_67)))), inference(resolution, [status(thm)], [c_12, c_139])).
% 2.81/1.40  tff(c_161, plain, (![B_74, A_75]: (v3_pre_topc(B_74, A_75) | ~v4_pre_topc(B_74, A_75) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_75))) | ~v3_tdlat_3(A_75) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.81/1.40  tff(c_197, plain, (![A_84, B_85]: (v3_pre_topc(k2_pre_topc(A_84, B_85), A_84) | ~v4_pre_topc(k2_pre_topc(A_84, B_85), A_84) | ~v3_tdlat_3(A_84) | ~v2_pre_topc(A_84) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84))), inference(resolution, [status(thm)], [c_16, c_161])).
% 2.81/1.40  tff(c_216, plain, (![A_88, A_89]: (v3_pre_topc(k2_pre_topc(A_88, k1_tarski(A_89)), A_88) | ~v3_tdlat_3(A_88) | ~m1_subset_1(k1_tarski(A_89), k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88) | ~r2_hidden(A_89, u1_struct_0(A_88)))), inference(resolution, [status(thm)], [c_149, c_197])).
% 2.81/1.40  tff(c_220, plain, (![A_88, A_10]: (v3_pre_topc(k2_pre_topc(A_88, k1_tarski(A_10)), A_88) | ~v3_tdlat_3(A_88) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88) | ~r2_hidden(A_10, u1_struct_0(A_88)))), inference(resolution, [status(thm)], [c_12, c_216])).
% 2.81/1.40  tff(c_186, plain, (![B_81, A_82, C_83]: (r1_xboole_0(B_81, k2_pre_topc(A_82, C_83)) | ~v3_pre_topc(B_81, A_82) | ~r1_xboole_0(B_81, C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82) | ~v2_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.81/1.40  tff(c_282, plain, (![B_105, A_106, A_107]: (r1_xboole_0(B_105, k2_pre_topc(A_106, k1_tarski(A_107))) | ~v3_pre_topc(B_105, A_106) | ~r1_xboole_0(B_105, k1_tarski(A_107)) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106) | ~r2_hidden(A_107, u1_struct_0(A_106)))), inference(resolution, [status(thm)], [c_12, c_186])).
% 2.81/1.40  tff(c_40, plain, (~r1_xboole_0(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')), k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.81/1.40  tff(c_115, plain, (~r1_xboole_0(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')), k2_pre_topc('#skF_3', k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_40])).
% 2.81/1.40  tff(c_128, plain, (~r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k2_pre_topc('#skF_3', k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_115])).
% 2.81/1.40  tff(c_285, plain, (~v3_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), '#skF_3') | ~r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_tarski('#skF_5')) | ~m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~r2_hidden('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_282, c_128])).
% 2.81/1.40  tff(c_290, plain, (~v3_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), '#skF_3') | ~r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_tarski('#skF_5')) | ~m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden('#skF_5', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_285])).
% 2.81/1.40  tff(c_292, plain, (~r2_hidden('#skF_5', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_290])).
% 2.81/1.40  tff(c_295, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_14, c_292])).
% 2.81/1.40  tff(c_298, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_295])).
% 2.81/1.40  tff(c_300, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_298])).
% 2.81/1.40  tff(c_301, plain, (~m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_tarski('#skF_5')) | ~v3_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), '#skF_3')), inference(splitRight, [status(thm)], [c_290])).
% 2.81/1.40  tff(c_308, plain, (~v3_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_301])).
% 2.81/1.40  tff(c_311, plain, (~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~r2_hidden('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_220, c_308])).
% 2.81/1.40  tff(c_314, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_48, c_311])).
% 2.81/1.40  tff(c_317, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_14, c_314])).
% 2.81/1.40  tff(c_320, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_317])).
% 2.81/1.40  tff(c_322, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_320])).
% 2.81/1.40  tff(c_323, plain, (~r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_tarski('#skF_5')) | ~m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_301])).
% 2.81/1.40  tff(c_325, plain, (~m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_323])).
% 2.81/1.40  tff(c_332, plain, (~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_16, c_325])).
% 2.81/1.40  tff(c_335, plain, (~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_332])).
% 2.81/1.40  tff(c_339, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_12, c_335])).
% 2.81/1.40  tff(c_342, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_14, c_339])).
% 2.81/1.40  tff(c_345, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_342])).
% 2.81/1.40  tff(c_347, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_345])).
% 2.81/1.40  tff(c_348, plain, (~r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_tarski('#skF_5'))), inference(splitRight, [status(thm)], [c_323])).
% 2.81/1.40  tff(c_354, plain, (r2_hidden('#skF_5', k2_pre_topc('#skF_3', k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_74, c_348])).
% 2.81/1.40  tff(c_226, plain, (![A_94, C_95, B_96]: (k2_pre_topc(A_94, k6_domain_1(u1_struct_0(A_94), C_95))=k2_pre_topc(A_94, k6_domain_1(u1_struct_0(A_94), B_96)) | ~r2_hidden(B_96, k2_pre_topc(A_94, k6_domain_1(u1_struct_0(A_94), C_95))) | ~m1_subset_1(C_95, u1_struct_0(A_94)) | ~m1_subset_1(B_96, u1_struct_0(A_94)) | ~l1_pre_topc(A_94) | ~v3_tdlat_3(A_94) | ~v2_pre_topc(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.81/1.40  tff(c_229, plain, (![B_96]: (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), B_96))=k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')) | ~r2_hidden(B_96, k2_pre_topc('#skF_3', k1_tarski('#skF_4'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1(B_96, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_122, c_226])).
% 2.81/1.40  tff(c_242, plain, (![B_96]: (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), B_96))=k2_pre_topc('#skF_3', k1_tarski('#skF_4')) | ~r2_hidden(B_96, k2_pre_topc('#skF_3', k1_tarski('#skF_4'))) | ~m1_subset_1(B_96, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_122, c_229])).
% 2.81/1.40  tff(c_243, plain, (![B_96]: (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), B_96))=k2_pre_topc('#skF_3', k1_tarski('#skF_4')) | ~r2_hidden(B_96, k2_pre_topc('#skF_3', k1_tarski('#skF_4'))) | ~m1_subset_1(B_96, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_52, c_242])).
% 2.81/1.40  tff(c_357, plain, (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5'))=k2_pre_topc('#skF_3', k1_tarski('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_354, c_243])).
% 2.81/1.40  tff(c_363, plain, (k2_pre_topc('#skF_3', k1_tarski('#skF_5'))=k2_pre_topc('#skF_3', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_113, c_357])).
% 2.81/1.40  tff(c_365, plain, $false, inference(negUnitSimplification, [status(thm)], [c_127, c_363])).
% 2.81/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.40  
% 2.81/1.40  Inference rules
% 2.81/1.40  ----------------------
% 2.81/1.40  #Ref     : 0
% 2.81/1.40  #Sup     : 60
% 2.81/1.40  #Fact    : 0
% 2.81/1.40  #Define  : 0
% 2.81/1.40  #Split   : 6
% 2.81/1.40  #Chain   : 0
% 2.81/1.40  #Close   : 0
% 2.81/1.40  
% 2.81/1.40  Ordering : KBO
% 2.81/1.40  
% 2.81/1.40  Simplification rules
% 2.81/1.40  ----------------------
% 2.81/1.40  #Subsume      : 5
% 2.81/1.40  #Demod        : 28
% 2.81/1.40  #Tautology    : 18
% 2.81/1.40  #SimpNegUnit  : 8
% 2.81/1.40  #BackRed      : 2
% 2.81/1.40  
% 2.81/1.40  #Partial instantiations: 0
% 2.81/1.40  #Strategies tried      : 1
% 2.81/1.40  
% 2.81/1.40  Timing (in seconds)
% 2.81/1.40  ----------------------
% 2.81/1.40  Preprocessing        : 0.34
% 2.81/1.40  Parsing              : 0.19
% 2.81/1.40  CNF conversion       : 0.02
% 2.81/1.40  Main loop            : 0.29
% 2.81/1.40  Inferencing          : 0.11
% 2.81/1.40  Reduction            : 0.08
% 2.81/1.40  Demodulation         : 0.05
% 2.81/1.40  BG Simplification    : 0.02
% 2.81/1.40  Subsumption          : 0.05
% 2.81/1.40  Abstraction          : 0.01
% 2.81/1.40  MUC search           : 0.00
% 2.81/1.40  Cooper               : 0.00
% 2.81/1.40  Total                : 0.67
% 2.81/1.40  Index Insertion      : 0.00
% 2.81/1.40  Index Deletion       : 0.00
% 2.81/1.40  Index Matching       : 0.00
% 2.81/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
