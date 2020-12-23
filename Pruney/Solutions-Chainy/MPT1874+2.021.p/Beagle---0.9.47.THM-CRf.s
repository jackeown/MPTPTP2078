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
% DateTime   : Thu Dec  3 10:29:39 EST 2020

% Result     : Theorem 4.14s
% Output     : CNFRefutation 4.43s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 415 expanded)
%              Number of leaves         :   38 ( 158 expanded)
%              Depth                    :   15
%              Number of atoms          :  213 (1093 expanded)
%              Number of equality atoms :   28 ( 158 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tex_2(B,A)
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( r2_hidden(C,B)
                   => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C))) = k6_domain_1(u1_struct_0(A),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tex_2)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r1_tarski(C,B)
                 => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_24,plain,(
    ! [A_20] :
      ( l1_struct_0(A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_63,plain,(
    ! [A_40] :
      ( u1_struct_0(A_40) = k2_struct_0(A_40)
      | ~ l1_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_68,plain,(
    ! [A_41] :
      ( u1_struct_0(A_41) = k2_struct_0(A_41)
      | ~ l1_pre_topc(A_41) ) ),
    inference(resolution,[status(thm)],[c_24,c_63])).

tff(c_72,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_68])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_75,plain,(
    m1_subset_1('#skF_5',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_42])).

tff(c_132,plain,(
    ! [A_63,B_64] :
      ( k6_domain_1(A_63,B_64) = k1_tarski(B_64)
      | ~ m1_subset_1(B_64,A_63)
      | v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_144,plain,
    ( k6_domain_1(k2_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_75,c_132])).

tff(c_145,plain,(
    v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_26,plain,(
    ! [A_21] :
      ( ~ v1_xboole_0(k2_struct_0(A_21))
      | ~ l1_struct_0(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_148,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_145,c_26])).

tff(c_151,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_148])).

tff(c_154,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_151])).

tff(c_158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_154])).

tff(c_160,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( r2_hidden(A_17,B_18)
      | v1_xboole_0(B_18)
      | ~ m1_subset_1(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k1_tarski(A_15),k1_zfmisc_1(B_16))
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_50,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_229,plain,(
    ! [A_83,B_84] :
      ( r1_tarski('#skF_2'(A_83,B_84),B_84)
      | v2_tex_2(B_84,A_83)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_234,plain,(
    ! [B_84] :
      ( r1_tarski('#skF_2'('#skF_3',B_84),B_84)
      | v2_tex_2(B_84,'#skF_3')
      | ~ m1_subset_1(B_84,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_229])).

tff(c_237,plain,(
    ! [B_84] :
      ( r1_tarski('#skF_2'('#skF_3',B_84),B_84)
      | v2_tex_2(B_84,'#skF_3')
      | ~ m1_subset_1(B_84,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_234])).

tff(c_279,plain,(
    ! [B_89] :
      ( r1_tarski('#skF_2'('#skF_3',B_89),B_89)
      | v2_tex_2(B_89,'#skF_3')
      | ~ m1_subset_1(B_89,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_237])).

tff(c_285,plain,(
    ! [A_15] :
      ( r1_tarski('#skF_2'('#skF_3',k1_tarski(A_15)),k1_tarski(A_15))
      | v2_tex_2(k1_tarski(A_15),'#skF_3')
      | ~ r2_hidden(A_15,k2_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_18,c_279])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_90,plain,(
    ! [A_53,B_54] :
      ( ~ r2_hidden('#skF_1'(A_53,B_54),B_54)
      | r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_101,plain,(
    ! [A_55] : r1_tarski(A_55,A_55) ),
    inference(resolution,[status(thm)],[c_6,c_90])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | ~ r1_tarski(k1_tarski(A_7),B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_106,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(resolution,[status(thm)],[c_101,c_10])).

tff(c_40,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(k1_tarski(A_7),B_8)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_108,plain,(
    ! [C_57,B_58,A_59] :
      ( r2_hidden(C_57,B_58)
      | ~ r2_hidden(C_57,A_59)
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_185,plain,(
    ! [A_73,B_74,B_75] :
      ( r2_hidden('#skF_1'(A_73,B_74),B_75)
      | ~ r1_tarski(A_73,B_75)
      | r1_tarski(A_73,B_74) ) ),
    inference(resolution,[status(thm)],[c_6,c_108])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_404,plain,(
    ! [A_102,B_103,B_104,B_105] :
      ( r2_hidden('#skF_1'(A_102,B_103),B_104)
      | ~ r1_tarski(B_105,B_104)
      | ~ r1_tarski(A_102,B_105)
      | r1_tarski(A_102,B_103) ) ),
    inference(resolution,[status(thm)],[c_185,c_2])).

tff(c_450,plain,(
    ! [A_109,B_110,B_111,A_112] :
      ( r2_hidden('#skF_1'(A_109,B_110),B_111)
      | ~ r1_tarski(A_109,k1_tarski(A_112))
      | r1_tarski(A_109,B_110)
      | ~ r2_hidden(A_112,B_111) ) ),
    inference(resolution,[status(thm)],[c_12,c_404])).

tff(c_557,plain,(
    ! [A_127,B_128,B_129,A_130] :
      ( r2_hidden('#skF_1'(k1_tarski(A_127),B_128),B_129)
      | r1_tarski(k1_tarski(A_127),B_128)
      | ~ r2_hidden(A_130,B_129)
      | ~ r2_hidden(A_127,k1_tarski(A_130)) ) ),
    inference(resolution,[status(thm)],[c_12,c_450])).

tff(c_579,plain,(
    ! [A_131,B_132] :
      ( r2_hidden('#skF_1'(k1_tarski(A_131),B_132),'#skF_4')
      | r1_tarski(k1_tarski(A_131),B_132)
      | ~ r2_hidden(A_131,k1_tarski('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_40,c_557])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_591,plain,(
    ! [A_133] :
      ( r1_tarski(k1_tarski(A_133),'#skF_4')
      | ~ r2_hidden(A_133,k1_tarski('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_579,c_4])).

tff(c_619,plain,(
    r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_106,c_591])).

tff(c_192,plain,(
    ! [A_73,B_74,B_2,B_75] :
      ( r2_hidden('#skF_1'(A_73,B_74),B_2)
      | ~ r1_tarski(B_75,B_2)
      | ~ r1_tarski(A_73,B_75)
      | r1_tarski(A_73,B_74) ) ),
    inference(resolution,[status(thm)],[c_185,c_2])).

tff(c_698,plain,(
    ! [A_141,B_142] :
      ( r2_hidden('#skF_1'(A_141,B_142),'#skF_4')
      | ~ r1_tarski(A_141,k1_tarski('#skF_5'))
      | r1_tarski(A_141,B_142) ) ),
    inference(resolution,[status(thm)],[c_619,c_192])).

tff(c_710,plain,(
    ! [A_143] :
      ( ~ r1_tarski(A_143,k1_tarski('#skF_5'))
      | r1_tarski(A_143,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_698,c_4])).

tff(c_723,plain,
    ( r1_tarski('#skF_2'('#skF_3',k1_tarski('#skF_5')),'#skF_4')
    | v2_tex_2(k1_tarski('#skF_5'),'#skF_3')
    | ~ r2_hidden('#skF_5',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_285,c_710])).

tff(c_898,plain,(
    ~ r2_hidden('#skF_5',k2_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_723])).

tff(c_904,plain,
    ( v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_898])).

tff(c_908,plain,(
    v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_904])).

tff(c_910,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_908])).

tff(c_912,plain,(
    r2_hidden('#skF_5',k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_723])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_74,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_46])).

tff(c_44,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_640,plain,(
    ! [A_134,B_135,C_136] :
      ( k9_subset_1(u1_struct_0(A_134),B_135,k2_pre_topc(A_134,C_136)) = C_136
      | ~ r1_tarski(C_136,B_135)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ v2_tex_2(B_135,A_134)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134)
      | v2_struct_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1568,plain,(
    ! [A_199,B_200,A_201] :
      ( k9_subset_1(u1_struct_0(A_199),B_200,k2_pre_topc(A_199,k1_tarski(A_201))) = k1_tarski(A_201)
      | ~ r1_tarski(k1_tarski(A_201),B_200)
      | ~ v2_tex_2(B_200,A_199)
      | ~ m1_subset_1(B_200,k1_zfmisc_1(u1_struct_0(A_199)))
      | ~ l1_pre_topc(A_199)
      | ~ v2_pre_topc(A_199)
      | v2_struct_0(A_199)
      | ~ r2_hidden(A_201,u1_struct_0(A_199)) ) ),
    inference(resolution,[status(thm)],[c_18,c_640])).

tff(c_1593,plain,(
    ! [B_200,A_201] :
      ( k9_subset_1(k2_struct_0('#skF_3'),B_200,k2_pre_topc('#skF_3',k1_tarski(A_201))) = k1_tarski(A_201)
      | ~ r1_tarski(k1_tarski(A_201),B_200)
      | ~ v2_tex_2(B_200,'#skF_3')
      | ~ m1_subset_1(B_200,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(A_201,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_1568])).

tff(c_1597,plain,(
    ! [B_200,A_201] :
      ( k9_subset_1(k2_struct_0('#skF_3'),B_200,k2_pre_topc('#skF_3',k1_tarski(A_201))) = k1_tarski(A_201)
      | ~ r1_tarski(k1_tarski(A_201),B_200)
      | ~ v2_tex_2(B_200,'#skF_3')
      | ~ m1_subset_1(B_200,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(A_201,k2_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_50,c_48,c_72,c_1593])).

tff(c_1616,plain,(
    ! [B_203,A_204] :
      ( k9_subset_1(k2_struct_0('#skF_3'),B_203,k2_pre_topc('#skF_3',k1_tarski(A_204))) = k1_tarski(A_204)
      | ~ r1_tarski(k1_tarski(A_204),B_203)
      | ~ v2_tex_2(B_203,'#skF_3')
      | ~ m1_subset_1(B_203,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ r2_hidden(A_204,k2_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1597])).

tff(c_167,plain,(
    ! [A_67,B_68,C_69] :
      ( k9_subset_1(A_67,B_68,C_69) = k3_xboole_0(B_68,C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_173,plain,(
    ! [B_68] : k9_subset_1(k2_struct_0('#skF_3'),B_68,'#skF_4') = k3_xboole_0(B_68,'#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_167])).

tff(c_201,plain,(
    ! [A_79,C_80,B_81] :
      ( k9_subset_1(A_79,C_80,B_81) = k9_subset_1(A_79,B_81,C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_205,plain,(
    ! [B_81] : k9_subset_1(k2_struct_0('#skF_3'),B_81,'#skF_4') = k9_subset_1(k2_struct_0('#skF_3'),'#skF_4',B_81) ),
    inference(resolution,[status(thm)],[c_74,c_201])).

tff(c_208,plain,(
    ! [B_81] : k9_subset_1(k2_struct_0('#skF_3'),'#skF_4',B_81) = k3_xboole_0(B_81,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_205])).

tff(c_1635,plain,(
    ! [A_204] :
      ( k3_xboole_0(k2_pre_topc('#skF_3',k1_tarski(A_204)),'#skF_4') = k1_tarski(A_204)
      | ~ r1_tarski(k1_tarski(A_204),'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ r2_hidden(A_204,k2_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1616,c_208])).

tff(c_1666,plain,(
    ! [A_207] :
      ( k3_xboole_0(k2_pre_topc('#skF_3',k1_tarski(A_207)),'#skF_4') = k1_tarski(A_207)
      | ~ r1_tarski(k1_tarski(A_207),'#skF_4')
      | ~ r2_hidden(A_207,k2_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_44,c_1635])).

tff(c_159,plain,(
    k6_domain_1(k2_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_38,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_73,plain,(
    k9_subset_1(k2_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k6_domain_1(k2_struct_0('#skF_3'),'#skF_5'))) != k6_domain_1(k2_struct_0('#skF_3'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_72,c_72,c_38])).

tff(c_161,plain,(
    k9_subset_1(k2_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) != k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_159,c_73])).

tff(c_209,plain,(
    k3_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_5')),'#skF_4') != k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_161])).

tff(c_1672,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_5',k2_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1666,c_209])).

tff(c_1680,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_912,c_619,c_1672])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:00:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.14/1.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.38/1.75  
% 4.38/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.38/1.75  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.38/1.75  
% 4.38/1.75  %Foreground sorts:
% 4.38/1.75  
% 4.38/1.75  
% 4.38/1.75  %Background operators:
% 4.38/1.75  
% 4.38/1.75  
% 4.38/1.75  %Foreground operators:
% 4.38/1.75  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.38/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.38/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.38/1.75  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.38/1.75  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.38/1.75  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.38/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.38/1.75  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.38/1.75  tff('#skF_5', type, '#skF_5': $i).
% 4.38/1.75  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.38/1.75  tff('#skF_3', type, '#skF_3': $i).
% 4.38/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.38/1.75  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.38/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.38/1.75  tff('#skF_4', type, '#skF_4': $i).
% 4.38/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.38/1.75  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.38/1.75  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.38/1.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.38/1.75  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.38/1.75  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.38/1.75  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.38/1.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.38/1.75  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.38/1.75  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.38/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.38/1.75  
% 4.43/1.77  tff(f_118, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_tex_2)).
% 4.43/1.77  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.43/1.77  tff(f_60, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.43/1.77  tff(f_79, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.43/1.77  tff(f_72, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 4.43/1.77  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.43/1.77  tff(f_50, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 4.43/1.77  tff(f_98, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 4.43/1.77  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.43/1.77  tff(f_38, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.43/1.77  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.43/1.77  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 4.43/1.77  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.43/1.77  tff(c_24, plain, (![A_20]: (l1_struct_0(A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.43/1.77  tff(c_52, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.43/1.77  tff(c_63, plain, (![A_40]: (u1_struct_0(A_40)=k2_struct_0(A_40) | ~l1_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.43/1.77  tff(c_68, plain, (![A_41]: (u1_struct_0(A_41)=k2_struct_0(A_41) | ~l1_pre_topc(A_41))), inference(resolution, [status(thm)], [c_24, c_63])).
% 4.43/1.77  tff(c_72, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_68])).
% 4.43/1.77  tff(c_42, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.43/1.77  tff(c_75, plain, (m1_subset_1('#skF_5', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_42])).
% 4.43/1.77  tff(c_132, plain, (![A_63, B_64]: (k6_domain_1(A_63, B_64)=k1_tarski(B_64) | ~m1_subset_1(B_64, A_63) | v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.43/1.77  tff(c_144, plain, (k6_domain_1(k2_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_75, c_132])).
% 4.43/1.77  tff(c_145, plain, (v1_xboole_0(k2_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_144])).
% 4.43/1.77  tff(c_26, plain, (![A_21]: (~v1_xboole_0(k2_struct_0(A_21)) | ~l1_struct_0(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.43/1.77  tff(c_148, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_145, c_26])).
% 4.43/1.77  tff(c_151, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_52, c_148])).
% 4.43/1.77  tff(c_154, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_24, c_151])).
% 4.43/1.77  tff(c_158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_154])).
% 4.43/1.77  tff(c_160, plain, (~v1_xboole_0(k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_144])).
% 4.43/1.77  tff(c_20, plain, (![A_17, B_18]: (r2_hidden(A_17, B_18) | v1_xboole_0(B_18) | ~m1_subset_1(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.43/1.77  tff(c_18, plain, (![A_15, B_16]: (m1_subset_1(k1_tarski(A_15), k1_zfmisc_1(B_16)) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.43/1.77  tff(c_50, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.43/1.77  tff(c_229, plain, (![A_83, B_84]: (r1_tarski('#skF_2'(A_83, B_84), B_84) | v2_tex_2(B_84, A_83) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83) | ~v2_pre_topc(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.43/1.77  tff(c_234, plain, (![B_84]: (r1_tarski('#skF_2'('#skF_3', B_84), B_84) | v2_tex_2(B_84, '#skF_3') | ~m1_subset_1(B_84, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_229])).
% 4.43/1.77  tff(c_237, plain, (![B_84]: (r1_tarski('#skF_2'('#skF_3', B_84), B_84) | v2_tex_2(B_84, '#skF_3') | ~m1_subset_1(B_84, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_234])).
% 4.43/1.77  tff(c_279, plain, (![B_89]: (r1_tarski('#skF_2'('#skF_3', B_89), B_89) | v2_tex_2(B_89, '#skF_3') | ~m1_subset_1(B_89, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_237])).
% 4.43/1.77  tff(c_285, plain, (![A_15]: (r1_tarski('#skF_2'('#skF_3', k1_tarski(A_15)), k1_tarski(A_15)) | v2_tex_2(k1_tarski(A_15), '#skF_3') | ~r2_hidden(A_15, k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_18, c_279])).
% 4.43/1.77  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.43/1.77  tff(c_90, plain, (![A_53, B_54]: (~r2_hidden('#skF_1'(A_53, B_54), B_54) | r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.43/1.77  tff(c_101, plain, (![A_55]: (r1_tarski(A_55, A_55))), inference(resolution, [status(thm)], [c_6, c_90])).
% 4.43/1.77  tff(c_10, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | ~r1_tarski(k1_tarski(A_7), B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.43/1.77  tff(c_106, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(resolution, [status(thm)], [c_101, c_10])).
% 4.43/1.77  tff(c_40, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.43/1.77  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(k1_tarski(A_7), B_8) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.43/1.77  tff(c_108, plain, (![C_57, B_58, A_59]: (r2_hidden(C_57, B_58) | ~r2_hidden(C_57, A_59) | ~r1_tarski(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.43/1.77  tff(c_185, plain, (![A_73, B_74, B_75]: (r2_hidden('#skF_1'(A_73, B_74), B_75) | ~r1_tarski(A_73, B_75) | r1_tarski(A_73, B_74))), inference(resolution, [status(thm)], [c_6, c_108])).
% 4.43/1.77  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.43/1.77  tff(c_404, plain, (![A_102, B_103, B_104, B_105]: (r2_hidden('#skF_1'(A_102, B_103), B_104) | ~r1_tarski(B_105, B_104) | ~r1_tarski(A_102, B_105) | r1_tarski(A_102, B_103))), inference(resolution, [status(thm)], [c_185, c_2])).
% 4.43/1.77  tff(c_450, plain, (![A_109, B_110, B_111, A_112]: (r2_hidden('#skF_1'(A_109, B_110), B_111) | ~r1_tarski(A_109, k1_tarski(A_112)) | r1_tarski(A_109, B_110) | ~r2_hidden(A_112, B_111))), inference(resolution, [status(thm)], [c_12, c_404])).
% 4.43/1.77  tff(c_557, plain, (![A_127, B_128, B_129, A_130]: (r2_hidden('#skF_1'(k1_tarski(A_127), B_128), B_129) | r1_tarski(k1_tarski(A_127), B_128) | ~r2_hidden(A_130, B_129) | ~r2_hidden(A_127, k1_tarski(A_130)))), inference(resolution, [status(thm)], [c_12, c_450])).
% 4.43/1.77  tff(c_579, plain, (![A_131, B_132]: (r2_hidden('#skF_1'(k1_tarski(A_131), B_132), '#skF_4') | r1_tarski(k1_tarski(A_131), B_132) | ~r2_hidden(A_131, k1_tarski('#skF_5')))), inference(resolution, [status(thm)], [c_40, c_557])).
% 4.43/1.77  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.43/1.77  tff(c_591, plain, (![A_133]: (r1_tarski(k1_tarski(A_133), '#skF_4') | ~r2_hidden(A_133, k1_tarski('#skF_5')))), inference(resolution, [status(thm)], [c_579, c_4])).
% 4.43/1.77  tff(c_619, plain, (r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_106, c_591])).
% 4.43/1.77  tff(c_192, plain, (![A_73, B_74, B_2, B_75]: (r2_hidden('#skF_1'(A_73, B_74), B_2) | ~r1_tarski(B_75, B_2) | ~r1_tarski(A_73, B_75) | r1_tarski(A_73, B_74))), inference(resolution, [status(thm)], [c_185, c_2])).
% 4.43/1.77  tff(c_698, plain, (![A_141, B_142]: (r2_hidden('#skF_1'(A_141, B_142), '#skF_4') | ~r1_tarski(A_141, k1_tarski('#skF_5')) | r1_tarski(A_141, B_142))), inference(resolution, [status(thm)], [c_619, c_192])).
% 4.43/1.77  tff(c_710, plain, (![A_143]: (~r1_tarski(A_143, k1_tarski('#skF_5')) | r1_tarski(A_143, '#skF_4'))), inference(resolution, [status(thm)], [c_698, c_4])).
% 4.43/1.77  tff(c_723, plain, (r1_tarski('#skF_2'('#skF_3', k1_tarski('#skF_5')), '#skF_4') | v2_tex_2(k1_tarski('#skF_5'), '#skF_3') | ~r2_hidden('#skF_5', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_285, c_710])).
% 4.43/1.77  tff(c_898, plain, (~r2_hidden('#skF_5', k2_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_723])).
% 4.43/1.77  tff(c_904, plain, (v1_xboole_0(k2_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_898])).
% 4.43/1.77  tff(c_908, plain, (v1_xboole_0(k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_904])).
% 4.43/1.77  tff(c_910, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160, c_908])).
% 4.43/1.77  tff(c_912, plain, (r2_hidden('#skF_5', k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_723])).
% 4.43/1.77  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.43/1.77  tff(c_74, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_46])).
% 4.43/1.77  tff(c_44, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.43/1.77  tff(c_640, plain, (![A_134, B_135, C_136]: (k9_subset_1(u1_struct_0(A_134), B_135, k2_pre_topc(A_134, C_136))=C_136 | ~r1_tarski(C_136, B_135) | ~m1_subset_1(C_136, k1_zfmisc_1(u1_struct_0(A_134))) | ~v2_tex_2(B_135, A_134) | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0(A_134))) | ~l1_pre_topc(A_134) | ~v2_pre_topc(A_134) | v2_struct_0(A_134))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.43/1.77  tff(c_1568, plain, (![A_199, B_200, A_201]: (k9_subset_1(u1_struct_0(A_199), B_200, k2_pre_topc(A_199, k1_tarski(A_201)))=k1_tarski(A_201) | ~r1_tarski(k1_tarski(A_201), B_200) | ~v2_tex_2(B_200, A_199) | ~m1_subset_1(B_200, k1_zfmisc_1(u1_struct_0(A_199))) | ~l1_pre_topc(A_199) | ~v2_pre_topc(A_199) | v2_struct_0(A_199) | ~r2_hidden(A_201, u1_struct_0(A_199)))), inference(resolution, [status(thm)], [c_18, c_640])).
% 4.43/1.77  tff(c_1593, plain, (![B_200, A_201]: (k9_subset_1(k2_struct_0('#skF_3'), B_200, k2_pre_topc('#skF_3', k1_tarski(A_201)))=k1_tarski(A_201) | ~r1_tarski(k1_tarski(A_201), B_200) | ~v2_tex_2(B_200, '#skF_3') | ~m1_subset_1(B_200, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r2_hidden(A_201, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_72, c_1568])).
% 4.43/1.77  tff(c_1597, plain, (![B_200, A_201]: (k9_subset_1(k2_struct_0('#skF_3'), B_200, k2_pre_topc('#skF_3', k1_tarski(A_201)))=k1_tarski(A_201) | ~r1_tarski(k1_tarski(A_201), B_200) | ~v2_tex_2(B_200, '#skF_3') | ~m1_subset_1(B_200, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3') | ~r2_hidden(A_201, k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_50, c_48, c_72, c_1593])).
% 4.43/1.77  tff(c_1616, plain, (![B_203, A_204]: (k9_subset_1(k2_struct_0('#skF_3'), B_203, k2_pre_topc('#skF_3', k1_tarski(A_204)))=k1_tarski(A_204) | ~r1_tarski(k1_tarski(A_204), B_203) | ~v2_tex_2(B_203, '#skF_3') | ~m1_subset_1(B_203, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~r2_hidden(A_204, k2_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_52, c_1597])).
% 4.43/1.77  tff(c_167, plain, (![A_67, B_68, C_69]: (k9_subset_1(A_67, B_68, C_69)=k3_xboole_0(B_68, C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.43/1.77  tff(c_173, plain, (![B_68]: (k9_subset_1(k2_struct_0('#skF_3'), B_68, '#skF_4')=k3_xboole_0(B_68, '#skF_4'))), inference(resolution, [status(thm)], [c_74, c_167])).
% 4.43/1.77  tff(c_201, plain, (![A_79, C_80, B_81]: (k9_subset_1(A_79, C_80, B_81)=k9_subset_1(A_79, B_81, C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.43/1.77  tff(c_205, plain, (![B_81]: (k9_subset_1(k2_struct_0('#skF_3'), B_81, '#skF_4')=k9_subset_1(k2_struct_0('#skF_3'), '#skF_4', B_81))), inference(resolution, [status(thm)], [c_74, c_201])).
% 4.43/1.77  tff(c_208, plain, (![B_81]: (k9_subset_1(k2_struct_0('#skF_3'), '#skF_4', B_81)=k3_xboole_0(B_81, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_205])).
% 4.43/1.77  tff(c_1635, plain, (![A_204]: (k3_xboole_0(k2_pre_topc('#skF_3', k1_tarski(A_204)), '#skF_4')=k1_tarski(A_204) | ~r1_tarski(k1_tarski(A_204), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~r2_hidden(A_204, k2_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1616, c_208])).
% 4.43/1.77  tff(c_1666, plain, (![A_207]: (k3_xboole_0(k2_pre_topc('#skF_3', k1_tarski(A_207)), '#skF_4')=k1_tarski(A_207) | ~r1_tarski(k1_tarski(A_207), '#skF_4') | ~r2_hidden(A_207, k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_44, c_1635])).
% 4.43/1.77  tff(c_159, plain, (k6_domain_1(k2_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_144])).
% 4.43/1.77  tff(c_38, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')))!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.43/1.77  tff(c_73, plain, (k9_subset_1(k2_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k6_domain_1(k2_struct_0('#skF_3'), '#skF_5')))!=k6_domain_1(k2_struct_0('#skF_3'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_72, c_72, c_38])).
% 4.43/1.77  tff(c_161, plain, (k9_subset_1(k2_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k1_tarski('#skF_5')))!=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_159, c_73])).
% 4.43/1.77  tff(c_209, plain, (k3_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_5')), '#skF_4')!=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_208, c_161])).
% 4.43/1.77  tff(c_1672, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4') | ~r2_hidden('#skF_5', k2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1666, c_209])).
% 4.43/1.77  tff(c_1680, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_912, c_619, c_1672])).
% 4.43/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.43/1.77  
% 4.43/1.77  Inference rules
% 4.43/1.77  ----------------------
% 4.43/1.77  #Ref     : 0
% 4.43/1.77  #Sup     : 370
% 4.43/1.77  #Fact    : 0
% 4.43/1.77  #Define  : 0
% 4.43/1.77  #Split   : 9
% 4.43/1.77  #Chain   : 0
% 4.43/1.77  #Close   : 0
% 4.43/1.77  
% 4.43/1.77  Ordering : KBO
% 4.43/1.77  
% 4.43/1.77  Simplification rules
% 4.43/1.77  ----------------------
% 4.43/1.77  #Subsume      : 60
% 4.43/1.77  #Demod        : 121
% 4.43/1.77  #Tautology    : 106
% 4.43/1.77  #SimpNegUnit  : 13
% 4.43/1.77  #BackRed      : 5
% 4.43/1.77  
% 4.43/1.77  #Partial instantiations: 0
% 4.43/1.77  #Strategies tried      : 1
% 4.43/1.77  
% 4.43/1.77  Timing (in seconds)
% 4.43/1.77  ----------------------
% 4.43/1.77  Preprocessing        : 0.34
% 4.43/1.77  Parsing              : 0.19
% 4.43/1.77  CNF conversion       : 0.02
% 4.43/1.77  Main loop            : 0.62
% 4.43/1.77  Inferencing          : 0.22
% 4.43/1.77  Reduction            : 0.18
% 4.43/1.77  Demodulation         : 0.12
% 4.43/1.77  BG Simplification    : 0.03
% 4.43/1.77  Subsumption          : 0.14
% 4.43/1.77  Abstraction          : 0.03
% 4.43/1.77  MUC search           : 0.00
% 4.43/1.77  Cooper               : 0.00
% 4.43/1.77  Total                : 1.02
% 4.43/1.77  Index Insertion      : 0.00
% 4.43/1.77  Index Deletion       : 0.00
% 4.43/1.77  Index Matching       : 0.00
% 4.43/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
