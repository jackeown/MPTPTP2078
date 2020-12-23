%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:20 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 106 expanded)
%              Number of leaves         :   27 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :  166 ( 395 expanded)
%              Number of equality atoms :   23 (  50 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tex_2(B,A)
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ~ ( r2_hidden(C,B)
                      & ! [D] :
                          ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                         => ~ ( v4_pre_topc(D,A)
                              & k9_subset_1(u1_struct_0(A),B,D) = k1_tarski(C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tex_2)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ~ ( r2_hidden(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = k1_tarski(C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tex_2)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r1_tarski(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).

tff(c_32,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_34,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_71,plain,(
    ! [A_72,B_73,C_74] :
      ( r1_tarski(k2_tarski(A_72,B_73),C_74)
      | ~ r2_hidden(B_73,C_74)
      | ~ r2_hidden(A_72,C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_80,plain,(
    ! [A_1,C_74] :
      ( r1_tarski(k1_tarski(A_1),C_74)
      | ~ r2_hidden(A_1,C_74)
      | ~ r2_hidden(A_1,C_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_71])).

tff(c_40,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_36,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_288,plain,(
    ! [A_110,B_111,C_112] :
      ( k9_subset_1(u1_struct_0(A_110),B_111,'#skF_3'(A_110,B_111,C_112)) = k1_tarski(C_112)
      | ~ r2_hidden(C_112,B_111)
      | ~ m1_subset_1(C_112,u1_struct_0(A_110))
      | ~ v2_tex_2(B_111,A_110)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_299,plain,(
    ! [C_112] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_3'('#skF_4','#skF_5',C_112)) = k1_tarski(C_112)
      | ~ r2_hidden(C_112,'#skF_5')
      | ~ m1_subset_1(C_112,u1_struct_0('#skF_4'))
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_288])).

tff(c_306,plain,(
    ! [C_112] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_3'('#skF_4','#skF_5',C_112)) = k1_tarski(C_112)
      | ~ r2_hidden(C_112,'#skF_5')
      | ~ m1_subset_1(C_112,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_299])).

tff(c_28,plain,(
    ! [A_33,B_41,C_45] :
      ( m1_subset_1('#skF_3'(A_33,B_41,C_45),k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ r2_hidden(C_45,B_41)
      | ~ m1_subset_1(C_45,u1_struct_0(A_33))
      | ~ v2_tex_2(B_41,A_33)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_10,plain,(
    ! [A_5,B_6,C_7] :
      ( m1_subset_1(k9_subset_1(A_5,B_6,C_7),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(C_7,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_142,plain,(
    ! [A_88,B_89,C_90] :
      ( v4_pre_topc('#skF_1'(A_88,B_89,C_90),A_88)
      | ~ r1_tarski(C_90,B_89)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ v2_tex_2(B_89,A_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_151,plain,(
    ! [A_88,B_89,B_6,C_7] :
      ( v4_pre_topc('#skF_1'(A_88,B_89,k9_subset_1(u1_struct_0(A_88),B_6,C_7)),A_88)
      | ~ r1_tarski(k9_subset_1(u1_struct_0(A_88),B_6,C_7),B_89)
      | ~ v2_tex_2(B_89,A_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(u1_struct_0(A_88))) ) ),
    inference(resolution,[status(thm)],[c_10,c_142])).

tff(c_241,plain,(
    ! [A_106,B_107,C_108] :
      ( k9_subset_1(u1_struct_0(A_106),B_107,'#skF_1'(A_106,B_107,C_108)) = C_108
      | ~ r1_tarski(C_108,B_107)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ v2_tex_2(B_107,A_106)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_728,plain,(
    ! [A_180,B_181,B_182,C_183] :
      ( k9_subset_1(u1_struct_0(A_180),B_181,'#skF_1'(A_180,B_181,k9_subset_1(u1_struct_0(A_180),B_182,C_183))) = k9_subset_1(u1_struct_0(A_180),B_182,C_183)
      | ~ r1_tarski(k9_subset_1(u1_struct_0(A_180),B_182,C_183),B_181)
      | ~ v2_tex_2(B_181,A_180)
      | ~ m1_subset_1(B_181,k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ l1_pre_topc(A_180)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(u1_struct_0(A_180))) ) ),
    inference(resolution,[status(thm)],[c_10,c_241])).

tff(c_208,plain,(
    ! [A_100,B_101,C_102] :
      ( m1_subset_1('#skF_1'(A_100,B_101,C_102),k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ r1_tarski(C_102,B_101)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ v2_tex_2(B_101,A_100)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_30,plain,(
    ! [D_58] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',D_58) != k1_tarski('#skF_6')
      | ~ v4_pre_topc(D_58,'#skF_4')
      | ~ m1_subset_1(D_58,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_226,plain,(
    ! [B_101,C_102] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_1'('#skF_4',B_101,C_102)) != k1_tarski('#skF_6')
      | ~ v4_pre_topc('#skF_1'('#skF_4',B_101,C_102),'#skF_4')
      | ~ r1_tarski(C_102,B_101)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_101,'#skF_4')
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_208,c_30])).

tff(c_238,plain,(
    ! [B_101,C_102] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_1'('#skF_4',B_101,C_102)) != k1_tarski('#skF_6')
      | ~ v4_pre_topc('#skF_1'('#skF_4',B_101,C_102),'#skF_4')
      | ~ r1_tarski(C_102,B_101)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_101,'#skF_4')
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_226])).

tff(c_748,plain,(
    ! [B_182,C_183] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_182,C_183) != k1_tarski('#skF_6')
      | ~ v4_pre_topc('#skF_1'('#skF_4','#skF_5',k9_subset_1(u1_struct_0('#skF_4'),B_182,C_183)),'#skF_4')
      | ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_4'),B_182,C_183),'#skF_5')
      | ~ m1_subset_1(k9_subset_1(u1_struct_0('#skF_4'),B_182,C_183),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_4'),B_182,C_183),'#skF_5')
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ m1_subset_1(C_183,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_728,c_238])).

tff(c_940,plain,(
    ! [B_192,C_193] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_192,C_193) != k1_tarski('#skF_6')
      | ~ v4_pre_topc('#skF_1'('#skF_4','#skF_5',k9_subset_1(u1_struct_0('#skF_4'),B_192,C_193)),'#skF_4')
      | ~ m1_subset_1(k9_subset_1(u1_struct_0('#skF_4'),B_192,C_193),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_4'),B_192,C_193),'#skF_5')
      | ~ m1_subset_1(C_193,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_38,c_36,c_748])).

tff(c_982,plain,(
    ! [B_194,C_195] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_194,C_195) != k1_tarski('#skF_6')
      | ~ v4_pre_topc('#skF_1'('#skF_4','#skF_5',k9_subset_1(u1_struct_0('#skF_4'),B_194,C_195)),'#skF_4')
      | ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_4'),B_194,C_195),'#skF_5')
      | ~ m1_subset_1(C_195,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_10,c_940])).

tff(c_1007,plain,(
    ! [B_6,C_7] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_6,C_7) != k1_tarski('#skF_6')
      | ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_4'),B_6,C_7),'#skF_5')
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ m1_subset_1(C_7,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_151,c_982])).

tff(c_1020,plain,(
    ! [B_196,C_197] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_196,C_197) != k1_tarski('#skF_6')
      | ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_4'),B_196,C_197),'#skF_5')
      | ~ m1_subset_1(C_197,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_1007])).

tff(c_1051,plain,(
    ! [C_198] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_3'('#skF_4','#skF_5',C_198)) != k1_tarski('#skF_6')
      | ~ r1_tarski(k1_tarski(C_198),'#skF_5')
      | ~ m1_subset_1('#skF_3'('#skF_4','#skF_5',C_198),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(C_198,'#skF_5')
      | ~ m1_subset_1(C_198,u1_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_1020])).

tff(c_1055,plain,(
    ! [C_45] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_3'('#skF_4','#skF_5',C_45)) != k1_tarski('#skF_6')
      | ~ r1_tarski(k1_tarski(C_45),'#skF_5')
      | ~ r2_hidden(C_45,'#skF_5')
      | ~ m1_subset_1(C_45,u1_struct_0('#skF_4'))
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_1051])).

tff(c_1060,plain,(
    ! [C_203] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_3'('#skF_4','#skF_5',C_203)) != k1_tarski('#skF_6')
      | ~ r1_tarski(k1_tarski(C_203),'#skF_5')
      | ~ r2_hidden(C_203,'#skF_5')
      | ~ m1_subset_1(C_203,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_1055])).

tff(c_1064,plain,(
    ! [C_204] :
      ( k1_tarski(C_204) != k1_tarski('#skF_6')
      | ~ r1_tarski(k1_tarski(C_204),'#skF_5')
      | ~ r2_hidden(C_204,'#skF_5')
      | ~ m1_subset_1(C_204,u1_struct_0('#skF_4'))
      | ~ r2_hidden(C_204,'#skF_5')
      | ~ m1_subset_1(C_204,u1_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_1060])).

tff(c_1070,plain,(
    ! [A_205] :
      ( k1_tarski(A_205) != k1_tarski('#skF_6')
      | ~ m1_subset_1(A_205,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_205,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_80,c_1064])).

tff(c_1073,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_1070])).

tff(c_1077,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1073])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:35:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.72/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/1.65  
% 3.72/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/1.65  %$ v4_pre_topc > v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2
% 3.72/1.65  
% 3.72/1.65  %Foreground sorts:
% 3.72/1.65  
% 3.72/1.65  
% 3.72/1.65  %Background operators:
% 3.72/1.65  
% 3.72/1.65  
% 3.72/1.65  %Foreground operators:
% 3.72/1.65  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.72/1.65  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.72/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.72/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.72/1.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.72/1.65  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.72/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.72/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.72/1.65  tff('#skF_5', type, '#skF_5': $i).
% 3.72/1.65  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.72/1.65  tff('#skF_6', type, '#skF_6': $i).
% 3.72/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.72/1.65  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.72/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.72/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.72/1.65  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.72/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.72/1.65  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.72/1.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.72/1.65  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.72/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.72/1.65  
% 3.72/1.66  tff(f_101, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tex_2)).
% 3.72/1.66  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.72/1.66  tff(f_33, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.72/1.66  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_tex_2)).
% 3.72/1.66  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 3.72/1.66  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tex_2)).
% 3.72/1.66  tff(c_32, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.72/1.66  tff(c_34, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.72/1.66  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.72/1.66  tff(c_71, plain, (![A_72, B_73, C_74]: (r1_tarski(k2_tarski(A_72, B_73), C_74) | ~r2_hidden(B_73, C_74) | ~r2_hidden(A_72, C_74))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.72/1.66  tff(c_80, plain, (![A_1, C_74]: (r1_tarski(k1_tarski(A_1), C_74) | ~r2_hidden(A_1, C_74) | ~r2_hidden(A_1, C_74))), inference(superposition, [status(thm), theory('equality')], [c_2, c_71])).
% 3.72/1.66  tff(c_40, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.72/1.66  tff(c_36, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.72/1.66  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.72/1.66  tff(c_288, plain, (![A_110, B_111, C_112]: (k9_subset_1(u1_struct_0(A_110), B_111, '#skF_3'(A_110, B_111, C_112))=k1_tarski(C_112) | ~r2_hidden(C_112, B_111) | ~m1_subset_1(C_112, u1_struct_0(A_110)) | ~v2_tex_2(B_111, A_110) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.72/1.66  tff(c_299, plain, (![C_112]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_3'('#skF_4', '#skF_5', C_112))=k1_tarski(C_112) | ~r2_hidden(C_112, '#skF_5') | ~m1_subset_1(C_112, u1_struct_0('#skF_4')) | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_38, c_288])).
% 3.72/1.66  tff(c_306, plain, (![C_112]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_3'('#skF_4', '#skF_5', C_112))=k1_tarski(C_112) | ~r2_hidden(C_112, '#skF_5') | ~m1_subset_1(C_112, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_299])).
% 3.72/1.66  tff(c_28, plain, (![A_33, B_41, C_45]: (m1_subset_1('#skF_3'(A_33, B_41, C_45), k1_zfmisc_1(u1_struct_0(A_33))) | ~r2_hidden(C_45, B_41) | ~m1_subset_1(C_45, u1_struct_0(A_33)) | ~v2_tex_2(B_41, A_33) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.72/1.66  tff(c_10, plain, (![A_5, B_6, C_7]: (m1_subset_1(k9_subset_1(A_5, B_6, C_7), k1_zfmisc_1(A_5)) | ~m1_subset_1(C_7, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.72/1.66  tff(c_142, plain, (![A_88, B_89, C_90]: (v4_pre_topc('#skF_1'(A_88, B_89, C_90), A_88) | ~r1_tarski(C_90, B_89) | ~m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0(A_88))) | ~v2_tex_2(B_89, A_88) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.72/1.66  tff(c_151, plain, (![A_88, B_89, B_6, C_7]: (v4_pre_topc('#skF_1'(A_88, B_89, k9_subset_1(u1_struct_0(A_88), B_6, C_7)), A_88) | ~r1_tarski(k9_subset_1(u1_struct_0(A_88), B_6, C_7), B_89) | ~v2_tex_2(B_89, A_88) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88) | ~m1_subset_1(C_7, k1_zfmisc_1(u1_struct_0(A_88))))), inference(resolution, [status(thm)], [c_10, c_142])).
% 3.72/1.66  tff(c_241, plain, (![A_106, B_107, C_108]: (k9_subset_1(u1_struct_0(A_106), B_107, '#skF_1'(A_106, B_107, C_108))=C_108 | ~r1_tarski(C_108, B_107) | ~m1_subset_1(C_108, k1_zfmisc_1(u1_struct_0(A_106))) | ~v2_tex_2(B_107, A_106) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.72/1.66  tff(c_728, plain, (![A_180, B_181, B_182, C_183]: (k9_subset_1(u1_struct_0(A_180), B_181, '#skF_1'(A_180, B_181, k9_subset_1(u1_struct_0(A_180), B_182, C_183)))=k9_subset_1(u1_struct_0(A_180), B_182, C_183) | ~r1_tarski(k9_subset_1(u1_struct_0(A_180), B_182, C_183), B_181) | ~v2_tex_2(B_181, A_180) | ~m1_subset_1(B_181, k1_zfmisc_1(u1_struct_0(A_180))) | ~l1_pre_topc(A_180) | ~m1_subset_1(C_183, k1_zfmisc_1(u1_struct_0(A_180))))), inference(resolution, [status(thm)], [c_10, c_241])).
% 3.72/1.66  tff(c_208, plain, (![A_100, B_101, C_102]: (m1_subset_1('#skF_1'(A_100, B_101, C_102), k1_zfmisc_1(u1_struct_0(A_100))) | ~r1_tarski(C_102, B_101) | ~m1_subset_1(C_102, k1_zfmisc_1(u1_struct_0(A_100))) | ~v2_tex_2(B_101, A_100) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.72/1.66  tff(c_30, plain, (![D_58]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', D_58)!=k1_tarski('#skF_6') | ~v4_pre_topc(D_58, '#skF_4') | ~m1_subset_1(D_58, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.72/1.66  tff(c_226, plain, (![B_101, C_102]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_1'('#skF_4', B_101, C_102))!=k1_tarski('#skF_6') | ~v4_pre_topc('#skF_1'('#skF_4', B_101, C_102), '#skF_4') | ~r1_tarski(C_102, B_101) | ~m1_subset_1(C_102, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_101, '#skF_4') | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_208, c_30])).
% 3.72/1.66  tff(c_238, plain, (![B_101, C_102]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_1'('#skF_4', B_101, C_102))!=k1_tarski('#skF_6') | ~v4_pre_topc('#skF_1'('#skF_4', B_101, C_102), '#skF_4') | ~r1_tarski(C_102, B_101) | ~m1_subset_1(C_102, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_101, '#skF_4') | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_226])).
% 3.72/1.66  tff(c_748, plain, (![B_182, C_183]: (k9_subset_1(u1_struct_0('#skF_4'), B_182, C_183)!=k1_tarski('#skF_6') | ~v4_pre_topc('#skF_1'('#skF_4', '#skF_5', k9_subset_1(u1_struct_0('#skF_4'), B_182, C_183)), '#skF_4') | ~r1_tarski(k9_subset_1(u1_struct_0('#skF_4'), B_182, C_183), '#skF_5') | ~m1_subset_1(k9_subset_1(u1_struct_0('#skF_4'), B_182, C_183), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(k9_subset_1(u1_struct_0('#skF_4'), B_182, C_183), '#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~m1_subset_1(C_183, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_728, c_238])).
% 3.72/1.66  tff(c_940, plain, (![B_192, C_193]: (k9_subset_1(u1_struct_0('#skF_4'), B_192, C_193)!=k1_tarski('#skF_6') | ~v4_pre_topc('#skF_1'('#skF_4', '#skF_5', k9_subset_1(u1_struct_0('#skF_4'), B_192, C_193)), '#skF_4') | ~m1_subset_1(k9_subset_1(u1_struct_0('#skF_4'), B_192, C_193), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(k9_subset_1(u1_struct_0('#skF_4'), B_192, C_193), '#skF_5') | ~m1_subset_1(C_193, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_38, c_36, c_748])).
% 3.72/1.66  tff(c_982, plain, (![B_194, C_195]: (k9_subset_1(u1_struct_0('#skF_4'), B_194, C_195)!=k1_tarski('#skF_6') | ~v4_pre_topc('#skF_1'('#skF_4', '#skF_5', k9_subset_1(u1_struct_0('#skF_4'), B_194, C_195)), '#skF_4') | ~r1_tarski(k9_subset_1(u1_struct_0('#skF_4'), B_194, C_195), '#skF_5') | ~m1_subset_1(C_195, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_10, c_940])).
% 3.72/1.66  tff(c_1007, plain, (![B_6, C_7]: (k9_subset_1(u1_struct_0('#skF_4'), B_6, C_7)!=k1_tarski('#skF_6') | ~r1_tarski(k9_subset_1(u1_struct_0('#skF_4'), B_6, C_7), '#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~m1_subset_1(C_7, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_151, c_982])).
% 3.72/1.66  tff(c_1020, plain, (![B_196, C_197]: (k9_subset_1(u1_struct_0('#skF_4'), B_196, C_197)!=k1_tarski('#skF_6') | ~r1_tarski(k9_subset_1(u1_struct_0('#skF_4'), B_196, C_197), '#skF_5') | ~m1_subset_1(C_197, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_1007])).
% 3.72/1.66  tff(c_1051, plain, (![C_198]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_3'('#skF_4', '#skF_5', C_198))!=k1_tarski('#skF_6') | ~r1_tarski(k1_tarski(C_198), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_4', '#skF_5', C_198), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r2_hidden(C_198, '#skF_5') | ~m1_subset_1(C_198, u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_306, c_1020])).
% 3.72/1.66  tff(c_1055, plain, (![C_45]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_3'('#skF_4', '#skF_5', C_45))!=k1_tarski('#skF_6') | ~r1_tarski(k1_tarski(C_45), '#skF_5') | ~r2_hidden(C_45, '#skF_5') | ~m1_subset_1(C_45, u1_struct_0('#skF_4')) | ~v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_1051])).
% 3.72/1.66  tff(c_1060, plain, (![C_203]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_3'('#skF_4', '#skF_5', C_203))!=k1_tarski('#skF_6') | ~r1_tarski(k1_tarski(C_203), '#skF_5') | ~r2_hidden(C_203, '#skF_5') | ~m1_subset_1(C_203, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_1055])).
% 3.72/1.66  tff(c_1064, plain, (![C_204]: (k1_tarski(C_204)!=k1_tarski('#skF_6') | ~r1_tarski(k1_tarski(C_204), '#skF_5') | ~r2_hidden(C_204, '#skF_5') | ~m1_subset_1(C_204, u1_struct_0('#skF_4')) | ~r2_hidden(C_204, '#skF_5') | ~m1_subset_1(C_204, u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_306, c_1060])).
% 3.72/1.66  tff(c_1070, plain, (![A_205]: (k1_tarski(A_205)!=k1_tarski('#skF_6') | ~m1_subset_1(A_205, u1_struct_0('#skF_4')) | ~r2_hidden(A_205, '#skF_5'))), inference(resolution, [status(thm)], [c_80, c_1064])).
% 3.72/1.66  tff(c_1073, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_34, c_1070])).
% 3.72/1.66  tff(c_1077, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_1073])).
% 3.72/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/1.66  
% 3.72/1.66  Inference rules
% 3.72/1.66  ----------------------
% 3.72/1.66  #Ref     : 0
% 3.72/1.66  #Sup     : 217
% 3.72/1.66  #Fact    : 0
% 3.72/1.66  #Define  : 0
% 3.72/1.66  #Split   : 3
% 3.72/1.66  #Chain   : 0
% 3.72/1.66  #Close   : 0
% 3.72/1.66  
% 3.72/1.66  Ordering : KBO
% 3.72/1.66  
% 3.72/1.66  Simplification rules
% 3.72/1.66  ----------------------
% 3.72/1.66  #Subsume      : 23
% 3.72/1.66  #Demod        : 132
% 3.72/1.66  #Tautology    : 32
% 3.72/1.66  #SimpNegUnit  : 0
% 3.72/1.66  #BackRed      : 0
% 3.72/1.66  
% 3.72/1.66  #Partial instantiations: 0
% 3.72/1.66  #Strategies tried      : 1
% 3.72/1.66  
% 3.72/1.66  Timing (in seconds)
% 3.72/1.66  ----------------------
% 3.72/1.66  Preprocessing        : 0.33
% 3.72/1.66  Parsing              : 0.18
% 3.72/1.66  CNF conversion       : 0.02
% 3.72/1.66  Main loop            : 0.51
% 3.72/1.67  Inferencing          : 0.20
% 3.72/1.67  Reduction            : 0.15
% 3.72/1.67  Demodulation         : 0.10
% 3.72/1.67  BG Simplification    : 0.03
% 3.72/1.67  Subsumption          : 0.11
% 3.72/1.67  Abstraction          : 0.03
% 3.72/1.67  MUC search           : 0.00
% 3.72/1.67  Cooper               : 0.00
% 3.72/1.67  Total                : 0.88
% 3.72/1.67  Index Insertion      : 0.00
% 3.72/1.67  Index Deletion       : 0.00
% 3.72/1.67  Index Matching       : 0.00
% 3.72/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
