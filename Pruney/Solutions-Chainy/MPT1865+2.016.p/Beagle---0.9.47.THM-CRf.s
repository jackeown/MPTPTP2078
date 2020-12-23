%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:19 EST 2020

% Result     : Theorem 5.35s
% Output     : CNFRefutation 5.35s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 128 expanded)
%              Number of leaves         :   26 (  58 expanded)
%              Depth                    :   13
%              Number of atoms          :  169 ( 374 expanded)
%              Number of equality atoms :   13 (  27 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k1_enumset1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tex_2)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_65,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).

tff(c_32,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_80,plain,(
    ! [A_60,B_61] :
      ( m1_subset_1(k1_tarski(A_60),k1_zfmisc_1(B_61))
      | ~ r2_hidden(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_89,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(k1_tarski(A_60),B_61)
      | ~ r2_hidden(A_60,B_61) ) ),
    inference(resolution,[status(thm)],[c_80,c_14])).

tff(c_91,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_1'(A_64,B_65),A_64)
      | r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_96,plain,(
    ! [A_64] : r1_tarski(A_64,A_64) ),
    inference(resolution,[status(thm)],[c_91,c_4])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_50,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(A_51,B_52)
      | ~ m1_subset_1(A_51,k1_zfmisc_1(B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_54,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_38,c_50])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_97,plain,(
    ! [C_66,B_67,A_68] :
      ( r2_hidden(C_66,B_67)
      | ~ r2_hidden(C_66,A_68)
      | ~ r1_tarski(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_133,plain,(
    ! [A_76,B_77,B_78] :
      ( r2_hidden('#skF_1'(A_76,B_77),B_78)
      | ~ r1_tarski(A_76,B_78)
      | r1_tarski(A_76,B_77) ) ),
    inference(resolution,[status(thm)],[c_6,c_97])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_182,plain,(
    ! [A_85,B_86,B_87,B_88] :
      ( r2_hidden('#skF_1'(A_85,B_86),B_87)
      | ~ r1_tarski(B_88,B_87)
      | ~ r1_tarski(A_85,B_88)
      | r1_tarski(A_85,B_86) ) ),
    inference(resolution,[status(thm)],[c_133,c_2])).

tff(c_195,plain,(
    ! [A_89,B_90] :
      ( r2_hidden('#skF_1'(A_89,B_90),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_89,'#skF_5')
      | r1_tarski(A_89,B_90) ) ),
    inference(resolution,[status(thm)],[c_54,c_182])).

tff(c_203,plain,(
    ! [A_89] :
      ( ~ r1_tarski(A_89,'#skF_5')
      | r1_tarski(A_89,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_195,c_4])).

tff(c_238,plain,(
    ! [A_95,B_96,B_97,A_98] :
      ( r2_hidden('#skF_1'(A_95,B_96),B_97)
      | ~ r1_tarski(A_95,k1_tarski(A_98))
      | r1_tarski(A_95,B_96)
      | ~ r2_hidden(A_98,B_97) ) ),
    inference(resolution,[status(thm)],[c_89,c_182])).

tff(c_251,plain,(
    ! [A_99,B_100,B_101] :
      ( r2_hidden('#skF_1'(k1_tarski(A_99),B_100),B_101)
      | r1_tarski(k1_tarski(A_99),B_100)
      | ~ r2_hidden(A_99,B_101) ) ),
    inference(resolution,[status(thm)],[c_96,c_238])).

tff(c_329,plain,(
    ! [A_115,B_116,B_117,B_118] :
      ( r2_hidden('#skF_1'(k1_tarski(A_115),B_116),B_117)
      | ~ r1_tarski(B_118,B_117)
      | r1_tarski(k1_tarski(A_115),B_116)
      | ~ r2_hidden(A_115,B_118) ) ),
    inference(resolution,[status(thm)],[c_251,c_2])).

tff(c_704,plain,(
    ! [A_164,B_165,A_166] :
      ( r2_hidden('#skF_1'(k1_tarski(A_164),B_165),u1_struct_0('#skF_4'))
      | r1_tarski(k1_tarski(A_164),B_165)
      | ~ r2_hidden(A_164,A_166)
      | ~ r1_tarski(A_166,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_203,c_329])).

tff(c_728,plain,(
    ! [B_165] :
      ( r2_hidden('#skF_1'(k1_tarski('#skF_6'),B_165),u1_struct_0('#skF_4'))
      | r1_tarski(k1_tarski('#skF_6'),B_165)
      | ~ r1_tarski('#skF_5','#skF_5') ) ),
    inference(resolution,[status(thm)],[c_32,c_704])).

tff(c_745,plain,(
    ! [B_167] :
      ( r2_hidden('#skF_1'(k1_tarski('#skF_6'),B_167),u1_struct_0('#skF_4'))
      | r1_tarski(k1_tarski('#skF_6'),B_167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_728])).

tff(c_759,plain,(
    r1_tarski(k1_tarski('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_745,c_4])).

tff(c_40,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_36,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_312,plain,(
    ! [A_112,B_113,C_114] :
      ( v4_pre_topc('#skF_2'(A_112,B_113,C_114),A_112)
      | ~ r1_tarski(C_114,B_113)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ v2_tex_2(B_113,A_112)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1268,plain,(
    ! [A_207,B_208,A_209] :
      ( v4_pre_topc('#skF_2'(A_207,B_208,A_209),A_207)
      | ~ r1_tarski(A_209,B_208)
      | ~ v2_tex_2(B_208,A_207)
      | ~ m1_subset_1(B_208,k1_zfmisc_1(u1_struct_0(A_207)))
      | ~ l1_pre_topc(A_207)
      | ~ r1_tarski(A_209,u1_struct_0(A_207)) ) ),
    inference(resolution,[status(thm)],[c_16,c_312])).

tff(c_1280,plain,(
    ! [A_209] :
      ( v4_pre_topc('#skF_2'('#skF_4','#skF_5',A_209),'#skF_4')
      | ~ r1_tarski(A_209,'#skF_5')
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_209,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_38,c_1268])).

tff(c_1287,plain,(
    ! [A_209] :
      ( v4_pre_topc('#skF_2'('#skF_4','#skF_5',A_209),'#skF_4')
      | ~ r1_tarski(A_209,'#skF_5')
      | ~ r1_tarski(A_209,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_1280])).

tff(c_760,plain,(
    ! [A_168,B_169,C_170] :
      ( k9_subset_1(u1_struct_0(A_168),B_169,'#skF_2'(A_168,B_169,C_170)) = C_170
      | ~ r1_tarski(C_170,B_169)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ v2_tex_2(B_169,A_168)
      | ~ m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ l1_pre_topc(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1968,plain,(
    ! [A_295,B_296,A_297] :
      ( k9_subset_1(u1_struct_0(A_295),B_296,'#skF_2'(A_295,B_296,A_297)) = A_297
      | ~ r1_tarski(A_297,B_296)
      | ~ v2_tex_2(B_296,A_295)
      | ~ m1_subset_1(B_296,k1_zfmisc_1(u1_struct_0(A_295)))
      | ~ l1_pre_topc(A_295)
      | ~ r1_tarski(A_297,u1_struct_0(A_295)) ) ),
    inference(resolution,[status(thm)],[c_16,c_760])).

tff(c_1980,plain,(
    ! [A_297] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_2'('#skF_4','#skF_5',A_297)) = A_297
      | ~ r1_tarski(A_297,'#skF_5')
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_297,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_38,c_1968])).

tff(c_1988,plain,(
    ! [A_298] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_2'('#skF_4','#skF_5',A_298)) = A_298
      | ~ r1_tarski(A_298,'#skF_5')
      | ~ r1_tarski(A_298,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_1980])).

tff(c_433,plain,(
    ! [A_130,B_131,C_132] :
      ( m1_subset_1('#skF_2'(A_130,B_131,C_132),k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ r1_tarski(C_132,B_131)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ v2_tex_2(B_131,A_130)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    ! [D_49] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',D_49) != k1_tarski('#skF_6')
      | ~ v4_pre_topc(D_49,'#skF_4')
      | ~ m1_subset_1(D_49,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_445,plain,(
    ! [B_131,C_132] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_2'('#skF_4',B_131,C_132)) != k1_tarski('#skF_6')
      | ~ v4_pre_topc('#skF_2'('#skF_4',B_131,C_132),'#skF_4')
      | ~ r1_tarski(C_132,B_131)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_131,'#skF_4')
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_433,c_30])).

tff(c_456,plain,(
    ! [B_131,C_132] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_2'('#skF_4',B_131,C_132)) != k1_tarski('#skF_6')
      | ~ v4_pre_topc('#skF_2'('#skF_4',B_131,C_132),'#skF_4')
      | ~ r1_tarski(C_132,B_131)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_131,'#skF_4')
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_445])).

tff(c_1993,plain,(
    ! [A_298] :
      ( k1_tarski('#skF_6') != A_298
      | ~ v4_pre_topc('#skF_2'('#skF_4','#skF_5',A_298),'#skF_4')
      | ~ r1_tarski(A_298,'#skF_5')
      | ~ m1_subset_1(A_298,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_298,'#skF_5')
      | ~ r1_tarski(A_298,u1_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1988,c_456])).

tff(c_2035,plain,(
    ! [A_299] :
      ( k1_tarski('#skF_6') != A_299
      | ~ v4_pre_topc('#skF_2'('#skF_4','#skF_5',A_299),'#skF_4')
      | ~ m1_subset_1(A_299,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_299,'#skF_5')
      | ~ r1_tarski(A_299,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1993])).

tff(c_2067,plain,(
    ! [A_300] :
      ( k1_tarski('#skF_6') != A_300
      | ~ v4_pre_topc('#skF_2'('#skF_4','#skF_5',A_300),'#skF_4')
      | ~ r1_tarski(A_300,'#skF_5')
      | ~ r1_tarski(A_300,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_16,c_2035])).

tff(c_2093,plain,(
    ! [A_301] :
      ( k1_tarski('#skF_6') != A_301
      | ~ r1_tarski(A_301,'#skF_5')
      | ~ r1_tarski(A_301,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1287,c_2067])).

tff(c_2151,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_759,c_2093])).

tff(c_2172,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_89,c_2151])).

tff(c_2176,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:35:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.35/2.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.35/2.14  
% 5.35/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.35/2.14  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k1_enumset1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_1
% 5.35/2.14  
% 5.35/2.14  %Foreground sorts:
% 5.35/2.14  
% 5.35/2.14  
% 5.35/2.14  %Background operators:
% 5.35/2.14  
% 5.35/2.14  
% 5.35/2.14  %Foreground operators:
% 5.35/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.35/2.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.35/2.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.35/2.14  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.35/2.14  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.35/2.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.35/2.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.35/2.14  tff('#skF_5', type, '#skF_5': $i).
% 5.35/2.14  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 5.35/2.14  tff('#skF_6', type, '#skF_6': $i).
% 5.35/2.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.35/2.14  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.35/2.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.35/2.14  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.35/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.35/2.14  tff('#skF_4', type, '#skF_4': $i).
% 5.35/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.35/2.14  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.35/2.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.35/2.14  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.35/2.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.35/2.14  
% 5.35/2.16  tff(f_87, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tex_2)).
% 5.35/2.16  tff(f_40, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 5.35/2.16  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.35/2.16  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.35/2.16  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tex_2)).
% 5.35/2.16  tff(c_32, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.35/2.16  tff(c_80, plain, (![A_60, B_61]: (m1_subset_1(k1_tarski(A_60), k1_zfmisc_1(B_61)) | ~r2_hidden(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.35/2.16  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.35/2.16  tff(c_89, plain, (![A_60, B_61]: (r1_tarski(k1_tarski(A_60), B_61) | ~r2_hidden(A_60, B_61))), inference(resolution, [status(thm)], [c_80, c_14])).
% 5.35/2.16  tff(c_91, plain, (![A_64, B_65]: (r2_hidden('#skF_1'(A_64, B_65), A_64) | r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.35/2.16  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.35/2.16  tff(c_96, plain, (![A_64]: (r1_tarski(A_64, A_64))), inference(resolution, [status(thm)], [c_91, c_4])).
% 5.35/2.16  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.35/2.16  tff(c_50, plain, (![A_51, B_52]: (r1_tarski(A_51, B_52) | ~m1_subset_1(A_51, k1_zfmisc_1(B_52)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.35/2.16  tff(c_54, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_38, c_50])).
% 5.35/2.16  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.35/2.16  tff(c_97, plain, (![C_66, B_67, A_68]: (r2_hidden(C_66, B_67) | ~r2_hidden(C_66, A_68) | ~r1_tarski(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.35/2.16  tff(c_133, plain, (![A_76, B_77, B_78]: (r2_hidden('#skF_1'(A_76, B_77), B_78) | ~r1_tarski(A_76, B_78) | r1_tarski(A_76, B_77))), inference(resolution, [status(thm)], [c_6, c_97])).
% 5.35/2.16  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.35/2.16  tff(c_182, plain, (![A_85, B_86, B_87, B_88]: (r2_hidden('#skF_1'(A_85, B_86), B_87) | ~r1_tarski(B_88, B_87) | ~r1_tarski(A_85, B_88) | r1_tarski(A_85, B_86))), inference(resolution, [status(thm)], [c_133, c_2])).
% 5.35/2.16  tff(c_195, plain, (![A_89, B_90]: (r2_hidden('#skF_1'(A_89, B_90), u1_struct_0('#skF_4')) | ~r1_tarski(A_89, '#skF_5') | r1_tarski(A_89, B_90))), inference(resolution, [status(thm)], [c_54, c_182])).
% 5.35/2.16  tff(c_203, plain, (![A_89]: (~r1_tarski(A_89, '#skF_5') | r1_tarski(A_89, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_195, c_4])).
% 5.35/2.16  tff(c_238, plain, (![A_95, B_96, B_97, A_98]: (r2_hidden('#skF_1'(A_95, B_96), B_97) | ~r1_tarski(A_95, k1_tarski(A_98)) | r1_tarski(A_95, B_96) | ~r2_hidden(A_98, B_97))), inference(resolution, [status(thm)], [c_89, c_182])).
% 5.35/2.16  tff(c_251, plain, (![A_99, B_100, B_101]: (r2_hidden('#skF_1'(k1_tarski(A_99), B_100), B_101) | r1_tarski(k1_tarski(A_99), B_100) | ~r2_hidden(A_99, B_101))), inference(resolution, [status(thm)], [c_96, c_238])).
% 5.35/2.16  tff(c_329, plain, (![A_115, B_116, B_117, B_118]: (r2_hidden('#skF_1'(k1_tarski(A_115), B_116), B_117) | ~r1_tarski(B_118, B_117) | r1_tarski(k1_tarski(A_115), B_116) | ~r2_hidden(A_115, B_118))), inference(resolution, [status(thm)], [c_251, c_2])).
% 5.35/2.16  tff(c_704, plain, (![A_164, B_165, A_166]: (r2_hidden('#skF_1'(k1_tarski(A_164), B_165), u1_struct_0('#skF_4')) | r1_tarski(k1_tarski(A_164), B_165) | ~r2_hidden(A_164, A_166) | ~r1_tarski(A_166, '#skF_5'))), inference(resolution, [status(thm)], [c_203, c_329])).
% 5.35/2.16  tff(c_728, plain, (![B_165]: (r2_hidden('#skF_1'(k1_tarski('#skF_6'), B_165), u1_struct_0('#skF_4')) | r1_tarski(k1_tarski('#skF_6'), B_165) | ~r1_tarski('#skF_5', '#skF_5'))), inference(resolution, [status(thm)], [c_32, c_704])).
% 5.35/2.16  tff(c_745, plain, (![B_167]: (r2_hidden('#skF_1'(k1_tarski('#skF_6'), B_167), u1_struct_0('#skF_4')) | r1_tarski(k1_tarski('#skF_6'), B_167))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_728])).
% 5.35/2.16  tff(c_759, plain, (r1_tarski(k1_tarski('#skF_6'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_745, c_4])).
% 5.35/2.16  tff(c_40, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.35/2.16  tff(c_36, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.35/2.16  tff(c_16, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.35/2.16  tff(c_312, plain, (![A_112, B_113, C_114]: (v4_pre_topc('#skF_2'(A_112, B_113, C_114), A_112) | ~r1_tarski(C_114, B_113) | ~m1_subset_1(C_114, k1_zfmisc_1(u1_struct_0(A_112))) | ~v2_tex_2(B_113, A_112) | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.35/2.16  tff(c_1268, plain, (![A_207, B_208, A_209]: (v4_pre_topc('#skF_2'(A_207, B_208, A_209), A_207) | ~r1_tarski(A_209, B_208) | ~v2_tex_2(B_208, A_207) | ~m1_subset_1(B_208, k1_zfmisc_1(u1_struct_0(A_207))) | ~l1_pre_topc(A_207) | ~r1_tarski(A_209, u1_struct_0(A_207)))), inference(resolution, [status(thm)], [c_16, c_312])).
% 5.35/2.16  tff(c_1280, plain, (![A_209]: (v4_pre_topc('#skF_2'('#skF_4', '#skF_5', A_209), '#skF_4') | ~r1_tarski(A_209, '#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_209, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_38, c_1268])).
% 5.35/2.16  tff(c_1287, plain, (![A_209]: (v4_pre_topc('#skF_2'('#skF_4', '#skF_5', A_209), '#skF_4') | ~r1_tarski(A_209, '#skF_5') | ~r1_tarski(A_209, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_1280])).
% 5.35/2.16  tff(c_760, plain, (![A_168, B_169, C_170]: (k9_subset_1(u1_struct_0(A_168), B_169, '#skF_2'(A_168, B_169, C_170))=C_170 | ~r1_tarski(C_170, B_169) | ~m1_subset_1(C_170, k1_zfmisc_1(u1_struct_0(A_168))) | ~v2_tex_2(B_169, A_168) | ~m1_subset_1(B_169, k1_zfmisc_1(u1_struct_0(A_168))) | ~l1_pre_topc(A_168))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.35/2.16  tff(c_1968, plain, (![A_295, B_296, A_297]: (k9_subset_1(u1_struct_0(A_295), B_296, '#skF_2'(A_295, B_296, A_297))=A_297 | ~r1_tarski(A_297, B_296) | ~v2_tex_2(B_296, A_295) | ~m1_subset_1(B_296, k1_zfmisc_1(u1_struct_0(A_295))) | ~l1_pre_topc(A_295) | ~r1_tarski(A_297, u1_struct_0(A_295)))), inference(resolution, [status(thm)], [c_16, c_760])).
% 5.35/2.16  tff(c_1980, plain, (![A_297]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_2'('#skF_4', '#skF_5', A_297))=A_297 | ~r1_tarski(A_297, '#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_297, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_38, c_1968])).
% 5.35/2.16  tff(c_1988, plain, (![A_298]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_2'('#skF_4', '#skF_5', A_298))=A_298 | ~r1_tarski(A_298, '#skF_5') | ~r1_tarski(A_298, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_1980])).
% 5.35/2.16  tff(c_433, plain, (![A_130, B_131, C_132]: (m1_subset_1('#skF_2'(A_130, B_131, C_132), k1_zfmisc_1(u1_struct_0(A_130))) | ~r1_tarski(C_132, B_131) | ~m1_subset_1(C_132, k1_zfmisc_1(u1_struct_0(A_130))) | ~v2_tex_2(B_131, A_130) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.35/2.16  tff(c_30, plain, (![D_49]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', D_49)!=k1_tarski('#skF_6') | ~v4_pre_topc(D_49, '#skF_4') | ~m1_subset_1(D_49, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.35/2.16  tff(c_445, plain, (![B_131, C_132]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_2'('#skF_4', B_131, C_132))!=k1_tarski('#skF_6') | ~v4_pre_topc('#skF_2'('#skF_4', B_131, C_132), '#skF_4') | ~r1_tarski(C_132, B_131) | ~m1_subset_1(C_132, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_131, '#skF_4') | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_433, c_30])).
% 5.35/2.16  tff(c_456, plain, (![B_131, C_132]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_2'('#skF_4', B_131, C_132))!=k1_tarski('#skF_6') | ~v4_pre_topc('#skF_2'('#skF_4', B_131, C_132), '#skF_4') | ~r1_tarski(C_132, B_131) | ~m1_subset_1(C_132, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_131, '#skF_4') | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_445])).
% 5.35/2.16  tff(c_1993, plain, (![A_298]: (k1_tarski('#skF_6')!=A_298 | ~v4_pre_topc('#skF_2'('#skF_4', '#skF_5', A_298), '#skF_4') | ~r1_tarski(A_298, '#skF_5') | ~m1_subset_1(A_298, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_298, '#skF_5') | ~r1_tarski(A_298, u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1988, c_456])).
% 5.35/2.16  tff(c_2035, plain, (![A_299]: (k1_tarski('#skF_6')!=A_299 | ~v4_pre_topc('#skF_2'('#skF_4', '#skF_5', A_299), '#skF_4') | ~m1_subset_1(A_299, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_299, '#skF_5') | ~r1_tarski(A_299, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1993])).
% 5.35/2.16  tff(c_2067, plain, (![A_300]: (k1_tarski('#skF_6')!=A_300 | ~v4_pre_topc('#skF_2'('#skF_4', '#skF_5', A_300), '#skF_4') | ~r1_tarski(A_300, '#skF_5') | ~r1_tarski(A_300, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_16, c_2035])).
% 5.35/2.16  tff(c_2093, plain, (![A_301]: (k1_tarski('#skF_6')!=A_301 | ~r1_tarski(A_301, '#skF_5') | ~r1_tarski(A_301, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1287, c_2067])).
% 5.35/2.16  tff(c_2151, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_759, c_2093])).
% 5.35/2.16  tff(c_2172, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_89, c_2151])).
% 5.35/2.16  tff(c_2176, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_2172])).
% 5.35/2.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.35/2.16  
% 5.35/2.16  Inference rules
% 5.35/2.16  ----------------------
% 5.35/2.16  #Ref     : 0
% 5.35/2.16  #Sup     : 532
% 5.35/2.16  #Fact    : 0
% 5.35/2.16  #Define  : 0
% 5.35/2.16  #Split   : 8
% 5.35/2.16  #Chain   : 0
% 5.35/2.16  #Close   : 0
% 5.35/2.16  
% 5.35/2.16  Ordering : KBO
% 5.35/2.16  
% 5.35/2.16  Simplification rules
% 5.35/2.16  ----------------------
% 5.35/2.16  #Subsume      : 161
% 5.35/2.16  #Demod        : 119
% 5.35/2.16  #Tautology    : 36
% 5.35/2.16  #SimpNegUnit  : 0
% 5.35/2.16  #BackRed      : 0
% 5.35/2.16  
% 5.35/2.16  #Partial instantiations: 0
% 5.35/2.16  #Strategies tried      : 1
% 5.35/2.16  
% 5.35/2.16  Timing (in seconds)
% 5.35/2.16  ----------------------
% 5.35/2.16  Preprocessing        : 0.39
% 5.35/2.16  Parsing              : 0.20
% 5.35/2.16  CNF conversion       : 0.04
% 5.35/2.16  Main loop            : 0.93
% 5.35/2.16  Inferencing          : 0.29
% 5.35/2.16  Reduction            : 0.24
% 5.35/2.16  Demodulation         : 0.16
% 5.35/2.16  BG Simplification    : 0.03
% 5.35/2.16  Subsumption          : 0.31
% 5.35/2.16  Abstraction          : 0.04
% 5.35/2.16  MUC search           : 0.00
% 5.35/2.16  Cooper               : 0.00
% 5.35/2.16  Total                : 1.36
% 5.35/2.16  Index Insertion      : 0.00
% 5.35/2.16  Index Deletion       : 0.00
% 5.35/2.16  Index Matching       : 0.00
% 5.35/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
