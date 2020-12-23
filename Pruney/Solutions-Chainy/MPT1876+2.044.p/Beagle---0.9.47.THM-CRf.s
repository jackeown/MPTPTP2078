%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:56 EST 2020

% Result     : Theorem 7.51s
% Output     : CNFRefutation 7.88s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 928 expanded)
%              Number of leaves         :   42 ( 331 expanded)
%              Depth                    :   27
%              Number of atoms          :  374 (2592 expanded)
%              Number of equality atoms :   18 (  83 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

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

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_181,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v2_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v2_tex_2(B,A)
            <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_41,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_120,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_161,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_149,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ ( v2_tex_2(B,A)
              & ! [C] :
                  ( ( ~ v2_struct_0(C)
                    & v1_pre_topc(C)
                    & v1_tdlat_3(C)
                    & m1_pre_topc(C,A) )
                 => B != u1_struct_0(C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_107,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ( ~ v2_struct_0(B)
              & ~ v7_struct_0(B) )
           => ( ~ v2_struct_0(B)
              & ~ v1_tdlat_3(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc32_tex_2)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

tff(c_54,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_58,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_68,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_71,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_62,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_73,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_62])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_10] : ~ v1_xboole_0(k1_tarski(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_111,plain,(
    ! [A_59,B_60] :
      ( m1_subset_1(k1_tarski(A_59),k1_zfmisc_1(B_60))
      | ~ r2_hidden(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_115,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(k1_tarski(A_59),B_60)
      | ~ r2_hidden(A_59,B_60) ) ),
    inference(resolution,[status(thm)],[c_111,c_18])).

tff(c_213,plain,(
    ! [B_81,A_82] :
      ( B_81 = A_82
      | ~ r1_tarski(A_82,B_81)
      | ~ v1_zfmisc_1(B_81)
      | v1_xboole_0(B_81)
      | v1_xboole_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_225,plain,(
    ! [A_59,B_60] :
      ( k1_tarski(A_59) = B_60
      | ~ v1_zfmisc_1(B_60)
      | v1_xboole_0(B_60)
      | v1_xboole_0(k1_tarski(A_59))
      | ~ r2_hidden(A_59,B_60) ) ),
    inference(resolution,[status(thm)],[c_115,c_213])).

tff(c_257,plain,(
    ! [A_86,B_87] :
      ( k1_tarski(A_86) = B_87
      | ~ v1_zfmisc_1(B_87)
      | v1_xboole_0(B_87)
      | ~ r2_hidden(A_86,B_87) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_225])).

tff(c_269,plain,(
    ! [A_1] :
      ( k1_tarski('#skF_1'(A_1)) = A_1
      | ~ v1_zfmisc_1(A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_257])).

tff(c_117,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_2'(A_63,B_64),A_63)
      | r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_128,plain,(
    ! [A_63] : r1_tarski(A_63,A_63) ),
    inference(resolution,[status(thm)],[c_117,c_8])).

tff(c_131,plain,(
    ! [C_65,B_66,A_67] :
      ( r2_hidden(C_65,B_66)
      | ~ r2_hidden(C_65,A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_168,plain,(
    ! [A_76,B_77] :
      ( r2_hidden('#skF_1'(A_76),B_77)
      | ~ r1_tarski(A_76,B_77)
      | v1_xboole_0(A_76) ) ),
    inference(resolution,[status(thm)],[c_4,c_131])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_545,plain,(
    ! [A_123,B_124,B_125] :
      ( r2_hidden('#skF_1'(A_123),B_124)
      | ~ r1_tarski(B_125,B_124)
      | ~ r1_tarski(A_123,B_125)
      | v1_xboole_0(A_123) ) ),
    inference(resolution,[status(thm)],[c_168,c_6])).

tff(c_942,plain,(
    ! [A_154,B_155,A_156] :
      ( r2_hidden('#skF_1'(A_154),B_155)
      | ~ r1_tarski(A_154,k1_tarski(A_156))
      | v1_xboole_0(A_154)
      | ~ r2_hidden(A_156,B_155) ) ),
    inference(resolution,[status(thm)],[c_115,c_545])).

tff(c_973,plain,(
    ! [A_156,B_155] :
      ( r2_hidden('#skF_1'(k1_tarski(A_156)),B_155)
      | v1_xboole_0(k1_tarski(A_156))
      | ~ r2_hidden(A_156,B_155) ) ),
    inference(resolution,[status(thm)],[c_128,c_942])).

tff(c_992,plain,(
    ! [A_158,B_159] :
      ( r2_hidden('#skF_1'(k1_tarski(A_158)),B_159)
      | ~ r2_hidden(A_158,B_159) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_973])).

tff(c_235,plain,(
    ! [A_59,B_60] :
      ( k1_tarski(A_59) = B_60
      | ~ v1_zfmisc_1(B_60)
      | v1_xboole_0(B_60)
      | ~ r2_hidden(A_59,B_60) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_225])).

tff(c_1331,plain,(
    ! [A_178,B_179] :
      ( k1_tarski('#skF_1'(k1_tarski(A_178))) = B_179
      | ~ v1_zfmisc_1(B_179)
      | v1_xboole_0(B_179)
      | ~ r2_hidden(A_178,B_179) ) ),
    inference(resolution,[status(thm)],[c_992,c_235])).

tff(c_1358,plain,(
    ! [A_180] :
      ( k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_180)))) = A_180
      | ~ v1_zfmisc_1(A_180)
      | v1_xboole_0(A_180) ) ),
    inference(resolution,[status(thm)],[c_4,c_1331])).

tff(c_987,plain,(
    ! [A_156,B_155] :
      ( r2_hidden('#skF_1'(k1_tarski(A_156)),B_155)
      | ~ r2_hidden(A_156,B_155) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_973])).

tff(c_7098,plain,(
    ! [A_374,B_375] :
      ( r2_hidden('#skF_1'(A_374),B_375)
      | ~ r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_374))),B_375)
      | ~ v1_zfmisc_1(A_374)
      | v1_xboole_0(A_374) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1358,c_987])).

tff(c_7162,plain,(
    ! [A_374] :
      ( r2_hidden('#skF_1'(A_374),k1_tarski('#skF_1'(A_374)))
      | ~ v1_zfmisc_1(A_374)
      | v1_xboole_0(A_374)
      | v1_xboole_0(k1_tarski('#skF_1'(A_374))) ) ),
    inference(resolution,[status(thm)],[c_4,c_7098])).

tff(c_7195,plain,(
    ! [A_376] :
      ( r2_hidden('#skF_1'(A_376),k1_tarski('#skF_1'(A_376)))
      | ~ v1_zfmisc_1(A_376)
      | v1_xboole_0(A_376) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_7162])).

tff(c_976,plain,(
    ! [A_59,B_155,A_156] :
      ( r2_hidden('#skF_1'(k1_tarski(A_59)),B_155)
      | v1_xboole_0(k1_tarski(A_59))
      | ~ r2_hidden(A_156,B_155)
      | ~ r2_hidden(A_59,k1_tarski(A_156)) ) ),
    inference(resolution,[status(thm)],[c_115,c_942])).

tff(c_1263,plain,(
    ! [A_172,B_173,A_174] :
      ( r2_hidden('#skF_1'(k1_tarski(A_172)),B_173)
      | ~ r2_hidden(A_174,B_173)
      | ~ r2_hidden(A_172,k1_tarski(A_174)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_976])).

tff(c_1284,plain,(
    ! [A_172,A_1] :
      ( r2_hidden('#skF_1'(k1_tarski(A_172)),A_1)
      | ~ r2_hidden(A_172,k1_tarski('#skF_1'(A_1)))
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_1263])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_96,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(A_55,B_56)
      | ~ m1_subset_1(A_55,k1_zfmisc_1(B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_109,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_50,c_96])).

tff(c_1102,plain,(
    ! [A_164,B_165,B_166] :
      ( r2_hidden('#skF_1'(k1_tarski(A_164)),B_165)
      | ~ r1_tarski(B_166,B_165)
      | ~ r2_hidden(A_164,B_166) ) ),
    inference(resolution,[status(thm)],[c_992,c_6])).

tff(c_1142,plain,(
    ! [A_167] :
      ( r2_hidden('#skF_1'(k1_tarski(A_167)),u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_167,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_109,c_1102])).

tff(c_2505,plain,(
    ! [A_229] :
      ( r2_hidden('#skF_1'(A_229),u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_229),'#skF_5')
      | ~ v1_zfmisc_1(A_229)
      | v1_xboole_0(A_229) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_1142])).

tff(c_275,plain,(
    ! [A_90] :
      ( k1_tarski('#skF_1'(A_90)) = A_90
      | ~ v1_zfmisc_1(A_90)
      | v1_xboole_0(A_90) ) ),
    inference(resolution,[status(thm)],[c_4,c_257])).

tff(c_281,plain,(
    ! [A_90,B_60] :
      ( r1_tarski(A_90,B_60)
      | ~ r2_hidden('#skF_1'(A_90),B_60)
      | ~ v1_zfmisc_1(A_90)
      | v1_xboole_0(A_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_115])).

tff(c_2547,plain,(
    ! [A_232] :
      ( r1_tarski(A_232,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_232),'#skF_5')
      | ~ v1_zfmisc_1(A_232)
      | v1_xboole_0(A_232) ) ),
    inference(resolution,[status(thm)],[c_2505,c_281])).

tff(c_2563,plain,(
    ! [A_172] :
      ( r1_tarski(k1_tarski(A_172),u1_struct_0('#skF_4'))
      | ~ v1_zfmisc_1(k1_tarski(A_172))
      | v1_xboole_0(k1_tarski(A_172))
      | ~ r2_hidden(A_172,k1_tarski('#skF_1'('#skF_5')))
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1284,c_2547])).

tff(c_2584,plain,(
    ! [A_172] :
      ( r1_tarski(k1_tarski(A_172),u1_struct_0('#skF_4'))
      | ~ v1_zfmisc_1(k1_tarski(A_172))
      | ~ r2_hidden(A_172,k1_tarski('#skF_1'('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_12,c_2563])).

tff(c_7230,plain,
    ( r1_tarski(k1_tarski('#skF_1'('#skF_5')),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_7195,c_2584])).

tff(c_7290,plain,
    ( r1_tarski(k1_tarski('#skF_1'('#skF_5')),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_7230])).

tff(c_7291,plain,
    ( r1_tarski(k1_tarski('#skF_1'('#skF_5')),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_7290])).

tff(c_7309,plain,(
    ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_7291])).

tff(c_7312,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_7309])).

tff(c_7314,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_71,c_7312])).

tff(c_7316,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_7314])).

tff(c_7317,plain,(
    r1_tarski(k1_tarski('#skF_1'('#skF_5')),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_7291])).

tff(c_137,plain,(
    ! [A_1,B_66] :
      ( r2_hidden('#skF_1'(A_1),B_66)
      | ~ r1_tarski(A_1,B_66)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_131])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,B_14)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1030,plain,(
    ! [A_158,B_159] :
      ( m1_subset_1('#skF_1'(k1_tarski(A_158)),B_159)
      | ~ r2_hidden(A_158,B_159) ) ),
    inference(resolution,[status(thm)],[c_992,c_16])).

tff(c_6853,plain,(
    ! [A_365,B_366] :
      ( m1_subset_1('#skF_1'(A_365),B_366)
      | ~ r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_365))),B_366)
      | ~ v1_zfmisc_1(A_365)
      | v1_xboole_0(A_365) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1358,c_1030])).

tff(c_6913,plain,(
    ! [A_365,B_66] :
      ( m1_subset_1('#skF_1'(A_365),B_66)
      | ~ v1_zfmisc_1(A_365)
      | v1_xboole_0(A_365)
      | ~ r1_tarski(k1_tarski('#skF_1'(A_365)),B_66)
      | v1_xboole_0(k1_tarski('#skF_1'(A_365))) ) ),
    inference(resolution,[status(thm)],[c_137,c_6853])).

tff(c_6946,plain,(
    ! [A_365,B_66] :
      ( m1_subset_1('#skF_1'(A_365),B_66)
      | ~ v1_zfmisc_1(A_365)
      | v1_xboole_0(A_365)
      | ~ r1_tarski(k1_tarski('#skF_1'(A_365)),B_66) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_6913])).

tff(c_7327,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_7317,c_6946])).

tff(c_7371,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_7327])).

tff(c_7372,plain,(
    m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_7371])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_180,plain,(
    ! [B_78,A_79] :
      ( ~ v1_xboole_0(B_78)
      | ~ r1_tarski(A_79,B_78)
      | v1_xboole_0(A_79) ) ),
    inference(resolution,[status(thm)],[c_168,c_2])).

tff(c_195,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_109,c_180])).

tff(c_203,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_195])).

tff(c_28,plain,(
    ! [A_22,B_23] :
      ( k6_domain_1(A_22,B_23) = k1_tarski(B_23)
      | ~ m1_subset_1(B_23,A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_7418,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')) = k1_tarski('#skF_1'('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_7372,c_28])).

tff(c_7421,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')) = k1_tarski('#skF_1'('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_203,c_7418])).

tff(c_48,plain,(
    ! [A_37,B_39] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_37),B_39),A_37)
      | ~ m1_subset_1(B_39,u1_struct_0(A_37))
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_7431,plain,
    ( v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7421,c_48])).

tff(c_7449,plain,
    ( v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_7372,c_7431])).

tff(c_7450,plain,(
    v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_7449])).

tff(c_7469,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_7450])).

tff(c_7471,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_7469])).

tff(c_7473,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_73,c_7471])).

tff(c_7474,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_8181,plain,(
    ! [A_478,B_479] :
      ( m1_pre_topc('#skF_3'(A_478,B_479),A_478)
      | ~ v2_tex_2(B_479,A_478)
      | ~ m1_subset_1(B_479,k1_zfmisc_1(u1_struct_0(A_478)))
      | v1_xboole_0(B_479)
      | ~ l1_pre_topc(A_478)
      | ~ v2_pre_topc(A_478)
      | v2_struct_0(A_478) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_8201,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_8181])).

tff(c_8212,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_7474,c_8201])).

tff(c_8213,plain,(
    m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_52,c_8212])).

tff(c_24,plain,(
    ! [B_20,A_18] :
      ( l1_pre_topc(B_20)
      | ~ m1_pre_topc(B_20,A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8219,plain,
    ( l1_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_8213,c_24])).

tff(c_8226,plain,(
    l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_8219])).

tff(c_22,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_7475,plain,(
    ~ v1_zfmisc_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_7974,plain,(
    ! [A_461,B_462] :
      ( ~ v2_struct_0('#skF_3'(A_461,B_462))
      | ~ v2_tex_2(B_462,A_461)
      | ~ m1_subset_1(B_462,k1_zfmisc_1(u1_struct_0(A_461)))
      | v1_xboole_0(B_462)
      | ~ l1_pre_topc(A_461)
      | ~ v2_pre_topc(A_461)
      | v2_struct_0(A_461) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_8001,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_7974])).

tff(c_8012,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_7474,c_8001])).

tff(c_8013,plain,(
    ~ v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_52,c_8012])).

tff(c_56,plain,(
    v2_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_7781,plain,(
    ! [A_445,B_446] :
      ( v1_tdlat_3('#skF_3'(A_445,B_446))
      | ~ v2_tex_2(B_446,A_445)
      | ~ m1_subset_1(B_446,k1_zfmisc_1(u1_struct_0(A_445)))
      | v1_xboole_0(B_446)
      | ~ l1_pre_topc(A_445)
      | ~ v2_pre_topc(A_445)
      | v2_struct_0(A_445) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_7808,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_7781])).

tff(c_7819,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_7474,c_7808])).

tff(c_7820,plain,(
    v1_tdlat_3('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_52,c_7819])).

tff(c_32,plain,(
    ! [B_27,A_25] :
      ( ~ v1_tdlat_3(B_27)
      | v7_struct_0(B_27)
      | v2_struct_0(B_27)
      | ~ m1_pre_topc(B_27,A_25)
      | ~ l1_pre_topc(A_25)
      | ~ v2_tdlat_3(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_8216,plain,
    ( ~ v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v7_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_8213,c_32])).

tff(c_8222,plain,
    ( v7_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_7820,c_8216])).

tff(c_8223,plain,(
    v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_8013,c_8222])).

tff(c_8354,plain,(
    ! [A_490,B_491] :
      ( u1_struct_0('#skF_3'(A_490,B_491)) = B_491
      | ~ v2_tex_2(B_491,A_490)
      | ~ m1_subset_1(B_491,k1_zfmisc_1(u1_struct_0(A_490)))
      | v1_xboole_0(B_491)
      | ~ l1_pre_topc(A_490)
      | ~ v2_pre_topc(A_490)
      | v2_struct_0(A_490) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_8388,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_8354])).

tff(c_8404,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_7474,c_8388])).

tff(c_8405,plain,(
    u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_52,c_8404])).

tff(c_26,plain,(
    ! [A_21] :
      ( v1_zfmisc_1(u1_struct_0(A_21))
      | ~ l1_struct_0(A_21)
      | ~ v7_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8426,plain,
    ( v1_zfmisc_1('#skF_5')
    | ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8405,c_26])).

tff(c_8448,plain,
    ( v1_zfmisc_1('#skF_5')
    | ~ l1_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8223,c_8426])).

tff(c_8449,plain,(
    ~ l1_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_7475,c_8448])).

tff(c_8453,plain,(
    ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_22,c_8449])).

tff(c_8457,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8226,c_8453])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:59:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.51/2.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.75/2.68  
% 7.75/2.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.75/2.69  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 7.75/2.69  
% 7.75/2.69  %Foreground sorts:
% 7.75/2.69  
% 7.75/2.69  
% 7.75/2.69  %Background operators:
% 7.75/2.69  
% 7.75/2.69  
% 7.75/2.69  %Foreground operators:
% 7.75/2.69  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.75/2.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.75/2.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.75/2.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.75/2.69  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.75/2.69  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 7.75/2.69  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.75/2.69  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 7.75/2.69  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.75/2.69  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 7.75/2.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.75/2.69  tff('#skF_5', type, '#skF_5': $i).
% 7.75/2.69  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 7.75/2.69  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 7.75/2.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.75/2.69  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.75/2.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.75/2.69  tff('#skF_4', type, '#skF_4': $i).
% 7.75/2.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.75/2.69  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.75/2.69  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 7.75/2.69  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.75/2.69  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.75/2.69  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.75/2.69  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.75/2.69  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 7.75/2.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.75/2.69  
% 7.88/2.71  tff(f_181, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 7.88/2.71  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.88/2.71  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 7.88/2.71  tff(f_45, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 7.88/2.71  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.88/2.71  tff(f_120, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 7.88/2.71  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.88/2.71  tff(f_49, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 7.88/2.71  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 7.88/2.71  tff(f_161, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 7.88/2.71  tff(f_149, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tex_2)).
% 7.88/2.71  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 7.88/2.71  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.88/2.71  tff(f_107, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((~v2_struct_0(B) & ~v7_struct_0(B)) => (~v2_struct_0(B) & ~v1_tdlat_3(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc32_tex_2)).
% 7.88/2.71  tff(f_70, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 7.88/2.71  tff(c_54, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_181])).
% 7.88/2.71  tff(c_60, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_181])).
% 7.88/2.71  tff(c_52, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_181])).
% 7.88/2.71  tff(c_58, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_181])).
% 7.88/2.71  tff(c_68, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_181])).
% 7.88/2.71  tff(c_71, plain, (v1_zfmisc_1('#skF_5')), inference(splitLeft, [status(thm)], [c_68])).
% 7.88/2.71  tff(c_62, plain, (~v1_zfmisc_1('#skF_5') | ~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_181])).
% 7.88/2.71  tff(c_73, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_62])).
% 7.88/2.71  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.88/2.71  tff(c_12, plain, (![A_10]: (~v1_xboole_0(k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.88/2.71  tff(c_111, plain, (![A_59, B_60]: (m1_subset_1(k1_tarski(A_59), k1_zfmisc_1(B_60)) | ~r2_hidden(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.88/2.71  tff(c_18, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.88/2.71  tff(c_115, plain, (![A_59, B_60]: (r1_tarski(k1_tarski(A_59), B_60) | ~r2_hidden(A_59, B_60))), inference(resolution, [status(thm)], [c_111, c_18])).
% 7.88/2.71  tff(c_213, plain, (![B_81, A_82]: (B_81=A_82 | ~r1_tarski(A_82, B_81) | ~v1_zfmisc_1(B_81) | v1_xboole_0(B_81) | v1_xboole_0(A_82))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.88/2.71  tff(c_225, plain, (![A_59, B_60]: (k1_tarski(A_59)=B_60 | ~v1_zfmisc_1(B_60) | v1_xboole_0(B_60) | v1_xboole_0(k1_tarski(A_59)) | ~r2_hidden(A_59, B_60))), inference(resolution, [status(thm)], [c_115, c_213])).
% 7.88/2.71  tff(c_257, plain, (![A_86, B_87]: (k1_tarski(A_86)=B_87 | ~v1_zfmisc_1(B_87) | v1_xboole_0(B_87) | ~r2_hidden(A_86, B_87))), inference(negUnitSimplification, [status(thm)], [c_12, c_225])).
% 7.88/2.71  tff(c_269, plain, (![A_1]: (k1_tarski('#skF_1'(A_1))=A_1 | ~v1_zfmisc_1(A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_257])).
% 7.88/2.71  tff(c_117, plain, (![A_63, B_64]: (r2_hidden('#skF_2'(A_63, B_64), A_63) | r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.88/2.71  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.88/2.71  tff(c_128, plain, (![A_63]: (r1_tarski(A_63, A_63))), inference(resolution, [status(thm)], [c_117, c_8])).
% 7.88/2.71  tff(c_131, plain, (![C_65, B_66, A_67]: (r2_hidden(C_65, B_66) | ~r2_hidden(C_65, A_67) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.88/2.71  tff(c_168, plain, (![A_76, B_77]: (r2_hidden('#skF_1'(A_76), B_77) | ~r1_tarski(A_76, B_77) | v1_xboole_0(A_76))), inference(resolution, [status(thm)], [c_4, c_131])).
% 7.88/2.71  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.88/2.71  tff(c_545, plain, (![A_123, B_124, B_125]: (r2_hidden('#skF_1'(A_123), B_124) | ~r1_tarski(B_125, B_124) | ~r1_tarski(A_123, B_125) | v1_xboole_0(A_123))), inference(resolution, [status(thm)], [c_168, c_6])).
% 7.88/2.71  tff(c_942, plain, (![A_154, B_155, A_156]: (r2_hidden('#skF_1'(A_154), B_155) | ~r1_tarski(A_154, k1_tarski(A_156)) | v1_xboole_0(A_154) | ~r2_hidden(A_156, B_155))), inference(resolution, [status(thm)], [c_115, c_545])).
% 7.88/2.71  tff(c_973, plain, (![A_156, B_155]: (r2_hidden('#skF_1'(k1_tarski(A_156)), B_155) | v1_xboole_0(k1_tarski(A_156)) | ~r2_hidden(A_156, B_155))), inference(resolution, [status(thm)], [c_128, c_942])).
% 7.88/2.71  tff(c_992, plain, (![A_158, B_159]: (r2_hidden('#skF_1'(k1_tarski(A_158)), B_159) | ~r2_hidden(A_158, B_159))), inference(negUnitSimplification, [status(thm)], [c_12, c_973])).
% 7.88/2.71  tff(c_235, plain, (![A_59, B_60]: (k1_tarski(A_59)=B_60 | ~v1_zfmisc_1(B_60) | v1_xboole_0(B_60) | ~r2_hidden(A_59, B_60))), inference(negUnitSimplification, [status(thm)], [c_12, c_225])).
% 7.88/2.71  tff(c_1331, plain, (![A_178, B_179]: (k1_tarski('#skF_1'(k1_tarski(A_178)))=B_179 | ~v1_zfmisc_1(B_179) | v1_xboole_0(B_179) | ~r2_hidden(A_178, B_179))), inference(resolution, [status(thm)], [c_992, c_235])).
% 7.88/2.71  tff(c_1358, plain, (![A_180]: (k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_180))))=A_180 | ~v1_zfmisc_1(A_180) | v1_xboole_0(A_180))), inference(resolution, [status(thm)], [c_4, c_1331])).
% 7.88/2.71  tff(c_987, plain, (![A_156, B_155]: (r2_hidden('#skF_1'(k1_tarski(A_156)), B_155) | ~r2_hidden(A_156, B_155))), inference(negUnitSimplification, [status(thm)], [c_12, c_973])).
% 7.88/2.71  tff(c_7098, plain, (![A_374, B_375]: (r2_hidden('#skF_1'(A_374), B_375) | ~r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_374))), B_375) | ~v1_zfmisc_1(A_374) | v1_xboole_0(A_374))), inference(superposition, [status(thm), theory('equality')], [c_1358, c_987])).
% 7.88/2.71  tff(c_7162, plain, (![A_374]: (r2_hidden('#skF_1'(A_374), k1_tarski('#skF_1'(A_374))) | ~v1_zfmisc_1(A_374) | v1_xboole_0(A_374) | v1_xboole_0(k1_tarski('#skF_1'(A_374))))), inference(resolution, [status(thm)], [c_4, c_7098])).
% 7.88/2.71  tff(c_7195, plain, (![A_376]: (r2_hidden('#skF_1'(A_376), k1_tarski('#skF_1'(A_376))) | ~v1_zfmisc_1(A_376) | v1_xboole_0(A_376))), inference(negUnitSimplification, [status(thm)], [c_12, c_7162])).
% 7.88/2.71  tff(c_976, plain, (![A_59, B_155, A_156]: (r2_hidden('#skF_1'(k1_tarski(A_59)), B_155) | v1_xboole_0(k1_tarski(A_59)) | ~r2_hidden(A_156, B_155) | ~r2_hidden(A_59, k1_tarski(A_156)))), inference(resolution, [status(thm)], [c_115, c_942])).
% 7.88/2.71  tff(c_1263, plain, (![A_172, B_173, A_174]: (r2_hidden('#skF_1'(k1_tarski(A_172)), B_173) | ~r2_hidden(A_174, B_173) | ~r2_hidden(A_172, k1_tarski(A_174)))), inference(negUnitSimplification, [status(thm)], [c_12, c_976])).
% 7.88/2.71  tff(c_1284, plain, (![A_172, A_1]: (r2_hidden('#skF_1'(k1_tarski(A_172)), A_1) | ~r2_hidden(A_172, k1_tarski('#skF_1'(A_1))) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_1263])).
% 7.88/2.71  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_181])).
% 7.88/2.71  tff(c_96, plain, (![A_55, B_56]: (r1_tarski(A_55, B_56) | ~m1_subset_1(A_55, k1_zfmisc_1(B_56)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.88/2.71  tff(c_109, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_96])).
% 7.88/2.71  tff(c_1102, plain, (![A_164, B_165, B_166]: (r2_hidden('#skF_1'(k1_tarski(A_164)), B_165) | ~r1_tarski(B_166, B_165) | ~r2_hidden(A_164, B_166))), inference(resolution, [status(thm)], [c_992, c_6])).
% 7.88/2.71  tff(c_1142, plain, (![A_167]: (r2_hidden('#skF_1'(k1_tarski(A_167)), u1_struct_0('#skF_4')) | ~r2_hidden(A_167, '#skF_5'))), inference(resolution, [status(thm)], [c_109, c_1102])).
% 7.88/2.71  tff(c_2505, plain, (![A_229]: (r2_hidden('#skF_1'(A_229), u1_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(A_229), '#skF_5') | ~v1_zfmisc_1(A_229) | v1_xboole_0(A_229))), inference(superposition, [status(thm), theory('equality')], [c_269, c_1142])).
% 7.88/2.71  tff(c_275, plain, (![A_90]: (k1_tarski('#skF_1'(A_90))=A_90 | ~v1_zfmisc_1(A_90) | v1_xboole_0(A_90))), inference(resolution, [status(thm)], [c_4, c_257])).
% 7.88/2.71  tff(c_281, plain, (![A_90, B_60]: (r1_tarski(A_90, B_60) | ~r2_hidden('#skF_1'(A_90), B_60) | ~v1_zfmisc_1(A_90) | v1_xboole_0(A_90))), inference(superposition, [status(thm), theory('equality')], [c_275, c_115])).
% 7.88/2.71  tff(c_2547, plain, (![A_232]: (r1_tarski(A_232, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(A_232), '#skF_5') | ~v1_zfmisc_1(A_232) | v1_xboole_0(A_232))), inference(resolution, [status(thm)], [c_2505, c_281])).
% 7.88/2.71  tff(c_2563, plain, (![A_172]: (r1_tarski(k1_tarski(A_172), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski(A_172)) | v1_xboole_0(k1_tarski(A_172)) | ~r2_hidden(A_172, k1_tarski('#skF_1'('#skF_5'))) | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_1284, c_2547])).
% 7.88/2.71  tff(c_2584, plain, (![A_172]: (r1_tarski(k1_tarski(A_172), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski(A_172)) | ~r2_hidden(A_172, k1_tarski('#skF_1'('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_12, c_2563])).
% 7.88/2.71  tff(c_7230, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_7195, c_2584])).
% 7.88/2.71  tff(c_7290, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_7230])).
% 7.88/2.71  tff(c_7291, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_52, c_7290])).
% 7.88/2.71  tff(c_7309, plain, (~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))), inference(splitLeft, [status(thm)], [c_7291])).
% 7.88/2.71  tff(c_7312, plain, (~v1_zfmisc_1('#skF_5') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_269, c_7309])).
% 7.88/2.71  tff(c_7314, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_71, c_7312])).
% 7.88/2.71  tff(c_7316, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_7314])).
% 7.88/2.71  tff(c_7317, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_7291])).
% 7.88/2.71  tff(c_137, plain, (![A_1, B_66]: (r2_hidden('#skF_1'(A_1), B_66) | ~r1_tarski(A_1, B_66) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_131])).
% 7.88/2.71  tff(c_16, plain, (![A_13, B_14]: (m1_subset_1(A_13, B_14) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.88/2.71  tff(c_1030, plain, (![A_158, B_159]: (m1_subset_1('#skF_1'(k1_tarski(A_158)), B_159) | ~r2_hidden(A_158, B_159))), inference(resolution, [status(thm)], [c_992, c_16])).
% 7.88/2.71  tff(c_6853, plain, (![A_365, B_366]: (m1_subset_1('#skF_1'(A_365), B_366) | ~r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_365))), B_366) | ~v1_zfmisc_1(A_365) | v1_xboole_0(A_365))), inference(superposition, [status(thm), theory('equality')], [c_1358, c_1030])).
% 7.88/2.71  tff(c_6913, plain, (![A_365, B_66]: (m1_subset_1('#skF_1'(A_365), B_66) | ~v1_zfmisc_1(A_365) | v1_xboole_0(A_365) | ~r1_tarski(k1_tarski('#skF_1'(A_365)), B_66) | v1_xboole_0(k1_tarski('#skF_1'(A_365))))), inference(resolution, [status(thm)], [c_137, c_6853])).
% 7.88/2.71  tff(c_6946, plain, (![A_365, B_66]: (m1_subset_1('#skF_1'(A_365), B_66) | ~v1_zfmisc_1(A_365) | v1_xboole_0(A_365) | ~r1_tarski(k1_tarski('#skF_1'(A_365)), B_66))), inference(negUnitSimplification, [status(thm)], [c_12, c_6913])).
% 7.88/2.71  tff(c_7327, plain, (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_7317, c_6946])).
% 7.88/2.71  tff(c_7371, plain, (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_7327])).
% 7.88/2.71  tff(c_7372, plain, (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_52, c_7371])).
% 7.88/2.71  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.88/2.71  tff(c_180, plain, (![B_78, A_79]: (~v1_xboole_0(B_78) | ~r1_tarski(A_79, B_78) | v1_xboole_0(A_79))), inference(resolution, [status(thm)], [c_168, c_2])).
% 7.88/2.71  tff(c_195, plain, (~v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_109, c_180])).
% 7.88/2.71  tff(c_203, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_52, c_195])).
% 7.88/2.71  tff(c_28, plain, (![A_22, B_23]: (k6_domain_1(A_22, B_23)=k1_tarski(B_23) | ~m1_subset_1(B_23, A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.88/2.71  tff(c_7418, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'('#skF_5'))=k1_tarski('#skF_1'('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_7372, c_28])).
% 7.88/2.71  tff(c_7421, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'('#skF_5'))=k1_tarski('#skF_1'('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_203, c_7418])).
% 7.88/2.71  tff(c_48, plain, (![A_37, B_39]: (v2_tex_2(k6_domain_1(u1_struct_0(A_37), B_39), A_37) | ~m1_subset_1(B_39, u1_struct_0(A_37)) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.88/2.71  tff(c_7431, plain, (v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7421, c_48])).
% 7.88/2.71  tff(c_7449, plain, (v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_7372, c_7431])).
% 7.88/2.71  tff(c_7450, plain, (v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_60, c_7449])).
% 7.88/2.71  tff(c_7469, plain, (v2_tex_2('#skF_5', '#skF_4') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_269, c_7450])).
% 7.88/2.71  tff(c_7471, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_7469])).
% 7.88/2.71  tff(c_7473, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_73, c_7471])).
% 7.88/2.71  tff(c_7474, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_68])).
% 7.88/2.71  tff(c_8181, plain, (![A_478, B_479]: (m1_pre_topc('#skF_3'(A_478, B_479), A_478) | ~v2_tex_2(B_479, A_478) | ~m1_subset_1(B_479, k1_zfmisc_1(u1_struct_0(A_478))) | v1_xboole_0(B_479) | ~l1_pre_topc(A_478) | ~v2_pre_topc(A_478) | v2_struct_0(A_478))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.88/2.71  tff(c_8201, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_50, c_8181])).
% 7.88/2.71  tff(c_8212, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_7474, c_8201])).
% 7.88/2.71  tff(c_8213, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_60, c_52, c_8212])).
% 7.88/2.71  tff(c_24, plain, (![B_20, A_18]: (l1_pre_topc(B_20) | ~m1_pre_topc(B_20, A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.88/2.71  tff(c_8219, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_8213, c_24])).
% 7.88/2.71  tff(c_8226, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_8219])).
% 7.88/2.71  tff(c_22, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.88/2.71  tff(c_7475, plain, (~v1_zfmisc_1('#skF_5')), inference(splitRight, [status(thm)], [c_68])).
% 7.88/2.71  tff(c_7974, plain, (![A_461, B_462]: (~v2_struct_0('#skF_3'(A_461, B_462)) | ~v2_tex_2(B_462, A_461) | ~m1_subset_1(B_462, k1_zfmisc_1(u1_struct_0(A_461))) | v1_xboole_0(B_462) | ~l1_pre_topc(A_461) | ~v2_pre_topc(A_461) | v2_struct_0(A_461))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.88/2.71  tff(c_8001, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_50, c_7974])).
% 7.88/2.71  tff(c_8012, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_7474, c_8001])).
% 7.88/2.71  tff(c_8013, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_60, c_52, c_8012])).
% 7.88/2.71  tff(c_56, plain, (v2_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_181])).
% 7.88/2.71  tff(c_7781, plain, (![A_445, B_446]: (v1_tdlat_3('#skF_3'(A_445, B_446)) | ~v2_tex_2(B_446, A_445) | ~m1_subset_1(B_446, k1_zfmisc_1(u1_struct_0(A_445))) | v1_xboole_0(B_446) | ~l1_pre_topc(A_445) | ~v2_pre_topc(A_445) | v2_struct_0(A_445))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.88/2.71  tff(c_7808, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_50, c_7781])).
% 7.88/2.71  tff(c_7819, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_7474, c_7808])).
% 7.88/2.71  tff(c_7820, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_60, c_52, c_7819])).
% 7.88/2.71  tff(c_32, plain, (![B_27, A_25]: (~v1_tdlat_3(B_27) | v7_struct_0(B_27) | v2_struct_0(B_27) | ~m1_pre_topc(B_27, A_25) | ~l1_pre_topc(A_25) | ~v2_tdlat_3(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.88/2.71  tff(c_8216, plain, (~v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v7_struct_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_8213, c_32])).
% 7.88/2.71  tff(c_8222, plain, (v7_struct_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_7820, c_8216])).
% 7.88/2.71  tff(c_8223, plain, (v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_60, c_8013, c_8222])).
% 7.88/2.71  tff(c_8354, plain, (![A_490, B_491]: (u1_struct_0('#skF_3'(A_490, B_491))=B_491 | ~v2_tex_2(B_491, A_490) | ~m1_subset_1(B_491, k1_zfmisc_1(u1_struct_0(A_490))) | v1_xboole_0(B_491) | ~l1_pre_topc(A_490) | ~v2_pre_topc(A_490) | v2_struct_0(A_490))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.88/2.71  tff(c_8388, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_50, c_8354])).
% 7.88/2.71  tff(c_8404, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_7474, c_8388])).
% 7.88/2.71  tff(c_8405, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_60, c_52, c_8404])).
% 7.88/2.71  tff(c_26, plain, (![A_21]: (v1_zfmisc_1(u1_struct_0(A_21)) | ~l1_struct_0(A_21) | ~v7_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.88/2.71  tff(c_8426, plain, (v1_zfmisc_1('#skF_5') | ~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8405, c_26])).
% 7.88/2.71  tff(c_8448, plain, (v1_zfmisc_1('#skF_5') | ~l1_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_8223, c_8426])).
% 7.88/2.71  tff(c_8449, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_7475, c_8448])).
% 7.88/2.71  tff(c_8453, plain, (~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_22, c_8449])).
% 7.88/2.71  tff(c_8457, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8226, c_8453])).
% 7.88/2.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.88/2.71  
% 7.88/2.71  Inference rules
% 7.88/2.71  ----------------------
% 7.88/2.71  #Ref     : 0
% 7.88/2.71  #Sup     : 1911
% 7.88/2.71  #Fact    : 0
% 7.88/2.71  #Define  : 0
% 7.88/2.71  #Split   : 10
% 7.88/2.71  #Chain   : 0
% 7.88/2.71  #Close   : 0
% 7.88/2.71  
% 7.88/2.71  Ordering : KBO
% 7.88/2.71  
% 7.88/2.71  Simplification rules
% 7.88/2.71  ----------------------
% 7.88/2.71  #Subsume      : 447
% 7.88/2.71  #Demod        : 190
% 7.88/2.71  #Tautology    : 180
% 7.88/2.71  #SimpNegUnit  : 427
% 7.88/2.71  #BackRed      : 0
% 7.88/2.71  
% 7.88/2.71  #Partial instantiations: 0
% 7.88/2.71  #Strategies tried      : 1
% 7.88/2.71  
% 7.88/2.71  Timing (in seconds)
% 7.88/2.71  ----------------------
% 7.88/2.71  Preprocessing        : 0.33
% 7.88/2.71  Parsing              : 0.18
% 7.88/2.71  CNF conversion       : 0.02
% 7.88/2.71  Main loop            : 1.60
% 7.88/2.71  Inferencing          : 0.50
% 7.88/2.71  Reduction            : 0.41
% 7.88/2.71  Demodulation         : 0.24
% 7.88/2.71  BG Simplification    : 0.06
% 7.88/2.71  Subsumption          : 0.48
% 7.88/2.71  Abstraction          : 0.08
% 7.88/2.71  MUC search           : 0.00
% 7.88/2.71  Cooper               : 0.00
% 7.88/2.71  Total                : 1.98
% 7.88/2.71  Index Insertion      : 0.00
% 7.88/2.71  Index Deletion       : 0.00
% 7.88/2.71  Index Matching       : 0.00
% 7.88/2.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
