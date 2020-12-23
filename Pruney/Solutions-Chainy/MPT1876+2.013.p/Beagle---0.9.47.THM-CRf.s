%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:52 EST 2020

% Result     : Theorem 10.39s
% Output     : CNFRefutation 10.39s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 564 expanded)
%              Number of leaves         :   46 ( 214 expanded)
%              Depth                    :   17
%              Number of atoms          :  399 (1924 expanded)
%              Number of equality atoms :   24 (  54 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_225,negated_conjecture,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_46,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_164,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_205,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_193,axiom,(
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

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_151,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_tdlat_3(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_tdlat_3)).

tff(f_119,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_tdlat_3(A)
       => v2_pre_topc(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).

tff(f_137,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & v2_tdlat_3(A) )
       => ( ~ v2_struct_0(A)
          & v7_struct_0(A)
          & v2_pre_topc(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_1)).

tff(f_93,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

tff(c_72,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_76,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_86,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_91,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_80,plain,
    ( ~ v1_zfmisc_1('#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_93,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_80])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_282,plain,(
    ! [A_93,C_94,B_95] :
      ( m1_subset_1(A_93,C_94)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(C_94))
      | ~ r2_hidden(A_93,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_336,plain,(
    ! [A_99,B_100,A_101] :
      ( m1_subset_1(A_99,B_100)
      | ~ r2_hidden(A_99,A_101)
      | ~ r1_tarski(A_101,B_100) ) ),
    inference(resolution,[status(thm)],[c_28,c_282])).

tff(c_342,plain,(
    ! [A_1,B_100] :
      ( m1_subset_1('#skF_1'(A_1),B_100)
      | ~ r1_tarski(A_1,B_100)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_336])).

tff(c_14,plain,(
    ! [A_10] : ~ v1_xboole_0(k1_tarski(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_141,plain,(
    ! [B_68,A_69] :
      ( m1_subset_1(B_68,A_69)
      | ~ r2_hidden(B_68,A_69)
      | v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_145,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_141])).

tff(c_250,plain,(
    ! [A_90,B_91] :
      ( k6_domain_1(A_90,B_91) = k1_tarski(B_91)
      | ~ m1_subset_1(B_91,A_90)
      | v1_xboole_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_263,plain,(
    ! [A_1] :
      ( k6_domain_1(A_1,'#skF_1'(A_1)) = k1_tarski('#skF_1'(A_1))
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_145,c_250])).

tff(c_401,plain,(
    ! [A_107,B_108] :
      ( m1_subset_1(k6_domain_1(A_107,B_108),k1_zfmisc_1(A_107))
      | ~ m1_subset_1(B_108,A_107)
      | v1_xboole_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_26,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_601,plain,(
    ! [A_115,B_116] :
      ( r1_tarski(k6_domain_1(A_115,B_116),A_115)
      | ~ m1_subset_1(B_116,A_115)
      | v1_xboole_0(A_115) ) ),
    inference(resolution,[status(thm)],[c_401,c_26])).

tff(c_1991,plain,(
    ! [A_189] :
      ( r1_tarski(k1_tarski('#skF_1'(A_189)),A_189)
      | ~ m1_subset_1('#skF_1'(A_189),A_189)
      | v1_xboole_0(A_189)
      | v1_xboole_0(A_189) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_601])).

tff(c_12,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(A_7,C_9)
      | ~ r1_tarski(B_8,C_9)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5851,plain,(
    ! [A_292,A_293] :
      ( r1_tarski(A_292,A_293)
      | ~ r1_tarski(A_292,k1_tarski('#skF_1'(A_293)))
      | ~ m1_subset_1('#skF_1'(A_293),A_293)
      | v1_xboole_0(A_293) ) ),
    inference(resolution,[status(thm)],[c_1991,c_12])).

tff(c_5881,plain,(
    ! [A_293] :
      ( r1_tarski(k1_tarski('#skF_1'(A_293)),A_293)
      | ~ m1_subset_1('#skF_1'(A_293),A_293)
      | v1_xboole_0(A_293) ) ),
    inference(resolution,[status(thm)],[c_10,c_5851])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_111,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(A_62,B_63)
      | ~ m1_subset_1(A_62,k1_zfmisc_1(B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_120,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_68,c_111])).

tff(c_209,plain,(
    ! [A_83,C_84,B_85] :
      ( r1_tarski(A_83,C_84)
      | ~ r1_tarski(B_85,C_84)
      | ~ r1_tarski(A_83,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_214,plain,(
    ! [A_83] :
      ( r1_tarski(A_83,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_83,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_120,c_209])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( r2_hidden(B_12,A_11)
      | ~ m1_subset_1(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_661,plain,(
    ! [B_119,B_120,A_121] :
      ( m1_subset_1(B_119,B_120)
      | ~ r1_tarski(A_121,B_120)
      | ~ m1_subset_1(B_119,A_121)
      | v1_xboole_0(A_121) ) ),
    inference(resolution,[status(thm)],[c_18,c_336])).

tff(c_1496,plain,(
    ! [B_165,A_166] :
      ( m1_subset_1(B_165,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_165,A_166)
      | v1_xboole_0(A_166)
      | ~ r1_tarski(A_166,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_214,c_661])).

tff(c_12572,plain,(
    ! [A_421,B_422] :
      ( m1_subset_1('#skF_1'(A_421),u1_struct_0('#skF_3'))
      | v1_xboole_0(B_422)
      | ~ r1_tarski(B_422,'#skF_4')
      | ~ r1_tarski(A_421,B_422)
      | v1_xboole_0(A_421) ) ),
    inference(resolution,[status(thm)],[c_342,c_1496])).

tff(c_12575,plain,(
    ! [A_421] :
      ( m1_subset_1('#skF_1'(A_421),u1_struct_0('#skF_3'))
      | v1_xboole_0(k1_tarski('#skF_1'('#skF_4')))
      | ~ r1_tarski(A_421,k1_tarski('#skF_1'('#skF_4')))
      | v1_xboole_0(A_421)
      | ~ m1_subset_1('#skF_1'('#skF_4'),'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5881,c_12572])).

tff(c_12593,plain,(
    ! [A_421] :
      ( m1_subset_1('#skF_1'(A_421),u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_421,k1_tarski('#skF_1'('#skF_4')))
      | v1_xboole_0(A_421)
      | ~ m1_subset_1('#skF_1'('#skF_4'),'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_14,c_12575])).

tff(c_13180,plain,(
    ~ m1_subset_1('#skF_1'('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_12593])).

tff(c_13183,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_342,c_13180])).

tff(c_13192,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_13183])).

tff(c_13194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_13192])).

tff(c_13196,plain,(
    m1_subset_1('#skF_1'('#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_12593])).

tff(c_691,plain,(
    ! [B_119,A_83] :
      ( m1_subset_1(B_119,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_119,A_83)
      | v1_xboole_0(A_83)
      | ~ r1_tarski(A_83,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_214,c_661])).

tff(c_13200,plain,
    ( m1_subset_1('#skF_1'('#skF_4'),u1_struct_0('#skF_3'))
    | v1_xboole_0('#skF_4')
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_13196,c_691])).

tff(c_13211,plain,
    ( m1_subset_1('#skF_1'('#skF_4'),u1_struct_0('#skF_3'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_13200])).

tff(c_13212,plain,(
    m1_subset_1('#skF_1'('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_13211])).

tff(c_40,plain,(
    ! [A_28,B_29] :
      ( k6_domain_1(A_28,B_29) = k1_tarski(B_29)
      | ~ m1_subset_1(B_29,A_28)
      | v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_13203,plain,
    ( k6_domain_1('#skF_4','#skF_1'('#skF_4')) = k1_tarski('#skF_1'('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_13196,c_40])).

tff(c_13215,plain,(
    k6_domain_1('#skF_4','#skF_1'('#skF_4')) = k1_tarski('#skF_1'('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_13203])).

tff(c_54,plain,(
    ! [B_38,A_36] :
      ( B_38 = A_36
      | ~ r1_tarski(A_36,B_38)
      | ~ v1_zfmisc_1(B_38)
      | v1_xboole_0(B_38)
      | v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_7013,plain,(
    ! [A_307,B_308] :
      ( k6_domain_1(A_307,B_308) = A_307
      | ~ v1_zfmisc_1(A_307)
      | v1_xboole_0(k6_domain_1(A_307,B_308))
      | ~ m1_subset_1(B_308,A_307)
      | v1_xboole_0(A_307) ) ),
    inference(resolution,[status(thm)],[c_601,c_54])).

tff(c_7067,plain,(
    ! [A_1] :
      ( k6_domain_1(A_1,'#skF_1'(A_1)) = A_1
      | ~ v1_zfmisc_1(A_1)
      | v1_xboole_0(k1_tarski('#skF_1'(A_1)))
      | ~ m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1)
      | v1_xboole_0(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_7013])).

tff(c_9810,plain,(
    ! [A_376] :
      ( k6_domain_1(A_376,'#skF_1'(A_376)) = A_376
      | ~ v1_zfmisc_1(A_376)
      | ~ m1_subset_1('#skF_1'(A_376),A_376)
      | v1_xboole_0(A_376)
      | v1_xboole_0(A_376) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_7067])).

tff(c_9862,plain,(
    ! [B_100] :
      ( k6_domain_1(B_100,'#skF_1'(B_100)) = B_100
      | ~ v1_zfmisc_1(B_100)
      | ~ r1_tarski(B_100,B_100)
      | v1_xboole_0(B_100) ) ),
    inference(resolution,[status(thm)],[c_342,c_9810])).

tff(c_9903,plain,(
    ! [B_100] :
      ( k6_domain_1(B_100,'#skF_1'(B_100)) = B_100
      | ~ v1_zfmisc_1(B_100)
      | v1_xboole_0(B_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_9862])).

tff(c_13247,plain,
    ( k1_tarski('#skF_1'('#skF_4')) = '#skF_4'
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_13215,c_9903])).

tff(c_13305,plain,
    ( k1_tarski('#skF_1'('#skF_4')) = '#skF_4'
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_13247])).

tff(c_13306,plain,(
    k1_tarski('#skF_1'('#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_13305])).

tff(c_176,plain,(
    ! [B_75,A_76] :
      ( v1_xboole_0(B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_76))
      | ~ v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_190,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_68,c_176])).

tff(c_196,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_190])).

tff(c_1545,plain,(
    ! [A_167] :
      ( m1_subset_1('#skF_1'(A_167),u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_167,'#skF_4')
      | v1_xboole_0(A_167) ) ),
    inference(resolution,[status(thm)],[c_145,c_1496])).

tff(c_1550,plain,(
    ! [A_167] :
      ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_1'(A_167)) = k1_tarski('#skF_1'(A_167))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_167,'#skF_4')
      | v1_xboole_0(A_167) ) ),
    inference(resolution,[status(thm)],[c_1545,c_40])).

tff(c_3122,plain,(
    ! [A_223] :
      ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_1'(A_223)) = k1_tarski('#skF_1'(A_223))
      | ~ r1_tarski(A_223,'#skF_4')
      | v1_xboole_0(A_223) ) ),
    inference(negUnitSimplification,[status(thm)],[c_196,c_1550])).

tff(c_66,plain,(
    ! [A_45,B_47] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_45),B_47),A_45)
      | ~ m1_subset_1(B_47,u1_struct_0(A_45))
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_3137,plain,(
    ! [A_223] :
      ( v2_tex_2(k1_tarski('#skF_1'(A_223)),'#skF_3')
      | ~ m1_subset_1('#skF_1'(A_223),u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_223,'#skF_4')
      | v1_xboole_0(A_223) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3122,c_66])).

tff(c_3172,plain,(
    ! [A_223] :
      ( v2_tex_2(k1_tarski('#skF_1'(A_223)),'#skF_3')
      | ~ m1_subset_1('#skF_1'(A_223),u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_223,'#skF_4')
      | v1_xboole_0(A_223) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_3137])).

tff(c_3173,plain,(
    ! [A_223] :
      ( v2_tex_2(k1_tarski('#skF_1'(A_223)),'#skF_3')
      | ~ m1_subset_1('#skF_1'(A_223),u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_223,'#skF_4')
      | v1_xboole_0(A_223) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3172])).

tff(c_13458,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_4'),u1_struct_0('#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_13306,c_3173])).

tff(c_13558,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_13212,c_13458])).

tff(c_13560,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_93,c_13558])).

tff(c_13561,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_15233,plain,(
    ! [A_560,B_561] :
      ( m1_pre_topc('#skF_2'(A_560,B_561),A_560)
      | ~ v2_tex_2(B_561,A_560)
      | ~ m1_subset_1(B_561,k1_zfmisc_1(u1_struct_0(A_560)))
      | v1_xboole_0(B_561)
      | ~ l1_pre_topc(A_560)
      | ~ v2_pre_topc(A_560)
      | v2_struct_0(A_560) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_15256,plain,
    ( m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_15233])).

tff(c_15276,plain,
    ( m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_13561,c_15256])).

tff(c_15277,plain,(
    m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_70,c_15276])).

tff(c_34,plain,(
    ! [B_24,A_22] :
      ( l1_pre_topc(B_24)
      | ~ m1_pre_topc(B_24,A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_15283,plain,
    ( l1_pre_topc('#skF_2'('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_15277,c_34])).

tff(c_15290,plain,(
    l1_pre_topc('#skF_2'('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_15283])).

tff(c_32,plain,(
    ! [A_21] :
      ( l1_struct_0(A_21)
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_14522,plain,(
    ! [A_533,B_534] :
      ( ~ v2_struct_0('#skF_2'(A_533,B_534))
      | ~ v2_tex_2(B_534,A_533)
      | ~ m1_subset_1(B_534,k1_zfmisc_1(u1_struct_0(A_533)))
      | v1_xboole_0(B_534)
      | ~ l1_pre_topc(A_533)
      | ~ v2_pre_topc(A_533)
      | v2_struct_0(A_533) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_14554,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_14522])).

tff(c_14574,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_13561,c_14554])).

tff(c_14575,plain,(
    ~ v2_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_70,c_14574])).

tff(c_74,plain,(
    v2_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_52,plain,(
    ! [B_35,A_33] :
      ( v2_tdlat_3(B_35)
      | ~ m1_pre_topc(B_35,A_33)
      | ~ l1_pre_topc(A_33)
      | ~ v2_tdlat_3(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_15280,plain,
    ( v2_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_15277,c_52])).

tff(c_15286,plain,
    ( v2_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_15280])).

tff(c_15287,plain,(
    v2_tdlat_3('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_15286])).

tff(c_44,plain,(
    ! [A_31] :
      ( v2_pre_topc(A_31)
      | ~ v2_tdlat_3(A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_15294,plain,
    ( v2_pre_topc('#skF_2'('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_15287,c_44])).

tff(c_15314,plain,(
    v2_pre_topc('#skF_2'('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15290,c_15294])).

tff(c_15063,plain,(
    ! [A_552,B_553] :
      ( v1_tdlat_3('#skF_2'(A_552,B_553))
      | ~ v2_tex_2(B_553,A_552)
      | ~ m1_subset_1(B_553,k1_zfmisc_1(u1_struct_0(A_552)))
      | v1_xboole_0(B_553)
      | ~ l1_pre_topc(A_552)
      | ~ v2_pre_topc(A_552)
      | v2_struct_0(A_552) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_15095,plain,
    ( v1_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_15063])).

tff(c_15115,plain,
    ( v1_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_13561,c_15095])).

tff(c_15116,plain,(
    v1_tdlat_3('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_70,c_15115])).

tff(c_48,plain,(
    ! [A_32] :
      ( v7_struct_0(A_32)
      | ~ v2_tdlat_3(A_32)
      | ~ v1_tdlat_3(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_13562,plain,(
    ~ v1_zfmisc_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_15315,plain,(
    ! [A_563,B_564] :
      ( u1_struct_0('#skF_2'(A_563,B_564)) = B_564
      | ~ v2_tex_2(B_564,A_563)
      | ~ m1_subset_1(B_564,k1_zfmisc_1(u1_struct_0(A_563)))
      | v1_xboole_0(B_564)
      | ~ l1_pre_topc(A_563)
      | ~ v2_pre_topc(A_563)
      | v2_struct_0(A_563) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_15347,plain,
    ( u1_struct_0('#skF_2'('#skF_3','#skF_4')) = '#skF_4'
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_15315])).

tff(c_15367,plain,
    ( u1_struct_0('#skF_2'('#skF_3','#skF_4')) = '#skF_4'
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_13561,c_15347])).

tff(c_15368,plain,(
    u1_struct_0('#skF_2'('#skF_3','#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_70,c_15367])).

tff(c_36,plain,(
    ! [A_25] :
      ( v1_zfmisc_1(u1_struct_0(A_25))
      | ~ l1_struct_0(A_25)
      | ~ v7_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_15389,plain,
    ( v1_zfmisc_1('#skF_4')
    | ~ l1_struct_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v7_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15368,c_36])).

tff(c_15410,plain,
    ( ~ l1_struct_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v7_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_13562,c_15389])).

tff(c_15412,plain,(
    ~ v7_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_15410])).

tff(c_15415,plain,
    ( ~ v2_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | ~ v1_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_pre_topc('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_15412])).

tff(c_15418,plain,(
    v2_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15290,c_15314,c_15116,c_15287,c_15415])).

tff(c_15420,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14575,c_15418])).

tff(c_15421,plain,(
    ~ l1_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_15410])).

tff(c_15443,plain,(
    ~ l1_pre_topc('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_32,c_15421])).

tff(c_15447,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15290,c_15443])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:05:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.39/3.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.39/3.75  
% 10.39/3.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.39/3.75  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 10.39/3.75  
% 10.39/3.75  %Foreground sorts:
% 10.39/3.75  
% 10.39/3.75  
% 10.39/3.75  %Background operators:
% 10.39/3.75  
% 10.39/3.75  
% 10.39/3.75  %Foreground operators:
% 10.39/3.75  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.39/3.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.39/3.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.39/3.75  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.39/3.75  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.39/3.75  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 10.39/3.75  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.39/3.75  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 10.39/3.75  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 10.39/3.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.39/3.75  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 10.39/3.75  tff('#skF_3', type, '#skF_3': $i).
% 10.39/3.75  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 10.39/3.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.39/3.75  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 10.39/3.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.39/3.75  tff('#skF_4', type, '#skF_4': $i).
% 10.39/3.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.39/3.75  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.39/3.75  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 10.39/3.75  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 10.39/3.75  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.39/3.75  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.39/3.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.39/3.75  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 10.39/3.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.39/3.75  
% 10.39/3.78  tff(f_225, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 10.39/3.78  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.39/3.78  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 10.39/3.78  tff(f_70, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.39/3.78  tff(f_76, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 10.39/3.78  tff(f_46, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 10.39/3.78  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 10.39/3.78  tff(f_107, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 10.39/3.78  tff(f_100, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 10.39/3.78  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 10.39/3.78  tff(f_164, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 10.39/3.78  tff(f_66, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 10.39/3.78  tff(f_205, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 10.39/3.78  tff(f_193, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tex_2)).
% 10.39/3.78  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 10.39/3.78  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 10.39/3.78  tff(f_151, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_tdlat_3(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_tdlat_3)).
% 10.39/3.78  tff(f_119, axiom, (![A]: (l1_pre_topc(A) => (v2_tdlat_3(A) => v2_pre_topc(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tdlat_3)).
% 10.39/3.78  tff(f_137, axiom, (![A]: (l1_pre_topc(A) => ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & v2_tdlat_3(A)) => ((~v2_struct_0(A) & v7_struct_0(A)) & v2_pre_topc(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_1)).
% 10.39/3.78  tff(f_93, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 10.39/3.78  tff(c_72, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_225])).
% 10.39/3.78  tff(c_78, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_225])).
% 10.39/3.78  tff(c_70, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_225])).
% 10.39/3.78  tff(c_76, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_225])).
% 10.39/3.78  tff(c_86, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_225])).
% 10.39/3.78  tff(c_91, plain, (v1_zfmisc_1('#skF_4')), inference(splitLeft, [status(thm)], [c_86])).
% 10.39/3.78  tff(c_80, plain, (~v1_zfmisc_1('#skF_4') | ~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_225])).
% 10.39/3.78  tff(c_93, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_80])).
% 10.39/3.78  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.39/3.78  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.39/3.78  tff(c_28, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.39/3.78  tff(c_282, plain, (![A_93, C_94, B_95]: (m1_subset_1(A_93, C_94) | ~m1_subset_1(B_95, k1_zfmisc_1(C_94)) | ~r2_hidden(A_93, B_95))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.39/3.78  tff(c_336, plain, (![A_99, B_100, A_101]: (m1_subset_1(A_99, B_100) | ~r2_hidden(A_99, A_101) | ~r1_tarski(A_101, B_100))), inference(resolution, [status(thm)], [c_28, c_282])).
% 10.39/3.78  tff(c_342, plain, (![A_1, B_100]: (m1_subset_1('#skF_1'(A_1), B_100) | ~r1_tarski(A_1, B_100) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_336])).
% 10.39/3.78  tff(c_14, plain, (![A_10]: (~v1_xboole_0(k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.39/3.78  tff(c_141, plain, (![B_68, A_69]: (m1_subset_1(B_68, A_69) | ~r2_hidden(B_68, A_69) | v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.39/3.78  tff(c_145, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_141])).
% 10.39/3.78  tff(c_250, plain, (![A_90, B_91]: (k6_domain_1(A_90, B_91)=k1_tarski(B_91) | ~m1_subset_1(B_91, A_90) | v1_xboole_0(A_90))), inference(cnfTransformation, [status(thm)], [f_107])).
% 10.39/3.78  tff(c_263, plain, (![A_1]: (k6_domain_1(A_1, '#skF_1'(A_1))=k1_tarski('#skF_1'(A_1)) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_145, c_250])).
% 10.39/3.78  tff(c_401, plain, (![A_107, B_108]: (m1_subset_1(k6_domain_1(A_107, B_108), k1_zfmisc_1(A_107)) | ~m1_subset_1(B_108, A_107) | v1_xboole_0(A_107))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.39/3.78  tff(c_26, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~m1_subset_1(A_16, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.39/3.78  tff(c_601, plain, (![A_115, B_116]: (r1_tarski(k6_domain_1(A_115, B_116), A_115) | ~m1_subset_1(B_116, A_115) | v1_xboole_0(A_115))), inference(resolution, [status(thm)], [c_401, c_26])).
% 10.39/3.78  tff(c_1991, plain, (![A_189]: (r1_tarski(k1_tarski('#skF_1'(A_189)), A_189) | ~m1_subset_1('#skF_1'(A_189), A_189) | v1_xboole_0(A_189) | v1_xboole_0(A_189))), inference(superposition, [status(thm), theory('equality')], [c_263, c_601])).
% 10.39/3.78  tff(c_12, plain, (![A_7, C_9, B_8]: (r1_tarski(A_7, C_9) | ~r1_tarski(B_8, C_9) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.39/3.78  tff(c_5851, plain, (![A_292, A_293]: (r1_tarski(A_292, A_293) | ~r1_tarski(A_292, k1_tarski('#skF_1'(A_293))) | ~m1_subset_1('#skF_1'(A_293), A_293) | v1_xboole_0(A_293))), inference(resolution, [status(thm)], [c_1991, c_12])).
% 10.39/3.78  tff(c_5881, plain, (![A_293]: (r1_tarski(k1_tarski('#skF_1'(A_293)), A_293) | ~m1_subset_1('#skF_1'(A_293), A_293) | v1_xboole_0(A_293))), inference(resolution, [status(thm)], [c_10, c_5851])).
% 10.39/3.78  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_225])).
% 10.39/3.78  tff(c_111, plain, (![A_62, B_63]: (r1_tarski(A_62, B_63) | ~m1_subset_1(A_62, k1_zfmisc_1(B_63)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.39/3.78  tff(c_120, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_68, c_111])).
% 10.39/3.78  tff(c_209, plain, (![A_83, C_84, B_85]: (r1_tarski(A_83, C_84) | ~r1_tarski(B_85, C_84) | ~r1_tarski(A_83, B_85))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.39/3.78  tff(c_214, plain, (![A_83]: (r1_tarski(A_83, u1_struct_0('#skF_3')) | ~r1_tarski(A_83, '#skF_4'))), inference(resolution, [status(thm)], [c_120, c_209])).
% 10.39/3.78  tff(c_18, plain, (![B_12, A_11]: (r2_hidden(B_12, A_11) | ~m1_subset_1(B_12, A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.39/3.78  tff(c_661, plain, (![B_119, B_120, A_121]: (m1_subset_1(B_119, B_120) | ~r1_tarski(A_121, B_120) | ~m1_subset_1(B_119, A_121) | v1_xboole_0(A_121))), inference(resolution, [status(thm)], [c_18, c_336])).
% 10.39/3.78  tff(c_1496, plain, (![B_165, A_166]: (m1_subset_1(B_165, u1_struct_0('#skF_3')) | ~m1_subset_1(B_165, A_166) | v1_xboole_0(A_166) | ~r1_tarski(A_166, '#skF_4'))), inference(resolution, [status(thm)], [c_214, c_661])).
% 10.39/3.78  tff(c_12572, plain, (![A_421, B_422]: (m1_subset_1('#skF_1'(A_421), u1_struct_0('#skF_3')) | v1_xboole_0(B_422) | ~r1_tarski(B_422, '#skF_4') | ~r1_tarski(A_421, B_422) | v1_xboole_0(A_421))), inference(resolution, [status(thm)], [c_342, c_1496])).
% 10.39/3.78  tff(c_12575, plain, (![A_421]: (m1_subset_1('#skF_1'(A_421), u1_struct_0('#skF_3')) | v1_xboole_0(k1_tarski('#skF_1'('#skF_4'))) | ~r1_tarski(A_421, k1_tarski('#skF_1'('#skF_4'))) | v1_xboole_0(A_421) | ~m1_subset_1('#skF_1'('#skF_4'), '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_5881, c_12572])).
% 10.39/3.78  tff(c_12593, plain, (![A_421]: (m1_subset_1('#skF_1'(A_421), u1_struct_0('#skF_3')) | ~r1_tarski(A_421, k1_tarski('#skF_1'('#skF_4'))) | v1_xboole_0(A_421) | ~m1_subset_1('#skF_1'('#skF_4'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_70, c_14, c_12575])).
% 10.39/3.78  tff(c_13180, plain, (~m1_subset_1('#skF_1'('#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_12593])).
% 10.39/3.78  tff(c_13183, plain, (~r1_tarski('#skF_4', '#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_342, c_13180])).
% 10.39/3.78  tff(c_13192, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_13183])).
% 10.39/3.78  tff(c_13194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_13192])).
% 10.39/3.78  tff(c_13196, plain, (m1_subset_1('#skF_1'('#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_12593])).
% 10.39/3.78  tff(c_691, plain, (![B_119, A_83]: (m1_subset_1(B_119, u1_struct_0('#skF_3')) | ~m1_subset_1(B_119, A_83) | v1_xboole_0(A_83) | ~r1_tarski(A_83, '#skF_4'))), inference(resolution, [status(thm)], [c_214, c_661])).
% 10.39/3.78  tff(c_13200, plain, (m1_subset_1('#skF_1'('#skF_4'), u1_struct_0('#skF_3')) | v1_xboole_0('#skF_4') | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_13196, c_691])).
% 10.39/3.78  tff(c_13211, plain, (m1_subset_1('#skF_1'('#skF_4'), u1_struct_0('#skF_3')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_13200])).
% 10.39/3.78  tff(c_13212, plain, (m1_subset_1('#skF_1'('#skF_4'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_70, c_13211])).
% 10.39/3.78  tff(c_40, plain, (![A_28, B_29]: (k6_domain_1(A_28, B_29)=k1_tarski(B_29) | ~m1_subset_1(B_29, A_28) | v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_107])).
% 10.39/3.78  tff(c_13203, plain, (k6_domain_1('#skF_4', '#skF_1'('#skF_4'))=k1_tarski('#skF_1'('#skF_4')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_13196, c_40])).
% 10.39/3.78  tff(c_13215, plain, (k6_domain_1('#skF_4', '#skF_1'('#skF_4'))=k1_tarski('#skF_1'('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_70, c_13203])).
% 10.39/3.78  tff(c_54, plain, (![B_38, A_36]: (B_38=A_36 | ~r1_tarski(A_36, B_38) | ~v1_zfmisc_1(B_38) | v1_xboole_0(B_38) | v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_164])).
% 10.39/3.78  tff(c_7013, plain, (![A_307, B_308]: (k6_domain_1(A_307, B_308)=A_307 | ~v1_zfmisc_1(A_307) | v1_xboole_0(k6_domain_1(A_307, B_308)) | ~m1_subset_1(B_308, A_307) | v1_xboole_0(A_307))), inference(resolution, [status(thm)], [c_601, c_54])).
% 10.39/3.78  tff(c_7067, plain, (![A_1]: (k6_domain_1(A_1, '#skF_1'(A_1))=A_1 | ~v1_zfmisc_1(A_1) | v1_xboole_0(k1_tarski('#skF_1'(A_1))) | ~m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1) | v1_xboole_0(A_1))), inference(superposition, [status(thm), theory('equality')], [c_263, c_7013])).
% 10.39/3.78  tff(c_9810, plain, (![A_376]: (k6_domain_1(A_376, '#skF_1'(A_376))=A_376 | ~v1_zfmisc_1(A_376) | ~m1_subset_1('#skF_1'(A_376), A_376) | v1_xboole_0(A_376) | v1_xboole_0(A_376))), inference(negUnitSimplification, [status(thm)], [c_14, c_7067])).
% 10.39/3.78  tff(c_9862, plain, (![B_100]: (k6_domain_1(B_100, '#skF_1'(B_100))=B_100 | ~v1_zfmisc_1(B_100) | ~r1_tarski(B_100, B_100) | v1_xboole_0(B_100))), inference(resolution, [status(thm)], [c_342, c_9810])).
% 10.39/3.78  tff(c_9903, plain, (![B_100]: (k6_domain_1(B_100, '#skF_1'(B_100))=B_100 | ~v1_zfmisc_1(B_100) | v1_xboole_0(B_100))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_9862])).
% 10.39/3.78  tff(c_13247, plain, (k1_tarski('#skF_1'('#skF_4'))='#skF_4' | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_13215, c_9903])).
% 10.39/3.78  tff(c_13305, plain, (k1_tarski('#skF_1'('#skF_4'))='#skF_4' | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_13247])).
% 10.39/3.78  tff(c_13306, plain, (k1_tarski('#skF_1'('#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_70, c_13305])).
% 10.39/3.78  tff(c_176, plain, (![B_75, A_76]: (v1_xboole_0(B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(A_76)) | ~v1_xboole_0(A_76))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.39/3.78  tff(c_190, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_68, c_176])).
% 10.39/3.78  tff(c_196, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_70, c_190])).
% 10.39/3.78  tff(c_1545, plain, (![A_167]: (m1_subset_1('#skF_1'(A_167), u1_struct_0('#skF_3')) | ~r1_tarski(A_167, '#skF_4') | v1_xboole_0(A_167))), inference(resolution, [status(thm)], [c_145, c_1496])).
% 10.39/3.78  tff(c_1550, plain, (![A_167]: (k6_domain_1(u1_struct_0('#skF_3'), '#skF_1'(A_167))=k1_tarski('#skF_1'(A_167)) | v1_xboole_0(u1_struct_0('#skF_3')) | ~r1_tarski(A_167, '#skF_4') | v1_xboole_0(A_167))), inference(resolution, [status(thm)], [c_1545, c_40])).
% 10.39/3.78  tff(c_3122, plain, (![A_223]: (k6_domain_1(u1_struct_0('#skF_3'), '#skF_1'(A_223))=k1_tarski('#skF_1'(A_223)) | ~r1_tarski(A_223, '#skF_4') | v1_xboole_0(A_223))), inference(negUnitSimplification, [status(thm)], [c_196, c_1550])).
% 10.39/3.78  tff(c_66, plain, (![A_45, B_47]: (v2_tex_2(k6_domain_1(u1_struct_0(A_45), B_47), A_45) | ~m1_subset_1(B_47, u1_struct_0(A_45)) | ~l1_pre_topc(A_45) | ~v2_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_205])).
% 10.39/3.78  tff(c_3137, plain, (![A_223]: (v2_tex_2(k1_tarski('#skF_1'(A_223)), '#skF_3') | ~m1_subset_1('#skF_1'(A_223), u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski(A_223, '#skF_4') | v1_xboole_0(A_223))), inference(superposition, [status(thm), theory('equality')], [c_3122, c_66])).
% 10.39/3.78  tff(c_3172, plain, (![A_223]: (v2_tex_2(k1_tarski('#skF_1'(A_223)), '#skF_3') | ~m1_subset_1('#skF_1'(A_223), u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | ~r1_tarski(A_223, '#skF_4') | v1_xboole_0(A_223))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_3137])).
% 10.39/3.78  tff(c_3173, plain, (![A_223]: (v2_tex_2(k1_tarski('#skF_1'(A_223)), '#skF_3') | ~m1_subset_1('#skF_1'(A_223), u1_struct_0('#skF_3')) | ~r1_tarski(A_223, '#skF_4') | v1_xboole_0(A_223))), inference(negUnitSimplification, [status(thm)], [c_78, c_3172])).
% 10.39/3.78  tff(c_13458, plain, (v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_1'('#skF_4'), u1_struct_0('#skF_3')) | ~r1_tarski('#skF_4', '#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_13306, c_3173])).
% 10.39/3.78  tff(c_13558, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_13212, c_13458])).
% 10.39/3.78  tff(c_13560, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_93, c_13558])).
% 10.39/3.78  tff(c_13561, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_86])).
% 10.39/3.78  tff(c_15233, plain, (![A_560, B_561]: (m1_pre_topc('#skF_2'(A_560, B_561), A_560) | ~v2_tex_2(B_561, A_560) | ~m1_subset_1(B_561, k1_zfmisc_1(u1_struct_0(A_560))) | v1_xboole_0(B_561) | ~l1_pre_topc(A_560) | ~v2_pre_topc(A_560) | v2_struct_0(A_560))), inference(cnfTransformation, [status(thm)], [f_193])).
% 10.39/3.78  tff(c_15256, plain, (m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_68, c_15233])).
% 10.39/3.78  tff(c_15276, plain, (m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_13561, c_15256])).
% 10.39/3.78  tff(c_15277, plain, (m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_78, c_70, c_15276])).
% 10.39/3.78  tff(c_34, plain, (![B_24, A_22]: (l1_pre_topc(B_24) | ~m1_pre_topc(B_24, A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.39/3.78  tff(c_15283, plain, (l1_pre_topc('#skF_2'('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_15277, c_34])).
% 10.39/3.78  tff(c_15290, plain, (l1_pre_topc('#skF_2'('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_15283])).
% 10.39/3.78  tff(c_32, plain, (![A_21]: (l1_struct_0(A_21) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.39/3.78  tff(c_14522, plain, (![A_533, B_534]: (~v2_struct_0('#skF_2'(A_533, B_534)) | ~v2_tex_2(B_534, A_533) | ~m1_subset_1(B_534, k1_zfmisc_1(u1_struct_0(A_533))) | v1_xboole_0(B_534) | ~l1_pre_topc(A_533) | ~v2_pre_topc(A_533) | v2_struct_0(A_533))), inference(cnfTransformation, [status(thm)], [f_193])).
% 10.39/3.78  tff(c_14554, plain, (~v2_struct_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_68, c_14522])).
% 10.39/3.78  tff(c_14574, plain, (~v2_struct_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_13561, c_14554])).
% 10.39/3.78  tff(c_14575, plain, (~v2_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_78, c_70, c_14574])).
% 10.39/3.78  tff(c_74, plain, (v2_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_225])).
% 10.39/3.78  tff(c_52, plain, (![B_35, A_33]: (v2_tdlat_3(B_35) | ~m1_pre_topc(B_35, A_33) | ~l1_pre_topc(A_33) | ~v2_tdlat_3(A_33) | ~v2_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_151])).
% 10.39/3.78  tff(c_15280, plain, (v2_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_15277, c_52])).
% 10.39/3.78  tff(c_15286, plain, (v2_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_15280])).
% 10.39/3.78  tff(c_15287, plain, (v2_tdlat_3('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_78, c_15286])).
% 10.39/3.78  tff(c_44, plain, (![A_31]: (v2_pre_topc(A_31) | ~v2_tdlat_3(A_31) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.39/3.78  tff(c_15294, plain, (v2_pre_topc('#skF_2'('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_15287, c_44])).
% 10.39/3.78  tff(c_15314, plain, (v2_pre_topc('#skF_2'('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_15290, c_15294])).
% 10.39/3.78  tff(c_15063, plain, (![A_552, B_553]: (v1_tdlat_3('#skF_2'(A_552, B_553)) | ~v2_tex_2(B_553, A_552) | ~m1_subset_1(B_553, k1_zfmisc_1(u1_struct_0(A_552))) | v1_xboole_0(B_553) | ~l1_pre_topc(A_552) | ~v2_pre_topc(A_552) | v2_struct_0(A_552))), inference(cnfTransformation, [status(thm)], [f_193])).
% 10.39/3.78  tff(c_15095, plain, (v1_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_68, c_15063])).
% 10.39/3.78  tff(c_15115, plain, (v1_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_13561, c_15095])).
% 10.39/3.78  tff(c_15116, plain, (v1_tdlat_3('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_78, c_70, c_15115])).
% 10.39/3.78  tff(c_48, plain, (![A_32]: (v7_struct_0(A_32) | ~v2_tdlat_3(A_32) | ~v1_tdlat_3(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_137])).
% 10.39/3.78  tff(c_13562, plain, (~v1_zfmisc_1('#skF_4')), inference(splitRight, [status(thm)], [c_86])).
% 10.39/3.78  tff(c_15315, plain, (![A_563, B_564]: (u1_struct_0('#skF_2'(A_563, B_564))=B_564 | ~v2_tex_2(B_564, A_563) | ~m1_subset_1(B_564, k1_zfmisc_1(u1_struct_0(A_563))) | v1_xboole_0(B_564) | ~l1_pre_topc(A_563) | ~v2_pre_topc(A_563) | v2_struct_0(A_563))), inference(cnfTransformation, [status(thm)], [f_193])).
% 10.39/3.78  tff(c_15347, plain, (u1_struct_0('#skF_2'('#skF_3', '#skF_4'))='#skF_4' | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_68, c_15315])).
% 10.39/3.78  tff(c_15367, plain, (u1_struct_0('#skF_2'('#skF_3', '#skF_4'))='#skF_4' | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_13561, c_15347])).
% 10.39/3.78  tff(c_15368, plain, (u1_struct_0('#skF_2'('#skF_3', '#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_78, c_70, c_15367])).
% 10.39/3.78  tff(c_36, plain, (![A_25]: (v1_zfmisc_1(u1_struct_0(A_25)) | ~l1_struct_0(A_25) | ~v7_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.39/3.78  tff(c_15389, plain, (v1_zfmisc_1('#skF_4') | ~l1_struct_0('#skF_2'('#skF_3', '#skF_4')) | ~v7_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_15368, c_36])).
% 10.39/3.78  tff(c_15410, plain, (~l1_struct_0('#skF_2'('#skF_3', '#skF_4')) | ~v7_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_13562, c_15389])).
% 10.39/3.78  tff(c_15412, plain, (~v7_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_15410])).
% 10.39/3.78  tff(c_15415, plain, (~v2_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | ~v1_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | ~v2_pre_topc('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_2'('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_15412])).
% 10.39/3.78  tff(c_15418, plain, (v2_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_15290, c_15314, c_15116, c_15287, c_15415])).
% 10.39/3.78  tff(c_15420, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14575, c_15418])).
% 10.39/3.78  tff(c_15421, plain, (~l1_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_15410])).
% 10.39/3.78  tff(c_15443, plain, (~l1_pre_topc('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_32, c_15421])).
% 10.39/3.78  tff(c_15447, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15290, c_15443])).
% 10.39/3.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.39/3.78  
% 10.39/3.78  Inference rules
% 10.39/3.78  ----------------------
% 10.39/3.78  #Ref     : 0
% 10.39/3.78  #Sup     : 3342
% 10.39/3.78  #Fact    : 0
% 10.39/3.78  #Define  : 0
% 10.39/3.78  #Split   : 41
% 10.39/3.78  #Chain   : 0
% 10.39/3.78  #Close   : 0
% 10.39/3.78  
% 10.39/3.78  Ordering : KBO
% 10.39/3.78  
% 10.39/3.78  Simplification rules
% 10.39/3.78  ----------------------
% 10.39/3.78  #Subsume      : 1030
% 10.39/3.78  #Demod        : 891
% 10.39/3.78  #Tautology    : 627
% 10.39/3.78  #SimpNegUnit  : 1275
% 10.39/3.78  #BackRed      : 1
% 10.39/3.78  
% 10.39/3.78  #Partial instantiations: 0
% 10.39/3.78  #Strategies tried      : 1
% 10.39/3.78  
% 10.39/3.78  Timing (in seconds)
% 10.39/3.78  ----------------------
% 10.39/3.78  Preprocessing        : 0.34
% 10.39/3.78  Parsing              : 0.18
% 10.39/3.78  CNF conversion       : 0.03
% 10.39/3.78  Main loop            : 2.62
% 10.39/3.78  Inferencing          : 0.70
% 10.39/3.78  Reduction            : 0.82
% 10.39/3.78  Demodulation         : 0.50
% 10.39/3.78  BG Simplification    : 0.07
% 10.39/3.78  Subsumption          : 0.86
% 10.39/3.78  Abstraction          : 0.11
% 10.39/3.78  MUC search           : 0.00
% 10.39/3.78  Cooper               : 0.00
% 10.39/3.78  Total                : 3.02
% 10.39/3.78  Index Insertion      : 0.00
% 10.39/3.78  Index Deletion       : 0.00
% 10.39/3.78  Index Matching       : 0.00
% 10.39/3.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
