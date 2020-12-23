%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:55 EST 2020

% Result     : Theorem 5.98s
% Output     : CNFRefutation 5.98s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 755 expanded)
%              Number of leaves         :   46 ( 283 expanded)
%              Depth                    :   14
%              Number of atoms          :  410 (2777 expanded)
%              Number of equality atoms :    1 (   3 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k7_tmap_1 > k6_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_4 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k7_tmap_1,type,(
    k7_tmap_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_242,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ( r1_xboole_0(u1_struct_0(C),B)
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(C))
                     => r1_tmap_1(C,k6_tmap_1(A,B),k2_tmap_1(A,k6_tmap_1(A,B),k7_tmap_1(A,B),C),D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_tmap_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_98,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc4_struct_0)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_114,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_178,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ~ r2_hidden(C,B)
               => r1_tmap_1(A,k6_tmap_1(A,B),k7_tmap_1(A,B),C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_tmap_1)).

tff(f_144,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_funct_1(k7_tmap_1(A,B))
        & v1_funct_2(k7_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B)))
        & m1_subset_1(k7_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

tff(f_160,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( ~ v2_struct_0(k6_tmap_1(A,B))
        & v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tmap_1)).

tff(f_129,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_218,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(D))
                         => ( ( E = F
                              & r1_tmap_1(B,A,C,E) )
                           => r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_76,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_70,plain,(
    m1_pre_topc('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_98,plain,(
    ! [B_130,A_131] :
      ( l1_pre_topc(B_130)
      | ~ m1_pre_topc(B_130,A_131)
      | ~ l1_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_101,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_98])).

tff(c_104,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_101])).

tff(c_32,plain,(
    ! [A_23] :
      ( l1_struct_0(A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3290,plain,(
    ! [A_493] :
      ( m1_subset_1('#skF_4'(A_493),k1_zfmisc_1(u1_struct_0(A_493)))
      | ~ l1_struct_0(A_493)
      | v2_struct_0(A_493) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_28,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(A_21,B_22)
      | ~ m1_subset_1(A_21,k1_zfmisc_1(B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3294,plain,(
    ! [A_493] :
      ( r1_tarski('#skF_4'(A_493),u1_struct_0(A_493))
      | ~ l1_struct_0(A_493)
      | v2_struct_0(A_493) ) ),
    inference(resolution,[status(thm)],[c_3290,c_28])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_187,plain,(
    ! [C_159,B_160,A_161] :
      ( r2_hidden(C_159,B_160)
      | ~ r2_hidden(C_159,A_161)
      | ~ r1_tarski(A_161,B_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_202,plain,(
    ! [A_1,B_160] :
      ( r2_hidden('#skF_1'(A_1),B_160)
      | ~ r1_tarski(A_1,B_160)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_187])).

tff(c_3351,plain,(
    ! [A_498,B_499] :
      ( r2_hidden('#skF_1'(A_498),B_499)
      | ~ r1_tarski(A_498,B_499)
      | v1_xboole_0(A_498) ) ),
    inference(resolution,[status(thm)],[c_4,c_187])).

tff(c_68,plain,(
    r1_xboole_0(u1_struct_0('#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_207,plain,(
    ! [A_162,B_163,C_164] :
      ( ~ r1_xboole_0(A_162,B_163)
      | ~ r2_hidden(C_164,B_163)
      | ~ r2_hidden(C_164,A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_219,plain,(
    ! [C_164] :
      ( ~ r2_hidden(C_164,'#skF_6')
      | ~ r2_hidden(C_164,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_68,c_207])).

tff(c_3405,plain,(
    ! [A_506] :
      ( ~ r2_hidden('#skF_1'(A_506),'#skF_6')
      | ~ r1_tarski(A_506,u1_struct_0('#skF_7'))
      | v1_xboole_0(A_506) ) ),
    inference(resolution,[status(thm)],[c_3351,c_219])).

tff(c_3436,plain,(
    ! [A_507] :
      ( ~ r1_tarski(A_507,u1_struct_0('#skF_7'))
      | ~ r1_tarski(A_507,'#skF_6')
      | v1_xboole_0(A_507) ) ),
    inference(resolution,[status(thm)],[c_202,c_3405])).

tff(c_3440,plain,
    ( ~ r1_tarski('#skF_4'('#skF_7'),'#skF_6')
    | v1_xboole_0('#skF_4'('#skF_7'))
    | ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_3294,c_3436])).

tff(c_3451,plain,
    ( ~ r1_tarski('#skF_4'('#skF_7'),'#skF_6')
    | v1_xboole_0('#skF_4'('#skF_7'))
    | ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3440])).

tff(c_3455,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_3451])).

tff(c_3458,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_3455])).

tff(c_3462,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_3458])).

tff(c_3464,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_3451])).

tff(c_116,plain,(
    ! [A_137,B_138] :
      ( r2_hidden('#skF_2'(A_137,B_138),A_137)
      | r1_tarski(A_137,B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_120,plain,(
    ! [A_137,B_138] :
      ( ~ v1_xboole_0(A_137)
      | r1_tarski(A_137,B_138) ) ),
    inference(resolution,[status(thm)],[c_116,c_2])).

tff(c_3463,plain,
    ( ~ r1_tarski('#skF_4'('#skF_7'),'#skF_6')
    | v1_xboole_0('#skF_4'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_3451])).

tff(c_3465,plain,(
    ~ r1_tarski('#skF_4'('#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_3463])).

tff(c_3486,plain,(
    ~ v1_xboole_0('#skF_4'('#skF_7')) ),
    inference(resolution,[status(thm)],[c_120,c_3465])).

tff(c_269,plain,(
    ! [A_168] :
      ( m1_subset_1('#skF_4'(A_168),k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ l1_struct_0(A_168)
      | v2_struct_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_273,plain,(
    ! [A_168] :
      ( r1_tarski('#skF_4'(A_168),u1_struct_0(A_168))
      | ~ l1_struct_0(A_168)
      | v2_struct_0(A_168) ) ),
    inference(resolution,[status(thm)],[c_269,c_28])).

tff(c_252,plain,(
    ! [A_166,B_167] :
      ( r2_hidden('#skF_1'(A_166),B_167)
      | ~ r1_tarski(A_166,B_167)
      | v1_xboole_0(A_166) ) ),
    inference(resolution,[status(thm)],[c_4,c_187])).

tff(c_3182,plain,(
    ! [A_487] :
      ( ~ r2_hidden('#skF_1'(A_487),'#skF_6')
      | ~ r1_tarski(A_487,u1_struct_0('#skF_7'))
      | v1_xboole_0(A_487) ) ),
    inference(resolution,[status(thm)],[c_252,c_219])).

tff(c_3200,plain,(
    ! [A_488] :
      ( ~ r1_tarski(A_488,u1_struct_0('#skF_7'))
      | ~ r1_tarski(A_488,'#skF_6')
      | v1_xboole_0(A_488) ) ),
    inference(resolution,[status(thm)],[c_202,c_3182])).

tff(c_3204,plain,
    ( ~ r1_tarski('#skF_4'('#skF_7'),'#skF_6')
    | v1_xboole_0('#skF_4'('#skF_7'))
    | ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_273,c_3200])).

tff(c_3215,plain,
    ( ~ r1_tarski('#skF_4'('#skF_7'),'#skF_6')
    | v1_xboole_0('#skF_4'('#skF_7'))
    | ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3204])).

tff(c_3220,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_3215])).

tff(c_3240,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_3220])).

tff(c_3244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_3240])).

tff(c_3246,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_3215])).

tff(c_3245,plain,
    ( ~ r1_tarski('#skF_4'('#skF_7'),'#skF_6')
    | v1_xboole_0('#skF_4'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_3215])).

tff(c_3247,plain,(
    ~ r1_tarski('#skF_4'('#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_3245])).

tff(c_3258,plain,(
    ~ v1_xboole_0('#skF_4'('#skF_7')) ),
    inference(resolution,[status(thm)],[c_120,c_3247])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_66,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_772,plain,(
    ! [C_216,A_217,B_218] :
      ( m1_subset_1(C_216,u1_struct_0(A_217))
      | ~ m1_subset_1(C_216,u1_struct_0(B_218))
      | ~ m1_pre_topc(B_218,A_217)
      | v2_struct_0(B_218)
      | ~ l1_pre_topc(A_217)
      | v2_struct_0(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_774,plain,(
    ! [A_217] :
      ( m1_subset_1('#skF_8',u1_struct_0(A_217))
      | ~ m1_pre_topc('#skF_7',A_217)
      | v2_struct_0('#skF_7')
      | ~ l1_pre_topc(A_217)
      | v2_struct_0(A_217) ) ),
    inference(resolution,[status(thm)],[c_66,c_772])).

tff(c_777,plain,(
    ! [A_217] :
      ( m1_subset_1('#skF_8',u1_struct_0(A_217))
      | ~ m1_pre_topc('#skF_7',A_217)
      | ~ l1_pre_topc(A_217)
      | v2_struct_0(A_217) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_774])).

tff(c_26,plain,(
    ! [A_19,B_20] :
      ( r2_hidden(A_19,B_20)
      | v1_xboole_0(B_20)
      | ~ m1_subset_1(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_220,plain,(
    ! [C_165] :
      ( ~ r2_hidden(C_165,'#skF_6')
      | ~ r2_hidden(C_165,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_68,c_207])).

tff(c_241,plain,(
    ! [A_19] :
      ( ~ r2_hidden(A_19,'#skF_6')
      | v1_xboole_0(u1_struct_0('#skF_7'))
      | ~ m1_subset_1(A_19,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_26,c_220])).

tff(c_293,plain,(
    ! [A_171] :
      ( ~ r2_hidden(A_171,'#skF_6')
      | ~ m1_subset_1(A_171,u1_struct_0('#skF_7')) ) ),
    inference(splitLeft,[status(thm)],[c_241])).

tff(c_297,plain,(
    ~ r2_hidden('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_293])).

tff(c_78,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_74,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_60,plain,(
    ! [A_42,B_46,C_48] :
      ( r1_tmap_1(A_42,k6_tmap_1(A_42,B_46),k7_tmap_1(A_42,B_46),C_48)
      | r2_hidden(C_48,B_46)
      | ~ m1_subset_1(C_48,u1_struct_0(A_42))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42)
      | ~ v2_pre_topc(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_50,plain,(
    ! [A_38,B_39] :
      ( v1_funct_2(k7_tmap_1(A_38,B_39),u1_struct_0(A_38),u1_struct_0(k6_tmap_1(A_38,B_39)))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_512,plain,(
    ! [A_198,B_199] :
      ( ~ v2_struct_0(k6_tmap_1(A_198,B_199))
      | ~ m1_subset_1(B_199,k1_zfmisc_1(u1_struct_0(A_198)))
      | ~ l1_pre_topc(A_198)
      | ~ v2_pre_topc(A_198)
      | v2_struct_0(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_522,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_512])).

tff(c_527,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_522])).

tff(c_528,plain,(
    ~ v2_struct_0(k6_tmap_1('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_527])).

tff(c_303,plain,(
    ! [A_172,B_173] :
      ( v2_pre_topc(k6_tmap_1(A_172,B_173))
      | ~ m1_subset_1(B_173,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ l1_pre_topc(A_172)
      | ~ v2_pre_topc(A_172)
      | v2_struct_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_313,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_303])).

tff(c_318,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_313])).

tff(c_319,plain,(
    v2_pre_topc(k6_tmap_1('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_318])).

tff(c_388,plain,(
    ! [A_180,B_181] :
      ( l1_pre_topc(k6_tmap_1(A_180,B_181))
      | ~ m1_subset_1(B_181,k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ l1_pre_topc(A_180)
      | ~ v2_pre_topc(A_180)
      | v2_struct_0(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_398,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_388])).

tff(c_403,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_398])).

tff(c_404,plain,(
    l1_pre_topc(k6_tmap_1('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_403])).

tff(c_687,plain,(
    ! [A_207,B_208] :
      ( v1_funct_1(k7_tmap_1(A_207,B_208))
      | ~ m1_subset_1(B_208,k1_zfmisc_1(u1_struct_0(A_207)))
      | ~ l1_pre_topc(A_207)
      | ~ v2_pre_topc(A_207)
      | v2_struct_0(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_697,plain,
    ( v1_funct_1(k7_tmap_1('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_687])).

tff(c_702,plain,
    ( v1_funct_1(k7_tmap_1('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_697])).

tff(c_703,plain,(
    v1_funct_1(k7_tmap_1('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_702])).

tff(c_48,plain,(
    ! [A_38,B_39] :
      ( m1_subset_1(k7_tmap_1(A_38,B_39),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_38),u1_struct_0(k6_tmap_1(A_38,B_39)))))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_1241,plain,(
    ! [C_274,F_273,A_276,D_275,B_272] :
      ( r1_tmap_1(D_275,A_276,k2_tmap_1(B_272,A_276,C_274,D_275),F_273)
      | ~ r1_tmap_1(B_272,A_276,C_274,F_273)
      | ~ m1_subset_1(F_273,u1_struct_0(D_275))
      | ~ m1_subset_1(F_273,u1_struct_0(B_272))
      | ~ m1_pre_topc(D_275,B_272)
      | v2_struct_0(D_275)
      | ~ m1_subset_1(C_274,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_272),u1_struct_0(A_276))))
      | ~ v1_funct_2(C_274,u1_struct_0(B_272),u1_struct_0(A_276))
      | ~ v1_funct_1(C_274)
      | ~ l1_pre_topc(B_272)
      | ~ v2_pre_topc(B_272)
      | v2_struct_0(B_272)
      | ~ l1_pre_topc(A_276)
      | ~ v2_pre_topc(A_276)
      | v2_struct_0(A_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_2953,plain,(
    ! [D_469,A_470,B_471,F_472] :
      ( r1_tmap_1(D_469,k6_tmap_1(A_470,B_471),k2_tmap_1(A_470,k6_tmap_1(A_470,B_471),k7_tmap_1(A_470,B_471),D_469),F_472)
      | ~ r1_tmap_1(A_470,k6_tmap_1(A_470,B_471),k7_tmap_1(A_470,B_471),F_472)
      | ~ m1_subset_1(F_472,u1_struct_0(D_469))
      | ~ m1_subset_1(F_472,u1_struct_0(A_470))
      | ~ m1_pre_topc(D_469,A_470)
      | v2_struct_0(D_469)
      | ~ v1_funct_2(k7_tmap_1(A_470,B_471),u1_struct_0(A_470),u1_struct_0(k6_tmap_1(A_470,B_471)))
      | ~ v1_funct_1(k7_tmap_1(A_470,B_471))
      | ~ l1_pre_topc(k6_tmap_1(A_470,B_471))
      | ~ v2_pre_topc(k6_tmap_1(A_470,B_471))
      | v2_struct_0(k6_tmap_1(A_470,B_471))
      | ~ m1_subset_1(B_471,k1_zfmisc_1(u1_struct_0(A_470)))
      | ~ l1_pre_topc(A_470)
      | ~ v2_pre_topc(A_470)
      | v2_struct_0(A_470) ) ),
    inference(resolution,[status(thm)],[c_48,c_1241])).

tff(c_64,plain,(
    ~ r1_tmap_1('#skF_7',k6_tmap_1('#skF_5','#skF_6'),k2_tmap_1('#skF_5',k6_tmap_1('#skF_5','#skF_6'),k7_tmap_1('#skF_5','#skF_6'),'#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_2956,plain,
    ( ~ r1_tmap_1('#skF_5',k6_tmap_1('#skF_5','#skF_6'),k7_tmap_1('#skF_5','#skF_6'),'#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_pre_topc('#skF_7','#skF_5')
    | v2_struct_0('#skF_7')
    | ~ v1_funct_2(k7_tmap_1('#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0(k6_tmap_1('#skF_5','#skF_6')))
    | ~ v1_funct_1(k7_tmap_1('#skF_5','#skF_6'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_5','#skF_6'))
    | ~ v2_pre_topc(k6_tmap_1('#skF_5','#skF_6'))
    | v2_struct_0(k6_tmap_1('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_2953,c_64])).

tff(c_2959,plain,
    ( ~ r1_tmap_1('#skF_5',k6_tmap_1('#skF_5','#skF_6'),k7_tmap_1('#skF_5','#skF_6'),'#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_7')
    | ~ v1_funct_2(k7_tmap_1('#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0(k6_tmap_1('#skF_5','#skF_6')))
    | v2_struct_0(k6_tmap_1('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_319,c_404,c_703,c_70,c_66,c_2956])).

tff(c_2960,plain,
    ( ~ r1_tmap_1('#skF_5',k6_tmap_1('#skF_5','#skF_6'),k7_tmap_1('#skF_5','#skF_6'),'#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ v1_funct_2(k7_tmap_1('#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0(k6_tmap_1('#skF_5','#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_528,c_72,c_2959])).

tff(c_3048,plain,(
    ~ v1_funct_2(k7_tmap_1('#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0(k6_tmap_1('#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_2960])).

tff(c_3051,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_3048])).

tff(c_3054,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_3051])).

tff(c_3056,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_3054])).

tff(c_3057,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ r1_tmap_1('#skF_5',k6_tmap_1('#skF_5','#skF_6'),k7_tmap_1('#skF_5','#skF_6'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_2960])).

tff(c_3059,plain,(
    ~ r1_tmap_1('#skF_5',k6_tmap_1('#skF_5','#skF_6'),k7_tmap_1('#skF_5','#skF_6'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_3057])).

tff(c_3062,plain,
    ( r2_hidden('#skF_8','#skF_6')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_3059])).

tff(c_3065,plain,
    ( r2_hidden('#skF_8','#skF_6')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_3062])).

tff(c_3066,plain,(
    ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_297,c_3065])).

tff(c_3069,plain,
    ( ~ m1_pre_topc('#skF_7','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_777,c_3066])).

tff(c_3072,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_70,c_3069])).

tff(c_3074,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_3072])).

tff(c_3075,plain,(
    ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_3057])).

tff(c_3079,plain,
    ( ~ m1_pre_topc('#skF_7','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_777,c_3075])).

tff(c_3082,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_70,c_3079])).

tff(c_3084,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_3082])).

tff(c_3085,plain,(
    v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_241])).

tff(c_245,plain,
    ( ~ r2_hidden('#skF_1'(u1_struct_0('#skF_7')),'#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_4,c_220])).

tff(c_246,plain,(
    ~ r2_hidden('#skF_1'(u1_struct_0('#skF_7')),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_245])).

tff(c_265,plain,
    ( ~ r1_tarski(u1_struct_0('#skF_7'),'#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_252,c_246])).

tff(c_287,plain,(
    ~ r1_tarski(u1_struct_0('#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_265])).

tff(c_291,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_120,c_287])).

tff(c_3090,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3085,c_291])).

tff(c_3091,plain,(
    v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_265])).

tff(c_3138,plain,(
    ! [A_482] :
      ( r1_tarski('#skF_4'(A_482),u1_struct_0(A_482))
      | ~ l1_struct_0(A_482)
      | v2_struct_0(A_482) ) ),
    inference(resolution,[status(thm)],[c_269,c_28])).

tff(c_268,plain,(
    ! [B_167,A_166] :
      ( ~ v1_xboole_0(B_167)
      | ~ r1_tarski(A_166,B_167)
      | v1_xboole_0(A_166) ) ),
    inference(resolution,[status(thm)],[c_252,c_2])).

tff(c_3259,plain,(
    ! [A_492] :
      ( ~ v1_xboole_0(u1_struct_0(A_492))
      | v1_xboole_0('#skF_4'(A_492))
      | ~ l1_struct_0(A_492)
      | v2_struct_0(A_492) ) ),
    inference(resolution,[status(thm)],[c_3138,c_268])).

tff(c_3262,plain,
    ( v1_xboole_0('#skF_4'('#skF_7'))
    | ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_3091,c_3259])).

tff(c_3265,plain,
    ( v1_xboole_0('#skF_4'('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3246,c_3262])).

tff(c_3267,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3258,c_3265])).

tff(c_3268,plain,(
    v1_xboole_0('#skF_4'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_3245])).

tff(c_36,plain,(
    ! [A_27] :
      ( ~ v1_xboole_0('#skF_4'(A_27))
      | ~ l1_struct_0(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3277,plain,
    ( ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_3268,c_36])).

tff(c_3282,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3246,c_3277])).

tff(c_3284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3282])).

tff(c_3285,plain,(
    v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_245])).

tff(c_3381,plain,(
    ! [B_502,A_503] :
      ( ~ v1_xboole_0(B_502)
      | ~ r1_tarski(A_503,B_502)
      | v1_xboole_0(A_503) ) ),
    inference(resolution,[status(thm)],[c_3351,c_2])).

tff(c_3559,plain,(
    ! [A_518] :
      ( ~ v1_xboole_0(u1_struct_0(A_518))
      | v1_xboole_0('#skF_4'(A_518))
      | ~ l1_struct_0(A_518)
      | v2_struct_0(A_518) ) ),
    inference(resolution,[status(thm)],[c_3294,c_3381])).

tff(c_3562,plain,
    ( v1_xboole_0('#skF_4'('#skF_7'))
    | ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_3285,c_3559])).

tff(c_3565,plain,
    ( v1_xboole_0('#skF_4'('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3464,c_3562])).

tff(c_3567,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3486,c_3565])).

tff(c_3568,plain,(
    v1_xboole_0('#skF_4'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_3463])).

tff(c_3590,plain,
    ( ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_3568,c_36])).

tff(c_3595,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3464,c_3590])).

tff(c_3597,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3595])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:12:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.98/2.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.98/2.14  
% 5.98/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.98/2.14  %$ r1_tmap_1 > v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k7_tmap_1 > k6_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_4 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2
% 5.98/2.14  
% 5.98/2.14  %Foreground sorts:
% 5.98/2.14  
% 5.98/2.14  
% 5.98/2.14  %Background operators:
% 5.98/2.14  
% 5.98/2.14  
% 5.98/2.14  %Foreground operators:
% 5.98/2.14  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.98/2.14  tff(k7_tmap_1, type, k7_tmap_1: ($i * $i) > $i).
% 5.98/2.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.98/2.14  tff('#skF_4', type, '#skF_4': $i > $i).
% 5.98/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.98/2.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.98/2.14  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.98/2.14  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 5.98/2.14  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.98/2.14  tff('#skF_7', type, '#skF_7': $i).
% 5.98/2.14  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.98/2.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.98/2.14  tff('#skF_5', type, '#skF_5': $i).
% 5.98/2.14  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.98/2.14  tff('#skF_6', type, '#skF_6': $i).
% 5.98/2.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.98/2.14  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 5.98/2.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.98/2.14  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.98/2.14  tff('#skF_8', type, '#skF_8': $i).
% 5.98/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.98/2.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.98/2.14  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 5.98/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.98/2.14  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.98/2.14  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.98/2.14  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.98/2.14  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 5.98/2.14  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.98/2.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.98/2.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.98/2.14  
% 5.98/2.17  tff(f_242, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r1_xboole_0(u1_struct_0(C), B) => (![D]: (m1_subset_1(D, u1_struct_0(C)) => r1_tmap_1(C, k6_tmap_1(A, B), k2_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C), D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_tmap_1)).
% 5.98/2.17  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.98/2.17  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.98/2.17  tff(f_98, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc4_struct_0)).
% 5.98/2.17  tff(f_76, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.98/2.17  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.98/2.17  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.98/2.17  tff(f_60, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.98/2.17  tff(f_114, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 5.98/2.17  tff(f_72, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 5.98/2.17  tff(f_178, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (~r2_hidden(C, B) => r1_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_tmap_1)).
% 5.98/2.17  tff(f_144, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_funct_1(k7_tmap_1(A, B)) & v1_funct_2(k7_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))) & m1_subset_1(k7_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 5.98/2.17  tff(f_160, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((~v2_struct_0(k6_tmap_1(A, B)) & v1_pre_topc(k6_tmap_1(A, B))) & v2_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_tmap_1)).
% 5.98/2.17  tff(f_129, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 5.98/2.17  tff(f_218, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 5.98/2.17  tff(c_72, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.98/2.17  tff(c_76, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.98/2.17  tff(c_70, plain, (m1_pre_topc('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.98/2.17  tff(c_98, plain, (![B_130, A_131]: (l1_pre_topc(B_130) | ~m1_pre_topc(B_130, A_131) | ~l1_pre_topc(A_131))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.98/2.17  tff(c_101, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_70, c_98])).
% 5.98/2.17  tff(c_104, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_101])).
% 5.98/2.17  tff(c_32, plain, (![A_23]: (l1_struct_0(A_23) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.98/2.17  tff(c_3290, plain, (![A_493]: (m1_subset_1('#skF_4'(A_493), k1_zfmisc_1(u1_struct_0(A_493))) | ~l1_struct_0(A_493) | v2_struct_0(A_493))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.98/2.17  tff(c_28, plain, (![A_21, B_22]: (r1_tarski(A_21, B_22) | ~m1_subset_1(A_21, k1_zfmisc_1(B_22)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.98/2.17  tff(c_3294, plain, (![A_493]: (r1_tarski('#skF_4'(A_493), u1_struct_0(A_493)) | ~l1_struct_0(A_493) | v2_struct_0(A_493))), inference(resolution, [status(thm)], [c_3290, c_28])).
% 5.98/2.17  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.98/2.17  tff(c_187, plain, (![C_159, B_160, A_161]: (r2_hidden(C_159, B_160) | ~r2_hidden(C_159, A_161) | ~r1_tarski(A_161, B_160))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.98/2.17  tff(c_202, plain, (![A_1, B_160]: (r2_hidden('#skF_1'(A_1), B_160) | ~r1_tarski(A_1, B_160) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_187])).
% 5.98/2.17  tff(c_3351, plain, (![A_498, B_499]: (r2_hidden('#skF_1'(A_498), B_499) | ~r1_tarski(A_498, B_499) | v1_xboole_0(A_498))), inference(resolution, [status(thm)], [c_4, c_187])).
% 5.98/2.17  tff(c_68, plain, (r1_xboole_0(u1_struct_0('#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.98/2.17  tff(c_207, plain, (![A_162, B_163, C_164]: (~r1_xboole_0(A_162, B_163) | ~r2_hidden(C_164, B_163) | ~r2_hidden(C_164, A_162))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.98/2.17  tff(c_219, plain, (![C_164]: (~r2_hidden(C_164, '#skF_6') | ~r2_hidden(C_164, u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_68, c_207])).
% 5.98/2.17  tff(c_3405, plain, (![A_506]: (~r2_hidden('#skF_1'(A_506), '#skF_6') | ~r1_tarski(A_506, u1_struct_0('#skF_7')) | v1_xboole_0(A_506))), inference(resolution, [status(thm)], [c_3351, c_219])).
% 5.98/2.17  tff(c_3436, plain, (![A_507]: (~r1_tarski(A_507, u1_struct_0('#skF_7')) | ~r1_tarski(A_507, '#skF_6') | v1_xboole_0(A_507))), inference(resolution, [status(thm)], [c_202, c_3405])).
% 5.98/2.17  tff(c_3440, plain, (~r1_tarski('#skF_4'('#skF_7'), '#skF_6') | v1_xboole_0('#skF_4'('#skF_7')) | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_3294, c_3436])).
% 5.98/2.17  tff(c_3451, plain, (~r1_tarski('#skF_4'('#skF_7'), '#skF_6') | v1_xboole_0('#skF_4'('#skF_7')) | ~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_72, c_3440])).
% 5.98/2.17  tff(c_3455, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_3451])).
% 5.98/2.17  tff(c_3458, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_32, c_3455])).
% 5.98/2.17  tff(c_3462, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_3458])).
% 5.98/2.17  tff(c_3464, plain, (l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_3451])).
% 5.98/2.17  tff(c_116, plain, (![A_137, B_138]: (r2_hidden('#skF_2'(A_137, B_138), A_137) | r1_tarski(A_137, B_138))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.98/2.17  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.98/2.17  tff(c_120, plain, (![A_137, B_138]: (~v1_xboole_0(A_137) | r1_tarski(A_137, B_138))), inference(resolution, [status(thm)], [c_116, c_2])).
% 5.98/2.17  tff(c_3463, plain, (~r1_tarski('#skF_4'('#skF_7'), '#skF_6') | v1_xboole_0('#skF_4'('#skF_7'))), inference(splitRight, [status(thm)], [c_3451])).
% 5.98/2.17  tff(c_3465, plain, (~r1_tarski('#skF_4'('#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_3463])).
% 5.98/2.17  tff(c_3486, plain, (~v1_xboole_0('#skF_4'('#skF_7'))), inference(resolution, [status(thm)], [c_120, c_3465])).
% 5.98/2.17  tff(c_269, plain, (![A_168]: (m1_subset_1('#skF_4'(A_168), k1_zfmisc_1(u1_struct_0(A_168))) | ~l1_struct_0(A_168) | v2_struct_0(A_168))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.98/2.17  tff(c_273, plain, (![A_168]: (r1_tarski('#skF_4'(A_168), u1_struct_0(A_168)) | ~l1_struct_0(A_168) | v2_struct_0(A_168))), inference(resolution, [status(thm)], [c_269, c_28])).
% 5.98/2.17  tff(c_252, plain, (![A_166, B_167]: (r2_hidden('#skF_1'(A_166), B_167) | ~r1_tarski(A_166, B_167) | v1_xboole_0(A_166))), inference(resolution, [status(thm)], [c_4, c_187])).
% 5.98/2.17  tff(c_3182, plain, (![A_487]: (~r2_hidden('#skF_1'(A_487), '#skF_6') | ~r1_tarski(A_487, u1_struct_0('#skF_7')) | v1_xboole_0(A_487))), inference(resolution, [status(thm)], [c_252, c_219])).
% 5.98/2.17  tff(c_3200, plain, (![A_488]: (~r1_tarski(A_488, u1_struct_0('#skF_7')) | ~r1_tarski(A_488, '#skF_6') | v1_xboole_0(A_488))), inference(resolution, [status(thm)], [c_202, c_3182])).
% 5.98/2.17  tff(c_3204, plain, (~r1_tarski('#skF_4'('#skF_7'), '#skF_6') | v1_xboole_0('#skF_4'('#skF_7')) | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_273, c_3200])).
% 5.98/2.17  tff(c_3215, plain, (~r1_tarski('#skF_4'('#skF_7'), '#skF_6') | v1_xboole_0('#skF_4'('#skF_7')) | ~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_72, c_3204])).
% 5.98/2.17  tff(c_3220, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_3215])).
% 5.98/2.17  tff(c_3240, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_32, c_3220])).
% 5.98/2.17  tff(c_3244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_3240])).
% 5.98/2.17  tff(c_3246, plain, (l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_3215])).
% 5.98/2.17  tff(c_3245, plain, (~r1_tarski('#skF_4'('#skF_7'), '#skF_6') | v1_xboole_0('#skF_4'('#skF_7'))), inference(splitRight, [status(thm)], [c_3215])).
% 5.98/2.17  tff(c_3247, plain, (~r1_tarski('#skF_4'('#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_3245])).
% 5.98/2.17  tff(c_3258, plain, (~v1_xboole_0('#skF_4'('#skF_7'))), inference(resolution, [status(thm)], [c_120, c_3247])).
% 5.98/2.17  tff(c_80, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.98/2.17  tff(c_66, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.98/2.17  tff(c_772, plain, (![C_216, A_217, B_218]: (m1_subset_1(C_216, u1_struct_0(A_217)) | ~m1_subset_1(C_216, u1_struct_0(B_218)) | ~m1_pre_topc(B_218, A_217) | v2_struct_0(B_218) | ~l1_pre_topc(A_217) | v2_struct_0(A_217))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.98/2.17  tff(c_774, plain, (![A_217]: (m1_subset_1('#skF_8', u1_struct_0(A_217)) | ~m1_pre_topc('#skF_7', A_217) | v2_struct_0('#skF_7') | ~l1_pre_topc(A_217) | v2_struct_0(A_217))), inference(resolution, [status(thm)], [c_66, c_772])).
% 5.98/2.17  tff(c_777, plain, (![A_217]: (m1_subset_1('#skF_8', u1_struct_0(A_217)) | ~m1_pre_topc('#skF_7', A_217) | ~l1_pre_topc(A_217) | v2_struct_0(A_217))), inference(negUnitSimplification, [status(thm)], [c_72, c_774])).
% 5.98/2.17  tff(c_26, plain, (![A_19, B_20]: (r2_hidden(A_19, B_20) | v1_xboole_0(B_20) | ~m1_subset_1(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.98/2.17  tff(c_220, plain, (![C_165]: (~r2_hidden(C_165, '#skF_6') | ~r2_hidden(C_165, u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_68, c_207])).
% 5.98/2.17  tff(c_241, plain, (![A_19]: (~r2_hidden(A_19, '#skF_6') | v1_xboole_0(u1_struct_0('#skF_7')) | ~m1_subset_1(A_19, u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_26, c_220])).
% 5.98/2.17  tff(c_293, plain, (![A_171]: (~r2_hidden(A_171, '#skF_6') | ~m1_subset_1(A_171, u1_struct_0('#skF_7')))), inference(splitLeft, [status(thm)], [c_241])).
% 5.98/2.17  tff(c_297, plain, (~r2_hidden('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_66, c_293])).
% 5.98/2.17  tff(c_78, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.98/2.17  tff(c_74, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.98/2.17  tff(c_60, plain, (![A_42, B_46, C_48]: (r1_tmap_1(A_42, k6_tmap_1(A_42, B_46), k7_tmap_1(A_42, B_46), C_48) | r2_hidden(C_48, B_46) | ~m1_subset_1(C_48, u1_struct_0(A_42)) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42) | ~v2_pre_topc(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_178])).
% 5.98/2.17  tff(c_50, plain, (![A_38, B_39]: (v1_funct_2(k7_tmap_1(A_38, B_39), u1_struct_0(A_38), u1_struct_0(k6_tmap_1(A_38, B_39))) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.98/2.17  tff(c_512, plain, (![A_198, B_199]: (~v2_struct_0(k6_tmap_1(A_198, B_199)) | ~m1_subset_1(B_199, k1_zfmisc_1(u1_struct_0(A_198))) | ~l1_pre_topc(A_198) | ~v2_pre_topc(A_198) | v2_struct_0(A_198))), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.98/2.17  tff(c_522, plain, (~v2_struct_0(k6_tmap_1('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_74, c_512])).
% 5.98/2.17  tff(c_527, plain, (~v2_struct_0(k6_tmap_1('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_522])).
% 5.98/2.17  tff(c_528, plain, (~v2_struct_0(k6_tmap_1('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_80, c_527])).
% 5.98/2.17  tff(c_303, plain, (![A_172, B_173]: (v2_pre_topc(k6_tmap_1(A_172, B_173)) | ~m1_subset_1(B_173, k1_zfmisc_1(u1_struct_0(A_172))) | ~l1_pre_topc(A_172) | ~v2_pre_topc(A_172) | v2_struct_0(A_172))), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.98/2.17  tff(c_313, plain, (v2_pre_topc(k6_tmap_1('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_74, c_303])).
% 5.98/2.17  tff(c_318, plain, (v2_pre_topc(k6_tmap_1('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_313])).
% 5.98/2.17  tff(c_319, plain, (v2_pre_topc(k6_tmap_1('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_80, c_318])).
% 5.98/2.17  tff(c_388, plain, (![A_180, B_181]: (l1_pre_topc(k6_tmap_1(A_180, B_181)) | ~m1_subset_1(B_181, k1_zfmisc_1(u1_struct_0(A_180))) | ~l1_pre_topc(A_180) | ~v2_pre_topc(A_180) | v2_struct_0(A_180))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.98/2.17  tff(c_398, plain, (l1_pre_topc(k6_tmap_1('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_74, c_388])).
% 5.98/2.17  tff(c_403, plain, (l1_pre_topc(k6_tmap_1('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_398])).
% 5.98/2.17  tff(c_404, plain, (l1_pre_topc(k6_tmap_1('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_80, c_403])).
% 5.98/2.17  tff(c_687, plain, (![A_207, B_208]: (v1_funct_1(k7_tmap_1(A_207, B_208)) | ~m1_subset_1(B_208, k1_zfmisc_1(u1_struct_0(A_207))) | ~l1_pre_topc(A_207) | ~v2_pre_topc(A_207) | v2_struct_0(A_207))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.98/2.17  tff(c_697, plain, (v1_funct_1(k7_tmap_1('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_74, c_687])).
% 5.98/2.17  tff(c_702, plain, (v1_funct_1(k7_tmap_1('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_697])).
% 5.98/2.17  tff(c_703, plain, (v1_funct_1(k7_tmap_1('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_80, c_702])).
% 5.98/2.17  tff(c_48, plain, (![A_38, B_39]: (m1_subset_1(k7_tmap_1(A_38, B_39), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_38), u1_struct_0(k6_tmap_1(A_38, B_39))))) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.98/2.17  tff(c_1241, plain, (![C_274, F_273, A_276, D_275, B_272]: (r1_tmap_1(D_275, A_276, k2_tmap_1(B_272, A_276, C_274, D_275), F_273) | ~r1_tmap_1(B_272, A_276, C_274, F_273) | ~m1_subset_1(F_273, u1_struct_0(D_275)) | ~m1_subset_1(F_273, u1_struct_0(B_272)) | ~m1_pre_topc(D_275, B_272) | v2_struct_0(D_275) | ~m1_subset_1(C_274, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_272), u1_struct_0(A_276)))) | ~v1_funct_2(C_274, u1_struct_0(B_272), u1_struct_0(A_276)) | ~v1_funct_1(C_274) | ~l1_pre_topc(B_272) | ~v2_pre_topc(B_272) | v2_struct_0(B_272) | ~l1_pre_topc(A_276) | ~v2_pre_topc(A_276) | v2_struct_0(A_276))), inference(cnfTransformation, [status(thm)], [f_218])).
% 5.98/2.17  tff(c_2953, plain, (![D_469, A_470, B_471, F_472]: (r1_tmap_1(D_469, k6_tmap_1(A_470, B_471), k2_tmap_1(A_470, k6_tmap_1(A_470, B_471), k7_tmap_1(A_470, B_471), D_469), F_472) | ~r1_tmap_1(A_470, k6_tmap_1(A_470, B_471), k7_tmap_1(A_470, B_471), F_472) | ~m1_subset_1(F_472, u1_struct_0(D_469)) | ~m1_subset_1(F_472, u1_struct_0(A_470)) | ~m1_pre_topc(D_469, A_470) | v2_struct_0(D_469) | ~v1_funct_2(k7_tmap_1(A_470, B_471), u1_struct_0(A_470), u1_struct_0(k6_tmap_1(A_470, B_471))) | ~v1_funct_1(k7_tmap_1(A_470, B_471)) | ~l1_pre_topc(k6_tmap_1(A_470, B_471)) | ~v2_pre_topc(k6_tmap_1(A_470, B_471)) | v2_struct_0(k6_tmap_1(A_470, B_471)) | ~m1_subset_1(B_471, k1_zfmisc_1(u1_struct_0(A_470))) | ~l1_pre_topc(A_470) | ~v2_pre_topc(A_470) | v2_struct_0(A_470))), inference(resolution, [status(thm)], [c_48, c_1241])).
% 5.98/2.17  tff(c_64, plain, (~r1_tmap_1('#skF_7', k6_tmap_1('#skF_5', '#skF_6'), k2_tmap_1('#skF_5', k6_tmap_1('#skF_5', '#skF_6'), k7_tmap_1('#skF_5', '#skF_6'), '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.98/2.17  tff(c_2956, plain, (~r1_tmap_1('#skF_5', k6_tmap_1('#skF_5', '#skF_6'), k7_tmap_1('#skF_5', '#skF_6'), '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_7', '#skF_5') | v2_struct_0('#skF_7') | ~v1_funct_2(k7_tmap_1('#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0(k6_tmap_1('#skF_5', '#skF_6'))) | ~v1_funct_1(k7_tmap_1('#skF_5', '#skF_6')) | ~l1_pre_topc(k6_tmap_1('#skF_5', '#skF_6')) | ~v2_pre_topc(k6_tmap_1('#skF_5', '#skF_6')) | v2_struct_0(k6_tmap_1('#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_2953, c_64])).
% 5.98/2.17  tff(c_2959, plain, (~r1_tmap_1('#skF_5', k6_tmap_1('#skF_5', '#skF_6'), k7_tmap_1('#skF_5', '#skF_6'), '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | v2_struct_0('#skF_7') | ~v1_funct_2(k7_tmap_1('#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0(k6_tmap_1('#skF_5', '#skF_6'))) | v2_struct_0(k6_tmap_1('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_319, c_404, c_703, c_70, c_66, c_2956])).
% 5.98/2.17  tff(c_2960, plain, (~r1_tmap_1('#skF_5', k6_tmap_1('#skF_5', '#skF_6'), k7_tmap_1('#skF_5', '#skF_6'), '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~v1_funct_2(k7_tmap_1('#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0(k6_tmap_1('#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_80, c_528, c_72, c_2959])).
% 5.98/2.17  tff(c_3048, plain, (~v1_funct_2(k7_tmap_1('#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0(k6_tmap_1('#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_2960])).
% 5.98/2.17  tff(c_3051, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_50, c_3048])).
% 5.98/2.17  tff(c_3054, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_3051])).
% 5.98/2.17  tff(c_3056, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_3054])).
% 5.98/2.17  tff(c_3057, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~r1_tmap_1('#skF_5', k6_tmap_1('#skF_5', '#skF_6'), k7_tmap_1('#skF_5', '#skF_6'), '#skF_8')), inference(splitRight, [status(thm)], [c_2960])).
% 5.98/2.17  tff(c_3059, plain, (~r1_tmap_1('#skF_5', k6_tmap_1('#skF_5', '#skF_6'), k7_tmap_1('#skF_5', '#skF_6'), '#skF_8')), inference(splitLeft, [status(thm)], [c_3057])).
% 5.98/2.17  tff(c_3062, plain, (r2_hidden('#skF_8', '#skF_6') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_60, c_3059])).
% 5.98/2.17  tff(c_3065, plain, (r2_hidden('#skF_8', '#skF_6') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_3062])).
% 5.98/2.17  tff(c_3066, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80, c_297, c_3065])).
% 5.98/2.17  tff(c_3069, plain, (~m1_pre_topc('#skF_7', '#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_777, c_3066])).
% 5.98/2.17  tff(c_3072, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_70, c_3069])).
% 5.98/2.17  tff(c_3074, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_3072])).
% 5.98/2.17  tff(c_3075, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_3057])).
% 5.98/2.17  tff(c_3079, plain, (~m1_pre_topc('#skF_7', '#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_777, c_3075])).
% 5.98/2.17  tff(c_3082, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_70, c_3079])).
% 5.98/2.17  tff(c_3084, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_3082])).
% 5.98/2.17  tff(c_3085, plain, (v1_xboole_0(u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_241])).
% 5.98/2.17  tff(c_245, plain, (~r2_hidden('#skF_1'(u1_struct_0('#skF_7')), '#skF_6') | v1_xboole_0(u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_4, c_220])).
% 5.98/2.17  tff(c_246, plain, (~r2_hidden('#skF_1'(u1_struct_0('#skF_7')), '#skF_6')), inference(splitLeft, [status(thm)], [c_245])).
% 5.98/2.17  tff(c_265, plain, (~r1_tarski(u1_struct_0('#skF_7'), '#skF_6') | v1_xboole_0(u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_252, c_246])).
% 5.98/2.17  tff(c_287, plain, (~r1_tarski(u1_struct_0('#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_265])).
% 5.98/2.17  tff(c_291, plain, (~v1_xboole_0(u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_120, c_287])).
% 5.98/2.17  tff(c_3090, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3085, c_291])).
% 5.98/2.17  tff(c_3091, plain, (v1_xboole_0(u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_265])).
% 5.98/2.17  tff(c_3138, plain, (![A_482]: (r1_tarski('#skF_4'(A_482), u1_struct_0(A_482)) | ~l1_struct_0(A_482) | v2_struct_0(A_482))), inference(resolution, [status(thm)], [c_269, c_28])).
% 5.98/2.17  tff(c_268, plain, (![B_167, A_166]: (~v1_xboole_0(B_167) | ~r1_tarski(A_166, B_167) | v1_xboole_0(A_166))), inference(resolution, [status(thm)], [c_252, c_2])).
% 5.98/2.17  tff(c_3259, plain, (![A_492]: (~v1_xboole_0(u1_struct_0(A_492)) | v1_xboole_0('#skF_4'(A_492)) | ~l1_struct_0(A_492) | v2_struct_0(A_492))), inference(resolution, [status(thm)], [c_3138, c_268])).
% 5.98/2.17  tff(c_3262, plain, (v1_xboole_0('#skF_4'('#skF_7')) | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_3091, c_3259])).
% 5.98/2.17  tff(c_3265, plain, (v1_xboole_0('#skF_4'('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3246, c_3262])).
% 5.98/2.17  tff(c_3267, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_3258, c_3265])).
% 5.98/2.17  tff(c_3268, plain, (v1_xboole_0('#skF_4'('#skF_7'))), inference(splitRight, [status(thm)], [c_3245])).
% 5.98/2.17  tff(c_36, plain, (![A_27]: (~v1_xboole_0('#skF_4'(A_27)) | ~l1_struct_0(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.98/2.17  tff(c_3277, plain, (~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_3268, c_36])).
% 5.98/2.17  tff(c_3282, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3246, c_3277])).
% 5.98/2.17  tff(c_3284, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_3282])).
% 5.98/2.17  tff(c_3285, plain, (v1_xboole_0(u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_245])).
% 5.98/2.17  tff(c_3381, plain, (![B_502, A_503]: (~v1_xboole_0(B_502) | ~r1_tarski(A_503, B_502) | v1_xboole_0(A_503))), inference(resolution, [status(thm)], [c_3351, c_2])).
% 5.98/2.17  tff(c_3559, plain, (![A_518]: (~v1_xboole_0(u1_struct_0(A_518)) | v1_xboole_0('#skF_4'(A_518)) | ~l1_struct_0(A_518) | v2_struct_0(A_518))), inference(resolution, [status(thm)], [c_3294, c_3381])).
% 5.98/2.17  tff(c_3562, plain, (v1_xboole_0('#skF_4'('#skF_7')) | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_3285, c_3559])).
% 5.98/2.17  tff(c_3565, plain, (v1_xboole_0('#skF_4'('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3464, c_3562])).
% 5.98/2.17  tff(c_3567, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_3486, c_3565])).
% 5.98/2.17  tff(c_3568, plain, (v1_xboole_0('#skF_4'('#skF_7'))), inference(splitRight, [status(thm)], [c_3463])).
% 5.98/2.17  tff(c_3590, plain, (~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_3568, c_36])).
% 5.98/2.17  tff(c_3595, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3464, c_3590])).
% 5.98/2.17  tff(c_3597, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_3595])).
% 5.98/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.98/2.17  
% 5.98/2.17  Inference rules
% 5.98/2.17  ----------------------
% 5.98/2.17  #Ref     : 0
% 5.98/2.17  #Sup     : 719
% 5.98/2.17  #Fact    : 0
% 5.98/2.17  #Define  : 0
% 5.98/2.17  #Split   : 28
% 5.98/2.17  #Chain   : 0
% 5.98/2.17  #Close   : 0
% 5.98/2.17  
% 5.98/2.17  Ordering : KBO
% 5.98/2.17  
% 5.98/2.17  Simplification rules
% 5.98/2.17  ----------------------
% 5.98/2.17  #Subsume      : 291
% 5.98/2.17  #Demod        : 125
% 5.98/2.17  #Tautology    : 56
% 5.98/2.17  #SimpNegUnit  : 105
% 5.98/2.17  #BackRed      : 0
% 5.98/2.17  
% 5.98/2.17  #Partial instantiations: 0
% 5.98/2.17  #Strategies tried      : 1
% 5.98/2.17  
% 5.98/2.17  Timing (in seconds)
% 5.98/2.17  ----------------------
% 5.98/2.17  Preprocessing        : 0.35
% 5.98/2.17  Parsing              : 0.19
% 5.98/2.17  CNF conversion       : 0.03
% 5.98/2.17  Main loop            : 1.03
% 5.98/2.17  Inferencing          : 0.35
% 5.98/2.17  Reduction            : 0.28
% 5.98/2.17  Demodulation         : 0.16
% 5.98/2.17  BG Simplification    : 0.03
% 5.98/2.18  Subsumption          : 0.29
% 5.98/2.18  Abstraction          : 0.03
% 5.98/2.18  MUC search           : 0.00
% 5.98/2.18  Cooper               : 0.00
% 5.98/2.18  Total                : 1.43
% 5.98/2.18  Index Insertion      : 0.00
% 5.98/2.18  Index Deletion       : 0.00
% 5.98/2.18  Index Matching       : 0.00
% 5.98/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
