%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:53 EST 2020

% Result     : Theorem 4.12s
% Output     : CNFRefutation 4.50s
% Verified   : 
% Statistics : Number of formulae       :  130 (1153 expanded)
%              Number of leaves         :   47 ( 420 expanded)
%              Depth                    :   21
%              Number of atoms          :  313 (4806 expanded)
%              Number of equality atoms :   31 ( 345 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(r1_funct_2,type,(
    r1_funct_2: ( $i * $i * $i * $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_191,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,B) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(B),u1_struct_0(A))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
                   => ( g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                     => r1_funct_2(u1_struct_0(B),u1_struct_0(A),u1_struct_0(C),u1_struct_0(A),D,k2_tmap_1(B,A,D,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_tmap_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_158,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_154,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_120,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(B)
        & ~ v1_xboole_0(D)
        & v1_funct_1(E)
        & v1_funct_2(E,A,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,C,D)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( r1_funct_2(A,B,C,D,E,F)
      <=> E = F ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_147,axiom,(
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
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(c_68,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_26,plain,(
    ! [A_19] :
      ( l1_struct_0(A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_62,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_58,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_78,plain,(
    ! [B_71,A_72] :
      ( l1_pre_topc(B_71)
      | ~ m1_pre_topc(B_71,A_72)
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_84,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_78])).

tff(c_88,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_84])).

tff(c_46,plain,(
    ! [A_54] :
      ( m1_pre_topc(A_54,A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_50,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_377,plain,(
    ! [A_158,B_159] :
      ( m1_pre_topc(A_158,g1_pre_topc(u1_struct_0(B_159),u1_pre_topc(B_159)))
      | ~ m1_pre_topc(A_158,B_159)
      | ~ l1_pre_topc(B_159)
      | ~ l1_pre_topc(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_390,plain,(
    ! [A_158] :
      ( m1_pre_topc(A_158,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_158,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_158) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_377])).

tff(c_405,plain,(
    ! [A_161] :
      ( m1_pre_topc(A_161,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_161,'#skF_2')
      | ~ l1_pre_topc(A_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_390])).

tff(c_32,plain,(
    ! [B_26,A_24] :
      ( m1_pre_topc(B_26,A_24)
      | ~ m1_pre_topc(B_26,g1_pre_topc(u1_struct_0(A_24),u1_pre_topc(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_411,plain,(
    ! [A_161] :
      ( m1_pre_topc(A_161,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc(A_161,'#skF_2')
      | ~ l1_pre_topc(A_161) ) ),
    inference(resolution,[status(thm)],[c_405,c_32])).

tff(c_430,plain,(
    ! [A_166] :
      ( m1_pre_topc(A_166,'#skF_3')
      | ~ m1_pre_topc(A_166,'#skF_2')
      | ~ l1_pre_topc(A_166) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_411])).

tff(c_437,plain,
    ( m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_430])).

tff(c_444,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_437])).

tff(c_267,plain,(
    ! [B_120,A_121] :
      ( m1_subset_1(u1_struct_0(B_120),k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ m1_pre_topc(B_120,A_121)
      | ~ l1_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_271,plain,(
    ! [B_120,A_121] :
      ( r1_tarski(u1_struct_0(B_120),u1_struct_0(A_121))
      | ~ m1_pre_topc(B_120,A_121)
      | ~ l1_pre_topc(A_121) ) ),
    inference(resolution,[status(thm)],[c_267,c_8])).

tff(c_272,plain,(
    ! [B_122,A_123] :
      ( r1_tarski(u1_struct_0(B_122),u1_struct_0(A_123))
      | ~ m1_pre_topc(B_122,A_123)
      | ~ l1_pre_topc(A_123) ) ),
    inference(resolution,[status(thm)],[c_267,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_469,plain,(
    ! [B_168,A_169] :
      ( u1_struct_0(B_168) = u1_struct_0(A_169)
      | ~ r1_tarski(u1_struct_0(A_169),u1_struct_0(B_168))
      | ~ m1_pre_topc(B_168,A_169)
      | ~ l1_pre_topc(A_169) ) ),
    inference(resolution,[status(thm)],[c_272,c_2])).

tff(c_480,plain,(
    ! [B_170,A_171] :
      ( u1_struct_0(B_170) = u1_struct_0(A_171)
      | ~ m1_pre_topc(A_171,B_170)
      | ~ l1_pre_topc(B_170)
      | ~ m1_pre_topc(B_170,A_171)
      | ~ l1_pre_topc(A_171) ) ),
    inference(resolution,[status(thm)],[c_271,c_469])).

tff(c_484,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_444,c_480])).

tff(c_501,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_88,c_484])).

tff(c_54,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_520,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_54])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_519,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_52])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_571,plain,(
    ! [F_174,D_176,A_175,C_172,B_173] :
      ( r1_funct_2(A_175,B_173,C_172,D_176,F_174,F_174)
      | ~ m1_subset_1(F_174,k1_zfmisc_1(k2_zfmisc_1(C_172,D_176)))
      | ~ v1_funct_2(F_174,C_172,D_176)
      | ~ m1_subset_1(F_174,k1_zfmisc_1(k2_zfmisc_1(A_175,B_173)))
      | ~ v1_funct_2(F_174,A_175,B_173)
      | ~ v1_funct_1(F_174)
      | v1_xboole_0(D_176)
      | v1_xboole_0(B_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1072,plain,(
    ! [A_228,C_230,B_227,D_229,A_226] :
      ( r1_funct_2(A_226,B_227,C_230,D_229,A_228,A_228)
      | ~ v1_funct_2(A_228,C_230,D_229)
      | ~ m1_subset_1(A_228,k1_zfmisc_1(k2_zfmisc_1(A_226,B_227)))
      | ~ v1_funct_2(A_228,A_226,B_227)
      | ~ v1_funct_1(A_228)
      | v1_xboole_0(D_229)
      | v1_xboole_0(B_227)
      | ~ r1_tarski(A_228,k2_zfmisc_1(C_230,D_229)) ) ),
    inference(resolution,[status(thm)],[c_10,c_571])).

tff(c_1074,plain,(
    ! [C_230,D_229] :
      ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),C_230,D_229,'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',C_230,D_229)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(D_229)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(C_230,D_229)) ) ),
    inference(resolution,[status(thm)],[c_519,c_1072])).

tff(c_1080,plain,(
    ! [C_230,D_229] :
      ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),C_230,D_229,'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',C_230,D_229)
      | v1_xboole_0(D_229)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(C_230,D_229)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_520,c_1074])).

tff(c_1266,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1080])).

tff(c_30,plain,(
    ! [A_23] :
      ( ~ v1_xboole_0(u1_struct_0(A_23))
      | ~ l1_struct_0(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1269,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1266,c_30])).

tff(c_1272,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1269])).

tff(c_1275,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_1272])).

tff(c_1279,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1275])).

tff(c_1281,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1080])).

tff(c_38,plain,(
    ! [D_33,A_30,C_32,B_31,F_35] :
      ( r1_funct_2(A_30,B_31,C_32,D_33,F_35,F_35)
      | ~ m1_subset_1(F_35,k1_zfmisc_1(k2_zfmisc_1(C_32,D_33)))
      | ~ v1_funct_2(F_35,C_32,D_33)
      | ~ m1_subset_1(F_35,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ v1_funct_2(F_35,A_30,B_31)
      | ~ v1_funct_1(F_35)
      | v1_xboole_0(D_33)
      | v1_xboole_0(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_611,plain,(
    ! [A_30,B_31] :
      ( r1_funct_2(A_30,B_31,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ v1_funct_2('#skF_4',A_30,B_31)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_31) ) ),
    inference(resolution,[status(thm)],[c_519,c_38])).

tff(c_628,plain,(
    ! [A_30,B_31] :
      ( r1_funct_2(A_30,B_31,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ v1_funct_2('#skF_4',A_30,B_31)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_520,c_611])).

tff(c_1361,plain,(
    ! [A_30,B_31] :
      ( r1_funct_2(A_30,B_31,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ v1_funct_2('#skF_4',A_30,B_31)
      | v1_xboole_0(B_31) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1281,c_628])).

tff(c_70,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_420,plain,(
    ! [A_162,B_163,C_164,D_165] :
      ( k2_partfun1(A_162,B_163,C_164,D_165) = k7_relat_1(C_164,D_165)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163)))
      | ~ v1_funct_1(C_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_422,plain,(
    ! [D_165] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_165) = k7_relat_1('#skF_4',D_165)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_52,c_420])).

tff(c_428,plain,(
    ! [D_165] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_165) = k7_relat_1('#skF_4',D_165) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_422])).

tff(c_512,plain,(
    ! [D_165] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',D_165) = k7_relat_1('#skF_4',D_165) ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_428])).

tff(c_105,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_52,c_8])).

tff(c_518,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_105])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_64,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_699,plain,(
    ! [A_185,B_186,C_187,D_188] :
      ( k2_partfun1(u1_struct_0(A_185),u1_struct_0(B_186),C_187,u1_struct_0(D_188)) = k2_tmap_1(A_185,B_186,C_187,D_188)
      | ~ m1_pre_topc(D_188,A_185)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_185),u1_struct_0(B_186))))
      | ~ v1_funct_2(C_187,u1_struct_0(A_185),u1_struct_0(B_186))
      | ~ v1_funct_1(C_187)
      | ~ l1_pre_topc(B_186)
      | ~ v2_pre_topc(B_186)
      | v2_struct_0(B_186)
      | ~ l1_pre_topc(A_185)
      | ~ v2_pre_topc(A_185)
      | v2_struct_0(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_1201,plain,(
    ! [A_280,B_281,A_282,D_283] :
      ( k2_partfun1(u1_struct_0(A_280),u1_struct_0(B_281),A_282,u1_struct_0(D_283)) = k2_tmap_1(A_280,B_281,A_282,D_283)
      | ~ m1_pre_topc(D_283,A_280)
      | ~ v1_funct_2(A_282,u1_struct_0(A_280),u1_struct_0(B_281))
      | ~ v1_funct_1(A_282)
      | ~ l1_pre_topc(B_281)
      | ~ v2_pre_topc(B_281)
      | v2_struct_0(B_281)
      | ~ l1_pre_topc(A_280)
      | ~ v2_pre_topc(A_280)
      | v2_struct_0(A_280)
      | ~ r1_tarski(A_282,k2_zfmisc_1(u1_struct_0(A_280),u1_struct_0(B_281))) ) ),
    inference(resolution,[status(thm)],[c_10,c_699])).

tff(c_1205,plain,(
    ! [B_281,A_282,D_283] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_281),A_282,u1_struct_0(D_283)) = k2_tmap_1('#skF_2',B_281,A_282,D_283)
      | ~ m1_pre_topc(D_283,'#skF_2')
      | ~ v1_funct_2(A_282,u1_struct_0('#skF_2'),u1_struct_0(B_281))
      | ~ v1_funct_1(A_282)
      | ~ l1_pre_topc(B_281)
      | ~ v2_pre_topc(B_281)
      | v2_struct_0(B_281)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_282,k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_281))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_1201])).

tff(c_1219,plain,(
    ! [B_281,A_282,D_283] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_281),A_282,u1_struct_0(D_283)) = k2_tmap_1('#skF_2',B_281,A_282,D_283)
      | ~ m1_pre_topc(D_283,'#skF_2')
      | ~ v1_funct_2(A_282,u1_struct_0('#skF_3'),u1_struct_0(B_281))
      | ~ v1_funct_1(A_282)
      | ~ l1_pre_topc(B_281)
      | ~ v2_pre_topc(B_281)
      | v2_struct_0(B_281)
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_282,k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_281))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_501,c_501,c_1205])).

tff(c_1469,plain,(
    ! [B_359,A_360,D_361] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_359),A_360,u1_struct_0(D_361)) = k2_tmap_1('#skF_2',B_359,A_360,D_361)
      | ~ m1_pre_topc(D_361,'#skF_2')
      | ~ v1_funct_2(A_360,u1_struct_0('#skF_3'),u1_struct_0(B_359))
      | ~ v1_funct_1(A_360)
      | ~ l1_pre_topc(B_359)
      | ~ v2_pre_topc(B_359)
      | v2_struct_0(B_359)
      | ~ r1_tarski(A_360,k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_359))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1219])).

tff(c_1471,plain,(
    ! [D_361] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_361)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_361)
      | ~ m1_pre_topc(D_361,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_518,c_1469])).

tff(c_1482,plain,(
    ! [D_361] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_361)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_361)
      | ~ m1_pre_topc(D_361,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_56,c_520,c_512,c_1471])).

tff(c_1489,plain,(
    ! [D_362] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_362)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_362)
      | ~ m1_pre_topc(D_362,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1482])).

tff(c_109,plain,(
    ! [C_78,A_79,B_80] :
      ( v1_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_117,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_109])).

tff(c_131,plain,(
    ! [C_86,A_87,B_88] :
      ( v4_relat_1(C_86,A_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_139,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_131])).

tff(c_14,plain,(
    ! [B_6,A_5] :
      ( r1_tarski(k1_relat_1(B_6),A_5)
      | ~ v4_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_209,plain,(
    ! [B_107,A_108] :
      ( k7_relat_1(B_107,A_108) = B_107
      | ~ r1_tarski(k1_relat_1(B_107),A_108)
      | ~ v1_relat_1(B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_228,plain,(
    ! [B_110,A_111] :
      ( k7_relat_1(B_110,A_111) = B_110
      | ~ v4_relat_1(B_110,A_111)
      | ~ v1_relat_1(B_110) ) ),
    inference(resolution,[status(thm)],[c_14,c_209])).

tff(c_237,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_139,c_228])).

tff(c_244,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_237])).

tff(c_514,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_244])).

tff(c_1495,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1489,c_514])).

tff(c_1507,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1495])).

tff(c_48,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_515,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_48])).

tff(c_1513,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1507,c_515])).

tff(c_1525,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1361,c_1513])).

tff(c_1534,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_520,c_519,c_1525])).

tff(c_1536,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1281,c_1534])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:40:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.12/1.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.12/1.76  
% 4.12/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.12/1.77  %$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.12/1.77  
% 4.12/1.77  %Foreground sorts:
% 4.12/1.77  
% 4.12/1.77  
% 4.12/1.77  %Background operators:
% 4.12/1.77  
% 4.12/1.77  
% 4.12/1.77  %Foreground operators:
% 4.12/1.77  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.12/1.77  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.12/1.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.12/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.12/1.77  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.12/1.77  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.12/1.77  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.12/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.12/1.77  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.12/1.77  tff('#skF_2', type, '#skF_2': $i).
% 4.12/1.77  tff('#skF_3', type, '#skF_3': $i).
% 4.12/1.77  tff('#skF_1', type, '#skF_1': $i).
% 4.12/1.77  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.12/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.12/1.77  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.12/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.12/1.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.12/1.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.12/1.77  tff('#skF_4', type, '#skF_4': $i).
% 4.12/1.77  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 4.12/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.12/1.77  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.12/1.77  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 4.12/1.77  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.12/1.77  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.12/1.77  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 4.12/1.77  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.12/1.77  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.12/1.77  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.12/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.12/1.77  
% 4.50/1.79  tff(f_191, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_tmap_1)).
% 4.50/1.79  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.50/1.79  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.50/1.79  tff(f_158, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.50/1.79  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 4.50/1.79  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 4.50/1.79  tff(f_154, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.50/1.79  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.50/1.79  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.50/1.79  tff(f_120, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 4.50/1.79  tff(f_82, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.50/1.79  tff(f_63, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 4.50/1.79  tff(f_147, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 4.50/1.79  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.50/1.79  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.50/1.79  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 4.50/1.79  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 4.50/1.79  tff(c_68, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.50/1.79  tff(c_26, plain, (![A_19]: (l1_struct_0(A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.50/1.79  tff(c_72, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.50/1.79  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.50/1.79  tff(c_62, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.50/1.79  tff(c_58, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.50/1.79  tff(c_78, plain, (![B_71, A_72]: (l1_pre_topc(B_71) | ~m1_pre_topc(B_71, A_72) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.50/1.79  tff(c_84, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_58, c_78])).
% 4.50/1.79  tff(c_88, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_84])).
% 4.50/1.79  tff(c_46, plain, (![A_54]: (m1_pre_topc(A_54, A_54) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.50/1.79  tff(c_50, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.50/1.79  tff(c_377, plain, (![A_158, B_159]: (m1_pre_topc(A_158, g1_pre_topc(u1_struct_0(B_159), u1_pre_topc(B_159))) | ~m1_pre_topc(A_158, B_159) | ~l1_pre_topc(B_159) | ~l1_pre_topc(A_158))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.50/1.79  tff(c_390, plain, (![A_158]: (m1_pre_topc(A_158, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_158, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_158))), inference(superposition, [status(thm), theory('equality')], [c_50, c_377])).
% 4.50/1.79  tff(c_405, plain, (![A_161]: (m1_pre_topc(A_161, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_161, '#skF_2') | ~l1_pre_topc(A_161))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_390])).
% 4.50/1.79  tff(c_32, plain, (![B_26, A_24]: (m1_pre_topc(B_26, A_24) | ~m1_pre_topc(B_26, g1_pre_topc(u1_struct_0(A_24), u1_pre_topc(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.50/1.79  tff(c_411, plain, (![A_161]: (m1_pre_topc(A_161, '#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(A_161, '#skF_2') | ~l1_pre_topc(A_161))), inference(resolution, [status(thm)], [c_405, c_32])).
% 4.50/1.79  tff(c_430, plain, (![A_166]: (m1_pre_topc(A_166, '#skF_3') | ~m1_pre_topc(A_166, '#skF_2') | ~l1_pre_topc(A_166))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_411])).
% 4.50/1.79  tff(c_437, plain, (m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_46, c_430])).
% 4.50/1.79  tff(c_444, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_437])).
% 4.50/1.79  tff(c_267, plain, (![B_120, A_121]: (m1_subset_1(u1_struct_0(B_120), k1_zfmisc_1(u1_struct_0(A_121))) | ~m1_pre_topc(B_120, A_121) | ~l1_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.50/1.79  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.50/1.79  tff(c_271, plain, (![B_120, A_121]: (r1_tarski(u1_struct_0(B_120), u1_struct_0(A_121)) | ~m1_pre_topc(B_120, A_121) | ~l1_pre_topc(A_121))), inference(resolution, [status(thm)], [c_267, c_8])).
% 4.50/1.79  tff(c_272, plain, (![B_122, A_123]: (r1_tarski(u1_struct_0(B_122), u1_struct_0(A_123)) | ~m1_pre_topc(B_122, A_123) | ~l1_pre_topc(A_123))), inference(resolution, [status(thm)], [c_267, c_8])).
% 4.50/1.79  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.50/1.79  tff(c_469, plain, (![B_168, A_169]: (u1_struct_0(B_168)=u1_struct_0(A_169) | ~r1_tarski(u1_struct_0(A_169), u1_struct_0(B_168)) | ~m1_pre_topc(B_168, A_169) | ~l1_pre_topc(A_169))), inference(resolution, [status(thm)], [c_272, c_2])).
% 4.50/1.79  tff(c_480, plain, (![B_170, A_171]: (u1_struct_0(B_170)=u1_struct_0(A_171) | ~m1_pre_topc(A_171, B_170) | ~l1_pre_topc(B_170) | ~m1_pre_topc(B_170, A_171) | ~l1_pre_topc(A_171))), inference(resolution, [status(thm)], [c_271, c_469])).
% 4.50/1.79  tff(c_484, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_444, c_480])).
% 4.50/1.79  tff(c_501, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_88, c_484])).
% 4.50/1.79  tff(c_54, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.50/1.79  tff(c_520, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_501, c_54])).
% 4.50/1.79  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.50/1.79  tff(c_519, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_501, c_52])).
% 4.50/1.79  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.50/1.79  tff(c_571, plain, (![F_174, D_176, A_175, C_172, B_173]: (r1_funct_2(A_175, B_173, C_172, D_176, F_174, F_174) | ~m1_subset_1(F_174, k1_zfmisc_1(k2_zfmisc_1(C_172, D_176))) | ~v1_funct_2(F_174, C_172, D_176) | ~m1_subset_1(F_174, k1_zfmisc_1(k2_zfmisc_1(A_175, B_173))) | ~v1_funct_2(F_174, A_175, B_173) | ~v1_funct_1(F_174) | v1_xboole_0(D_176) | v1_xboole_0(B_173))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.50/1.79  tff(c_1072, plain, (![A_228, C_230, B_227, D_229, A_226]: (r1_funct_2(A_226, B_227, C_230, D_229, A_228, A_228) | ~v1_funct_2(A_228, C_230, D_229) | ~m1_subset_1(A_228, k1_zfmisc_1(k2_zfmisc_1(A_226, B_227))) | ~v1_funct_2(A_228, A_226, B_227) | ~v1_funct_1(A_228) | v1_xboole_0(D_229) | v1_xboole_0(B_227) | ~r1_tarski(A_228, k2_zfmisc_1(C_230, D_229)))), inference(resolution, [status(thm)], [c_10, c_571])).
% 4.50/1.79  tff(c_1074, plain, (![C_230, D_229]: (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), C_230, D_229, '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', C_230, D_229) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(D_229) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', k2_zfmisc_1(C_230, D_229)))), inference(resolution, [status(thm)], [c_519, c_1072])).
% 4.50/1.79  tff(c_1080, plain, (![C_230, D_229]: (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), C_230, D_229, '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', C_230, D_229) | v1_xboole_0(D_229) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', k2_zfmisc_1(C_230, D_229)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_520, c_1074])).
% 4.50/1.79  tff(c_1266, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_1080])).
% 4.50/1.79  tff(c_30, plain, (![A_23]: (~v1_xboole_0(u1_struct_0(A_23)) | ~l1_struct_0(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.50/1.79  tff(c_1269, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1266, c_30])).
% 4.50/1.79  tff(c_1272, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_72, c_1269])).
% 4.50/1.79  tff(c_1275, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_1272])).
% 4.50/1.79  tff(c_1279, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_1275])).
% 4.50/1.79  tff(c_1281, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_1080])).
% 4.50/1.79  tff(c_38, plain, (![D_33, A_30, C_32, B_31, F_35]: (r1_funct_2(A_30, B_31, C_32, D_33, F_35, F_35) | ~m1_subset_1(F_35, k1_zfmisc_1(k2_zfmisc_1(C_32, D_33))) | ~v1_funct_2(F_35, C_32, D_33) | ~m1_subset_1(F_35, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~v1_funct_2(F_35, A_30, B_31) | ~v1_funct_1(F_35) | v1_xboole_0(D_33) | v1_xboole_0(B_31))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.50/1.79  tff(c_611, plain, (![A_30, B_31]: (r1_funct_2(A_30, B_31, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~v1_funct_2('#skF_4', A_30, B_31) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_31))), inference(resolution, [status(thm)], [c_519, c_38])).
% 4.50/1.79  tff(c_628, plain, (![A_30, B_31]: (r1_funct_2(A_30, B_31, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~v1_funct_2('#skF_4', A_30, B_31) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_31))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_520, c_611])).
% 4.50/1.79  tff(c_1361, plain, (![A_30, B_31]: (r1_funct_2(A_30, B_31, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~v1_funct_2('#skF_4', A_30, B_31) | v1_xboole_0(B_31))), inference(negUnitSimplification, [status(thm)], [c_1281, c_628])).
% 4.50/1.79  tff(c_70, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.50/1.79  tff(c_420, plain, (![A_162, B_163, C_164, D_165]: (k2_partfun1(A_162, B_163, C_164, D_165)=k7_relat_1(C_164, D_165) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))) | ~v1_funct_1(C_164))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.50/1.79  tff(c_422, plain, (![D_165]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_165)=k7_relat_1('#skF_4', D_165) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_52, c_420])).
% 4.50/1.79  tff(c_428, plain, (![D_165]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_165)=k7_relat_1('#skF_4', D_165))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_422])).
% 4.50/1.79  tff(c_512, plain, (![D_165]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', D_165)=k7_relat_1('#skF_4', D_165))), inference(demodulation, [status(thm), theory('equality')], [c_501, c_428])).
% 4.50/1.79  tff(c_105, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_52, c_8])).
% 4.50/1.79  tff(c_518, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_501, c_105])).
% 4.50/1.79  tff(c_66, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.50/1.79  tff(c_64, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.50/1.79  tff(c_699, plain, (![A_185, B_186, C_187, D_188]: (k2_partfun1(u1_struct_0(A_185), u1_struct_0(B_186), C_187, u1_struct_0(D_188))=k2_tmap_1(A_185, B_186, C_187, D_188) | ~m1_pre_topc(D_188, A_185) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_185), u1_struct_0(B_186)))) | ~v1_funct_2(C_187, u1_struct_0(A_185), u1_struct_0(B_186)) | ~v1_funct_1(C_187) | ~l1_pre_topc(B_186) | ~v2_pre_topc(B_186) | v2_struct_0(B_186) | ~l1_pre_topc(A_185) | ~v2_pre_topc(A_185) | v2_struct_0(A_185))), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.50/1.79  tff(c_1201, plain, (![A_280, B_281, A_282, D_283]: (k2_partfun1(u1_struct_0(A_280), u1_struct_0(B_281), A_282, u1_struct_0(D_283))=k2_tmap_1(A_280, B_281, A_282, D_283) | ~m1_pre_topc(D_283, A_280) | ~v1_funct_2(A_282, u1_struct_0(A_280), u1_struct_0(B_281)) | ~v1_funct_1(A_282) | ~l1_pre_topc(B_281) | ~v2_pre_topc(B_281) | v2_struct_0(B_281) | ~l1_pre_topc(A_280) | ~v2_pre_topc(A_280) | v2_struct_0(A_280) | ~r1_tarski(A_282, k2_zfmisc_1(u1_struct_0(A_280), u1_struct_0(B_281))))), inference(resolution, [status(thm)], [c_10, c_699])).
% 4.50/1.79  tff(c_1205, plain, (![B_281, A_282, D_283]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_281), A_282, u1_struct_0(D_283))=k2_tmap_1('#skF_2', B_281, A_282, D_283) | ~m1_pre_topc(D_283, '#skF_2') | ~v1_funct_2(A_282, u1_struct_0('#skF_2'), u1_struct_0(B_281)) | ~v1_funct_1(A_282) | ~l1_pre_topc(B_281) | ~v2_pre_topc(B_281) | v2_struct_0(B_281) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_282, k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_281))))), inference(superposition, [status(thm), theory('equality')], [c_501, c_1201])).
% 4.50/1.79  tff(c_1219, plain, (![B_281, A_282, D_283]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_281), A_282, u1_struct_0(D_283))=k2_tmap_1('#skF_2', B_281, A_282, D_283) | ~m1_pre_topc(D_283, '#skF_2') | ~v1_funct_2(A_282, u1_struct_0('#skF_3'), u1_struct_0(B_281)) | ~v1_funct_1(A_282) | ~l1_pre_topc(B_281) | ~v2_pre_topc(B_281) | v2_struct_0(B_281) | v2_struct_0('#skF_2') | ~r1_tarski(A_282, k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_281))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_501, c_501, c_1205])).
% 4.50/1.79  tff(c_1469, plain, (![B_359, A_360, D_361]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_359), A_360, u1_struct_0(D_361))=k2_tmap_1('#skF_2', B_359, A_360, D_361) | ~m1_pre_topc(D_361, '#skF_2') | ~v1_funct_2(A_360, u1_struct_0('#skF_3'), u1_struct_0(B_359)) | ~v1_funct_1(A_360) | ~l1_pre_topc(B_359) | ~v2_pre_topc(B_359) | v2_struct_0(B_359) | ~r1_tarski(A_360, k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_359))))), inference(negUnitSimplification, [status(thm)], [c_66, c_1219])).
% 4.50/1.79  tff(c_1471, plain, (![D_361]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_361))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_361) | ~m1_pre_topc(D_361, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_518, c_1469])).
% 4.50/1.79  tff(c_1482, plain, (![D_361]: (k7_relat_1('#skF_4', u1_struct_0(D_361))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_361) | ~m1_pre_topc(D_361, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_56, c_520, c_512, c_1471])).
% 4.50/1.79  tff(c_1489, plain, (![D_362]: (k7_relat_1('#skF_4', u1_struct_0(D_362))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_362) | ~m1_pre_topc(D_362, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_72, c_1482])).
% 4.50/1.79  tff(c_109, plain, (![C_78, A_79, B_80]: (v1_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.50/1.79  tff(c_117, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_109])).
% 4.50/1.79  tff(c_131, plain, (![C_86, A_87, B_88]: (v4_relat_1(C_86, A_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.50/1.79  tff(c_139, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_52, c_131])).
% 4.50/1.79  tff(c_14, plain, (![B_6, A_5]: (r1_tarski(k1_relat_1(B_6), A_5) | ~v4_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.50/1.79  tff(c_209, plain, (![B_107, A_108]: (k7_relat_1(B_107, A_108)=B_107 | ~r1_tarski(k1_relat_1(B_107), A_108) | ~v1_relat_1(B_107))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.50/1.79  tff(c_228, plain, (![B_110, A_111]: (k7_relat_1(B_110, A_111)=B_110 | ~v4_relat_1(B_110, A_111) | ~v1_relat_1(B_110))), inference(resolution, [status(thm)], [c_14, c_209])).
% 4.50/1.79  tff(c_237, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_139, c_228])).
% 4.50/1.79  tff(c_244, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_117, c_237])).
% 4.50/1.79  tff(c_514, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_501, c_244])).
% 4.50/1.79  tff(c_1495, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1489, c_514])).
% 4.50/1.79  tff(c_1507, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1495])).
% 4.50/1.79  tff(c_48, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.50/1.79  tff(c_515, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_501, c_48])).
% 4.50/1.79  tff(c_1513, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1507, c_515])).
% 4.50/1.79  tff(c_1525, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_1361, c_1513])).
% 4.50/1.79  tff(c_1534, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_520, c_519, c_1525])).
% 4.50/1.79  tff(c_1536, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1281, c_1534])).
% 4.50/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.50/1.79  
% 4.50/1.79  Inference rules
% 4.50/1.79  ----------------------
% 4.50/1.79  #Ref     : 0
% 4.50/1.79  #Sup     : 267
% 4.50/1.79  #Fact    : 0
% 4.50/1.79  #Define  : 0
% 4.50/1.79  #Split   : 6
% 4.50/1.79  #Chain   : 0
% 4.50/1.79  #Close   : 0
% 4.50/1.79  
% 4.50/1.79  Ordering : KBO
% 4.50/1.79  
% 4.50/1.79  Simplification rules
% 4.50/1.79  ----------------------
% 4.50/1.79  #Subsume      : 41
% 4.50/1.79  #Demod        : 370
% 4.50/1.79  #Tautology    : 93
% 4.50/1.79  #SimpNegUnit  : 18
% 4.50/1.79  #BackRed      : 10
% 4.50/1.79  
% 4.50/1.79  #Partial instantiations: 0
% 4.50/1.79  #Strategies tried      : 1
% 4.50/1.79  
% 4.50/1.79  Timing (in seconds)
% 4.50/1.79  ----------------------
% 4.50/1.79  Preprocessing        : 0.39
% 4.50/1.79  Parsing              : 0.21
% 4.50/1.79  CNF conversion       : 0.03
% 4.50/1.79  Main loop            : 0.60
% 4.50/1.79  Inferencing          : 0.21
% 4.50/1.79  Reduction            : 0.21
% 4.50/1.79  Demodulation         : 0.15
% 4.50/1.79  BG Simplification    : 0.03
% 4.50/1.79  Subsumption          : 0.12
% 4.50/1.79  Abstraction          : 0.03
% 4.50/1.79  MUC search           : 0.00
% 4.50/1.79  Cooper               : 0.00
% 4.50/1.79  Total                : 1.03
% 4.50/1.79  Index Insertion      : 0.00
% 4.50/1.79  Index Deletion       : 0.00
% 4.50/1.79  Index Matching       : 0.00
% 4.50/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
