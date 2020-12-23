%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:54 EST 2020

% Result     : Theorem 6.10s
% Output     : CNFRefutation 6.10s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 716 expanded)
%              Number of leaves         :   47 ( 265 expanded)
%              Depth                    :   19
%              Number of atoms          :  322 (2889 expanded)
%              Number of equality atoms :   30 ( 257 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_214,negated_conjecture,(
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

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_181,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_142,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_160,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( ( v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v2_pre_topc(C)
                & l1_pre_topc(C) )
             => ( B = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C))
               => ( m1_pre_topc(B,A)
                <=> m1_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tmap_1)).

tff(f_167,axiom,(
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

tff(f_106,axiom,(
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

tff(f_76,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_133,axiom,(
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

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(c_72,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_22,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_66,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_62,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_86,plain,(
    ! [B_81,A_82] :
      ( l1_pre_topc(B_81)
      | ~ m1_pre_topc(B_81,A_82)
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_89,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_86])).

tff(c_92,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_89])).

tff(c_68,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_793,plain,(
    ! [B_184,C_185,A_186] :
      ( m1_pre_topc(B_184,C_185)
      | ~ r1_tarski(u1_struct_0(B_184),u1_struct_0(C_185))
      | ~ m1_pre_topc(C_185,A_186)
      | ~ m1_pre_topc(B_184,A_186)
      | ~ l1_pre_topc(A_186)
      | ~ v2_pre_topc(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_820,plain,(
    ! [B_189,A_190] :
      ( m1_pre_topc(B_189,B_189)
      | ~ m1_pre_topc(B_189,A_190)
      | ~ l1_pre_topc(A_190)
      | ~ v2_pre_topc(A_190) ) ),
    inference(resolution,[status(thm)],[c_6,c_793])).

tff(c_826,plain,
    ( m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_820])).

tff(c_831,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_826])).

tff(c_38,plain,(
    ! [B_46,A_44] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_46),u1_pre_topc(B_46)),A_44)
      | ~ m1_pre_topc(B_46,A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_54,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_211,plain,(
    ! [A_115] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_115),u1_pre_topc(A_115)))
      | ~ l1_pre_topc(A_115)
      | ~ v2_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_214,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_211])).

tff(c_216,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_214])).

tff(c_228,plain,(
    ! [B_120,A_121] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_120),u1_pre_topc(B_120)),A_121)
      | ~ m1_pre_topc(B_120,A_121)
      | ~ l1_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_24,plain,(
    ! [B_20,A_18] :
      ( l1_pre_topc(B_20)
      | ~ m1_pre_topc(B_20,A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_243,plain,(
    ! [B_124,A_125] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(B_124),u1_pre_topc(B_124)))
      | ~ m1_pre_topc(B_124,A_125)
      | ~ l1_pre_topc(A_125) ) ),
    inference(resolution,[status(thm)],[c_228,c_24])).

tff(c_247,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_243])).

tff(c_251,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_247])).

tff(c_804,plain,(
    ! [C_187,A_188] :
      ( m1_pre_topc(C_187,A_188)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_187),u1_pre_topc(C_187)),A_188)
      | ~ l1_pre_topc(C_187)
      | ~ v2_pre_topc(C_187)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_187),u1_pre_topc(C_187)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_187),u1_pre_topc(C_187)))
      | ~ l1_pre_topc(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_813,plain,(
    ! [A_188] :
      ( m1_pre_topc('#skF_2',A_188)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),A_188)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_188) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_804])).

tff(c_876,plain,(
    ! [A_191] :
      ( m1_pre_topc('#skF_2',A_191)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),A_191)
      | ~ l1_pre_topc(A_191) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_54,c_251,c_54,c_68,c_66,c_813])).

tff(c_886,plain,(
    ! [A_192] :
      ( m1_pre_topc('#skF_2',A_192)
      | ~ m1_pre_topc('#skF_3',A_192)
      | ~ l1_pre_topc(A_192) ) ),
    inference(resolution,[status(thm)],[c_38,c_876])).

tff(c_223,plain,(
    ! [B_118,A_119] :
      ( m1_subset_1(u1_struct_0(B_118),k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ m1_pre_topc(B_118,A_119)
      | ~ l1_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_227,plain,(
    ! [B_118,A_119] :
      ( r1_tarski(u1_struct_0(B_118),u1_struct_0(A_119))
      | ~ m1_pre_topc(B_118,A_119)
      | ~ l1_pre_topc(A_119) ) ),
    inference(resolution,[status(thm)],[c_223,c_8])).

tff(c_239,plain,(
    ! [B_122,A_123] :
      ( r1_tarski(u1_struct_0(B_122),u1_struct_0(A_123))
      | ~ m1_pre_topc(B_122,A_123)
      | ~ l1_pre_topc(A_123) ) ),
    inference(resolution,[status(thm)],[c_223,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_264,plain,(
    ! [B_127,A_128] :
      ( u1_struct_0(B_127) = u1_struct_0(A_128)
      | ~ r1_tarski(u1_struct_0(A_128),u1_struct_0(B_127))
      | ~ m1_pre_topc(B_127,A_128)
      | ~ l1_pre_topc(A_128) ) ),
    inference(resolution,[status(thm)],[c_239,c_2])).

tff(c_275,plain,(
    ! [B_129,A_130] :
      ( u1_struct_0(B_129) = u1_struct_0(A_130)
      | ~ m1_pre_topc(A_130,B_129)
      | ~ l1_pre_topc(B_129)
      | ~ m1_pre_topc(B_129,A_130)
      | ~ l1_pre_topc(A_130) ) ),
    inference(resolution,[status(thm)],[c_227,c_264])).

tff(c_281,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_275])).

tff(c_288,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_66,c_281])).

tff(c_289,plain,(
    ~ m1_pre_topc('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_288])).

tff(c_895,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_886,c_289])).

tff(c_911,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_831,c_895])).

tff(c_912,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_288])).

tff(c_58,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_942,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_912,c_58])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_941,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_912,c_56])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1768,plain,(
    ! [B_234,C_232,D_235,A_236,F_233] :
      ( r1_funct_2(A_236,B_234,C_232,D_235,F_233,F_233)
      | ~ m1_subset_1(F_233,k1_zfmisc_1(k2_zfmisc_1(C_232,D_235)))
      | ~ v1_funct_2(F_233,C_232,D_235)
      | ~ m1_subset_1(F_233,k1_zfmisc_1(k2_zfmisc_1(A_236,B_234)))
      | ~ v1_funct_2(F_233,A_236,B_234)
      | ~ v1_funct_1(F_233)
      | v1_xboole_0(D_235)
      | v1_xboole_0(B_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2624,plain,(
    ! [B_289,C_288,A_291,D_290,A_287] :
      ( r1_funct_2(A_287,B_289,C_288,D_290,A_291,A_291)
      | ~ v1_funct_2(A_291,C_288,D_290)
      | ~ m1_subset_1(A_291,k1_zfmisc_1(k2_zfmisc_1(A_287,B_289)))
      | ~ v1_funct_2(A_291,A_287,B_289)
      | ~ v1_funct_1(A_291)
      | v1_xboole_0(D_290)
      | v1_xboole_0(B_289)
      | ~ r1_tarski(A_291,k2_zfmisc_1(C_288,D_290)) ) ),
    inference(resolution,[status(thm)],[c_10,c_1768])).

tff(c_2626,plain,(
    ! [C_288,D_290] :
      ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),C_288,D_290,'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',C_288,D_290)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(D_290)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(C_288,D_290)) ) ),
    inference(resolution,[status(thm)],[c_941,c_2624])).

tff(c_2632,plain,(
    ! [C_288,D_290] :
      ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),C_288,D_290,'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',C_288,D_290)
      | v1_xboole_0(D_290)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(C_288,D_290)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_942,c_2626])).

tff(c_3871,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2632])).

tff(c_26,plain,(
    ! [A_21] :
      ( ~ v1_xboole_0(u1_struct_0(A_21))
      | ~ l1_struct_0(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3874,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_3871,c_26])).

tff(c_3877,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_3874])).

tff(c_3880,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_3877])).

tff(c_3884,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3880])).

tff(c_3886,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_2632])).

tff(c_97,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_56,c_8])).

tff(c_940,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_912,c_97])).

tff(c_3887,plain,(
    ! [C_333,D_334] :
      ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),C_333,D_334,'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',C_333,D_334)
      | v1_xboole_0(D_334)
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(C_333,D_334)) ) ),
    inference(splitRight,[status(thm)],[c_2632])).

tff(c_74,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_20,plain,(
    ! [A_13,B_14,C_15,D_16] :
      ( k2_partfun1(A_13,B_14,C_15,D_16) = k7_relat_1(C_15,D_16)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1047,plain,(
    ! [D_16] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',D_16) = k7_relat_1('#skF_4',D_16)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_941,c_20])).

tff(c_1062,plain,(
    ! [D_16] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',D_16) = k7_relat_1('#skF_4',D_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1047])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_1916,plain,(
    ! [A_252,B_253,C_254,D_255] :
      ( k2_partfun1(u1_struct_0(A_252),u1_struct_0(B_253),C_254,u1_struct_0(D_255)) = k2_tmap_1(A_252,B_253,C_254,D_255)
      | ~ m1_pre_topc(D_255,A_252)
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_252),u1_struct_0(B_253))))
      | ~ v1_funct_2(C_254,u1_struct_0(A_252),u1_struct_0(B_253))
      | ~ v1_funct_1(C_254)
      | ~ l1_pre_topc(B_253)
      | ~ v2_pre_topc(B_253)
      | v2_struct_0(B_253)
      | ~ l1_pre_topc(A_252)
      | ~ v2_pre_topc(A_252)
      | v2_struct_0(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1924,plain,(
    ! [B_253,C_254,D_255] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_253),C_254,u1_struct_0(D_255)) = k2_tmap_1('#skF_2',B_253,C_254,D_255)
      | ~ m1_pre_topc(D_255,'#skF_2')
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_253))))
      | ~ v1_funct_2(C_254,u1_struct_0('#skF_2'),u1_struct_0(B_253))
      | ~ v1_funct_1(C_254)
      | ~ l1_pre_topc(B_253)
      | ~ v2_pre_topc(B_253)
      | v2_struct_0(B_253)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_912,c_1916])).

tff(c_1939,plain,(
    ! [B_253,C_254,D_255] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_253),C_254,u1_struct_0(D_255)) = k2_tmap_1('#skF_2',B_253,C_254,D_255)
      | ~ m1_pre_topc(D_255,'#skF_2')
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_253))))
      | ~ v1_funct_2(C_254,u1_struct_0('#skF_3'),u1_struct_0(B_253))
      | ~ v1_funct_1(C_254)
      | ~ l1_pre_topc(B_253)
      | ~ v2_pre_topc(B_253)
      | v2_struct_0(B_253)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_912,c_912,c_1924])).

tff(c_1962,plain,(
    ! [B_260,C_261,D_262] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_260),C_261,u1_struct_0(D_262)) = k2_tmap_1('#skF_2',B_260,C_261,D_262)
      | ~ m1_pre_topc(D_262,'#skF_2')
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_260))))
      | ~ v1_funct_2(C_261,u1_struct_0('#skF_3'),u1_struct_0(B_260))
      | ~ v1_funct_1(C_261)
      | ~ l1_pre_topc(B_260)
      | ~ v2_pre_topc(B_260)
      | v2_struct_0(B_260) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1939])).

tff(c_1966,plain,(
    ! [D_262] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_262)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_262)
      | ~ m1_pre_topc(D_262,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_941,c_1962])).

tff(c_1976,plain,(
    ! [D_262] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_262)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_262)
      | ~ m1_pre_topc(D_262,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_60,c_942,c_1062,c_1966])).

tff(c_1982,plain,(
    ! [D_263] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_263)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_263)
      | ~ m1_pre_topc(D_263,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1976])).

tff(c_112,plain,(
    ! [C_86,A_87,B_88] :
      ( v1_relat_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_120,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_112])).

tff(c_156,plain,(
    ! [C_102,A_103,B_104] :
      ( v4_relat_1(C_102,A_103)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_164,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_56,c_156])).

tff(c_178,plain,(
    ! [B_110,A_111] :
      ( k7_relat_1(B_110,A_111) = B_110
      | ~ v4_relat_1(B_110,A_111)
      | ~ v1_relat_1(B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_184,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_164,c_178])).

tff(c_190,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_184])).

tff(c_936,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_912,c_190])).

tff(c_1988,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1982,c_936])).

tff(c_2003,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1988])).

tff(c_52,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_938,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_912,c_52])).

tff(c_2010,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2003,c_938])).

tff(c_3890,plain,
    ( ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_3887,c_2010])).

tff(c_3895,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_940,c_942,c_3890])).

tff(c_3897,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3886,c_3895])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:52:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.10/2.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.10/2.19  
% 6.10/2.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.10/2.19  %$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.10/2.19  
% 6.10/2.19  %Foreground sorts:
% 6.10/2.19  
% 6.10/2.19  
% 6.10/2.19  %Background operators:
% 6.10/2.19  
% 6.10/2.19  
% 6.10/2.19  %Foreground operators:
% 6.10/2.19  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.10/2.19  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 6.10/2.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.10/2.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.10/2.19  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 6.10/2.19  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.10/2.19  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.10/2.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.10/2.19  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.10/2.19  tff('#skF_2', type, '#skF_2': $i).
% 6.10/2.19  tff('#skF_3', type, '#skF_3': $i).
% 6.10/2.19  tff('#skF_1', type, '#skF_1': $i).
% 6.10/2.19  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 6.10/2.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.10/2.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.10/2.19  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.10/2.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.10/2.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.10/2.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.10/2.19  tff('#skF_4', type, '#skF_4': $i).
% 6.10/2.19  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 6.10/2.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.10/2.19  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.10/2.19  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 6.10/2.19  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.10/2.19  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.10/2.19  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 6.10/2.19  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.10/2.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.10/2.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.10/2.19  
% 6.10/2.21  tff(f_214, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_tmap_1)).
% 6.10/2.21  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.10/2.21  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 6.10/2.21  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.10/2.21  tff(f_181, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 6.10/2.21  tff(f_142, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tmap_1)).
% 6.10/2.21  tff(f_84, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_pre_topc)).
% 6.10/2.21  tff(f_160, axiom, (![A]: (l1_pre_topc(A) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((B = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) => (m1_pre_topc(B, A) <=> m1_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_tmap_1)).
% 6.10/2.21  tff(f_167, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 6.10/2.21  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.10/2.21  tff(f_106, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 6.10/2.21  tff(f_76, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 6.10/2.21  tff(f_57, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 6.10/2.21  tff(f_133, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 6.10/2.21  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.10/2.21  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.10/2.21  tff(f_41, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 6.10/2.21  tff(c_72, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_214])).
% 6.10/2.21  tff(c_22, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.10/2.21  tff(c_76, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_214])).
% 6.10/2.21  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_214])).
% 6.10/2.21  tff(c_66, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_214])).
% 6.10/2.21  tff(c_62, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_214])).
% 6.10/2.21  tff(c_86, plain, (![B_81, A_82]: (l1_pre_topc(B_81) | ~m1_pre_topc(B_81, A_82) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.10/2.21  tff(c_89, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_86])).
% 6.10/2.21  tff(c_92, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_89])).
% 6.10/2.21  tff(c_68, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_214])).
% 6.10/2.21  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.10/2.21  tff(c_793, plain, (![B_184, C_185, A_186]: (m1_pre_topc(B_184, C_185) | ~r1_tarski(u1_struct_0(B_184), u1_struct_0(C_185)) | ~m1_pre_topc(C_185, A_186) | ~m1_pre_topc(B_184, A_186) | ~l1_pre_topc(A_186) | ~v2_pre_topc(A_186))), inference(cnfTransformation, [status(thm)], [f_181])).
% 6.10/2.21  tff(c_820, plain, (![B_189, A_190]: (m1_pre_topc(B_189, B_189) | ~m1_pre_topc(B_189, A_190) | ~l1_pre_topc(A_190) | ~v2_pre_topc(A_190))), inference(resolution, [status(thm)], [c_6, c_793])).
% 6.10/2.21  tff(c_826, plain, (m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_820])).
% 6.10/2.21  tff(c_831, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_826])).
% 6.10/2.21  tff(c_38, plain, (![B_46, A_44]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_46), u1_pre_topc(B_46)), A_44) | ~m1_pre_topc(B_46, A_44) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.10/2.21  tff(c_54, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_214])).
% 6.10/2.21  tff(c_211, plain, (![A_115]: (v2_pre_topc(g1_pre_topc(u1_struct_0(A_115), u1_pre_topc(A_115))) | ~l1_pre_topc(A_115) | ~v2_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.10/2.21  tff(c_214, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_54, c_211])).
% 6.10/2.21  tff(c_216, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_214])).
% 6.10/2.21  tff(c_228, plain, (![B_120, A_121]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_120), u1_pre_topc(B_120)), A_121) | ~m1_pre_topc(B_120, A_121) | ~l1_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.10/2.21  tff(c_24, plain, (![B_20, A_18]: (l1_pre_topc(B_20) | ~m1_pre_topc(B_20, A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.10/2.21  tff(c_243, plain, (![B_124, A_125]: (l1_pre_topc(g1_pre_topc(u1_struct_0(B_124), u1_pre_topc(B_124))) | ~m1_pre_topc(B_124, A_125) | ~l1_pre_topc(A_125))), inference(resolution, [status(thm)], [c_228, c_24])).
% 6.10/2.21  tff(c_247, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_243])).
% 6.10/2.21  tff(c_251, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_247])).
% 6.10/2.21  tff(c_804, plain, (![C_187, A_188]: (m1_pre_topc(C_187, A_188) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_187), u1_pre_topc(C_187)), A_188) | ~l1_pre_topc(C_187) | ~v2_pre_topc(C_187) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_187), u1_pre_topc(C_187))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_187), u1_pre_topc(C_187))) | ~l1_pre_topc(A_188))), inference(cnfTransformation, [status(thm)], [f_160])).
% 6.10/2.21  tff(c_813, plain, (![A_188]: (m1_pre_topc('#skF_2', A_188) | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), A_188) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_188))), inference(superposition, [status(thm), theory('equality')], [c_54, c_804])).
% 6.10/2.21  tff(c_876, plain, (![A_191]: (m1_pre_topc('#skF_2', A_191) | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), A_191) | ~l1_pre_topc(A_191))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_54, c_251, c_54, c_68, c_66, c_813])).
% 6.10/2.21  tff(c_886, plain, (![A_192]: (m1_pre_topc('#skF_2', A_192) | ~m1_pre_topc('#skF_3', A_192) | ~l1_pre_topc(A_192))), inference(resolution, [status(thm)], [c_38, c_876])).
% 6.10/2.21  tff(c_223, plain, (![B_118, A_119]: (m1_subset_1(u1_struct_0(B_118), k1_zfmisc_1(u1_struct_0(A_119))) | ~m1_pre_topc(B_118, A_119) | ~l1_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_167])).
% 6.10/2.21  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.10/2.21  tff(c_227, plain, (![B_118, A_119]: (r1_tarski(u1_struct_0(B_118), u1_struct_0(A_119)) | ~m1_pre_topc(B_118, A_119) | ~l1_pre_topc(A_119))), inference(resolution, [status(thm)], [c_223, c_8])).
% 6.10/2.21  tff(c_239, plain, (![B_122, A_123]: (r1_tarski(u1_struct_0(B_122), u1_struct_0(A_123)) | ~m1_pre_topc(B_122, A_123) | ~l1_pre_topc(A_123))), inference(resolution, [status(thm)], [c_223, c_8])).
% 6.10/2.21  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.10/2.21  tff(c_264, plain, (![B_127, A_128]: (u1_struct_0(B_127)=u1_struct_0(A_128) | ~r1_tarski(u1_struct_0(A_128), u1_struct_0(B_127)) | ~m1_pre_topc(B_127, A_128) | ~l1_pre_topc(A_128))), inference(resolution, [status(thm)], [c_239, c_2])).
% 6.10/2.21  tff(c_275, plain, (![B_129, A_130]: (u1_struct_0(B_129)=u1_struct_0(A_130) | ~m1_pre_topc(A_130, B_129) | ~l1_pre_topc(B_129) | ~m1_pre_topc(B_129, A_130) | ~l1_pre_topc(A_130))), inference(resolution, [status(thm)], [c_227, c_264])).
% 6.10/2.21  tff(c_281, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_62, c_275])).
% 6.10/2.21  tff(c_288, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_66, c_281])).
% 6.10/2.21  tff(c_289, plain, (~m1_pre_topc('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_288])).
% 6.10/2.21  tff(c_895, plain, (~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_886, c_289])).
% 6.10/2.21  tff(c_911, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_831, c_895])).
% 6.10/2.21  tff(c_912, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_288])).
% 6.10/2.21  tff(c_58, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_214])).
% 6.10/2.21  tff(c_942, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_912, c_58])).
% 6.10/2.21  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_214])).
% 6.10/2.21  tff(c_941, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_912, c_56])).
% 6.10/2.21  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.10/2.21  tff(c_1768, plain, (![B_234, C_232, D_235, A_236, F_233]: (r1_funct_2(A_236, B_234, C_232, D_235, F_233, F_233) | ~m1_subset_1(F_233, k1_zfmisc_1(k2_zfmisc_1(C_232, D_235))) | ~v1_funct_2(F_233, C_232, D_235) | ~m1_subset_1(F_233, k1_zfmisc_1(k2_zfmisc_1(A_236, B_234))) | ~v1_funct_2(F_233, A_236, B_234) | ~v1_funct_1(F_233) | v1_xboole_0(D_235) | v1_xboole_0(B_234))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.10/2.21  tff(c_2624, plain, (![B_289, C_288, A_291, D_290, A_287]: (r1_funct_2(A_287, B_289, C_288, D_290, A_291, A_291) | ~v1_funct_2(A_291, C_288, D_290) | ~m1_subset_1(A_291, k1_zfmisc_1(k2_zfmisc_1(A_287, B_289))) | ~v1_funct_2(A_291, A_287, B_289) | ~v1_funct_1(A_291) | v1_xboole_0(D_290) | v1_xboole_0(B_289) | ~r1_tarski(A_291, k2_zfmisc_1(C_288, D_290)))), inference(resolution, [status(thm)], [c_10, c_1768])).
% 6.10/2.21  tff(c_2626, plain, (![C_288, D_290]: (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), C_288, D_290, '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', C_288, D_290) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(D_290) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', k2_zfmisc_1(C_288, D_290)))), inference(resolution, [status(thm)], [c_941, c_2624])).
% 6.10/2.21  tff(c_2632, plain, (![C_288, D_290]: (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), C_288, D_290, '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', C_288, D_290) | v1_xboole_0(D_290) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', k2_zfmisc_1(C_288, D_290)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_942, c_2626])).
% 6.10/2.21  tff(c_3871, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_2632])).
% 6.10/2.21  tff(c_26, plain, (![A_21]: (~v1_xboole_0(u1_struct_0(A_21)) | ~l1_struct_0(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.10/2.21  tff(c_3874, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_3871, c_26])).
% 6.10/2.21  tff(c_3877, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_76, c_3874])).
% 6.10/2.21  tff(c_3880, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_3877])).
% 6.10/2.21  tff(c_3884, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_3880])).
% 6.10/2.21  tff(c_3886, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_2632])).
% 6.10/2.21  tff(c_97, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_56, c_8])).
% 6.10/2.21  tff(c_940, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_912, c_97])).
% 6.10/2.21  tff(c_3887, plain, (![C_333, D_334]: (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), C_333, D_334, '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', C_333, D_334) | v1_xboole_0(D_334) | ~r1_tarski('#skF_4', k2_zfmisc_1(C_333, D_334)))), inference(splitRight, [status(thm)], [c_2632])).
% 6.10/2.21  tff(c_74, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_214])).
% 6.10/2.21  tff(c_20, plain, (![A_13, B_14, C_15, D_16]: (k2_partfun1(A_13, B_14, C_15, D_16)=k7_relat_1(C_15, D_16) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.10/2.21  tff(c_1047, plain, (![D_16]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', D_16)=k7_relat_1('#skF_4', D_16) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_941, c_20])).
% 6.10/2.21  tff(c_1062, plain, (![D_16]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', D_16)=k7_relat_1('#skF_4', D_16))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1047])).
% 6.10/2.21  tff(c_70, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_214])).
% 6.10/2.21  tff(c_1916, plain, (![A_252, B_253, C_254, D_255]: (k2_partfun1(u1_struct_0(A_252), u1_struct_0(B_253), C_254, u1_struct_0(D_255))=k2_tmap_1(A_252, B_253, C_254, D_255) | ~m1_pre_topc(D_255, A_252) | ~m1_subset_1(C_254, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_252), u1_struct_0(B_253)))) | ~v1_funct_2(C_254, u1_struct_0(A_252), u1_struct_0(B_253)) | ~v1_funct_1(C_254) | ~l1_pre_topc(B_253) | ~v2_pre_topc(B_253) | v2_struct_0(B_253) | ~l1_pre_topc(A_252) | ~v2_pre_topc(A_252) | v2_struct_0(A_252))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.10/2.21  tff(c_1924, plain, (![B_253, C_254, D_255]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_253), C_254, u1_struct_0(D_255))=k2_tmap_1('#skF_2', B_253, C_254, D_255) | ~m1_pre_topc(D_255, '#skF_2') | ~m1_subset_1(C_254, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_253)))) | ~v1_funct_2(C_254, u1_struct_0('#skF_2'), u1_struct_0(B_253)) | ~v1_funct_1(C_254) | ~l1_pre_topc(B_253) | ~v2_pre_topc(B_253) | v2_struct_0(B_253) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_912, c_1916])).
% 6.10/2.21  tff(c_1939, plain, (![B_253, C_254, D_255]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_253), C_254, u1_struct_0(D_255))=k2_tmap_1('#skF_2', B_253, C_254, D_255) | ~m1_pre_topc(D_255, '#skF_2') | ~m1_subset_1(C_254, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_253)))) | ~v1_funct_2(C_254, u1_struct_0('#skF_3'), u1_struct_0(B_253)) | ~v1_funct_1(C_254) | ~l1_pre_topc(B_253) | ~v2_pre_topc(B_253) | v2_struct_0(B_253) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_912, c_912, c_1924])).
% 6.10/2.21  tff(c_1962, plain, (![B_260, C_261, D_262]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_260), C_261, u1_struct_0(D_262))=k2_tmap_1('#skF_2', B_260, C_261, D_262) | ~m1_pre_topc(D_262, '#skF_2') | ~m1_subset_1(C_261, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_260)))) | ~v1_funct_2(C_261, u1_struct_0('#skF_3'), u1_struct_0(B_260)) | ~v1_funct_1(C_261) | ~l1_pre_topc(B_260) | ~v2_pre_topc(B_260) | v2_struct_0(B_260))), inference(negUnitSimplification, [status(thm)], [c_70, c_1939])).
% 6.10/2.21  tff(c_1966, plain, (![D_262]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_262))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_262) | ~m1_pre_topc(D_262, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_941, c_1962])).
% 6.10/2.21  tff(c_1976, plain, (![D_262]: (k7_relat_1('#skF_4', u1_struct_0(D_262))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_262) | ~m1_pre_topc(D_262, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_60, c_942, c_1062, c_1966])).
% 6.10/2.21  tff(c_1982, plain, (![D_263]: (k7_relat_1('#skF_4', u1_struct_0(D_263))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_263) | ~m1_pre_topc(D_263, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_76, c_1976])).
% 6.10/2.21  tff(c_112, plain, (![C_86, A_87, B_88]: (v1_relat_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.10/2.21  tff(c_120, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_112])).
% 6.10/2.21  tff(c_156, plain, (![C_102, A_103, B_104]: (v4_relat_1(C_102, A_103) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.10/2.21  tff(c_164, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_56, c_156])).
% 6.10/2.21  tff(c_178, plain, (![B_110, A_111]: (k7_relat_1(B_110, A_111)=B_110 | ~v4_relat_1(B_110, A_111) | ~v1_relat_1(B_110))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.10/2.21  tff(c_184, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_164, c_178])).
% 6.10/2.21  tff(c_190, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_120, c_184])).
% 6.10/2.21  tff(c_936, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_912, c_190])).
% 6.10/2.21  tff(c_1988, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1982, c_936])).
% 6.10/2.21  tff(c_2003, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1988])).
% 6.10/2.21  tff(c_52, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_214])).
% 6.10/2.21  tff(c_938, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_912, c_52])).
% 6.10/2.21  tff(c_2010, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2003, c_938])).
% 6.10/2.21  tff(c_3890, plain, (~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_3887, c_2010])).
% 6.10/2.21  tff(c_3895, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_940, c_942, c_3890])).
% 6.10/2.21  tff(c_3897, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3886, c_3895])).
% 6.10/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.10/2.21  
% 6.10/2.21  Inference rules
% 6.10/2.21  ----------------------
% 6.10/2.21  #Ref     : 0
% 6.10/2.21  #Sup     : 760
% 6.10/2.21  #Fact    : 0
% 6.10/2.21  #Define  : 0
% 6.10/2.21  #Split   : 15
% 6.10/2.21  #Chain   : 0
% 6.10/2.21  #Close   : 0
% 6.10/2.21  
% 6.10/2.21  Ordering : KBO
% 6.10/2.21  
% 6.10/2.21  Simplification rules
% 6.10/2.21  ----------------------
% 6.10/2.21  #Subsume      : 114
% 6.10/2.21  #Demod        : 1441
% 6.10/2.21  #Tautology    : 335
% 6.10/2.21  #SimpNegUnit  : 17
% 6.10/2.21  #BackRed      : 13
% 6.10/2.21  
% 6.10/2.21  #Partial instantiations: 0
% 6.10/2.21  #Strategies tried      : 1
% 6.10/2.21  
% 6.10/2.21  Timing (in seconds)
% 6.10/2.21  ----------------------
% 6.10/2.21  Preprocessing        : 0.38
% 6.10/2.21  Parsing              : 0.20
% 6.10/2.22  CNF conversion       : 0.03
% 6.10/2.22  Main loop            : 1.05
% 6.10/2.22  Inferencing          : 0.33
% 6.10/2.22  Reduction            : 0.41
% 6.10/2.22  Demodulation         : 0.31
% 6.10/2.22  BG Simplification    : 0.04
% 6.10/2.22  Subsumption          : 0.21
% 6.10/2.22  Abstraction          : 0.05
% 6.10/2.22  MUC search           : 0.00
% 6.10/2.22  Cooper               : 0.00
% 6.10/2.22  Total                : 1.48
% 6.10/2.22  Index Insertion      : 0.00
% 6.10/2.22  Index Deletion       : 0.00
% 6.10/2.22  Index Matching       : 0.00
% 6.10/2.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
