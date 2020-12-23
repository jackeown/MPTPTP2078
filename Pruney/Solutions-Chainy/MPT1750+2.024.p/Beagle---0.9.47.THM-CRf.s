%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:54 EST 2020

% Result     : Theorem 6.19s
% Output     : CNFRefutation 6.57s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 718 expanded)
%              Number of leaves         :   47 ( 266 expanded)
%              Depth                    :   17
%              Number of atoms          :  329 (2915 expanded)
%              Number of equality atoms :   30 ( 256 expanded)
%              Maximal formula depth    :   16 (   5 average)
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

tff(f_212,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_tmap_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_179,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_140,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_158,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tmap_1)).

tff(f_165,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_104,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(B)
        & ~ v1_xboole_0(D)
        & v1_funct_1(E)
        & v1_funct_2(E,A,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,C,D)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => r1_funct_2(A,B,C,D,E,E) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).

tff(f_76,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_131,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(c_70,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_22,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_64,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_60,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_85,plain,(
    ! [B_82,A_83] :
      ( l1_pre_topc(B_82)
      | ~ m1_pre_topc(B_82,A_83)
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_88,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_85])).

tff(c_91,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_88])).

tff(c_66,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_791,plain,(
    ! [B_184,C_185,A_186] :
      ( m1_pre_topc(B_184,C_185)
      | ~ r1_tarski(u1_struct_0(B_184),u1_struct_0(C_185))
      | ~ m1_pre_topc(C_185,A_186)
      | ~ m1_pre_topc(B_184,A_186)
      | ~ l1_pre_topc(A_186)
      | ~ v2_pre_topc(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_818,plain,(
    ! [B_189,A_190] :
      ( m1_pre_topc(B_189,B_189)
      | ~ m1_pre_topc(B_189,A_190)
      | ~ l1_pre_topc(A_190)
      | ~ v2_pre_topc(A_190) ) ),
    inference(resolution,[status(thm)],[c_6,c_791])).

tff(c_824,plain,
    ( m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_818])).

tff(c_829,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_824])).

tff(c_36,plain,(
    ! [B_46,A_44] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_46),u1_pre_topc(B_46)),A_44)
      | ~ m1_pre_topc(B_46,A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_52,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_193,plain,(
    ! [A_112] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_112),u1_pre_topc(A_112)))
      | ~ l1_pre_topc(A_112)
      | ~ v2_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_196,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_193])).

tff(c_198,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_196])).

tff(c_229,plain,(
    ! [B_122,A_123] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_122),u1_pre_topc(B_122)),A_123)
      | ~ m1_pre_topc(B_122,A_123)
      | ~ l1_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_24,plain,(
    ! [B_20,A_18] :
      ( l1_pre_topc(B_20)
      | ~ m1_pre_topc(B_20,A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_259,plain,(
    ! [B_129,A_130] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(B_129),u1_pre_topc(B_129)))
      | ~ m1_pre_topc(B_129,A_130)
      | ~ l1_pre_topc(A_130) ) ),
    inference(resolution,[status(thm)],[c_229,c_24])).

tff(c_263,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_259])).

tff(c_267,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_263])).

tff(c_802,plain,(
    ! [C_187,A_188] :
      ( m1_pre_topc(C_187,A_188)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_187),u1_pre_topc(C_187)),A_188)
      | ~ l1_pre_topc(C_187)
      | ~ v2_pre_topc(C_187)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_187),u1_pre_topc(C_187)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_187),u1_pre_topc(C_187)))
      | ~ l1_pre_topc(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_811,plain,(
    ! [A_188] :
      ( m1_pre_topc('#skF_2',A_188)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),A_188)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_188) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_802])).

tff(c_874,plain,(
    ! [A_191] :
      ( m1_pre_topc('#skF_2',A_191)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),A_191)
      | ~ l1_pre_topc(A_191) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_52,c_267,c_52,c_66,c_64,c_811])).

tff(c_884,plain,(
    ! [A_192] :
      ( m1_pre_topc('#skF_2',A_192)
      | ~ m1_pre_topc('#skF_3',A_192)
      | ~ l1_pre_topc(A_192) ) ),
    inference(resolution,[status(thm)],[c_36,c_874])).

tff(c_220,plain,(
    ! [B_118,A_119] :
      ( m1_subset_1(u1_struct_0(B_118),k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ m1_pre_topc(B_118,A_119)
      | ~ l1_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_224,plain,(
    ! [B_118,A_119] :
      ( r1_tarski(u1_struct_0(B_118),u1_struct_0(A_119))
      | ~ m1_pre_topc(B_118,A_119)
      | ~ l1_pre_topc(A_119) ) ),
    inference(resolution,[status(thm)],[c_220,c_8])).

tff(c_225,plain,(
    ! [B_120,A_121] :
      ( r1_tarski(u1_struct_0(B_120),u1_struct_0(A_121))
      | ~ m1_pre_topc(B_120,A_121)
      | ~ l1_pre_topc(A_121) ) ),
    inference(resolution,[status(thm)],[c_220,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_281,plain,(
    ! [B_132,A_133] :
      ( u1_struct_0(B_132) = u1_struct_0(A_133)
      | ~ r1_tarski(u1_struct_0(A_133),u1_struct_0(B_132))
      | ~ m1_pre_topc(B_132,A_133)
      | ~ l1_pre_topc(A_133) ) ),
    inference(resolution,[status(thm)],[c_225,c_2])).

tff(c_292,plain,(
    ! [B_134,A_135] :
      ( u1_struct_0(B_134) = u1_struct_0(A_135)
      | ~ m1_pre_topc(A_135,B_134)
      | ~ l1_pre_topc(B_134)
      | ~ m1_pre_topc(B_134,A_135)
      | ~ l1_pre_topc(A_135) ) ),
    inference(resolution,[status(thm)],[c_224,c_281])).

tff(c_298,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_292])).

tff(c_305,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_64,c_298])).

tff(c_306,plain,(
    ~ m1_pre_topc('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_305])).

tff(c_891,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_884,c_306])).

tff(c_908,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_829,c_891])).

tff(c_909,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_305])).

tff(c_56,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_940,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_909,c_56])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_939,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_909,c_54])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1914,plain,(
    ! [A_274,D_273,C_269,E_271,F_270,B_272] :
      ( r1_funct_2(A_274,B_272,C_269,D_273,E_271,E_271)
      | ~ m1_subset_1(F_270,k1_zfmisc_1(k2_zfmisc_1(C_269,D_273)))
      | ~ v1_funct_2(F_270,C_269,D_273)
      | ~ v1_funct_1(F_270)
      | ~ m1_subset_1(E_271,k1_zfmisc_1(k2_zfmisc_1(A_274,B_272)))
      | ~ v1_funct_2(E_271,A_274,B_272)
      | ~ v1_funct_1(E_271)
      | v1_xboole_0(D_273)
      | v1_xboole_0(B_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2847,plain,(
    ! [E_320,A_319,D_322,C_324,B_321,A_323] :
      ( r1_funct_2(A_319,B_321,C_324,D_322,E_320,E_320)
      | ~ v1_funct_2(A_323,C_324,D_322)
      | ~ v1_funct_1(A_323)
      | ~ m1_subset_1(E_320,k1_zfmisc_1(k2_zfmisc_1(A_319,B_321)))
      | ~ v1_funct_2(E_320,A_319,B_321)
      | ~ v1_funct_1(E_320)
      | v1_xboole_0(D_322)
      | v1_xboole_0(B_321)
      | ~ r1_tarski(A_323,k2_zfmisc_1(C_324,D_322)) ) ),
    inference(resolution,[status(thm)],[c_10,c_1914])).

tff(c_2849,plain,(
    ! [C_324,D_322,A_323] :
      ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),C_324,D_322,'#skF_4','#skF_4')
      | ~ v1_funct_2(A_323,C_324,D_322)
      | ~ v1_funct_1(A_323)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(D_322)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_323,k2_zfmisc_1(C_324,D_322)) ) ),
    inference(resolution,[status(thm)],[c_939,c_2847])).

tff(c_2855,plain,(
    ! [C_324,D_322,A_323] :
      ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),C_324,D_322,'#skF_4','#skF_4')
      | ~ v1_funct_2(A_323,C_324,D_322)
      | ~ v1_funct_1(A_323)
      | v1_xboole_0(D_322)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_323,k2_zfmisc_1(C_324,D_322)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_940,c_2849])).

tff(c_5031,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2855])).

tff(c_26,plain,(
    ! [A_21] :
      ( ~ v1_xboole_0(u1_struct_0(A_21))
      | ~ l1_struct_0(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_5034,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_5031,c_26])).

tff(c_5037,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_5034])).

tff(c_5040,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_5037])).

tff(c_5044,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_5040])).

tff(c_5046,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_2855])).

tff(c_72,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_240,plain,(
    ! [A_124,B_125,C_126,D_127] :
      ( k2_partfun1(A_124,B_125,C_126,D_127) = k7_relat_1(C_126,D_127)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125)))
      | ~ v1_funct_1(C_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_242,plain,(
    ! [D_127] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_127) = k7_relat_1('#skF_4',D_127)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_240])).

tff(c_248,plain,(
    ! [D_127] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_127) = k7_relat_1('#skF_4',D_127) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_242])).

tff(c_933,plain,(
    ! [D_127] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',D_127) = k7_relat_1('#skF_4',D_127) ),
    inference(demodulation,[status(thm),theory(equality)],[c_909,c_248])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_2182,plain,(
    ! [A_279,B_280,C_281,D_282] :
      ( k2_partfun1(u1_struct_0(A_279),u1_struct_0(B_280),C_281,u1_struct_0(D_282)) = k2_tmap_1(A_279,B_280,C_281,D_282)
      | ~ m1_pre_topc(D_282,A_279)
      | ~ m1_subset_1(C_281,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_279),u1_struct_0(B_280))))
      | ~ v1_funct_2(C_281,u1_struct_0(A_279),u1_struct_0(B_280))
      | ~ v1_funct_1(C_281)
      | ~ l1_pre_topc(B_280)
      | ~ v2_pre_topc(B_280)
      | v2_struct_0(B_280)
      | ~ l1_pre_topc(A_279)
      | ~ v2_pre_topc(A_279)
      | v2_struct_0(A_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2190,plain,(
    ! [B_280,C_281,D_282] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_280),C_281,u1_struct_0(D_282)) = k2_tmap_1('#skF_2',B_280,C_281,D_282)
      | ~ m1_pre_topc(D_282,'#skF_2')
      | ~ m1_subset_1(C_281,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_280))))
      | ~ v1_funct_2(C_281,u1_struct_0('#skF_2'),u1_struct_0(B_280))
      | ~ v1_funct_1(C_281)
      | ~ l1_pre_topc(B_280)
      | ~ v2_pre_topc(B_280)
      | v2_struct_0(B_280)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_909,c_2182])).

tff(c_2205,plain,(
    ! [B_280,C_281,D_282] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_280),C_281,u1_struct_0(D_282)) = k2_tmap_1('#skF_2',B_280,C_281,D_282)
      | ~ m1_pre_topc(D_282,'#skF_2')
      | ~ m1_subset_1(C_281,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_280))))
      | ~ v1_funct_2(C_281,u1_struct_0('#skF_3'),u1_struct_0(B_280))
      | ~ v1_funct_1(C_281)
      | ~ l1_pre_topc(B_280)
      | ~ v2_pre_topc(B_280)
      | v2_struct_0(B_280)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_909,c_909,c_2190])).

tff(c_2241,plain,(
    ! [B_284,C_285,D_286] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_284),C_285,u1_struct_0(D_286)) = k2_tmap_1('#skF_2',B_284,C_285,D_286)
      | ~ m1_pre_topc(D_286,'#skF_2')
      | ~ m1_subset_1(C_285,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_284))))
      | ~ v1_funct_2(C_285,u1_struct_0('#skF_3'),u1_struct_0(B_284))
      | ~ v1_funct_1(C_285)
      | ~ l1_pre_topc(B_284)
      | ~ v2_pre_topc(B_284)
      | v2_struct_0(B_284) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2205])).

tff(c_2245,plain,(
    ! [D_286] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_286)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_286)
      | ~ m1_pre_topc(D_286,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_939,c_2241])).

tff(c_2255,plain,(
    ! [D_286] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_286)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_286)
      | ~ m1_pre_topc(D_286,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_58,c_940,c_933,c_2245])).

tff(c_2291,plain,(
    ! [D_288] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_288)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_288)
      | ~ m1_pre_topc(D_288,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2255])).

tff(c_14,plain,(
    ! [C_9,A_7,B_8] :
      ( v1_relat_1(C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_110,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_14])).

tff(c_138,plain,(
    ! [C_97,A_98,B_99] :
      ( v4_relat_1(C_97,A_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_146,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_138])).

tff(c_176,plain,(
    ! [B_110,A_111] :
      ( k7_relat_1(B_110,A_111) = B_110
      | ~ v4_relat_1(B_110,A_111)
      | ~ v1_relat_1(B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_182,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_146,c_176])).

tff(c_188,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_182])).

tff(c_935,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_909,c_188])).

tff(c_2297,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2291,c_935])).

tff(c_2312,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2297])).

tff(c_50,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_934,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_909,c_50])).

tff(c_2319,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2312,c_934])).

tff(c_111,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_54,c_8])).

tff(c_938,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_909,c_111])).

tff(c_5047,plain,(
    ! [C_399,D_400,A_401] :
      ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),C_399,D_400,'#skF_4','#skF_4')
      | ~ v1_funct_2(A_401,C_399,D_400)
      | ~ v1_funct_1(A_401)
      | v1_xboole_0(D_400)
      | ~ r1_tarski(A_401,k2_zfmisc_1(C_399,D_400)) ) ),
    inference(splitRight,[status(thm)],[c_2855])).

tff(c_5049,plain,
    ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_938,c_5047])).

tff(c_5055,plain,
    ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_940,c_5049])).

tff(c_5057,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5046,c_2319,c_5055])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:57:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.19/2.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.19/2.29  
% 6.19/2.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.19/2.30  %$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.19/2.30  
% 6.19/2.30  %Foreground sorts:
% 6.19/2.30  
% 6.19/2.30  
% 6.19/2.30  %Background operators:
% 6.19/2.30  
% 6.19/2.30  
% 6.19/2.30  %Foreground operators:
% 6.19/2.30  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.19/2.30  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 6.19/2.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.19/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.19/2.30  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 6.19/2.30  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.19/2.30  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.19/2.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.19/2.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.19/2.30  tff('#skF_2', type, '#skF_2': $i).
% 6.19/2.30  tff('#skF_3', type, '#skF_3': $i).
% 6.19/2.30  tff('#skF_1', type, '#skF_1': $i).
% 6.19/2.30  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 6.19/2.30  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.19/2.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.19/2.30  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.19/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.19/2.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.19/2.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.19/2.30  tff('#skF_4', type, '#skF_4': $i).
% 6.19/2.30  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 6.19/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.19/2.30  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.19/2.30  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 6.19/2.30  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.19/2.30  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.19/2.30  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 6.19/2.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.19/2.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.19/2.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.19/2.30  
% 6.57/2.32  tff(f_212, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_tmap_1)).
% 6.57/2.32  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.57/2.32  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 6.57/2.32  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.57/2.32  tff(f_179, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 6.57/2.32  tff(f_140, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tmap_1)).
% 6.57/2.32  tff(f_84, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_pre_topc)).
% 6.57/2.32  tff(f_158, axiom, (![A]: (l1_pre_topc(A) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((B = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) => (m1_pre_topc(B, A) <=> m1_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tmap_1)).
% 6.57/2.32  tff(f_165, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 6.57/2.32  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.57/2.32  tff(f_104, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => r1_funct_2(A, B, C, D, E, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r1_funct_2)).
% 6.57/2.32  tff(f_76, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 6.57/2.32  tff(f_57, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 6.57/2.32  tff(f_131, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 6.57/2.32  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.57/2.32  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.57/2.32  tff(f_41, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 6.57/2.32  tff(c_70, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_212])).
% 6.57/2.32  tff(c_22, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.57/2.32  tff(c_74, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_212])).
% 6.57/2.32  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_212])).
% 6.57/2.32  tff(c_64, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_212])).
% 6.57/2.32  tff(c_60, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_212])).
% 6.57/2.32  tff(c_85, plain, (![B_82, A_83]: (l1_pre_topc(B_82) | ~m1_pre_topc(B_82, A_83) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.57/2.32  tff(c_88, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_85])).
% 6.57/2.32  tff(c_91, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_88])).
% 6.57/2.32  tff(c_66, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_212])).
% 6.57/2.32  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.57/2.32  tff(c_791, plain, (![B_184, C_185, A_186]: (m1_pre_topc(B_184, C_185) | ~r1_tarski(u1_struct_0(B_184), u1_struct_0(C_185)) | ~m1_pre_topc(C_185, A_186) | ~m1_pre_topc(B_184, A_186) | ~l1_pre_topc(A_186) | ~v2_pre_topc(A_186))), inference(cnfTransformation, [status(thm)], [f_179])).
% 6.57/2.32  tff(c_818, plain, (![B_189, A_190]: (m1_pre_topc(B_189, B_189) | ~m1_pre_topc(B_189, A_190) | ~l1_pre_topc(A_190) | ~v2_pre_topc(A_190))), inference(resolution, [status(thm)], [c_6, c_791])).
% 6.57/2.32  tff(c_824, plain, (m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_818])).
% 6.57/2.32  tff(c_829, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_824])).
% 6.57/2.32  tff(c_36, plain, (![B_46, A_44]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_46), u1_pre_topc(B_46)), A_44) | ~m1_pre_topc(B_46, A_44) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.57/2.32  tff(c_52, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_212])).
% 6.57/2.32  tff(c_193, plain, (![A_112]: (v2_pre_topc(g1_pre_topc(u1_struct_0(A_112), u1_pre_topc(A_112))) | ~l1_pre_topc(A_112) | ~v2_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.57/2.32  tff(c_196, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_52, c_193])).
% 6.57/2.32  tff(c_198, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_196])).
% 6.57/2.32  tff(c_229, plain, (![B_122, A_123]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_122), u1_pre_topc(B_122)), A_123) | ~m1_pre_topc(B_122, A_123) | ~l1_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.57/2.32  tff(c_24, plain, (![B_20, A_18]: (l1_pre_topc(B_20) | ~m1_pre_topc(B_20, A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.57/2.32  tff(c_259, plain, (![B_129, A_130]: (l1_pre_topc(g1_pre_topc(u1_struct_0(B_129), u1_pre_topc(B_129))) | ~m1_pre_topc(B_129, A_130) | ~l1_pre_topc(A_130))), inference(resolution, [status(thm)], [c_229, c_24])).
% 6.57/2.32  tff(c_263, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_259])).
% 6.57/2.32  tff(c_267, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_263])).
% 6.57/2.32  tff(c_802, plain, (![C_187, A_188]: (m1_pre_topc(C_187, A_188) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_187), u1_pre_topc(C_187)), A_188) | ~l1_pre_topc(C_187) | ~v2_pre_topc(C_187) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_187), u1_pre_topc(C_187))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_187), u1_pre_topc(C_187))) | ~l1_pre_topc(A_188))), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.57/2.32  tff(c_811, plain, (![A_188]: (m1_pre_topc('#skF_2', A_188) | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), A_188) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_188))), inference(superposition, [status(thm), theory('equality')], [c_52, c_802])).
% 6.57/2.32  tff(c_874, plain, (![A_191]: (m1_pre_topc('#skF_2', A_191) | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), A_191) | ~l1_pre_topc(A_191))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_52, c_267, c_52, c_66, c_64, c_811])).
% 6.57/2.32  tff(c_884, plain, (![A_192]: (m1_pre_topc('#skF_2', A_192) | ~m1_pre_topc('#skF_3', A_192) | ~l1_pre_topc(A_192))), inference(resolution, [status(thm)], [c_36, c_874])).
% 6.57/2.32  tff(c_220, plain, (![B_118, A_119]: (m1_subset_1(u1_struct_0(B_118), k1_zfmisc_1(u1_struct_0(A_119))) | ~m1_pre_topc(B_118, A_119) | ~l1_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.57/2.32  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.57/2.32  tff(c_224, plain, (![B_118, A_119]: (r1_tarski(u1_struct_0(B_118), u1_struct_0(A_119)) | ~m1_pre_topc(B_118, A_119) | ~l1_pre_topc(A_119))), inference(resolution, [status(thm)], [c_220, c_8])).
% 6.57/2.32  tff(c_225, plain, (![B_120, A_121]: (r1_tarski(u1_struct_0(B_120), u1_struct_0(A_121)) | ~m1_pre_topc(B_120, A_121) | ~l1_pre_topc(A_121))), inference(resolution, [status(thm)], [c_220, c_8])).
% 6.57/2.32  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.57/2.32  tff(c_281, plain, (![B_132, A_133]: (u1_struct_0(B_132)=u1_struct_0(A_133) | ~r1_tarski(u1_struct_0(A_133), u1_struct_0(B_132)) | ~m1_pre_topc(B_132, A_133) | ~l1_pre_topc(A_133))), inference(resolution, [status(thm)], [c_225, c_2])).
% 6.57/2.32  tff(c_292, plain, (![B_134, A_135]: (u1_struct_0(B_134)=u1_struct_0(A_135) | ~m1_pre_topc(A_135, B_134) | ~l1_pre_topc(B_134) | ~m1_pre_topc(B_134, A_135) | ~l1_pre_topc(A_135))), inference(resolution, [status(thm)], [c_224, c_281])).
% 6.57/2.32  tff(c_298, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_60, c_292])).
% 6.57/2.32  tff(c_305, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_64, c_298])).
% 6.57/2.32  tff(c_306, plain, (~m1_pre_topc('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_305])).
% 6.57/2.32  tff(c_891, plain, (~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_884, c_306])).
% 6.57/2.32  tff(c_908, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_829, c_891])).
% 6.57/2.32  tff(c_909, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_305])).
% 6.57/2.32  tff(c_56, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_212])).
% 6.57/2.32  tff(c_940, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_909, c_56])).
% 6.57/2.32  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_212])).
% 6.57/2.32  tff(c_939, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_909, c_54])).
% 6.57/2.32  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.57/2.32  tff(c_1914, plain, (![A_274, D_273, C_269, E_271, F_270, B_272]: (r1_funct_2(A_274, B_272, C_269, D_273, E_271, E_271) | ~m1_subset_1(F_270, k1_zfmisc_1(k2_zfmisc_1(C_269, D_273))) | ~v1_funct_2(F_270, C_269, D_273) | ~v1_funct_1(F_270) | ~m1_subset_1(E_271, k1_zfmisc_1(k2_zfmisc_1(A_274, B_272))) | ~v1_funct_2(E_271, A_274, B_272) | ~v1_funct_1(E_271) | v1_xboole_0(D_273) | v1_xboole_0(B_272))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.57/2.32  tff(c_2847, plain, (![E_320, A_319, D_322, C_324, B_321, A_323]: (r1_funct_2(A_319, B_321, C_324, D_322, E_320, E_320) | ~v1_funct_2(A_323, C_324, D_322) | ~v1_funct_1(A_323) | ~m1_subset_1(E_320, k1_zfmisc_1(k2_zfmisc_1(A_319, B_321))) | ~v1_funct_2(E_320, A_319, B_321) | ~v1_funct_1(E_320) | v1_xboole_0(D_322) | v1_xboole_0(B_321) | ~r1_tarski(A_323, k2_zfmisc_1(C_324, D_322)))), inference(resolution, [status(thm)], [c_10, c_1914])).
% 6.57/2.32  tff(c_2849, plain, (![C_324, D_322, A_323]: (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), C_324, D_322, '#skF_4', '#skF_4') | ~v1_funct_2(A_323, C_324, D_322) | ~v1_funct_1(A_323) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(D_322) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski(A_323, k2_zfmisc_1(C_324, D_322)))), inference(resolution, [status(thm)], [c_939, c_2847])).
% 6.57/2.32  tff(c_2855, plain, (![C_324, D_322, A_323]: (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), C_324, D_322, '#skF_4', '#skF_4') | ~v1_funct_2(A_323, C_324, D_322) | ~v1_funct_1(A_323) | v1_xboole_0(D_322) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski(A_323, k2_zfmisc_1(C_324, D_322)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_940, c_2849])).
% 6.57/2.32  tff(c_5031, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_2855])).
% 6.57/2.32  tff(c_26, plain, (![A_21]: (~v1_xboole_0(u1_struct_0(A_21)) | ~l1_struct_0(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.57/2.32  tff(c_5034, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_5031, c_26])).
% 6.57/2.32  tff(c_5037, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_74, c_5034])).
% 6.57/2.32  tff(c_5040, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_5037])).
% 6.57/2.32  tff(c_5044, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_5040])).
% 6.57/2.32  tff(c_5046, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_2855])).
% 6.57/2.32  tff(c_72, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_212])).
% 6.57/2.32  tff(c_240, plain, (![A_124, B_125, C_126, D_127]: (k2_partfun1(A_124, B_125, C_126, D_127)=k7_relat_1(C_126, D_127) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))) | ~v1_funct_1(C_126))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.57/2.32  tff(c_242, plain, (![D_127]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_127)=k7_relat_1('#skF_4', D_127) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_240])).
% 6.57/2.32  tff(c_248, plain, (![D_127]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_127)=k7_relat_1('#skF_4', D_127))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_242])).
% 6.57/2.32  tff(c_933, plain, (![D_127]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', D_127)=k7_relat_1('#skF_4', D_127))), inference(demodulation, [status(thm), theory('equality')], [c_909, c_248])).
% 6.57/2.32  tff(c_68, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_212])).
% 6.57/2.32  tff(c_2182, plain, (![A_279, B_280, C_281, D_282]: (k2_partfun1(u1_struct_0(A_279), u1_struct_0(B_280), C_281, u1_struct_0(D_282))=k2_tmap_1(A_279, B_280, C_281, D_282) | ~m1_pre_topc(D_282, A_279) | ~m1_subset_1(C_281, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_279), u1_struct_0(B_280)))) | ~v1_funct_2(C_281, u1_struct_0(A_279), u1_struct_0(B_280)) | ~v1_funct_1(C_281) | ~l1_pre_topc(B_280) | ~v2_pre_topc(B_280) | v2_struct_0(B_280) | ~l1_pre_topc(A_279) | ~v2_pre_topc(A_279) | v2_struct_0(A_279))), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.57/2.32  tff(c_2190, plain, (![B_280, C_281, D_282]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_280), C_281, u1_struct_0(D_282))=k2_tmap_1('#skF_2', B_280, C_281, D_282) | ~m1_pre_topc(D_282, '#skF_2') | ~m1_subset_1(C_281, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_280)))) | ~v1_funct_2(C_281, u1_struct_0('#skF_2'), u1_struct_0(B_280)) | ~v1_funct_1(C_281) | ~l1_pre_topc(B_280) | ~v2_pre_topc(B_280) | v2_struct_0(B_280) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_909, c_2182])).
% 6.57/2.32  tff(c_2205, plain, (![B_280, C_281, D_282]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_280), C_281, u1_struct_0(D_282))=k2_tmap_1('#skF_2', B_280, C_281, D_282) | ~m1_pre_topc(D_282, '#skF_2') | ~m1_subset_1(C_281, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_280)))) | ~v1_funct_2(C_281, u1_struct_0('#skF_3'), u1_struct_0(B_280)) | ~v1_funct_1(C_281) | ~l1_pre_topc(B_280) | ~v2_pre_topc(B_280) | v2_struct_0(B_280) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_909, c_909, c_2190])).
% 6.57/2.32  tff(c_2241, plain, (![B_284, C_285, D_286]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_284), C_285, u1_struct_0(D_286))=k2_tmap_1('#skF_2', B_284, C_285, D_286) | ~m1_pre_topc(D_286, '#skF_2') | ~m1_subset_1(C_285, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_284)))) | ~v1_funct_2(C_285, u1_struct_0('#skF_3'), u1_struct_0(B_284)) | ~v1_funct_1(C_285) | ~l1_pre_topc(B_284) | ~v2_pre_topc(B_284) | v2_struct_0(B_284))), inference(negUnitSimplification, [status(thm)], [c_68, c_2205])).
% 6.57/2.32  tff(c_2245, plain, (![D_286]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_286))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_286) | ~m1_pre_topc(D_286, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_939, c_2241])).
% 6.57/2.32  tff(c_2255, plain, (![D_286]: (k7_relat_1('#skF_4', u1_struct_0(D_286))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_286) | ~m1_pre_topc(D_286, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_58, c_940, c_933, c_2245])).
% 6.57/2.32  tff(c_2291, plain, (![D_288]: (k7_relat_1('#skF_4', u1_struct_0(D_288))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_288) | ~m1_pre_topc(D_288, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_74, c_2255])).
% 6.57/2.32  tff(c_14, plain, (![C_9, A_7, B_8]: (v1_relat_1(C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.57/2.32  tff(c_110, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_14])).
% 6.57/2.32  tff(c_138, plain, (![C_97, A_98, B_99]: (v4_relat_1(C_97, A_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.57/2.32  tff(c_146, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_138])).
% 6.57/2.32  tff(c_176, plain, (![B_110, A_111]: (k7_relat_1(B_110, A_111)=B_110 | ~v4_relat_1(B_110, A_111) | ~v1_relat_1(B_110))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.57/2.32  tff(c_182, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_146, c_176])).
% 6.57/2.32  tff(c_188, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_182])).
% 6.57/2.32  tff(c_935, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_909, c_188])).
% 6.57/2.32  tff(c_2297, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2291, c_935])).
% 6.57/2.32  tff(c_2312, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2297])).
% 6.57/2.32  tff(c_50, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_212])).
% 6.57/2.32  tff(c_934, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_909, c_50])).
% 6.57/2.32  tff(c_2319, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2312, c_934])).
% 6.57/2.32  tff(c_111, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_54, c_8])).
% 6.57/2.32  tff(c_938, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_909, c_111])).
% 6.57/2.32  tff(c_5047, plain, (![C_399, D_400, A_401]: (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), C_399, D_400, '#skF_4', '#skF_4') | ~v1_funct_2(A_401, C_399, D_400) | ~v1_funct_1(A_401) | v1_xboole_0(D_400) | ~r1_tarski(A_401, k2_zfmisc_1(C_399, D_400)))), inference(splitRight, [status(thm)], [c_2855])).
% 6.57/2.32  tff(c_5049, plain, (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_938, c_5047])).
% 6.57/2.32  tff(c_5055, plain, (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_940, c_5049])).
% 6.57/2.32  tff(c_5057, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5046, c_2319, c_5055])).
% 6.57/2.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.57/2.32  
% 6.57/2.32  Inference rules
% 6.57/2.32  ----------------------
% 6.57/2.32  #Ref     : 0
% 6.57/2.32  #Sup     : 991
% 6.57/2.32  #Fact    : 0
% 6.57/2.32  #Define  : 0
% 6.57/2.32  #Split   : 16
% 6.57/2.32  #Chain   : 0
% 6.57/2.32  #Close   : 0
% 6.57/2.32  
% 6.57/2.32  Ordering : KBO
% 6.57/2.32  
% 6.57/2.32  Simplification rules
% 6.57/2.32  ----------------------
% 6.57/2.32  #Subsume      : 197
% 6.57/2.32  #Demod        : 1965
% 6.57/2.32  #Tautology    : 411
% 6.57/2.32  #SimpNegUnit  : 33
% 6.57/2.32  #BackRed      : 15
% 6.57/2.32  
% 6.57/2.32  #Partial instantiations: 0
% 6.57/2.32  #Strategies tried      : 1
% 6.57/2.32  
% 6.57/2.32  Timing (in seconds)
% 6.57/2.32  ----------------------
% 6.57/2.32  Preprocessing        : 0.41
% 6.57/2.32  Parsing              : 0.21
% 6.57/2.32  CNF conversion       : 0.03
% 6.57/2.32  Main loop            : 1.11
% 6.57/2.32  Inferencing          : 0.36
% 6.57/2.32  Reduction            : 0.42
% 6.57/2.32  Demodulation         : 0.31
% 6.57/2.32  BG Simplification    : 0.04
% 6.57/2.32  Subsumption          : 0.22
% 6.57/2.32  Abstraction          : 0.05
% 6.57/2.32  MUC search           : 0.00
% 6.57/2.32  Cooper               : 0.00
% 6.57/2.32  Total                : 1.57
% 6.57/2.32  Index Insertion      : 0.00
% 6.57/2.32  Index Deletion       : 0.00
% 6.57/2.32  Index Matching       : 0.00
% 6.57/2.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
