%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:53 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :  160 (1015 expanded)
%              Number of leaves         :   47 ( 346 expanded)
%              Depth                    :   19
%              Number of atoms          :  344 (3689 expanded)
%              Number of equality atoms :   58 ( 565 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(f_194,negated_conjecture,(
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

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_105,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_127,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

tff(f_161,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_154,axiom,(
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

tff(c_64,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_24,plain,(
    ! [A_21] :
      ( l1_struct_0(A_21)
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_58,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_54,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_77,plain,(
    ! [B_74,A_75] :
      ( l1_pre_topc(B_74)
      | ~ m1_pre_topc(B_74,A_75)
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_80,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_77])).

tff(c_83,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_80])).

tff(c_140,plain,(
    ! [A_94] :
      ( m1_subset_1(u1_pre_topc(A_94),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_94))))
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_144,plain,(
    ! [A_94] :
      ( r1_tarski(u1_pre_topc(A_94),k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(resolution,[status(thm)],[c_140,c_2])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_46,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_166,plain,(
    ! [D_105,B_106,C_107,A_108] :
      ( D_105 = B_106
      | g1_pre_topc(C_107,D_105) != g1_pre_topc(A_108,B_106)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(k1_zfmisc_1(A_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_171,plain,(
    ! [B_109,A_110] :
      ( u1_pre_topc('#skF_2') = B_109
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(A_110,B_109)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(k1_zfmisc_1(A_110))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_166])).

tff(c_180,plain,(
    ! [A_1,A_110] :
      ( u1_pre_topc('#skF_2') = A_1
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(A_110,A_1)
      | ~ r1_tarski(A_1,k1_zfmisc_1(A_110)) ) ),
    inference(resolution,[status(thm)],[c_4,c_171])).

tff(c_192,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3')
    | ~ r1_tarski(u1_pre_topc('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_180])).

tff(c_198,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_192])).

tff(c_201,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_144,c_198])).

tff(c_205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_201])).

tff(c_206,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_28,plain,(
    ! [A_25] :
      ( m1_subset_1(u1_pre_topc(A_25),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_25))))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_217,plain,
    ( m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_28])).

tff(c_223,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_217])).

tff(c_210,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_3')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_46])).

tff(c_34,plain,(
    ! [C_31,A_27,D_32,B_28] :
      ( C_31 = A_27
      | g1_pre_topc(C_31,D_32) != g1_pre_topc(A_27,B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(k1_zfmisc_1(A_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_244,plain,(
    ! [C_31,D_32] :
      ( u1_struct_0('#skF_2') = C_31
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_31,D_32)
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_34])).

tff(c_252,plain,(
    ! [C_31,D_32] :
      ( u1_struct_0('#skF_2') = C_31
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_31,D_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_244])).

tff(c_267,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_252])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_88,plain,(
    ! [C_76,A_77,B_78] :
      ( v1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_96,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_88])).

tff(c_108,plain,(
    ! [C_82,A_83,B_84] :
      ( v4_relat_1(C_82,A_83)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_116,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_108])).

tff(c_148,plain,(
    ! [B_99,A_100] :
      ( k1_relat_1(B_99) = A_100
      | ~ v1_partfun1(B_99,A_100)
      | ~ v4_relat_1(B_99,A_100)
      | ~ v1_relat_1(B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_151,plain,
    ( u1_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_116,c_148])).

tff(c_154,plain,
    ( u1_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_151])).

tff(c_155,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_279,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_155])).

tff(c_50,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_284,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_50])).

tff(c_283,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_48])).

tff(c_14,plain,(
    ! [C_14,A_11,B_12] :
      ( v1_partfun1(C_14,A_11)
      | ~ v1_funct_2(C_14,A_11,B_12)
      | ~ v1_funct_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12)))
      | v1_xboole_0(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_365,plain,
    ( v1_partfun1('#skF_4',u1_struct_0('#skF_3'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_283,c_14])).

tff(c_382,plain,
    ( v1_partfun1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_284,c_365])).

tff(c_383,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_279,c_382])).

tff(c_30,plain,(
    ! [A_26] :
      ( ~ v1_xboole_0(u1_struct_0(A_26))
      | ~ l1_struct_0(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_407,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_383,c_30])).

tff(c_410,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_407])).

tff(c_413,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_410])).

tff(c_417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_413])).

tff(c_418,plain,(
    u1_struct_0('#skF_2') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_425,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_50])).

tff(c_424,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_48])).

tff(c_810,plain,(
    ! [F_173,A_171,B_175,C_172,D_174] :
      ( r1_funct_2(A_171,B_175,C_172,D_174,F_173,F_173)
      | ~ m1_subset_1(F_173,k1_zfmisc_1(k2_zfmisc_1(C_172,D_174)))
      | ~ v1_funct_2(F_173,C_172,D_174)
      | ~ m1_subset_1(F_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_175)))
      | ~ v1_funct_2(F_173,A_171,B_175)
      | ~ v1_funct_1(F_173)
      | v1_xboole_0(D_174)
      | v1_xboole_0(B_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_812,plain,(
    ! [A_171,B_175] :
      ( r1_funct_2(A_171,B_175,k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_171,B_175)))
      | ~ v1_funct_2('#skF_4',A_171,B_175)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_175) ) ),
    inference(resolution,[status(thm)],[c_424,c_810])).

tff(c_818,plain,(
    ! [A_171,B_175] :
      ( r1_funct_2(A_171,B_175,k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_171,B_175)))
      | ~ v1_funct_2('#skF_4',A_171,B_175)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_175) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_425,c_812])).

tff(c_960,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_818])).

tff(c_963,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_960,c_30])).

tff(c_966,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_963])).

tff(c_994,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_966])).

tff(c_998,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_994])).

tff(c_1000,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_818])).

tff(c_87,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_48,c_2])).

tff(c_423,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_87])).

tff(c_1034,plain,(
    ! [A_207,B_208,A_206,D_204,C_205] :
      ( r1_funct_2(A_207,B_208,C_205,D_204,A_206,A_206)
      | ~ v1_funct_2(A_206,C_205,D_204)
      | ~ m1_subset_1(A_206,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208)))
      | ~ v1_funct_2(A_206,A_207,B_208)
      | ~ v1_funct_1(A_206)
      | v1_xboole_0(D_204)
      | v1_xboole_0(B_208)
      | ~ r1_tarski(A_206,k2_zfmisc_1(C_205,D_204)) ) ),
    inference(resolution,[status(thm)],[c_4,c_810])).

tff(c_1053,plain,(
    ! [B_212,C_211,A_213,D_214,A_215] :
      ( r1_funct_2(A_213,B_212,C_211,D_214,A_215,A_215)
      | ~ v1_funct_2(A_215,C_211,D_214)
      | ~ v1_funct_2(A_215,A_213,B_212)
      | ~ v1_funct_1(A_215)
      | v1_xboole_0(D_214)
      | v1_xboole_0(B_212)
      | ~ r1_tarski(A_215,k2_zfmisc_1(C_211,D_214))
      | ~ r1_tarski(A_215,k2_zfmisc_1(A_213,B_212)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1034])).

tff(c_1055,plain,(
    ! [A_213,B_212] :
      ( r1_funct_2(A_213,B_212,k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_2('#skF_4',A_213,B_212)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_212)
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(A_213,B_212)) ) ),
    inference(resolution,[status(thm)],[c_423,c_1053])).

tff(c_1058,plain,(
    ! [A_213,B_212] :
      ( r1_funct_2(A_213,B_212,k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',A_213,B_212)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_212)
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(A_213,B_212)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_425,c_1055])).

tff(c_1059,plain,(
    ! [A_213,B_212] :
      ( r1_funct_2(A_213,B_212,k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',A_213,B_212)
      | v1_xboole_0(B_212)
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(A_213,B_212)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1000,c_1058])).

tff(c_432,plain,
    ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_4'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_28])).

tff(c_441,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_432])).

tff(c_422,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_46])).

tff(c_32,plain,(
    ! [D_32,B_28,C_31,A_27] :
      ( D_32 = B_28
      | g1_pre_topc(C_31,D_32) != g1_pre_topc(A_27,B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(k1_zfmisc_1(A_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_627,plain,(
    ! [B_158,A_159] :
      ( u1_pre_topc('#skF_3') = B_158
      | g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')) != g1_pre_topc(A_159,B_158)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(k1_zfmisc_1(A_159))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_32])).

tff(c_638,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_441,c_627])).

tff(c_643,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_638,c_441])).

tff(c_597,plain,(
    ! [C_145,A_146,D_147,B_148] :
      ( C_145 = A_146
      | g1_pre_topc(C_145,D_147) != g1_pre_topc(A_146,B_148)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(k1_zfmisc_1(A_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_599,plain,(
    ! [A_146,B_148] :
      ( u1_struct_0('#skF_3') = A_146
      | g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')) != g1_pre_topc(A_146,B_148)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(k1_zfmisc_1(A_146))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_597])).

tff(c_710,plain,(
    ! [A_168,B_169] :
      ( u1_struct_0('#skF_3') = A_168
      | g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_3')) != g1_pre_topc(A_168,B_169)
      | ~ m1_subset_1(B_169,k1_zfmisc_1(k1_zfmisc_1(A_168))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_638,c_599])).

tff(c_721,plain,(
    u1_struct_0('#skF_3') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_643,c_710])).

tff(c_468,plain,(
    ! [B_132,A_133] :
      ( m1_subset_1(u1_struct_0(B_132),k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ m1_pre_topc(B_132,A_133)
      | ~ l1_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_477,plain,(
    ! [B_132] :
      ( m1_subset_1(u1_struct_0(B_132),k1_zfmisc_1(k1_relat_1('#skF_4')))
      | ~ m1_pre_topc(B_132,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_468])).

tff(c_522,plain,(
    ! [B_134] :
      ( m1_subset_1(u1_struct_0(B_134),k1_zfmisc_1(k1_relat_1('#skF_4')))
      | ~ m1_pre_topc(B_134,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_477])).

tff(c_529,plain,(
    ! [B_134] :
      ( r1_tarski(u1_struct_0(B_134),k1_relat_1('#skF_4'))
      | ~ m1_pre_topc(B_134,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_522,c_2])).

tff(c_745,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_721,c_529])).

tff(c_775,plain,(
    r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_745])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k7_relat_1(B_4,A_3) = B_4
      | ~ r1_tarski(k1_relat_1(B_4),A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_788,plain,
    ( k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_775,c_6])).

tff(c_791,plain,(
    k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_788])).

tff(c_66,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_602,plain,(
    ! [A_149,B_150,C_151,D_152] :
      ( k2_partfun1(A_149,B_150,C_151,D_152) = k7_relat_1(C_151,D_152)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150)))
      | ~ v1_funct_1(C_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_604,plain,(
    ! [D_152] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',D_152) = k7_relat_1('#skF_4',D_152)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_424,c_602])).

tff(c_610,plain,(
    ! [D_152] : k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',D_152) = k7_relat_1('#skF_4',D_152) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_604])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_60,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_1009,plain,(
    ! [A_200,B_201,C_202,D_203] :
      ( k2_partfun1(u1_struct_0(A_200),u1_struct_0(B_201),C_202,u1_struct_0(D_203)) = k2_tmap_1(A_200,B_201,C_202,D_203)
      | ~ m1_pre_topc(D_203,A_200)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_200),u1_struct_0(B_201))))
      | ~ v1_funct_2(C_202,u1_struct_0(A_200),u1_struct_0(B_201))
      | ~ v1_funct_1(C_202)
      | ~ l1_pre_topc(B_201)
      | ~ v2_pre_topc(B_201)
      | v2_struct_0(B_201)
      | ~ l1_pre_topc(A_200)
      | ~ v2_pre_topc(A_200)
      | v2_struct_0(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1015,plain,(
    ! [B_201,C_202,D_203] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_201),C_202,u1_struct_0(D_203)) = k2_tmap_1('#skF_2',B_201,C_202,D_203)
      | ~ m1_pre_topc(D_203,'#skF_2')
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_201))))
      | ~ v1_funct_2(C_202,u1_struct_0('#skF_2'),u1_struct_0(B_201))
      | ~ v1_funct_1(C_202)
      | ~ l1_pre_topc(B_201)
      | ~ v2_pre_topc(B_201)
      | v2_struct_0(B_201)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_1009])).

tff(c_1028,plain,(
    ! [B_201,C_202,D_203] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0(B_201),C_202,u1_struct_0(D_203)) = k2_tmap_1('#skF_2',B_201,C_202,D_203)
      | ~ m1_pre_topc(D_203,'#skF_2')
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_201))))
      | ~ v1_funct_2(C_202,k1_relat_1('#skF_4'),u1_struct_0(B_201))
      | ~ v1_funct_1(C_202)
      | ~ l1_pre_topc(B_201)
      | ~ v2_pre_topc(B_201)
      | v2_struct_0(B_201)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_418,c_418,c_1015])).

tff(c_1068,plain,(
    ! [B_218,C_219,D_220] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0(B_218),C_219,u1_struct_0(D_220)) = k2_tmap_1('#skF_2',B_218,C_219,D_220)
      | ~ m1_pre_topc(D_220,'#skF_2')
      | ~ m1_subset_1(C_219,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_218))))
      | ~ v1_funct_2(C_219,k1_relat_1('#skF_4'),u1_struct_0(B_218))
      | ~ v1_funct_1(C_219)
      | ~ l1_pre_topc(B_218)
      | ~ v2_pre_topc(B_218)
      | v2_struct_0(B_218) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1028])).

tff(c_1072,plain,(
    ! [D_220] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_220)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_220)
      | ~ m1_pre_topc(D_220,'#skF_2')
      | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_424,c_1068])).

tff(c_1083,plain,(
    ! [D_220] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_220)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_220)
      | ~ m1_pre_topc(D_220,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_52,c_425,c_610,c_1072])).

tff(c_1110,plain,(
    ! [D_225] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_225)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_225)
      | ~ m1_pre_topc(D_225,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1083])).

tff(c_1128,plain,
    ( k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_721,c_1110])).

tff(c_1138,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_791,c_1128])).

tff(c_44,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_420,plain,(
    ~ r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_44])).

tff(c_726,plain,(
    ~ r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_721,c_420])).

tff(c_1140,plain,(
    ~ r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1138,c_726])).

tff(c_1147,plain,
    ( ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1059,c_1140])).

tff(c_1156,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_425,c_1147])).

tff(c_1158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1000,c_1156])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 14:46:32 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.55  
% 3.44/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.55  %$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.44/1.55  
% 3.44/1.55  %Foreground sorts:
% 3.44/1.55  
% 3.44/1.55  
% 3.44/1.55  %Background operators:
% 3.44/1.55  
% 3.44/1.55  
% 3.44/1.55  %Foreground operators:
% 3.44/1.55  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.44/1.55  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.44/1.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.44/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.55  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.44/1.55  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.44/1.55  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.44/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.44/1.55  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.44/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.44/1.55  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.44/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.44/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.44/1.55  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.44/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.44/1.55  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.44/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.44/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.44/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.44/1.55  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 3.44/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.55  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.44/1.55  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.44/1.55  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.44/1.55  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.44/1.55  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.44/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.44/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.44/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.44/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.44/1.55  
% 3.44/1.58  tff(f_194, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_tmap_1)).
% 3.44/1.58  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.44/1.58  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.44/1.58  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 3.44/1.58  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.44/1.58  tff(f_105, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 3.44/1.58  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.44/1.58  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.44/1.58  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 3.44/1.58  tff(f_59, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.44/1.58  tff(f_96, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.44/1.58  tff(f_127, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 3.44/1.58  tff(f_161, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.44/1.58  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 3.44/1.58  tff(f_73, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.44/1.58  tff(f_154, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.44/1.58  tff(c_64, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.44/1.58  tff(c_24, plain, (![A_21]: (l1_struct_0(A_21) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.44/1.58  tff(c_68, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.44/1.58  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.44/1.58  tff(c_58, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.44/1.58  tff(c_54, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.44/1.58  tff(c_77, plain, (![B_74, A_75]: (l1_pre_topc(B_74) | ~m1_pre_topc(B_74, A_75) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.44/1.58  tff(c_80, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_77])).
% 3.44/1.58  tff(c_83, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_80])).
% 3.44/1.58  tff(c_140, plain, (![A_94]: (m1_subset_1(u1_pre_topc(A_94), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_94)))) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.44/1.58  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.44/1.58  tff(c_144, plain, (![A_94]: (r1_tarski(u1_pre_topc(A_94), k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94))), inference(resolution, [status(thm)], [c_140, c_2])).
% 3.44/1.58  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.44/1.58  tff(c_46, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.44/1.58  tff(c_166, plain, (![D_105, B_106, C_107, A_108]: (D_105=B_106 | g1_pre_topc(C_107, D_105)!=g1_pre_topc(A_108, B_106) | ~m1_subset_1(B_106, k1_zfmisc_1(k1_zfmisc_1(A_108))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.44/1.58  tff(c_171, plain, (![B_109, A_110]: (u1_pre_topc('#skF_2')=B_109 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(A_110, B_109) | ~m1_subset_1(B_109, k1_zfmisc_1(k1_zfmisc_1(A_110))))), inference(superposition, [status(thm), theory('equality')], [c_46, c_166])).
% 3.44/1.58  tff(c_180, plain, (![A_1, A_110]: (u1_pre_topc('#skF_2')=A_1 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(A_110, A_1) | ~r1_tarski(A_1, k1_zfmisc_1(A_110)))), inference(resolution, [status(thm)], [c_4, c_171])).
% 3.44/1.58  tff(c_192, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3') | ~r1_tarski(u1_pre_topc('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(reflexivity, [status(thm), theory('equality')], [c_180])).
% 3.44/1.58  tff(c_198, plain, (~r1_tarski(u1_pre_topc('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_192])).
% 3.44/1.58  tff(c_201, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_144, c_198])).
% 3.44/1.58  tff(c_205, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_201])).
% 3.44/1.58  tff(c_206, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3')), inference(splitRight, [status(thm)], [c_192])).
% 3.44/1.58  tff(c_28, plain, (![A_25]: (m1_subset_1(u1_pre_topc(A_25), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_25)))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.44/1.58  tff(c_217, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_206, c_28])).
% 3.44/1.58  tff(c_223, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_217])).
% 3.44/1.58  tff(c_210, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_3'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_206, c_46])).
% 3.44/1.58  tff(c_34, plain, (![C_31, A_27, D_32, B_28]: (C_31=A_27 | g1_pre_topc(C_31, D_32)!=g1_pre_topc(A_27, B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(k1_zfmisc_1(A_27))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.44/1.58  tff(c_244, plain, (![C_31, D_32]: (u1_struct_0('#skF_2')=C_31 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_31, D_32) | ~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_210, c_34])).
% 3.44/1.58  tff(c_252, plain, (![C_31, D_32]: (u1_struct_0('#skF_2')=C_31 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_31, D_32))), inference(demodulation, [status(thm), theory('equality')], [c_223, c_244])).
% 3.44/1.58  tff(c_267, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_252])).
% 3.44/1.58  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.44/1.58  tff(c_88, plain, (![C_76, A_77, B_78]: (v1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.44/1.58  tff(c_96, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_88])).
% 3.44/1.58  tff(c_108, plain, (![C_82, A_83, B_84]: (v4_relat_1(C_82, A_83) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.44/1.58  tff(c_116, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_108])).
% 3.44/1.58  tff(c_148, plain, (![B_99, A_100]: (k1_relat_1(B_99)=A_100 | ~v1_partfun1(B_99, A_100) | ~v4_relat_1(B_99, A_100) | ~v1_relat_1(B_99))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.44/1.58  tff(c_151, plain, (u1_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_2')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_116, c_148])).
% 3.44/1.58  tff(c_154, plain, (u1_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_151])).
% 3.44/1.58  tff(c_155, plain, (~v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_154])).
% 3.44/1.58  tff(c_279, plain, (~v1_partfun1('#skF_4', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_267, c_155])).
% 3.44/1.58  tff(c_50, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.44/1.58  tff(c_284, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_267, c_50])).
% 3.44/1.58  tff(c_283, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_267, c_48])).
% 3.44/1.58  tff(c_14, plain, (![C_14, A_11, B_12]: (v1_partfun1(C_14, A_11) | ~v1_funct_2(C_14, A_11, B_12) | ~v1_funct_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))) | v1_xboole_0(B_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.44/1.58  tff(c_365, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_3')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_283, c_14])).
% 3.44/1.58  tff(c_382, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_284, c_365])).
% 3.44/1.58  tff(c_383, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_279, c_382])).
% 3.44/1.58  tff(c_30, plain, (![A_26]: (~v1_xboole_0(u1_struct_0(A_26)) | ~l1_struct_0(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.44/1.58  tff(c_407, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_383, c_30])).
% 3.44/1.58  tff(c_410, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_68, c_407])).
% 3.44/1.58  tff(c_413, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_410])).
% 3.44/1.58  tff(c_417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_413])).
% 3.44/1.58  tff(c_418, plain, (u1_struct_0('#skF_2')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_154])).
% 3.44/1.58  tff(c_425, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_418, c_50])).
% 3.44/1.58  tff(c_424, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_418, c_48])).
% 3.44/1.58  tff(c_810, plain, (![F_173, A_171, B_175, C_172, D_174]: (r1_funct_2(A_171, B_175, C_172, D_174, F_173, F_173) | ~m1_subset_1(F_173, k1_zfmisc_1(k2_zfmisc_1(C_172, D_174))) | ~v1_funct_2(F_173, C_172, D_174) | ~m1_subset_1(F_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_175))) | ~v1_funct_2(F_173, A_171, B_175) | ~v1_funct_1(F_173) | v1_xboole_0(D_174) | v1_xboole_0(B_175))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.44/1.58  tff(c_812, plain, (![A_171, B_175]: (r1_funct_2(A_171, B_175, k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_171, B_175))) | ~v1_funct_2('#skF_4', A_171, B_175) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_175))), inference(resolution, [status(thm)], [c_424, c_810])).
% 3.44/1.58  tff(c_818, plain, (![A_171, B_175]: (r1_funct_2(A_171, B_175, k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_171, B_175))) | ~v1_funct_2('#skF_4', A_171, B_175) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_175))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_425, c_812])).
% 3.44/1.58  tff(c_960, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_818])).
% 3.44/1.58  tff(c_963, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_960, c_30])).
% 3.44/1.58  tff(c_966, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_68, c_963])).
% 3.44/1.58  tff(c_994, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_966])).
% 3.44/1.58  tff(c_998, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_994])).
% 3.44/1.58  tff(c_1000, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_818])).
% 3.44/1.58  tff(c_87, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_48, c_2])).
% 3.44/1.58  tff(c_423, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_418, c_87])).
% 3.44/1.58  tff(c_1034, plain, (![A_207, B_208, A_206, D_204, C_205]: (r1_funct_2(A_207, B_208, C_205, D_204, A_206, A_206) | ~v1_funct_2(A_206, C_205, D_204) | ~m1_subset_1(A_206, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))) | ~v1_funct_2(A_206, A_207, B_208) | ~v1_funct_1(A_206) | v1_xboole_0(D_204) | v1_xboole_0(B_208) | ~r1_tarski(A_206, k2_zfmisc_1(C_205, D_204)))), inference(resolution, [status(thm)], [c_4, c_810])).
% 3.44/1.58  tff(c_1053, plain, (![B_212, C_211, A_213, D_214, A_215]: (r1_funct_2(A_213, B_212, C_211, D_214, A_215, A_215) | ~v1_funct_2(A_215, C_211, D_214) | ~v1_funct_2(A_215, A_213, B_212) | ~v1_funct_1(A_215) | v1_xboole_0(D_214) | v1_xboole_0(B_212) | ~r1_tarski(A_215, k2_zfmisc_1(C_211, D_214)) | ~r1_tarski(A_215, k2_zfmisc_1(A_213, B_212)))), inference(resolution, [status(thm)], [c_4, c_1034])).
% 3.44/1.58  tff(c_1055, plain, (![A_213, B_212]: (r1_funct_2(A_213, B_212, k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_2('#skF_4', A_213, B_212) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_212) | ~r1_tarski('#skF_4', k2_zfmisc_1(A_213, B_212)))), inference(resolution, [status(thm)], [c_423, c_1053])).
% 3.44/1.58  tff(c_1058, plain, (![A_213, B_212]: (r1_funct_2(A_213, B_212, k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', A_213, B_212) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_212) | ~r1_tarski('#skF_4', k2_zfmisc_1(A_213, B_212)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_425, c_1055])).
% 3.44/1.58  tff(c_1059, plain, (![A_213, B_212]: (r1_funct_2(A_213, B_212, k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', A_213, B_212) | v1_xboole_0(B_212) | ~r1_tarski('#skF_4', k2_zfmisc_1(A_213, B_212)))), inference(negUnitSimplification, [status(thm)], [c_1000, c_1058])).
% 3.44/1.58  tff(c_432, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_4')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_418, c_28])).
% 3.44/1.58  tff(c_441, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_432])).
% 3.44/1.58  tff(c_422, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_418, c_46])).
% 3.44/1.58  tff(c_32, plain, (![D_32, B_28, C_31, A_27]: (D_32=B_28 | g1_pre_topc(C_31, D_32)!=g1_pre_topc(A_27, B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(k1_zfmisc_1(A_27))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.44/1.58  tff(c_627, plain, (![B_158, A_159]: (u1_pre_topc('#skF_3')=B_158 | g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))!=g1_pre_topc(A_159, B_158) | ~m1_subset_1(B_158, k1_zfmisc_1(k1_zfmisc_1(A_159))))), inference(superposition, [status(thm), theory('equality')], [c_422, c_32])).
% 3.44/1.58  tff(c_638, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_441, c_627])).
% 3.44/1.58  tff(c_643, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_638, c_441])).
% 3.44/1.58  tff(c_597, plain, (![C_145, A_146, D_147, B_148]: (C_145=A_146 | g1_pre_topc(C_145, D_147)!=g1_pre_topc(A_146, B_148) | ~m1_subset_1(B_148, k1_zfmisc_1(k1_zfmisc_1(A_146))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.44/1.58  tff(c_599, plain, (![A_146, B_148]: (u1_struct_0('#skF_3')=A_146 | g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))!=g1_pre_topc(A_146, B_148) | ~m1_subset_1(B_148, k1_zfmisc_1(k1_zfmisc_1(A_146))))), inference(superposition, [status(thm), theory('equality')], [c_422, c_597])).
% 3.44/1.58  tff(c_710, plain, (![A_168, B_169]: (u1_struct_0('#skF_3')=A_168 | g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_3'))!=g1_pre_topc(A_168, B_169) | ~m1_subset_1(B_169, k1_zfmisc_1(k1_zfmisc_1(A_168))))), inference(demodulation, [status(thm), theory('equality')], [c_638, c_599])).
% 3.44/1.58  tff(c_721, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_643, c_710])).
% 3.44/1.58  tff(c_468, plain, (![B_132, A_133]: (m1_subset_1(u1_struct_0(B_132), k1_zfmisc_1(u1_struct_0(A_133))) | ~m1_pre_topc(B_132, A_133) | ~l1_pre_topc(A_133))), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.44/1.58  tff(c_477, plain, (![B_132]: (m1_subset_1(u1_struct_0(B_132), k1_zfmisc_1(k1_relat_1('#skF_4'))) | ~m1_pre_topc(B_132, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_418, c_468])).
% 3.44/1.58  tff(c_522, plain, (![B_134]: (m1_subset_1(u1_struct_0(B_134), k1_zfmisc_1(k1_relat_1('#skF_4'))) | ~m1_pre_topc(B_134, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_477])).
% 3.44/1.58  tff(c_529, plain, (![B_134]: (r1_tarski(u1_struct_0(B_134), k1_relat_1('#skF_4')) | ~m1_pre_topc(B_134, '#skF_2'))), inference(resolution, [status(thm)], [c_522, c_2])).
% 3.44/1.58  tff(c_745, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_721, c_529])).
% 3.44/1.58  tff(c_775, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_745])).
% 3.44/1.58  tff(c_6, plain, (![B_4, A_3]: (k7_relat_1(B_4, A_3)=B_4 | ~r1_tarski(k1_relat_1(B_4), A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.44/1.58  tff(c_788, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_775, c_6])).
% 3.44/1.58  tff(c_791, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_788])).
% 3.44/1.58  tff(c_66, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.44/1.58  tff(c_602, plain, (![A_149, B_150, C_151, D_152]: (k2_partfun1(A_149, B_150, C_151, D_152)=k7_relat_1(C_151, D_152) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))) | ~v1_funct_1(C_151))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.44/1.58  tff(c_604, plain, (![D_152]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', D_152)=k7_relat_1('#skF_4', D_152) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_424, c_602])).
% 3.44/1.58  tff(c_610, plain, (![D_152]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', D_152)=k7_relat_1('#skF_4', D_152))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_604])).
% 3.44/1.58  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.44/1.58  tff(c_60, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.44/1.58  tff(c_1009, plain, (![A_200, B_201, C_202, D_203]: (k2_partfun1(u1_struct_0(A_200), u1_struct_0(B_201), C_202, u1_struct_0(D_203))=k2_tmap_1(A_200, B_201, C_202, D_203) | ~m1_pre_topc(D_203, A_200) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_200), u1_struct_0(B_201)))) | ~v1_funct_2(C_202, u1_struct_0(A_200), u1_struct_0(B_201)) | ~v1_funct_1(C_202) | ~l1_pre_topc(B_201) | ~v2_pre_topc(B_201) | v2_struct_0(B_201) | ~l1_pre_topc(A_200) | ~v2_pre_topc(A_200) | v2_struct_0(A_200))), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.44/1.58  tff(c_1015, plain, (![B_201, C_202, D_203]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_201), C_202, u1_struct_0(D_203))=k2_tmap_1('#skF_2', B_201, C_202, D_203) | ~m1_pre_topc(D_203, '#skF_2') | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_201)))) | ~v1_funct_2(C_202, u1_struct_0('#skF_2'), u1_struct_0(B_201)) | ~v1_funct_1(C_202) | ~l1_pre_topc(B_201) | ~v2_pre_topc(B_201) | v2_struct_0(B_201) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_418, c_1009])).
% 3.44/1.58  tff(c_1028, plain, (![B_201, C_202, D_203]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0(B_201), C_202, u1_struct_0(D_203))=k2_tmap_1('#skF_2', B_201, C_202, D_203) | ~m1_pre_topc(D_203, '#skF_2') | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_201)))) | ~v1_funct_2(C_202, k1_relat_1('#skF_4'), u1_struct_0(B_201)) | ~v1_funct_1(C_202) | ~l1_pre_topc(B_201) | ~v2_pre_topc(B_201) | v2_struct_0(B_201) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_418, c_418, c_1015])).
% 3.44/1.58  tff(c_1068, plain, (![B_218, C_219, D_220]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0(B_218), C_219, u1_struct_0(D_220))=k2_tmap_1('#skF_2', B_218, C_219, D_220) | ~m1_pre_topc(D_220, '#skF_2') | ~m1_subset_1(C_219, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_218)))) | ~v1_funct_2(C_219, k1_relat_1('#skF_4'), u1_struct_0(B_218)) | ~v1_funct_1(C_219) | ~l1_pre_topc(B_218) | ~v2_pre_topc(B_218) | v2_struct_0(B_218))), inference(negUnitSimplification, [status(thm)], [c_62, c_1028])).
% 3.44/1.58  tff(c_1072, plain, (![D_220]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_220))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_220) | ~m1_pre_topc(D_220, '#skF_2') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_424, c_1068])).
% 3.44/1.58  tff(c_1083, plain, (![D_220]: (k7_relat_1('#skF_4', u1_struct_0(D_220))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_220) | ~m1_pre_topc(D_220, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_52, c_425, c_610, c_1072])).
% 3.44/1.58  tff(c_1110, plain, (![D_225]: (k7_relat_1('#skF_4', u1_struct_0(D_225))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_225) | ~m1_pre_topc(D_225, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_68, c_1083])).
% 3.44/1.58  tff(c_1128, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_721, c_1110])).
% 3.44/1.58  tff(c_1138, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_791, c_1128])).
% 3.44/1.58  tff(c_44, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.44/1.58  tff(c_420, plain, (~r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_418, c_44])).
% 3.44/1.58  tff(c_726, plain, (~r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_721, c_420])).
% 3.44/1.58  tff(c_1140, plain, (~r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1138, c_726])).
% 3.44/1.58  tff(c_1147, plain, (~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1059, c_1140])).
% 3.44/1.58  tff(c_1156, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_423, c_425, c_1147])).
% 3.44/1.58  tff(c_1158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1000, c_1156])).
% 3.44/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.58  
% 3.44/1.58  Inference rules
% 3.44/1.58  ----------------------
% 3.44/1.58  #Ref     : 10
% 3.44/1.58  #Sup     : 212
% 3.44/1.58  #Fact    : 0
% 3.44/1.58  #Define  : 0
% 3.44/1.58  #Split   : 6
% 3.44/1.58  #Chain   : 0
% 3.44/1.58  #Close   : 0
% 3.44/1.58  
% 3.44/1.58  Ordering : KBO
% 3.44/1.58  
% 3.44/1.58  Simplification rules
% 3.44/1.58  ----------------------
% 3.44/1.58  #Subsume      : 22
% 3.44/1.58  #Demod        : 248
% 3.44/1.58  #Tautology    : 105
% 3.44/1.58  #SimpNegUnit  : 27
% 3.44/1.58  #BackRed      : 26
% 3.44/1.58  
% 3.44/1.58  #Partial instantiations: 0
% 3.44/1.58  #Strategies tried      : 1
% 3.44/1.58  
% 3.44/1.58  Timing (in seconds)
% 3.44/1.58  ----------------------
% 3.44/1.58  Preprocessing        : 0.35
% 3.44/1.58  Parsing              : 0.18
% 3.44/1.58  CNF conversion       : 0.02
% 3.44/1.58  Main loop            : 0.44
% 3.44/1.58  Inferencing          : 0.16
% 3.44/1.58  Reduction            : 0.15
% 3.44/1.58  Demodulation         : 0.10
% 3.44/1.58  BG Simplification    : 0.03
% 3.44/1.58  Subsumption          : 0.07
% 3.44/1.58  Abstraction          : 0.02
% 3.44/1.58  MUC search           : 0.00
% 3.44/1.58  Cooper               : 0.00
% 3.44/1.58  Total                : 0.84
% 3.44/1.58  Index Insertion      : 0.00
% 3.44/1.58  Index Deletion       : 0.00
% 3.44/1.58  Index Matching       : 0.00
% 3.44/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
