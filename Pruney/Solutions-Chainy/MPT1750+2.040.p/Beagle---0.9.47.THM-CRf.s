%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:57 EST 2020

% Result     : Theorem 4.54s
% Output     : CNFRefutation 4.72s
% Verified   : 
% Statistics : Number of formulae       :  136 (3493 expanded)
%              Number of leaves         :   41 (1233 expanded)
%              Depth                    :   27
%              Number of atoms          :  326 (14885 expanded)
%              Number of equality atoms :   27 (1074 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_189,negated_conjecture,(
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

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_156,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_152,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_118,axiom,(
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

tff(f_80,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_145,axiom,(
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

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(A,C)
       => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_43,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(c_64,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_22,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_58,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_54,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_80,plain,(
    ! [B_72,A_73] :
      ( l1_pre_topc(B_72)
      | ~ m1_pre_topc(B_72,A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_86,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_80])).

tff(c_90,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_86])).

tff(c_42,plain,(
    ! [A_52] :
      ( m1_pre_topc(A_52,A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_46,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_155,plain,(
    ! [A_91,B_92] :
      ( m1_pre_topc(A_91,g1_pre_topc(u1_struct_0(B_92),u1_pre_topc(B_92)))
      | ~ m1_pre_topc(A_91,B_92)
      | ~ l1_pre_topc(B_92)
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_168,plain,(
    ! [A_91] :
      ( m1_pre_topc(A_91,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_91,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_155])).

tff(c_183,plain,(
    ! [A_94] :
      ( m1_pre_topc(A_94,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_94,'#skF_2')
      | ~ l1_pre_topc(A_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_168])).

tff(c_28,plain,(
    ! [B_24,A_22] :
      ( m1_pre_topc(B_24,A_22)
      | ~ m1_pre_topc(B_24,g1_pre_topc(u1_struct_0(A_22),u1_pre_topc(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_189,plain,(
    ! [A_94] :
      ( m1_pre_topc(A_94,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc(A_94,'#skF_2')
      | ~ l1_pre_topc(A_94) ) ),
    inference(resolution,[status(thm)],[c_183,c_28])).

tff(c_198,plain,(
    ! [A_95] :
      ( m1_pre_topc(A_95,'#skF_3')
      | ~ m1_pre_topc(A_95,'#skF_2')
      | ~ l1_pre_topc(A_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_189])).

tff(c_205,plain,
    ( m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_198])).

tff(c_212,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_205])).

tff(c_109,plain,(
    ! [B_76,A_77] :
      ( m1_subset_1(u1_struct_0(B_76),k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ m1_pre_topc(B_76,A_77)
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_113,plain,(
    ! [B_76,A_77] :
      ( r1_tarski(u1_struct_0(B_76),u1_struct_0(A_77))
      | ~ m1_pre_topc(B_76,A_77)
      | ~ l1_pre_topc(A_77) ) ),
    inference(resolution,[status(thm)],[c_109,c_8])).

tff(c_114,plain,(
    ! [B_78,A_79] :
      ( r1_tarski(u1_struct_0(B_78),u1_struct_0(A_79))
      | ~ m1_pre_topc(B_78,A_79)
      | ~ l1_pre_topc(A_79) ) ),
    inference(resolution,[status(thm)],[c_109,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_261,plain,(
    ! [B_112,A_113] :
      ( u1_struct_0(B_112) = u1_struct_0(A_113)
      | ~ r1_tarski(u1_struct_0(A_113),u1_struct_0(B_112))
      | ~ m1_pre_topc(B_112,A_113)
      | ~ l1_pre_topc(A_113) ) ),
    inference(resolution,[status(thm)],[c_114,c_2])).

tff(c_272,plain,(
    ! [B_114,A_115] :
      ( u1_struct_0(B_114) = u1_struct_0(A_115)
      | ~ m1_pre_topc(A_115,B_114)
      | ~ l1_pre_topc(B_114)
      | ~ m1_pre_topc(B_114,A_115)
      | ~ l1_pre_topc(A_115) ) ),
    inference(resolution,[status(thm)],[c_113,c_261])).

tff(c_274,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_212,c_272])).

tff(c_289,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_90,c_274])).

tff(c_50,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_311,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_50])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_310,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_48])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_502,plain,(
    ! [F_129,A_130,D_133,B_132,C_131] :
      ( r1_funct_2(A_130,B_132,C_131,D_133,F_129,F_129)
      | ~ m1_subset_1(F_129,k1_zfmisc_1(k2_zfmisc_1(C_131,D_133)))
      | ~ v1_funct_2(F_129,C_131,D_133)
      | ~ m1_subset_1(F_129,k1_zfmisc_1(k2_zfmisc_1(A_130,B_132)))
      | ~ v1_funct_2(F_129,A_130,B_132)
      | ~ v1_funct_1(F_129)
      | v1_xboole_0(D_133)
      | v1_xboole_0(B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_997,plain,(
    ! [D_181,B_178,A_177,A_180,C_179] :
      ( r1_funct_2(A_177,B_178,C_179,D_181,A_180,A_180)
      | ~ v1_funct_2(A_180,C_179,D_181)
      | ~ m1_subset_1(A_180,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178)))
      | ~ v1_funct_2(A_180,A_177,B_178)
      | ~ v1_funct_1(A_180)
      | v1_xboole_0(D_181)
      | v1_xboole_0(B_178)
      | ~ r1_tarski(A_180,k2_zfmisc_1(C_179,D_181)) ) ),
    inference(resolution,[status(thm)],[c_10,c_502])).

tff(c_1001,plain,(
    ! [C_179,D_181] :
      ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),C_179,D_181,'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',C_179,D_181)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(D_181)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(C_179,D_181)) ) ),
    inference(resolution,[status(thm)],[c_310,c_997])).

tff(c_1012,plain,(
    ! [C_179,D_181] :
      ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),C_179,D_181,'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',C_179,D_181)
      | v1_xboole_0(D_181)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(C_179,D_181)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_311,c_1001])).

tff(c_1764,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1012])).

tff(c_26,plain,(
    ! [A_21] :
      ( ~ v1_xboole_0(u1_struct_0(A_21))
      | ~ l1_struct_0(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1793,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1764,c_26])).

tff(c_1796,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1793])).

tff(c_1799,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_1796])).

tff(c_1803,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1799])).

tff(c_1805,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1012])).

tff(c_94,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_48,c_8])).

tff(c_308,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_94])).

tff(c_1806,plain,(
    ! [C_243,D_244] :
      ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),C_243,D_244,'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',C_243,D_244)
      | v1_xboole_0(D_244)
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(C_243,D_244)) ) ),
    inference(splitRight,[status(thm)],[c_1012])).

tff(c_126,plain,(
    ! [B_83,A_84] :
      ( m1_pre_topc(B_83,A_84)
      | ~ m1_pre_topc(B_83,g1_pre_topc(u1_struct_0(A_84),u1_pre_topc(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_129,plain,(
    ! [B_83] :
      ( m1_pre_topc(B_83,'#skF_2')
      | ~ m1_pre_topc(B_83,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_126])).

tff(c_135,plain,(
    ! [B_83] :
      ( m1_pre_topc(B_83,'#skF_2')
      | ~ m1_pre_topc(B_83,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_129])).

tff(c_159,plain,(
    ! [A_91] :
      ( m1_pre_topc(A_91,'#skF_2')
      | ~ m1_pre_topc(A_91,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_91) ) ),
    inference(resolution,[status(thm)],[c_155,c_135])).

tff(c_171,plain,(
    ! [A_91] :
      ( m1_pre_topc(A_91,'#skF_2')
      | ~ m1_pre_topc(A_91,'#skF_3')
      | ~ l1_pre_topc(A_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_159])).

tff(c_40,plain,(
    ! [B_51,A_49] :
      ( m1_subset_1(u1_struct_0(B_51),k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ m1_pre_topc(B_51,A_49)
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_336,plain,(
    ! [B_51] :
      ( m1_subset_1(u1_struct_0(B_51),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_51,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_40])).

tff(c_429,plain,(
    ! [B_126] :
      ( m1_subset_1(u1_struct_0(B_126),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_126,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_336])).

tff(c_435,plain,
    ( m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_429])).

tff(c_437,plain,(
    ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_435])).

tff(c_440,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_171,c_437])).

tff(c_447,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_212,c_440])).

tff(c_449,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitRight,[status(thm)],[c_435])).

tff(c_66,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_60,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_760,plain,(
    ! [A_156,B_157,C_158,D_159] :
      ( k2_partfun1(u1_struct_0(A_156),u1_struct_0(B_157),C_158,u1_struct_0(D_159)) = k2_tmap_1(A_156,B_157,C_158,D_159)
      | ~ m1_pre_topc(D_159,A_156)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_156),u1_struct_0(B_157))))
      | ~ v1_funct_2(C_158,u1_struct_0(A_156),u1_struct_0(B_157))
      | ~ v1_funct_1(C_158)
      | ~ l1_pre_topc(B_157)
      | ~ v2_pre_topc(B_157)
      | v2_struct_0(B_157)
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_764,plain,(
    ! [B_157,C_158,D_159] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_157),C_158,u1_struct_0(D_159)) = k2_tmap_1('#skF_2',B_157,C_158,D_159)
      | ~ m1_pre_topc(D_159,'#skF_2')
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_157))))
      | ~ v1_funct_2(C_158,u1_struct_0('#skF_2'),u1_struct_0(B_157))
      | ~ v1_funct_1(C_158)
      | ~ l1_pre_topc(B_157)
      | ~ v2_pre_topc(B_157)
      | v2_struct_0(B_157)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_760])).

tff(c_778,plain,(
    ! [B_157,C_158,D_159] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_157),C_158,u1_struct_0(D_159)) = k2_tmap_1('#skF_2',B_157,C_158,D_159)
      | ~ m1_pre_topc(D_159,'#skF_2')
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_157))))
      | ~ v1_funct_2(C_158,u1_struct_0('#skF_3'),u1_struct_0(B_157))
      | ~ v1_funct_1(C_158)
      | ~ l1_pre_topc(B_157)
      | ~ v2_pre_topc(B_157)
      | v2_struct_0(B_157)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_289,c_289,c_764])).

tff(c_790,plain,(
    ! [B_164,C_165,D_166] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_164),C_165,u1_struct_0(D_166)) = k2_tmap_1('#skF_2',B_164,C_165,D_166)
      | ~ m1_pre_topc(D_166,'#skF_2')
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_164))))
      | ~ v1_funct_2(C_165,u1_struct_0('#skF_3'),u1_struct_0(B_164))
      | ~ v1_funct_1(C_165)
      | ~ l1_pre_topc(B_164)
      | ~ v2_pre_topc(B_164)
      | v2_struct_0(B_164) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_778])).

tff(c_792,plain,(
    ! [D_166] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_166)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_166)
      | ~ m1_pre_topc(D_166,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_310,c_790])).

tff(c_803,plain,(
    ! [D_166] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_166)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_166)
      | ~ m1_pre_topc(D_166,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_52,c_311,c_792])).

tff(c_810,plain,(
    ! [D_167] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_167)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_167)
      | ~ m1_pre_topc(D_167,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_803])).

tff(c_839,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0('#skF_3')) = k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_810])).

tff(c_853,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0('#skF_3')) = k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_449,c_839])).

tff(c_804,plain,(
    ! [D_166] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_166)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_166)
      | ~ m1_pre_topc(D_166,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_803])).

tff(c_858,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_2') = k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_853,c_804])).

tff(c_885,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_2') = k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_858])).

tff(c_16,plain,(
    ! [A_9,B_10,C_11,D_12] :
      ( m1_subset_1(k2_partfun1(A_9,B_10,C_11,D_12),k1_zfmisc_1(k2_zfmisc_1(A_9,B_10)))
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10)))
      | ~ v1_funct_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_878,plain,
    ( m1_subset_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_853,c_16])).

tff(c_897,plain,(
    m1_subset_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_310,c_878])).

tff(c_955,plain,(
    m1_subset_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_885,c_897])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_416,plain,(
    ! [A_122,B_123,D_124,C_125] :
      ( r2_relset_1(A_122,B_123,k2_partfun1(A_122,B_123,D_124,C_125),D_124)
      | ~ r1_tarski(A_122,C_125)
      | ~ m1_subset_1(D_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123)))
      | ~ v1_funct_2(D_124,A_122,B_123)
      | ~ v1_funct_1(D_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_428,plain,(
    ! [A_122,B_123,A_3,C_125] :
      ( r2_relset_1(A_122,B_123,k2_partfun1(A_122,B_123,A_3,C_125),A_3)
      | ~ r1_tarski(A_122,C_125)
      | ~ v1_funct_2(A_3,A_122,B_123)
      | ~ v1_funct_1(A_3)
      | ~ r1_tarski(A_3,k2_zfmisc_1(A_122,B_123)) ) ),
    inference(resolution,[status(thm)],[c_10,c_416])).

tff(c_861,plain,
    ( r2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_2'),'#skF_4')
    | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1('#skF_4')
    | ~ r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_853,c_428])).

tff(c_887,plain,(
    r2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_52,c_311,c_6,c_861])).

tff(c_936,plain,(
    r2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_885,c_887])).

tff(c_14,plain,(
    ! [D_8,C_7,A_5,B_6] :
      ( D_8 = C_7
      | ~ r2_relset_1(A_5,B_6,C_7,D_8)
      | ~ m1_subset_1(D_8,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6)))
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_938,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
    | ~ m1_subset_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_936,c_14])).

tff(c_941,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_subset_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_938])).

tff(c_1394,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_955,c_941])).

tff(c_44,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_306,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_44])).

tff(c_1404,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1394,c_306])).

tff(c_1809,plain,
    ( ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1806,c_1404])).

tff(c_1814,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_311,c_1809])).

tff(c_1816,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1805,c_1814])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:36:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.54/1.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.54/1.84  
% 4.54/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.54/1.84  %$ r1_funct_2 > r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.54/1.84  
% 4.54/1.84  %Foreground sorts:
% 4.54/1.84  
% 4.54/1.84  
% 4.54/1.84  %Background operators:
% 4.54/1.84  
% 4.54/1.84  
% 4.54/1.84  %Foreground operators:
% 4.54/1.84  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.54/1.84  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.54/1.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.54/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.54/1.84  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.54/1.84  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.54/1.84  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.54/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.54/1.84  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.54/1.84  tff('#skF_2', type, '#skF_2': $i).
% 4.54/1.84  tff('#skF_3', type, '#skF_3': $i).
% 4.54/1.84  tff('#skF_1', type, '#skF_1': $i).
% 4.54/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.54/1.84  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.54/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.54/1.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.54/1.84  tff('#skF_4', type, '#skF_4': $i).
% 4.54/1.84  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 4.54/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.54/1.84  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.54/1.84  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 4.54/1.84  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.54/1.84  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 4.54/1.84  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.54/1.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.54/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.54/1.84  
% 4.72/1.86  tff(f_189, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_tmap_1)).
% 4.72/1.86  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.72/1.86  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.72/1.86  tff(f_156, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.72/1.86  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 4.72/1.86  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 4.72/1.86  tff(f_152, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.72/1.86  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.72/1.86  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.72/1.86  tff(f_118, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 4.72/1.86  tff(f_80, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.72/1.86  tff(f_145, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 4.72/1.86  tff(f_51, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 4.72/1.86  tff(f_61, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_funct_2)).
% 4.72/1.86  tff(f_43, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.72/1.86  tff(c_64, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.72/1.86  tff(c_22, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.72/1.86  tff(c_68, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.72/1.86  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.72/1.86  tff(c_58, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.72/1.86  tff(c_54, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.72/1.86  tff(c_80, plain, (![B_72, A_73]: (l1_pre_topc(B_72) | ~m1_pre_topc(B_72, A_73) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.72/1.86  tff(c_86, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_80])).
% 4.72/1.86  tff(c_90, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_86])).
% 4.72/1.86  tff(c_42, plain, (![A_52]: (m1_pre_topc(A_52, A_52) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.72/1.86  tff(c_46, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.72/1.86  tff(c_155, plain, (![A_91, B_92]: (m1_pre_topc(A_91, g1_pre_topc(u1_struct_0(B_92), u1_pre_topc(B_92))) | ~m1_pre_topc(A_91, B_92) | ~l1_pre_topc(B_92) | ~l1_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.72/1.86  tff(c_168, plain, (![A_91]: (m1_pre_topc(A_91, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_91, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_91))), inference(superposition, [status(thm), theory('equality')], [c_46, c_155])).
% 4.72/1.86  tff(c_183, plain, (![A_94]: (m1_pre_topc(A_94, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_94, '#skF_2') | ~l1_pre_topc(A_94))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_168])).
% 4.72/1.86  tff(c_28, plain, (![B_24, A_22]: (m1_pre_topc(B_24, A_22) | ~m1_pre_topc(B_24, g1_pre_topc(u1_struct_0(A_22), u1_pre_topc(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.72/1.86  tff(c_189, plain, (![A_94]: (m1_pre_topc(A_94, '#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(A_94, '#skF_2') | ~l1_pre_topc(A_94))), inference(resolution, [status(thm)], [c_183, c_28])).
% 4.72/1.86  tff(c_198, plain, (![A_95]: (m1_pre_topc(A_95, '#skF_3') | ~m1_pre_topc(A_95, '#skF_2') | ~l1_pre_topc(A_95))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_189])).
% 4.72/1.86  tff(c_205, plain, (m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_198])).
% 4.72/1.86  tff(c_212, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_205])).
% 4.72/1.86  tff(c_109, plain, (![B_76, A_77]: (m1_subset_1(u1_struct_0(B_76), k1_zfmisc_1(u1_struct_0(A_77))) | ~m1_pre_topc(B_76, A_77) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.72/1.86  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.72/1.86  tff(c_113, plain, (![B_76, A_77]: (r1_tarski(u1_struct_0(B_76), u1_struct_0(A_77)) | ~m1_pre_topc(B_76, A_77) | ~l1_pre_topc(A_77))), inference(resolution, [status(thm)], [c_109, c_8])).
% 4.72/1.86  tff(c_114, plain, (![B_78, A_79]: (r1_tarski(u1_struct_0(B_78), u1_struct_0(A_79)) | ~m1_pre_topc(B_78, A_79) | ~l1_pre_topc(A_79))), inference(resolution, [status(thm)], [c_109, c_8])).
% 4.72/1.86  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.72/1.86  tff(c_261, plain, (![B_112, A_113]: (u1_struct_0(B_112)=u1_struct_0(A_113) | ~r1_tarski(u1_struct_0(A_113), u1_struct_0(B_112)) | ~m1_pre_topc(B_112, A_113) | ~l1_pre_topc(A_113))), inference(resolution, [status(thm)], [c_114, c_2])).
% 4.72/1.86  tff(c_272, plain, (![B_114, A_115]: (u1_struct_0(B_114)=u1_struct_0(A_115) | ~m1_pre_topc(A_115, B_114) | ~l1_pre_topc(B_114) | ~m1_pre_topc(B_114, A_115) | ~l1_pre_topc(A_115))), inference(resolution, [status(thm)], [c_113, c_261])).
% 4.72/1.86  tff(c_274, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_212, c_272])).
% 4.72/1.86  tff(c_289, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_90, c_274])).
% 4.72/1.86  tff(c_50, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.72/1.86  tff(c_311, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_289, c_50])).
% 4.72/1.86  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.72/1.86  tff(c_310, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_289, c_48])).
% 4.72/1.86  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.72/1.86  tff(c_502, plain, (![F_129, A_130, D_133, B_132, C_131]: (r1_funct_2(A_130, B_132, C_131, D_133, F_129, F_129) | ~m1_subset_1(F_129, k1_zfmisc_1(k2_zfmisc_1(C_131, D_133))) | ~v1_funct_2(F_129, C_131, D_133) | ~m1_subset_1(F_129, k1_zfmisc_1(k2_zfmisc_1(A_130, B_132))) | ~v1_funct_2(F_129, A_130, B_132) | ~v1_funct_1(F_129) | v1_xboole_0(D_133) | v1_xboole_0(B_132))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.72/1.86  tff(c_997, plain, (![D_181, B_178, A_177, A_180, C_179]: (r1_funct_2(A_177, B_178, C_179, D_181, A_180, A_180) | ~v1_funct_2(A_180, C_179, D_181) | ~m1_subset_1(A_180, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))) | ~v1_funct_2(A_180, A_177, B_178) | ~v1_funct_1(A_180) | v1_xboole_0(D_181) | v1_xboole_0(B_178) | ~r1_tarski(A_180, k2_zfmisc_1(C_179, D_181)))), inference(resolution, [status(thm)], [c_10, c_502])).
% 4.72/1.86  tff(c_1001, plain, (![C_179, D_181]: (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), C_179, D_181, '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', C_179, D_181) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(D_181) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', k2_zfmisc_1(C_179, D_181)))), inference(resolution, [status(thm)], [c_310, c_997])).
% 4.72/1.86  tff(c_1012, plain, (![C_179, D_181]: (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), C_179, D_181, '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', C_179, D_181) | v1_xboole_0(D_181) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', k2_zfmisc_1(C_179, D_181)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_311, c_1001])).
% 4.72/1.86  tff(c_1764, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_1012])).
% 4.72/1.86  tff(c_26, plain, (![A_21]: (~v1_xboole_0(u1_struct_0(A_21)) | ~l1_struct_0(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.72/1.86  tff(c_1793, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1764, c_26])).
% 4.72/1.86  tff(c_1796, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_68, c_1793])).
% 4.72/1.86  tff(c_1799, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_1796])).
% 4.72/1.86  tff(c_1803, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_1799])).
% 4.72/1.86  tff(c_1805, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_1012])).
% 4.72/1.86  tff(c_94, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_48, c_8])).
% 4.72/1.86  tff(c_308, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_289, c_94])).
% 4.72/1.86  tff(c_1806, plain, (![C_243, D_244]: (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), C_243, D_244, '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', C_243, D_244) | v1_xboole_0(D_244) | ~r1_tarski('#skF_4', k2_zfmisc_1(C_243, D_244)))), inference(splitRight, [status(thm)], [c_1012])).
% 4.72/1.86  tff(c_126, plain, (![B_83, A_84]: (m1_pre_topc(B_83, A_84) | ~m1_pre_topc(B_83, g1_pre_topc(u1_struct_0(A_84), u1_pre_topc(A_84))) | ~l1_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.72/1.86  tff(c_129, plain, (![B_83]: (m1_pre_topc(B_83, '#skF_2') | ~m1_pre_topc(B_83, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_126])).
% 4.72/1.86  tff(c_135, plain, (![B_83]: (m1_pre_topc(B_83, '#skF_2') | ~m1_pre_topc(B_83, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_129])).
% 4.72/1.86  tff(c_159, plain, (![A_91]: (m1_pre_topc(A_91, '#skF_2') | ~m1_pre_topc(A_91, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_91))), inference(resolution, [status(thm)], [c_155, c_135])).
% 4.72/1.86  tff(c_171, plain, (![A_91]: (m1_pre_topc(A_91, '#skF_2') | ~m1_pre_topc(A_91, '#skF_3') | ~l1_pre_topc(A_91))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_159])).
% 4.72/1.86  tff(c_40, plain, (![B_51, A_49]: (m1_subset_1(u1_struct_0(B_51), k1_zfmisc_1(u1_struct_0(A_49))) | ~m1_pre_topc(B_51, A_49) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.72/1.86  tff(c_336, plain, (![B_51]: (m1_subset_1(u1_struct_0(B_51), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_51, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_289, c_40])).
% 4.72/1.86  tff(c_429, plain, (![B_126]: (m1_subset_1(u1_struct_0(B_126), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_126, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_336])).
% 4.72/1.86  tff(c_435, plain, (m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_289, c_429])).
% 4.72/1.86  tff(c_437, plain, (~m1_pre_topc('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_435])).
% 4.72/1.86  tff(c_440, plain, (~m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_171, c_437])).
% 4.72/1.86  tff(c_447, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_212, c_440])).
% 4.72/1.86  tff(c_449, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(splitRight, [status(thm)], [c_435])).
% 4.72/1.86  tff(c_66, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.72/1.86  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.72/1.86  tff(c_60, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.72/1.86  tff(c_760, plain, (![A_156, B_157, C_158, D_159]: (k2_partfun1(u1_struct_0(A_156), u1_struct_0(B_157), C_158, u1_struct_0(D_159))=k2_tmap_1(A_156, B_157, C_158, D_159) | ~m1_pre_topc(D_159, A_156) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_156), u1_struct_0(B_157)))) | ~v1_funct_2(C_158, u1_struct_0(A_156), u1_struct_0(B_157)) | ~v1_funct_1(C_158) | ~l1_pre_topc(B_157) | ~v2_pre_topc(B_157) | v2_struct_0(B_157) | ~l1_pre_topc(A_156) | ~v2_pre_topc(A_156) | v2_struct_0(A_156))), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.72/1.86  tff(c_764, plain, (![B_157, C_158, D_159]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_157), C_158, u1_struct_0(D_159))=k2_tmap_1('#skF_2', B_157, C_158, D_159) | ~m1_pre_topc(D_159, '#skF_2') | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_157)))) | ~v1_funct_2(C_158, u1_struct_0('#skF_2'), u1_struct_0(B_157)) | ~v1_funct_1(C_158) | ~l1_pre_topc(B_157) | ~v2_pre_topc(B_157) | v2_struct_0(B_157) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_289, c_760])).
% 4.72/1.86  tff(c_778, plain, (![B_157, C_158, D_159]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_157), C_158, u1_struct_0(D_159))=k2_tmap_1('#skF_2', B_157, C_158, D_159) | ~m1_pre_topc(D_159, '#skF_2') | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_157)))) | ~v1_funct_2(C_158, u1_struct_0('#skF_3'), u1_struct_0(B_157)) | ~v1_funct_1(C_158) | ~l1_pre_topc(B_157) | ~v2_pre_topc(B_157) | v2_struct_0(B_157) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_289, c_289, c_764])).
% 4.72/1.86  tff(c_790, plain, (![B_164, C_165, D_166]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_164), C_165, u1_struct_0(D_166))=k2_tmap_1('#skF_2', B_164, C_165, D_166) | ~m1_pre_topc(D_166, '#skF_2') | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_164)))) | ~v1_funct_2(C_165, u1_struct_0('#skF_3'), u1_struct_0(B_164)) | ~v1_funct_1(C_165) | ~l1_pre_topc(B_164) | ~v2_pre_topc(B_164) | v2_struct_0(B_164))), inference(negUnitSimplification, [status(thm)], [c_62, c_778])).
% 4.72/1.86  tff(c_792, plain, (![D_166]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_166))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_166) | ~m1_pre_topc(D_166, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_310, c_790])).
% 4.72/1.86  tff(c_803, plain, (![D_166]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_166))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_166) | ~m1_pre_topc(D_166, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_52, c_311, c_792])).
% 4.72/1.86  tff(c_810, plain, (![D_167]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_167))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_167) | ~m1_pre_topc(D_167, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_68, c_803])).
% 4.72/1.86  tff(c_839, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0('#skF_3'))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_289, c_810])).
% 4.72/1.86  tff(c_853, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0('#skF_3'))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_449, c_839])).
% 4.72/1.86  tff(c_804, plain, (![D_166]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_166))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_166) | ~m1_pre_topc(D_166, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_68, c_803])).
% 4.72/1.86  tff(c_858, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_2')=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_853, c_804])).
% 4.72/1.86  tff(c_885, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_2')=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_858])).
% 4.72/1.86  tff(c_16, plain, (![A_9, B_10, C_11, D_12]: (m1_subset_1(k2_partfun1(A_9, B_10, C_11, D_12), k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))) | ~v1_funct_1(C_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.72/1.86  tff(c_878, plain, (m1_subset_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_853, c_16])).
% 4.72/1.86  tff(c_897, plain, (m1_subset_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_310, c_878])).
% 4.72/1.86  tff(c_955, plain, (m1_subset_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_885, c_897])).
% 4.72/1.86  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.72/1.86  tff(c_416, plain, (![A_122, B_123, D_124, C_125]: (r2_relset_1(A_122, B_123, k2_partfun1(A_122, B_123, D_124, C_125), D_124) | ~r1_tarski(A_122, C_125) | ~m1_subset_1(D_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))) | ~v1_funct_2(D_124, A_122, B_123) | ~v1_funct_1(D_124))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.72/1.86  tff(c_428, plain, (![A_122, B_123, A_3, C_125]: (r2_relset_1(A_122, B_123, k2_partfun1(A_122, B_123, A_3, C_125), A_3) | ~r1_tarski(A_122, C_125) | ~v1_funct_2(A_3, A_122, B_123) | ~v1_funct_1(A_3) | ~r1_tarski(A_3, k2_zfmisc_1(A_122, B_123)))), inference(resolution, [status(thm)], [c_10, c_416])).
% 4.72/1.86  tff(c_861, plain, (r2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_2'), '#skF_4') | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_853, c_428])).
% 4.72/1.86  tff(c_887, plain, (r2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_308, c_52, c_311, c_6, c_861])).
% 4.72/1.86  tff(c_936, plain, (r2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_885, c_887])).
% 4.72/1.86  tff(c_14, plain, (![D_8, C_7, A_5, B_6]: (D_8=C_7 | ~r2_relset_1(A_5, B_6, C_7, D_8) | ~m1_subset_1(D_8, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.72/1.86  tff(c_938, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~m1_subset_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_936, c_14])).
% 4.72/1.86  tff(c_941, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~m1_subset_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_310, c_938])).
% 4.72/1.86  tff(c_1394, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_955, c_941])).
% 4.72/1.86  tff(c_44, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.72/1.86  tff(c_306, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_289, c_44])).
% 4.72/1.86  tff(c_1404, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1394, c_306])).
% 4.72/1.86  tff(c_1809, plain, (~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1806, c_1404])).
% 4.72/1.86  tff(c_1814, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_308, c_311, c_1809])).
% 4.72/1.86  tff(c_1816, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1805, c_1814])).
% 4.72/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.72/1.86  
% 4.72/1.86  Inference rules
% 4.72/1.86  ----------------------
% 4.72/1.86  #Ref     : 0
% 4.72/1.86  #Sup     : 354
% 4.72/1.86  #Fact    : 0
% 4.72/1.86  #Define  : 0
% 4.72/1.86  #Split   : 7
% 4.72/1.86  #Chain   : 0
% 4.72/1.86  #Close   : 0
% 4.72/1.86  
% 4.72/1.86  Ordering : KBO
% 4.72/1.86  
% 4.72/1.86  Simplification rules
% 4.72/1.86  ----------------------
% 4.72/1.86  #Subsume      : 58
% 4.72/1.86  #Demod        : 621
% 4.72/1.86  #Tautology    : 152
% 4.72/1.86  #SimpNegUnit  : 32
% 4.72/1.86  #BackRed      : 30
% 4.72/1.86  
% 4.72/1.86  #Partial instantiations: 0
% 4.72/1.86  #Strategies tried      : 1
% 4.72/1.87  
% 4.72/1.87  Timing (in seconds)
% 4.72/1.87  ----------------------
% 4.72/1.87  Preprocessing        : 0.38
% 4.72/1.87  Parsing              : 0.21
% 4.72/1.87  CNF conversion       : 0.03
% 4.72/1.87  Main loop            : 0.66
% 4.72/1.87  Inferencing          : 0.23
% 4.72/1.87  Reduction            : 0.22
% 4.72/1.87  Demodulation         : 0.16
% 4.72/1.87  BG Simplification    : 0.03
% 4.72/1.87  Subsumption          : 0.13
% 4.72/1.87  Abstraction          : 0.03
% 4.72/1.87  MUC search           : 0.00
% 4.72/1.87  Cooper               : 0.00
% 4.72/1.87  Total                : 1.09
% 4.72/1.87  Index Insertion      : 0.00
% 4.72/1.87  Index Deletion       : 0.00
% 4.72/1.87  Index Matching       : 0.00
% 4.72/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
