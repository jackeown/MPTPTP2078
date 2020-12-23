%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:56 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :  130 (1155 expanded)
%              Number of leaves         :   46 ( 420 expanded)
%              Depth                    :   21
%              Number of atoms          :  318 (4801 expanded)
%              Number of equality atoms :   30 ( 344 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_190,negated_conjecture,(
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

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_157,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_153,axiom,(
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

tff(f_119,axiom,(
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

tff(f_81,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_146,axiom,(
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

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(c_66,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_24,plain,(
    ! [A_19] :
      ( l1_struct_0(A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_54,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_60,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_56,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_83,plain,(
    ! [B_76,A_77] :
      ( l1_pre_topc(B_76)
      | ~ m1_pre_topc(B_76,A_77)
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_89,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_83])).

tff(c_93,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_89])).

tff(c_44,plain,(
    ! [A_54] :
      ( m1_pre_topc(A_54,A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_48,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_240,plain,(
    ! [A_113,B_114] :
      ( m1_pre_topc(A_113,g1_pre_topc(u1_struct_0(B_114),u1_pre_topc(B_114)))
      | ~ m1_pre_topc(A_113,B_114)
      | ~ l1_pre_topc(B_114)
      | ~ l1_pre_topc(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_253,plain,(
    ! [A_113] :
      ( m1_pre_topc(A_113,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_113,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_240])).

tff(c_268,plain,(
    ! [A_116] :
      ( m1_pre_topc(A_116,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_116,'#skF_2')
      | ~ l1_pre_topc(A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_253])).

tff(c_30,plain,(
    ! [B_26,A_24] :
      ( m1_pre_topc(B_26,A_24)
      | ~ m1_pre_topc(B_26,g1_pre_topc(u1_struct_0(A_24),u1_pre_topc(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_274,plain,(
    ! [A_116] :
      ( m1_pre_topc(A_116,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc(A_116,'#skF_2')
      | ~ l1_pre_topc(A_116) ) ),
    inference(resolution,[status(thm)],[c_268,c_30])).

tff(c_284,plain,(
    ! [A_117] :
      ( m1_pre_topc(A_117,'#skF_3')
      | ~ m1_pre_topc(A_117,'#skF_2')
      | ~ l1_pre_topc(A_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_274])).

tff(c_291,plain,
    ( m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_284])).

tff(c_298,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_291])).

tff(c_192,plain,(
    ! [B_99,A_100] :
      ( m1_subset_1(u1_struct_0(B_99),k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ m1_pre_topc(B_99,A_100)
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_200,plain,(
    ! [B_99,A_100] :
      ( r1_tarski(u1_struct_0(B_99),u1_struct_0(A_100))
      | ~ m1_pre_topc(B_99,A_100)
      | ~ l1_pre_topc(A_100) ) ),
    inference(resolution,[status(thm)],[c_192,c_8])).

tff(c_213,plain,(
    ! [B_106,A_107] :
      ( r1_tarski(u1_struct_0(B_106),u1_struct_0(A_107))
      | ~ m1_pre_topc(B_106,A_107)
      | ~ l1_pre_topc(A_107) ) ),
    inference(resolution,[status(thm)],[c_192,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_314,plain,(
    ! [B_118,A_119] :
      ( u1_struct_0(B_118) = u1_struct_0(A_119)
      | ~ r1_tarski(u1_struct_0(A_119),u1_struct_0(B_118))
      | ~ m1_pre_topc(B_118,A_119)
      | ~ l1_pre_topc(A_119) ) ),
    inference(resolution,[status(thm)],[c_213,c_2])).

tff(c_344,plain,(
    ! [B_125,A_126] :
      ( u1_struct_0(B_125) = u1_struct_0(A_126)
      | ~ m1_pre_topc(A_126,B_125)
      | ~ l1_pre_topc(B_125)
      | ~ m1_pre_topc(B_125,A_126)
      | ~ l1_pre_topc(A_126) ) ),
    inference(resolution,[status(thm)],[c_200,c_314])).

tff(c_348,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_298,c_344])).

tff(c_365,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_93,c_348])).

tff(c_52,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_384,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_52])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_383,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_50])).

tff(c_36,plain,(
    ! [D_33,A_30,C_32,B_31,F_35] :
      ( r1_funct_2(A_30,B_31,C_32,D_33,F_35,F_35)
      | ~ m1_subset_1(F_35,k1_zfmisc_1(k2_zfmisc_1(C_32,D_33)))
      | ~ v1_funct_2(F_35,C_32,D_33)
      | ~ m1_subset_1(F_35,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ v1_funct_2(F_35,A_30,B_31)
      | ~ v1_funct_1(F_35)
      | v1_xboole_0(D_33)
      | v1_xboole_0(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_460,plain,(
    ! [A_30,B_31] :
      ( r1_funct_2(A_30,B_31,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ v1_funct_2('#skF_4',A_30,B_31)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_31) ) ),
    inference(resolution,[status(thm)],[c_383,c_36])).

tff(c_477,plain,(
    ! [A_30,B_31] :
      ( r1_funct_2(A_30,B_31,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ v1_funct_2('#skF_4',A_30,B_31)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_384,c_460])).

tff(c_927,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_477])).

tff(c_28,plain,(
    ! [A_23] :
      ( ~ v1_xboole_0(u1_struct_0(A_23))
      | ~ l1_struct_0(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_930,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_927,c_28])).

tff(c_933,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_930])).

tff(c_946,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_933])).

tff(c_950,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_946])).

tff(c_952,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_477])).

tff(c_97,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_50,c_8])).

tff(c_382,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_97])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_449,plain,(
    ! [F_129,A_130,D_131,C_127,B_128] :
      ( r1_funct_2(A_130,B_128,C_127,D_131,F_129,F_129)
      | ~ m1_subset_1(F_129,k1_zfmisc_1(k2_zfmisc_1(C_127,D_131)))
      | ~ v1_funct_2(F_129,C_127,D_131)
      | ~ m1_subset_1(F_129,k1_zfmisc_1(k2_zfmisc_1(A_130,B_128)))
      | ~ v1_funct_2(F_129,A_130,B_128)
      | ~ v1_funct_1(F_129)
      | v1_xboole_0(D_131)
      | v1_xboole_0(B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1030,plain,(
    ! [A_182,A_186,C_183,D_185,B_184] :
      ( r1_funct_2(A_182,B_184,C_183,D_185,A_186,A_186)
      | ~ v1_funct_2(A_186,C_183,D_185)
      | ~ m1_subset_1(A_186,k1_zfmisc_1(k2_zfmisc_1(A_182,B_184)))
      | ~ v1_funct_2(A_186,A_182,B_184)
      | ~ v1_funct_1(A_186)
      | v1_xboole_0(D_185)
      | v1_xboole_0(B_184)
      | ~ r1_tarski(A_186,k2_zfmisc_1(C_183,D_185)) ) ),
    inference(resolution,[status(thm)],[c_10,c_449])).

tff(c_1070,plain,(
    ! [D_193,A_197,C_194,A_196,B_195] :
      ( r1_funct_2(A_197,B_195,C_194,D_193,A_196,A_196)
      | ~ v1_funct_2(A_196,C_194,D_193)
      | ~ v1_funct_2(A_196,A_197,B_195)
      | ~ v1_funct_1(A_196)
      | v1_xboole_0(D_193)
      | v1_xboole_0(B_195)
      | ~ r1_tarski(A_196,k2_zfmisc_1(C_194,D_193))
      | ~ r1_tarski(A_196,k2_zfmisc_1(A_197,B_195)) ) ),
    inference(resolution,[status(thm)],[c_10,c_1030])).

tff(c_1072,plain,(
    ! [A_197,B_195] :
      ( r1_funct_2(A_197,B_195,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_2('#skF_4',A_197,B_195)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_195)
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(A_197,B_195)) ) ),
    inference(resolution,[status(thm)],[c_382,c_1070])).

tff(c_1078,plain,(
    ! [A_197,B_195] :
      ( r1_funct_2(A_197,B_195,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',A_197,B_195)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_195)
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(A_197,B_195)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_384,c_1072])).

tff(c_1079,plain,(
    ! [A_197,B_195] :
      ( r1_funct_2(A_197,B_195,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',A_197,B_195)
      | v1_xboole_0(B_195)
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(A_197,B_195)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_952,c_1078])).

tff(c_68,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_325,plain,(
    ! [A_120,B_121,C_122,D_123] :
      ( k2_partfun1(A_120,B_121,C_122,D_123) = k7_relat_1(C_122,D_123)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121)))
      | ~ v1_funct_1(C_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_327,plain,(
    ! [D_123] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_123) = k7_relat_1('#skF_4',D_123)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_325])).

tff(c_333,plain,(
    ! [D_123] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_123) = k7_relat_1('#skF_4',D_123) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_327])).

tff(c_376,plain,(
    ! [D_123] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',D_123) = k7_relat_1('#skF_4',D_123) ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_333])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_62,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_583,plain,(
    ! [A_140,B_141,C_142,D_143] :
      ( k2_partfun1(u1_struct_0(A_140),u1_struct_0(B_141),C_142,u1_struct_0(D_143)) = k2_tmap_1(A_140,B_141,C_142,D_143)
      | ~ m1_pre_topc(D_143,A_140)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_140),u1_struct_0(B_141))))
      | ~ v1_funct_2(C_142,u1_struct_0(A_140),u1_struct_0(B_141))
      | ~ v1_funct_1(C_142)
      | ~ l1_pre_topc(B_141)
      | ~ v2_pre_topc(B_141)
      | v2_struct_0(B_141)
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1041,plain,(
    ! [A_187,B_188,A_189,D_190] :
      ( k2_partfun1(u1_struct_0(A_187),u1_struct_0(B_188),A_189,u1_struct_0(D_190)) = k2_tmap_1(A_187,B_188,A_189,D_190)
      | ~ m1_pre_topc(D_190,A_187)
      | ~ v1_funct_2(A_189,u1_struct_0(A_187),u1_struct_0(B_188))
      | ~ v1_funct_1(A_189)
      | ~ l1_pre_topc(B_188)
      | ~ v2_pre_topc(B_188)
      | v2_struct_0(B_188)
      | ~ l1_pre_topc(A_187)
      | ~ v2_pre_topc(A_187)
      | v2_struct_0(A_187)
      | ~ r1_tarski(A_189,k2_zfmisc_1(u1_struct_0(A_187),u1_struct_0(B_188))) ) ),
    inference(resolution,[status(thm)],[c_10,c_583])).

tff(c_1045,plain,(
    ! [B_188,A_189,D_190] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_188),A_189,u1_struct_0(D_190)) = k2_tmap_1('#skF_2',B_188,A_189,D_190)
      | ~ m1_pre_topc(D_190,'#skF_2')
      | ~ v1_funct_2(A_189,u1_struct_0('#skF_2'),u1_struct_0(B_188))
      | ~ v1_funct_1(A_189)
      | ~ l1_pre_topc(B_188)
      | ~ v2_pre_topc(B_188)
      | v2_struct_0(B_188)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_189,k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_188))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_365,c_1041])).

tff(c_1056,plain,(
    ! [B_188,A_189,D_190] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_188),A_189,u1_struct_0(D_190)) = k2_tmap_1('#skF_2',B_188,A_189,D_190)
      | ~ m1_pre_topc(D_190,'#skF_2')
      | ~ v1_funct_2(A_189,u1_struct_0('#skF_3'),u1_struct_0(B_188))
      | ~ v1_funct_1(A_189)
      | ~ l1_pre_topc(B_188)
      | ~ v2_pre_topc(B_188)
      | v2_struct_0(B_188)
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_189,k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_188))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_365,c_365,c_1045])).

tff(c_1089,plain,(
    ! [B_200,A_201,D_202] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_200),A_201,u1_struct_0(D_202)) = k2_tmap_1('#skF_2',B_200,A_201,D_202)
      | ~ m1_pre_topc(D_202,'#skF_2')
      | ~ v1_funct_2(A_201,u1_struct_0('#skF_3'),u1_struct_0(B_200))
      | ~ v1_funct_1(A_201)
      | ~ l1_pre_topc(B_200)
      | ~ v2_pre_topc(B_200)
      | v2_struct_0(B_200)
      | ~ r1_tarski(A_201,k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_200))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1056])).

tff(c_1091,plain,(
    ! [D_202] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_202)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_202)
      | ~ m1_pre_topc(D_202,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_382,c_1089])).

tff(c_1099,plain,(
    ! [D_202] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_202)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_202)
      | ~ m1_pre_topc(D_202,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_54,c_384,c_376,c_1091])).

tff(c_1105,plain,(
    ! [D_203] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_203)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_203)
      | ~ m1_pre_topc(D_203,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1099])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_108,plain,(
    ! [B_80,A_81] :
      ( v1_relat_1(B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_81))
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_111,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_50,c_108])).

tff(c_117,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_111])).

tff(c_131,plain,(
    ! [C_86,A_87,B_88] :
      ( v4_relat_1(C_86,A_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_139,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_131])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( k7_relat_1(B_11,A_10) = B_11
      | ~ v4_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_143,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_139,c_16])).

tff(c_146,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_143])).

tff(c_380,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_146])).

tff(c_1111,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1105,c_380])).

tff(c_1123,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1111])).

tff(c_46,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_378,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_46])).

tff(c_1129,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1123,c_378])).

tff(c_1141,plain,
    ( ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1079,c_1129])).

tff(c_1150,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_384,c_1141])).

tff(c_1152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_952,c_1150])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:57:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.85/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/1.70  
% 3.85/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/1.71  %$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.85/1.71  
% 3.85/1.71  %Foreground sorts:
% 3.85/1.71  
% 3.85/1.71  
% 3.85/1.71  %Background operators:
% 3.85/1.71  
% 3.85/1.71  
% 3.85/1.71  %Foreground operators:
% 3.85/1.71  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.85/1.71  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.85/1.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.85/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.85/1.71  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.85/1.71  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.85/1.71  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.85/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.85/1.71  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.85/1.71  tff('#skF_2', type, '#skF_2': $i).
% 3.85/1.71  tff('#skF_3', type, '#skF_3': $i).
% 3.85/1.71  tff('#skF_1', type, '#skF_1': $i).
% 3.85/1.71  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.85/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.85/1.71  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.85/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.85/1.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.85/1.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.85/1.71  tff('#skF_4', type, '#skF_4': $i).
% 3.85/1.71  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 3.85/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.85/1.71  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.85/1.71  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.85/1.71  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.85/1.71  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.85/1.71  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.85/1.71  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.85/1.71  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.85/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.85/1.71  
% 3.85/1.73  tff(f_190, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_tmap_1)).
% 3.85/1.73  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.85/1.73  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.85/1.73  tff(f_157, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 3.85/1.73  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 3.85/1.73  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 3.85/1.73  tff(f_153, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.85/1.73  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.85/1.73  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.85/1.73  tff(f_119, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 3.85/1.73  tff(f_81, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.85/1.73  tff(f_62, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.85/1.73  tff(f_146, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.85/1.73  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.85/1.73  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.85/1.73  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.85/1.73  tff(f_50, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.85/1.73  tff(c_66, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.85/1.73  tff(c_24, plain, (![A_19]: (l1_struct_0(A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.85/1.73  tff(c_70, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.85/1.73  tff(c_54, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.85/1.73  tff(c_60, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.85/1.73  tff(c_56, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.85/1.73  tff(c_83, plain, (![B_76, A_77]: (l1_pre_topc(B_76) | ~m1_pre_topc(B_76, A_77) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.85/1.73  tff(c_89, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_56, c_83])).
% 3.85/1.73  tff(c_93, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_89])).
% 3.85/1.73  tff(c_44, plain, (![A_54]: (m1_pre_topc(A_54, A_54) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.85/1.73  tff(c_48, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.85/1.73  tff(c_240, plain, (![A_113, B_114]: (m1_pre_topc(A_113, g1_pre_topc(u1_struct_0(B_114), u1_pre_topc(B_114))) | ~m1_pre_topc(A_113, B_114) | ~l1_pre_topc(B_114) | ~l1_pre_topc(A_113))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.85/1.73  tff(c_253, plain, (![A_113]: (m1_pre_topc(A_113, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_113, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_113))), inference(superposition, [status(thm), theory('equality')], [c_48, c_240])).
% 3.85/1.73  tff(c_268, plain, (![A_116]: (m1_pre_topc(A_116, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_116, '#skF_2') | ~l1_pre_topc(A_116))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_253])).
% 3.85/1.73  tff(c_30, plain, (![B_26, A_24]: (m1_pre_topc(B_26, A_24) | ~m1_pre_topc(B_26, g1_pre_topc(u1_struct_0(A_24), u1_pre_topc(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.85/1.73  tff(c_274, plain, (![A_116]: (m1_pre_topc(A_116, '#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(A_116, '#skF_2') | ~l1_pre_topc(A_116))), inference(resolution, [status(thm)], [c_268, c_30])).
% 3.85/1.73  tff(c_284, plain, (![A_117]: (m1_pre_topc(A_117, '#skF_3') | ~m1_pre_topc(A_117, '#skF_2') | ~l1_pre_topc(A_117))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_274])).
% 3.85/1.73  tff(c_291, plain, (m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_284])).
% 3.85/1.73  tff(c_298, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_291])).
% 3.85/1.73  tff(c_192, plain, (![B_99, A_100]: (m1_subset_1(u1_struct_0(B_99), k1_zfmisc_1(u1_struct_0(A_100))) | ~m1_pre_topc(B_99, A_100) | ~l1_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.85/1.73  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.85/1.73  tff(c_200, plain, (![B_99, A_100]: (r1_tarski(u1_struct_0(B_99), u1_struct_0(A_100)) | ~m1_pre_topc(B_99, A_100) | ~l1_pre_topc(A_100))), inference(resolution, [status(thm)], [c_192, c_8])).
% 3.85/1.73  tff(c_213, plain, (![B_106, A_107]: (r1_tarski(u1_struct_0(B_106), u1_struct_0(A_107)) | ~m1_pre_topc(B_106, A_107) | ~l1_pre_topc(A_107))), inference(resolution, [status(thm)], [c_192, c_8])).
% 3.85/1.73  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.85/1.73  tff(c_314, plain, (![B_118, A_119]: (u1_struct_0(B_118)=u1_struct_0(A_119) | ~r1_tarski(u1_struct_0(A_119), u1_struct_0(B_118)) | ~m1_pre_topc(B_118, A_119) | ~l1_pre_topc(A_119))), inference(resolution, [status(thm)], [c_213, c_2])).
% 3.85/1.73  tff(c_344, plain, (![B_125, A_126]: (u1_struct_0(B_125)=u1_struct_0(A_126) | ~m1_pre_topc(A_126, B_125) | ~l1_pre_topc(B_125) | ~m1_pre_topc(B_125, A_126) | ~l1_pre_topc(A_126))), inference(resolution, [status(thm)], [c_200, c_314])).
% 3.85/1.73  tff(c_348, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_298, c_344])).
% 3.85/1.73  tff(c_365, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_93, c_348])).
% 3.85/1.73  tff(c_52, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.85/1.73  tff(c_384, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_365, c_52])).
% 3.85/1.73  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.85/1.73  tff(c_383, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_365, c_50])).
% 3.85/1.73  tff(c_36, plain, (![D_33, A_30, C_32, B_31, F_35]: (r1_funct_2(A_30, B_31, C_32, D_33, F_35, F_35) | ~m1_subset_1(F_35, k1_zfmisc_1(k2_zfmisc_1(C_32, D_33))) | ~v1_funct_2(F_35, C_32, D_33) | ~m1_subset_1(F_35, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~v1_funct_2(F_35, A_30, B_31) | ~v1_funct_1(F_35) | v1_xboole_0(D_33) | v1_xboole_0(B_31))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.85/1.73  tff(c_460, plain, (![A_30, B_31]: (r1_funct_2(A_30, B_31, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~v1_funct_2('#skF_4', A_30, B_31) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_31))), inference(resolution, [status(thm)], [c_383, c_36])).
% 3.85/1.73  tff(c_477, plain, (![A_30, B_31]: (r1_funct_2(A_30, B_31, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~v1_funct_2('#skF_4', A_30, B_31) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_31))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_384, c_460])).
% 3.85/1.73  tff(c_927, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_477])).
% 3.85/1.73  tff(c_28, plain, (![A_23]: (~v1_xboole_0(u1_struct_0(A_23)) | ~l1_struct_0(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.85/1.73  tff(c_930, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_927, c_28])).
% 3.85/1.73  tff(c_933, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_70, c_930])).
% 3.85/1.73  tff(c_946, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_933])).
% 3.85/1.73  tff(c_950, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_946])).
% 3.85/1.73  tff(c_952, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_477])).
% 3.85/1.73  tff(c_97, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_50, c_8])).
% 3.85/1.73  tff(c_382, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_365, c_97])).
% 3.85/1.73  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.85/1.73  tff(c_449, plain, (![F_129, A_130, D_131, C_127, B_128]: (r1_funct_2(A_130, B_128, C_127, D_131, F_129, F_129) | ~m1_subset_1(F_129, k1_zfmisc_1(k2_zfmisc_1(C_127, D_131))) | ~v1_funct_2(F_129, C_127, D_131) | ~m1_subset_1(F_129, k1_zfmisc_1(k2_zfmisc_1(A_130, B_128))) | ~v1_funct_2(F_129, A_130, B_128) | ~v1_funct_1(F_129) | v1_xboole_0(D_131) | v1_xboole_0(B_128))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.85/1.73  tff(c_1030, plain, (![A_182, A_186, C_183, D_185, B_184]: (r1_funct_2(A_182, B_184, C_183, D_185, A_186, A_186) | ~v1_funct_2(A_186, C_183, D_185) | ~m1_subset_1(A_186, k1_zfmisc_1(k2_zfmisc_1(A_182, B_184))) | ~v1_funct_2(A_186, A_182, B_184) | ~v1_funct_1(A_186) | v1_xboole_0(D_185) | v1_xboole_0(B_184) | ~r1_tarski(A_186, k2_zfmisc_1(C_183, D_185)))), inference(resolution, [status(thm)], [c_10, c_449])).
% 3.85/1.73  tff(c_1070, plain, (![D_193, A_197, C_194, A_196, B_195]: (r1_funct_2(A_197, B_195, C_194, D_193, A_196, A_196) | ~v1_funct_2(A_196, C_194, D_193) | ~v1_funct_2(A_196, A_197, B_195) | ~v1_funct_1(A_196) | v1_xboole_0(D_193) | v1_xboole_0(B_195) | ~r1_tarski(A_196, k2_zfmisc_1(C_194, D_193)) | ~r1_tarski(A_196, k2_zfmisc_1(A_197, B_195)))), inference(resolution, [status(thm)], [c_10, c_1030])).
% 3.85/1.73  tff(c_1072, plain, (![A_197, B_195]: (r1_funct_2(A_197, B_195, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_2('#skF_4', A_197, B_195) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_195) | ~r1_tarski('#skF_4', k2_zfmisc_1(A_197, B_195)))), inference(resolution, [status(thm)], [c_382, c_1070])).
% 3.85/1.73  tff(c_1078, plain, (![A_197, B_195]: (r1_funct_2(A_197, B_195, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', A_197, B_195) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_195) | ~r1_tarski('#skF_4', k2_zfmisc_1(A_197, B_195)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_384, c_1072])).
% 3.85/1.73  tff(c_1079, plain, (![A_197, B_195]: (r1_funct_2(A_197, B_195, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', A_197, B_195) | v1_xboole_0(B_195) | ~r1_tarski('#skF_4', k2_zfmisc_1(A_197, B_195)))), inference(negUnitSimplification, [status(thm)], [c_952, c_1078])).
% 3.85/1.73  tff(c_68, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.85/1.73  tff(c_325, plain, (![A_120, B_121, C_122, D_123]: (k2_partfun1(A_120, B_121, C_122, D_123)=k7_relat_1(C_122, D_123) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))) | ~v1_funct_1(C_122))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.85/1.73  tff(c_327, plain, (![D_123]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_123)=k7_relat_1('#skF_4', D_123) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_325])).
% 3.85/1.73  tff(c_333, plain, (![D_123]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_123)=k7_relat_1('#skF_4', D_123))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_327])).
% 3.85/1.73  tff(c_376, plain, (![D_123]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', D_123)=k7_relat_1('#skF_4', D_123))), inference(demodulation, [status(thm), theory('equality')], [c_365, c_333])).
% 3.85/1.73  tff(c_64, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.85/1.73  tff(c_62, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.85/1.73  tff(c_583, plain, (![A_140, B_141, C_142, D_143]: (k2_partfun1(u1_struct_0(A_140), u1_struct_0(B_141), C_142, u1_struct_0(D_143))=k2_tmap_1(A_140, B_141, C_142, D_143) | ~m1_pre_topc(D_143, A_140) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_140), u1_struct_0(B_141)))) | ~v1_funct_2(C_142, u1_struct_0(A_140), u1_struct_0(B_141)) | ~v1_funct_1(C_142) | ~l1_pre_topc(B_141) | ~v2_pre_topc(B_141) | v2_struct_0(B_141) | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140) | v2_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.85/1.73  tff(c_1041, plain, (![A_187, B_188, A_189, D_190]: (k2_partfun1(u1_struct_0(A_187), u1_struct_0(B_188), A_189, u1_struct_0(D_190))=k2_tmap_1(A_187, B_188, A_189, D_190) | ~m1_pre_topc(D_190, A_187) | ~v1_funct_2(A_189, u1_struct_0(A_187), u1_struct_0(B_188)) | ~v1_funct_1(A_189) | ~l1_pre_topc(B_188) | ~v2_pre_topc(B_188) | v2_struct_0(B_188) | ~l1_pre_topc(A_187) | ~v2_pre_topc(A_187) | v2_struct_0(A_187) | ~r1_tarski(A_189, k2_zfmisc_1(u1_struct_0(A_187), u1_struct_0(B_188))))), inference(resolution, [status(thm)], [c_10, c_583])).
% 3.85/1.73  tff(c_1045, plain, (![B_188, A_189, D_190]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_188), A_189, u1_struct_0(D_190))=k2_tmap_1('#skF_2', B_188, A_189, D_190) | ~m1_pre_topc(D_190, '#skF_2') | ~v1_funct_2(A_189, u1_struct_0('#skF_2'), u1_struct_0(B_188)) | ~v1_funct_1(A_189) | ~l1_pre_topc(B_188) | ~v2_pre_topc(B_188) | v2_struct_0(B_188) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_189, k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_188))))), inference(superposition, [status(thm), theory('equality')], [c_365, c_1041])).
% 3.85/1.73  tff(c_1056, plain, (![B_188, A_189, D_190]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_188), A_189, u1_struct_0(D_190))=k2_tmap_1('#skF_2', B_188, A_189, D_190) | ~m1_pre_topc(D_190, '#skF_2') | ~v1_funct_2(A_189, u1_struct_0('#skF_3'), u1_struct_0(B_188)) | ~v1_funct_1(A_189) | ~l1_pre_topc(B_188) | ~v2_pre_topc(B_188) | v2_struct_0(B_188) | v2_struct_0('#skF_2') | ~r1_tarski(A_189, k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_188))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_365, c_365, c_1045])).
% 3.85/1.73  tff(c_1089, plain, (![B_200, A_201, D_202]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_200), A_201, u1_struct_0(D_202))=k2_tmap_1('#skF_2', B_200, A_201, D_202) | ~m1_pre_topc(D_202, '#skF_2') | ~v1_funct_2(A_201, u1_struct_0('#skF_3'), u1_struct_0(B_200)) | ~v1_funct_1(A_201) | ~l1_pre_topc(B_200) | ~v2_pre_topc(B_200) | v2_struct_0(B_200) | ~r1_tarski(A_201, k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_200))))), inference(negUnitSimplification, [status(thm)], [c_64, c_1056])).
% 3.85/1.73  tff(c_1091, plain, (![D_202]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_202))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_202) | ~m1_pre_topc(D_202, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_382, c_1089])).
% 3.85/1.73  tff(c_1099, plain, (![D_202]: (k7_relat_1('#skF_4', u1_struct_0(D_202))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_202) | ~m1_pre_topc(D_202, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_54, c_384, c_376, c_1091])).
% 3.85/1.73  tff(c_1105, plain, (![D_203]: (k7_relat_1('#skF_4', u1_struct_0(D_203))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_203) | ~m1_pre_topc(D_203, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_70, c_1099])).
% 3.85/1.73  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.85/1.73  tff(c_108, plain, (![B_80, A_81]: (v1_relat_1(B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(A_81)) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.85/1.73  tff(c_111, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_50, c_108])).
% 3.85/1.73  tff(c_117, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_111])).
% 3.85/1.73  tff(c_131, plain, (![C_86, A_87, B_88]: (v4_relat_1(C_86, A_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.85/1.73  tff(c_139, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_131])).
% 3.85/1.73  tff(c_16, plain, (![B_11, A_10]: (k7_relat_1(B_11, A_10)=B_11 | ~v4_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.85/1.73  tff(c_143, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_139, c_16])).
% 3.85/1.73  tff(c_146, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_117, c_143])).
% 3.85/1.73  tff(c_380, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_365, c_146])).
% 3.85/1.73  tff(c_1111, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1105, c_380])).
% 3.85/1.73  tff(c_1123, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1111])).
% 3.85/1.73  tff(c_46, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.85/1.73  tff(c_378, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_365, c_46])).
% 3.85/1.73  tff(c_1129, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1123, c_378])).
% 3.85/1.73  tff(c_1141, plain, (~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1079, c_1129])).
% 3.85/1.73  tff(c_1150, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_382, c_384, c_1141])).
% 3.85/1.73  tff(c_1152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_952, c_1150])).
% 3.85/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/1.73  
% 3.85/1.73  Inference rules
% 3.85/1.73  ----------------------
% 3.85/1.73  #Ref     : 0
% 3.85/1.73  #Sup     : 204
% 3.85/1.73  #Fact    : 0
% 3.85/1.73  #Define  : 0
% 3.85/1.73  #Split   : 7
% 3.85/1.73  #Chain   : 0
% 3.85/1.73  #Close   : 0
% 3.85/1.73  
% 3.85/1.73  Ordering : KBO
% 3.85/1.73  
% 3.85/1.73  Simplification rules
% 3.85/1.73  ----------------------
% 3.85/1.73  #Subsume      : 41
% 3.85/1.73  #Demod        : 280
% 3.85/1.73  #Tautology    : 85
% 3.85/1.73  #SimpNegUnit  : 20
% 3.85/1.73  #BackRed      : 10
% 3.85/1.73  
% 3.85/1.73  #Partial instantiations: 0
% 3.85/1.73  #Strategies tried      : 1
% 3.85/1.73  
% 3.85/1.73  Timing (in seconds)
% 3.85/1.73  ----------------------
% 3.85/1.73  Preprocessing        : 0.38
% 3.85/1.73  Parsing              : 0.20
% 3.85/1.73  CNF conversion       : 0.03
% 3.85/1.73  Main loop            : 0.51
% 3.85/1.73  Inferencing          : 0.18
% 3.85/1.73  Reduction            : 0.17
% 3.85/1.73  Demodulation         : 0.12
% 3.85/1.73  BG Simplification    : 0.03
% 3.85/1.73  Subsumption          : 0.10
% 3.85/1.73  Abstraction          : 0.02
% 3.85/1.73  MUC search           : 0.00
% 3.85/1.73  Cooper               : 0.00
% 3.85/1.74  Total                : 0.94
% 3.85/1.74  Index Insertion      : 0.00
% 3.85/1.74  Index Deletion       : 0.00
% 3.85/1.74  Index Matching       : 0.00
% 3.85/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
