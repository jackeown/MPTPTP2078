%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:55 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 913 expanded)
%              Number of leaves         :   43 ( 313 expanded)
%              Depth                    :   21
%              Number of atoms          :  257 (3574 expanded)
%              Number of equality atoms :   43 ( 716 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_167,negated_conjecture,(
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

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_107,axiom,(
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

tff(f_76,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_134,axiom,(
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

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(c_54,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_16,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_44,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_60,plain,(
    ! [B_60,A_61] :
      ( l1_pre_topc(B_60)
      | ~ m1_pre_topc(B_60,A_61)
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_63,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_60])).

tff(c_66,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_63])).

tff(c_20,plain,(
    ! [A_19] :
      ( m1_subset_1(u1_pre_topc(A_19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_19))))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_36,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_114,plain,(
    ! [D_81,B_82,C_83,A_84] :
      ( D_81 = B_82
      | g1_pre_topc(C_83,D_81) != g1_pre_topc(A_84,B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k1_zfmisc_1(A_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_143,plain,(
    ! [B_94,A_95] :
      ( u1_pre_topc('#skF_2') = B_94
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(A_95,B_94)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(k1_zfmisc_1(A_95))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_114])).

tff(c_147,plain,(
    ! [A_19] :
      ( u1_pre_topc(A_19) = u1_pre_topc('#skF_2')
      | g1_pre_topc(u1_struct_0(A_19),u1_pre_topc(A_19)) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ l1_pre_topc(A_19) ) ),
    inference(resolution,[status(thm)],[c_20,c_143])).

tff(c_161,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_147])).

tff(c_163,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_161])).

tff(c_178,plain,
    ( m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_20])).

tff(c_182,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_178])).

tff(c_174,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_3')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_36])).

tff(c_26,plain,(
    ! [C_25,A_21,D_26,B_22] :
      ( C_25 = A_21
      | g1_pre_topc(C_25,D_26) != g1_pre_topc(A_21,B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k1_zfmisc_1(A_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_193,plain,(
    ! [C_25,D_26] :
      ( u1_struct_0('#skF_2') = C_25
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_25,D_26)
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_26])).

tff(c_201,plain,(
    ! [C_25,D_26] :
      ( u1_struct_0('#skF_2') = C_25
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_25,D_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_193])).

tff(c_207,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_201])).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_40,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_153,plain,(
    ! [C_99,A_102,D_100,B_101,F_98] :
      ( r1_funct_2(A_102,B_101,C_99,D_100,F_98,F_98)
      | ~ m1_subset_1(F_98,k1_zfmisc_1(k2_zfmisc_1(C_99,D_100)))
      | ~ v1_funct_2(F_98,C_99,D_100)
      | ~ m1_subset_1(F_98,k1_zfmisc_1(k2_zfmisc_1(A_102,B_101)))
      | ~ v1_funct_2(F_98,A_102,B_101)
      | ~ v1_funct_1(F_98)
      | v1_xboole_0(D_100)
      | v1_xboole_0(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_155,plain,(
    ! [A_102,B_101] :
      ( r1_funct_2(A_102,B_101,u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_102,B_101)))
      | ~ v1_funct_2('#skF_4',A_102,B_101)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_101) ) ),
    inference(resolution,[status(thm)],[c_38,c_153])).

tff(c_158,plain,(
    ! [A_102,B_101] :
      ( r1_funct_2(A_102,B_101,u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_102,B_101)))
      | ~ v1_funct_2('#skF_4',A_102,B_101)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_155])).

tff(c_310,plain,(
    ! [A_102,B_101] :
      ( r1_funct_2(A_102,B_101,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_102,B_101)))
      | ~ v1_funct_2('#skF_4',A_102,B_101)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_158])).

tff(c_311,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_310])).

tff(c_22,plain,(
    ! [A_20] :
      ( ~ v1_xboole_0(u1_struct_0(A_20))
      | ~ l1_struct_0(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_331,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_311,c_22])).

tff(c_334,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_331])).

tff(c_337,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_334])).

tff(c_341,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_337])).

tff(c_343,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_310])).

tff(c_222,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_40])).

tff(c_221,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_38])).

tff(c_28,plain,(
    ! [C_29,D_30,B_28,F_32,A_27] :
      ( r1_funct_2(A_27,B_28,C_29,D_30,F_32,F_32)
      | ~ m1_subset_1(F_32,k1_zfmisc_1(k2_zfmisc_1(C_29,D_30)))
      | ~ v1_funct_2(F_32,C_29,D_30)
      | ~ m1_subset_1(F_32,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_funct_2(F_32,A_27,B_28)
      | ~ v1_funct_1(F_32)
      | v1_xboole_0(D_30)
      | v1_xboole_0(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_260,plain,(
    ! [A_27,B_28] :
      ( r1_funct_2(A_27,B_28,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_funct_2('#skF_4',A_27,B_28)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_28) ) ),
    inference(resolution,[status(thm)],[c_221,c_28])).

tff(c_274,plain,(
    ! [A_27,B_28] :
      ( r1_funct_2(A_27,B_28,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_funct_2('#skF_4',A_27,B_28)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_222,c_260])).

tff(c_344,plain,(
    ! [A_27,B_28] :
      ( r1_funct_2(A_27,B_28,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_funct_2('#skF_4',A_27,B_28)
      | v1_xboole_0(B_28) ) ),
    inference(negUnitSimplification,[status(thm)],[c_343,c_274])).

tff(c_56,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_128,plain,(
    ! [A_89,B_90,C_91,D_92] :
      ( k2_partfun1(A_89,B_90,C_91,D_92) = k7_relat_1(C_91,D_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90)))
      | ~ v1_funct_1(C_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_130,plain,(
    ! [D_92] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_92) = k7_relat_1('#skF_4',D_92)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_128])).

tff(c_133,plain,(
    ! [D_92] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_92) = k7_relat_1('#skF_4',D_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_130])).

tff(c_217,plain,(
    ! [D_92] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',D_92) = k7_relat_1('#skF_4',D_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_133])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_50,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_353,plain,(
    ! [A_129,B_130,C_131,D_132] :
      ( k2_partfun1(u1_struct_0(A_129),u1_struct_0(B_130),C_131,u1_struct_0(D_132)) = k2_tmap_1(A_129,B_130,C_131,D_132)
      | ~ m1_pre_topc(D_132,A_129)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_129),u1_struct_0(B_130))))
      | ~ v1_funct_2(C_131,u1_struct_0(A_129),u1_struct_0(B_130))
      | ~ v1_funct_1(C_131)
      | ~ l1_pre_topc(B_130)
      | ~ v2_pre_topc(B_130)
      | v2_struct_0(B_130)
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129)
      | v2_struct_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_357,plain,(
    ! [B_130,C_131,D_132] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_130),C_131,u1_struct_0(D_132)) = k2_tmap_1('#skF_2',B_130,C_131,D_132)
      | ~ m1_pre_topc(D_132,'#skF_2')
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_130))))
      | ~ v1_funct_2(C_131,u1_struct_0('#skF_2'),u1_struct_0(B_130))
      | ~ v1_funct_1(C_131)
      | ~ l1_pre_topc(B_130)
      | ~ v2_pre_topc(B_130)
      | v2_struct_0(B_130)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_353])).

tff(c_365,plain,(
    ! [B_130,C_131,D_132] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_130),C_131,u1_struct_0(D_132)) = k2_tmap_1('#skF_2',B_130,C_131,D_132)
      | ~ m1_pre_topc(D_132,'#skF_2')
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_130))))
      | ~ v1_funct_2(C_131,u1_struct_0('#skF_3'),u1_struct_0(B_130))
      | ~ v1_funct_1(C_131)
      | ~ l1_pre_topc(B_130)
      | ~ v2_pre_topc(B_130)
      | v2_struct_0(B_130)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_207,c_207,c_357])).

tff(c_377,plain,(
    ! [B_136,C_137,D_138] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_136),C_137,u1_struct_0(D_138)) = k2_tmap_1('#skF_2',B_136,C_137,D_138)
      | ~ m1_pre_topc(D_138,'#skF_2')
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_136))))
      | ~ v1_funct_2(C_137,u1_struct_0('#skF_3'),u1_struct_0(B_136))
      | ~ v1_funct_1(C_137)
      | ~ l1_pre_topc(B_136)
      | ~ v2_pre_topc(B_136)
      | v2_struct_0(B_136) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_365])).

tff(c_379,plain,(
    ! [D_138] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_138)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_138)
      | ~ m1_pre_topc(D_138,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_221,c_377])).

tff(c_384,plain,(
    ! [D_138] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_138)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_138)
      | ~ m1_pre_topc(D_138,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_42,c_222,c_217,c_379])).

tff(c_389,plain,(
    ! [D_139] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_139)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_139)
      | ~ m1_pre_topc(D_139,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_384])).

tff(c_8,plain,(
    ! [C_7,A_5,B_6] :
      ( v1_relat_1(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_72,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_8])).

tff(c_83,plain,(
    ! [C_71,A_72,B_73] :
      ( v4_relat_1(C_71,A_72)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_87,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_83])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_94,plain,(
    ! [B_77,A_78] :
      ( k7_relat_1(B_77,A_78) = B_77
      | ~ r1_tarski(k1_relat_1(B_77),A_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_99,plain,(
    ! [B_79,A_80] :
      ( k7_relat_1(B_79,A_80) = B_79
      | ~ v4_relat_1(B_79,A_80)
      | ~ v1_relat_1(B_79) ) ),
    inference(resolution,[status(thm)],[c_4,c_94])).

tff(c_102,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_87,c_99])).

tff(c_105,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_102])).

tff(c_219,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_105])).

tff(c_395,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_219])).

tff(c_407,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_395])).

tff(c_34,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_218,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_34])).

tff(c_412,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_218])).

tff(c_422,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_344,c_412])).

tff(c_425,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_221,c_422])).

tff(c_427,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_343,c_425])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:45:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.44  
% 2.94/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.44  %$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.94/1.44  
% 2.94/1.44  %Foreground sorts:
% 2.94/1.44  
% 2.94/1.44  
% 2.94/1.44  %Background operators:
% 2.94/1.44  
% 2.94/1.44  
% 2.94/1.44  %Foreground operators:
% 2.94/1.44  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.94/1.44  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.94/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.94/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.94/1.44  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.94/1.44  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.94/1.44  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.94/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.94/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.94/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.94/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.94/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.94/1.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.94/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.94/1.44  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.94/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.94/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.94/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.94/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.94/1.44  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 2.94/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.94/1.44  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.94/1.44  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.94/1.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.94/1.44  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.94/1.44  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.94/1.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.94/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.94/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.94/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.94/1.44  
% 2.94/1.46  tff(f_167, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_tmap_1)).
% 2.94/1.46  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.94/1.46  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.94/1.46  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.94/1.46  tff(f_85, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 2.94/1.46  tff(f_107, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 2.94/1.46  tff(f_76, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.94/1.46  tff(f_53, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.94/1.46  tff(f_134, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 2.94/1.46  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.94/1.46  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.94/1.46  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.94/1.46  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.94/1.46  tff(c_54, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.94/1.46  tff(c_16, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.94/1.46  tff(c_58, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.94/1.46  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.94/1.46  tff(c_44, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.94/1.46  tff(c_60, plain, (![B_60, A_61]: (l1_pre_topc(B_60) | ~m1_pre_topc(B_60, A_61) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.94/1.46  tff(c_63, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_60])).
% 2.94/1.46  tff(c_66, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_63])).
% 2.94/1.46  tff(c_20, plain, (![A_19]: (m1_subset_1(u1_pre_topc(A_19), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_19)))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.94/1.46  tff(c_36, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.94/1.46  tff(c_114, plain, (![D_81, B_82, C_83, A_84]: (D_81=B_82 | g1_pre_topc(C_83, D_81)!=g1_pre_topc(A_84, B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(k1_zfmisc_1(A_84))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.94/1.46  tff(c_143, plain, (![B_94, A_95]: (u1_pre_topc('#skF_2')=B_94 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(A_95, B_94) | ~m1_subset_1(B_94, k1_zfmisc_1(k1_zfmisc_1(A_95))))), inference(superposition, [status(thm), theory('equality')], [c_36, c_114])).
% 2.94/1.46  tff(c_147, plain, (![A_19]: (u1_pre_topc(A_19)=u1_pre_topc('#skF_2') | g1_pre_topc(u1_struct_0(A_19), u1_pre_topc(A_19))!=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~l1_pre_topc(A_19))), inference(resolution, [status(thm)], [c_20, c_143])).
% 2.94/1.46  tff(c_161, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_147])).
% 2.94/1.46  tff(c_163, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_161])).
% 2.94/1.46  tff(c_178, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_163, c_20])).
% 2.94/1.46  tff(c_182, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_178])).
% 2.94/1.46  tff(c_174, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_3'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_36])).
% 2.94/1.46  tff(c_26, plain, (![C_25, A_21, D_26, B_22]: (C_25=A_21 | g1_pre_topc(C_25, D_26)!=g1_pre_topc(A_21, B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(k1_zfmisc_1(A_21))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.94/1.46  tff(c_193, plain, (![C_25, D_26]: (u1_struct_0('#skF_2')=C_25 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_25, D_26) | ~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_174, c_26])).
% 2.94/1.46  tff(c_201, plain, (![C_25, D_26]: (u1_struct_0('#skF_2')=C_25 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_25, D_26))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_193])).
% 2.94/1.46  tff(c_207, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_201])).
% 2.94/1.46  tff(c_42, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.94/1.46  tff(c_40, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.94/1.46  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.94/1.46  tff(c_153, plain, (![C_99, A_102, D_100, B_101, F_98]: (r1_funct_2(A_102, B_101, C_99, D_100, F_98, F_98) | ~m1_subset_1(F_98, k1_zfmisc_1(k2_zfmisc_1(C_99, D_100))) | ~v1_funct_2(F_98, C_99, D_100) | ~m1_subset_1(F_98, k1_zfmisc_1(k2_zfmisc_1(A_102, B_101))) | ~v1_funct_2(F_98, A_102, B_101) | ~v1_funct_1(F_98) | v1_xboole_0(D_100) | v1_xboole_0(B_101))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.94/1.46  tff(c_155, plain, (![A_102, B_101]: (r1_funct_2(A_102, B_101, u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_102, B_101))) | ~v1_funct_2('#skF_4', A_102, B_101) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_101))), inference(resolution, [status(thm)], [c_38, c_153])).
% 2.94/1.46  tff(c_158, plain, (![A_102, B_101]: (r1_funct_2(A_102, B_101, u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_102, B_101))) | ~v1_funct_2('#skF_4', A_102, B_101) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_101))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_155])).
% 2.94/1.46  tff(c_310, plain, (![A_102, B_101]: (r1_funct_2(A_102, B_101, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_102, B_101))) | ~v1_funct_2('#skF_4', A_102, B_101) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_101))), inference(demodulation, [status(thm), theory('equality')], [c_207, c_158])).
% 2.94/1.46  tff(c_311, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_310])).
% 2.94/1.46  tff(c_22, plain, (![A_20]: (~v1_xboole_0(u1_struct_0(A_20)) | ~l1_struct_0(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.94/1.46  tff(c_331, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_311, c_22])).
% 2.94/1.46  tff(c_334, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_58, c_331])).
% 2.94/1.46  tff(c_337, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_334])).
% 2.94/1.46  tff(c_341, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_337])).
% 2.94/1.46  tff(c_343, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_310])).
% 2.94/1.46  tff(c_222, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_207, c_40])).
% 2.94/1.46  tff(c_221, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_207, c_38])).
% 2.94/1.46  tff(c_28, plain, (![C_29, D_30, B_28, F_32, A_27]: (r1_funct_2(A_27, B_28, C_29, D_30, F_32, F_32) | ~m1_subset_1(F_32, k1_zfmisc_1(k2_zfmisc_1(C_29, D_30))) | ~v1_funct_2(F_32, C_29, D_30) | ~m1_subset_1(F_32, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~v1_funct_2(F_32, A_27, B_28) | ~v1_funct_1(F_32) | v1_xboole_0(D_30) | v1_xboole_0(B_28))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.94/1.46  tff(c_260, plain, (![A_27, B_28]: (r1_funct_2(A_27, B_28, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~v1_funct_2('#skF_4', A_27, B_28) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_28))), inference(resolution, [status(thm)], [c_221, c_28])).
% 2.94/1.46  tff(c_274, plain, (![A_27, B_28]: (r1_funct_2(A_27, B_28, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~v1_funct_2('#skF_4', A_27, B_28) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_28))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_222, c_260])).
% 2.94/1.46  tff(c_344, plain, (![A_27, B_28]: (r1_funct_2(A_27, B_28, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~v1_funct_2('#skF_4', A_27, B_28) | v1_xboole_0(B_28))), inference(negUnitSimplification, [status(thm)], [c_343, c_274])).
% 2.94/1.46  tff(c_56, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.94/1.46  tff(c_128, plain, (![A_89, B_90, C_91, D_92]: (k2_partfun1(A_89, B_90, C_91, D_92)=k7_relat_1(C_91, D_92) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))) | ~v1_funct_1(C_91))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.94/1.46  tff(c_130, plain, (![D_92]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_92)=k7_relat_1('#skF_4', D_92) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_38, c_128])).
% 2.94/1.46  tff(c_133, plain, (![D_92]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_92)=k7_relat_1('#skF_4', D_92))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_130])).
% 2.94/1.46  tff(c_217, plain, (![D_92]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', D_92)=k7_relat_1('#skF_4', D_92))), inference(demodulation, [status(thm), theory('equality')], [c_207, c_133])).
% 2.94/1.46  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.94/1.46  tff(c_50, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.94/1.46  tff(c_353, plain, (![A_129, B_130, C_131, D_132]: (k2_partfun1(u1_struct_0(A_129), u1_struct_0(B_130), C_131, u1_struct_0(D_132))=k2_tmap_1(A_129, B_130, C_131, D_132) | ~m1_pre_topc(D_132, A_129) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_129), u1_struct_0(B_130)))) | ~v1_funct_2(C_131, u1_struct_0(A_129), u1_struct_0(B_130)) | ~v1_funct_1(C_131) | ~l1_pre_topc(B_130) | ~v2_pre_topc(B_130) | v2_struct_0(B_130) | ~l1_pre_topc(A_129) | ~v2_pre_topc(A_129) | v2_struct_0(A_129))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.94/1.46  tff(c_357, plain, (![B_130, C_131, D_132]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_130), C_131, u1_struct_0(D_132))=k2_tmap_1('#skF_2', B_130, C_131, D_132) | ~m1_pre_topc(D_132, '#skF_2') | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_130)))) | ~v1_funct_2(C_131, u1_struct_0('#skF_2'), u1_struct_0(B_130)) | ~v1_funct_1(C_131) | ~l1_pre_topc(B_130) | ~v2_pre_topc(B_130) | v2_struct_0(B_130) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_207, c_353])).
% 2.94/1.46  tff(c_365, plain, (![B_130, C_131, D_132]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_130), C_131, u1_struct_0(D_132))=k2_tmap_1('#skF_2', B_130, C_131, D_132) | ~m1_pre_topc(D_132, '#skF_2') | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_130)))) | ~v1_funct_2(C_131, u1_struct_0('#skF_3'), u1_struct_0(B_130)) | ~v1_funct_1(C_131) | ~l1_pre_topc(B_130) | ~v2_pre_topc(B_130) | v2_struct_0(B_130) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_207, c_207, c_357])).
% 2.94/1.46  tff(c_377, plain, (![B_136, C_137, D_138]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_136), C_137, u1_struct_0(D_138))=k2_tmap_1('#skF_2', B_136, C_137, D_138) | ~m1_pre_topc(D_138, '#skF_2') | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_136)))) | ~v1_funct_2(C_137, u1_struct_0('#skF_3'), u1_struct_0(B_136)) | ~v1_funct_1(C_137) | ~l1_pre_topc(B_136) | ~v2_pre_topc(B_136) | v2_struct_0(B_136))), inference(negUnitSimplification, [status(thm)], [c_52, c_365])).
% 2.94/1.46  tff(c_379, plain, (![D_138]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_138))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_138) | ~m1_pre_topc(D_138, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_221, c_377])).
% 2.94/1.46  tff(c_384, plain, (![D_138]: (k7_relat_1('#skF_4', u1_struct_0(D_138))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_138) | ~m1_pre_topc(D_138, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_42, c_222, c_217, c_379])).
% 2.94/1.46  tff(c_389, plain, (![D_139]: (k7_relat_1('#skF_4', u1_struct_0(D_139))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_139) | ~m1_pre_topc(D_139, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_58, c_384])).
% 2.94/1.46  tff(c_8, plain, (![C_7, A_5, B_6]: (v1_relat_1(C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.94/1.46  tff(c_72, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_8])).
% 2.94/1.46  tff(c_83, plain, (![C_71, A_72, B_73]: (v4_relat_1(C_71, A_72) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.94/1.46  tff(c_87, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_83])).
% 2.94/1.46  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), A_1) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.94/1.46  tff(c_94, plain, (![B_77, A_78]: (k7_relat_1(B_77, A_78)=B_77 | ~r1_tarski(k1_relat_1(B_77), A_78) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.94/1.46  tff(c_99, plain, (![B_79, A_80]: (k7_relat_1(B_79, A_80)=B_79 | ~v4_relat_1(B_79, A_80) | ~v1_relat_1(B_79))), inference(resolution, [status(thm)], [c_4, c_94])).
% 2.94/1.46  tff(c_102, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_87, c_99])).
% 2.94/1.46  tff(c_105, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_102])).
% 2.94/1.46  tff(c_219, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_207, c_105])).
% 2.94/1.46  tff(c_395, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_389, c_219])).
% 2.94/1.46  tff(c_407, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_395])).
% 2.94/1.46  tff(c_34, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.94/1.46  tff(c_218, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_207, c_34])).
% 2.94/1.46  tff(c_412, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_407, c_218])).
% 2.94/1.46  tff(c_422, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_344, c_412])).
% 2.94/1.46  tff(c_425, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_222, c_221, c_422])).
% 2.94/1.46  tff(c_427, plain, $false, inference(negUnitSimplification, [status(thm)], [c_343, c_425])).
% 2.94/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.46  
% 2.94/1.46  Inference rules
% 2.94/1.46  ----------------------
% 2.94/1.46  #Ref     : 6
% 2.94/1.46  #Sup     : 68
% 2.94/1.46  #Fact    : 0
% 2.94/1.46  #Define  : 0
% 2.94/1.46  #Split   : 4
% 2.94/1.46  #Chain   : 0
% 2.94/1.46  #Close   : 0
% 2.94/1.46  
% 2.94/1.46  Ordering : KBO
% 2.94/1.46  
% 2.94/1.46  Simplification rules
% 2.94/1.46  ----------------------
% 2.94/1.46  #Subsume      : 9
% 2.94/1.46  #Demod        : 97
% 2.94/1.46  #Tautology    : 37
% 2.94/1.46  #SimpNegUnit  : 14
% 2.94/1.46  #BackRed      : 12
% 2.94/1.46  
% 2.94/1.46  #Partial instantiations: 0
% 2.94/1.46  #Strategies tried      : 1
% 2.94/1.46  
% 2.94/1.46  Timing (in seconds)
% 2.94/1.46  ----------------------
% 2.94/1.47  Preprocessing        : 0.35
% 2.94/1.47  Parsing              : 0.19
% 2.94/1.47  CNF conversion       : 0.03
% 2.94/1.47  Main loop            : 0.28
% 2.94/1.47  Inferencing          : 0.10
% 2.94/1.47  Reduction            : 0.09
% 2.94/1.47  Demodulation         : 0.06
% 2.94/1.47  BG Simplification    : 0.02
% 2.94/1.47  Subsumption          : 0.05
% 2.94/1.47  Abstraction          : 0.01
% 2.94/1.47  MUC search           : 0.00
% 2.94/1.47  Cooper               : 0.00
% 2.94/1.47  Total                : 0.68
% 2.94/1.47  Index Insertion      : 0.00
% 2.94/1.47  Index Deletion       : 0.00
% 2.94/1.47  Index Matching       : 0.00
% 2.94/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
