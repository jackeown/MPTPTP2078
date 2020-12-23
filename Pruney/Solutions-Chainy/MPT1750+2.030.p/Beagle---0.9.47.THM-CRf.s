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
% DateTime   : Thu Dec  3 10:26:55 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 272 expanded)
%              Number of leaves         :   39 ( 102 expanded)
%              Depth                    :   16
%              Number of atoms          :  201 (1093 expanded)
%              Number of equality atoms :   33 ( 253 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_154,negated_conjecture,(
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

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_94,axiom,(
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

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_121,axiom,(
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

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_12,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_36,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_14,plain,(
    ! [A_14] :
      ( m1_subset_1(u1_pre_topc(A_14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_14))))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_30,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_90,plain,(
    ! [C_68,A_69,D_70,B_71] :
      ( C_68 = A_69
      | g1_pre_topc(C_68,D_70) != g1_pre_topc(A_69,B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k1_zfmisc_1(A_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_94,plain,(
    ! [C_68,D_70] :
      ( u1_struct_0('#skF_2') = C_68
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_68,D_70)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_90])).

tff(c_152,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_161,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_152])).

tff(c_165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_161])).

tff(c_166,plain,(
    ! [C_68,D_70] :
      ( u1_struct_0('#skF_2') = C_68
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_68,D_70) ) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_184,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_166])).

tff(c_34,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_210,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_34])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_209,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_32])).

tff(c_22,plain,(
    ! [F_27,A_22,B_23,D_25,C_24] :
      ( r1_funct_2(A_22,B_23,C_24,D_25,F_27,F_27)
      | ~ m1_subset_1(F_27,k1_zfmisc_1(k2_zfmisc_1(C_24,D_25)))
      | ~ v1_funct_2(F_27,C_24,D_25)
      | ~ m1_subset_1(F_27,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_2(F_27,A_22,B_23)
      | ~ v1_funct_1(F_27)
      | v1_xboole_0(D_25)
      | v1_xboole_0(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_260,plain,(
    ! [A_22,B_23] :
      ( r1_funct_2(A_22,B_23,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_2('#skF_4',A_22,B_23)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_23) ) ),
    inference(resolution,[status(thm)],[c_209,c_22])).

tff(c_274,plain,(
    ! [A_22,B_23] :
      ( r1_funct_2(A_22,B_23,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_2('#skF_4',A_22,B_23)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_210,c_260])).

tff(c_306,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_274])).

tff(c_16,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0(u1_struct_0(A_15))
      | ~ l1_struct_0(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_309,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_306,c_16])).

tff(c_312,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_309])).

tff(c_315,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_312])).

tff(c_319,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_315])).

tff(c_321,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_274])).

tff(c_320,plain,(
    ! [A_22,B_23] :
      ( r1_funct_2(A_22,B_23,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_2('#skF_4',A_22,B_23)
      | v1_xboole_0(B_23) ) ),
    inference(splitRight,[status(thm)],[c_274])).

tff(c_38,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_50,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_104,plain,(
    ! [A_76,B_77,C_78,D_79] :
      ( k2_partfun1(A_76,B_77,C_78,D_79) = k7_relat_1(C_78,D_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77)))
      | ~ v1_funct_1(C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_106,plain,(
    ! [D_79] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_79) = k7_relat_1('#skF_4',D_79)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_104])).

tff(c_109,plain,(
    ! [D_79] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_79) = k7_relat_1('#skF_4',D_79) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_106])).

tff(c_204,plain,(
    ! [D_79] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',D_79) = k7_relat_1('#skF_4',D_79) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_109])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_44,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_322,plain,(
    ! [A_112,B_113,C_114,D_115] :
      ( k2_partfun1(u1_struct_0(A_112),u1_struct_0(B_113),C_114,u1_struct_0(D_115)) = k2_tmap_1(A_112,B_113,C_114,D_115)
      | ~ m1_pre_topc(D_115,A_112)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_112),u1_struct_0(B_113))))
      | ~ v1_funct_2(C_114,u1_struct_0(A_112),u1_struct_0(B_113))
      | ~ v1_funct_1(C_114)
      | ~ l1_pre_topc(B_113)
      | ~ v2_pre_topc(B_113)
      | v2_struct_0(B_113)
      | ~ l1_pre_topc(A_112)
      | ~ v2_pre_topc(A_112)
      | v2_struct_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_326,plain,(
    ! [B_113,C_114,D_115] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_113),C_114,u1_struct_0(D_115)) = k2_tmap_1('#skF_2',B_113,C_114,D_115)
      | ~ m1_pre_topc(D_115,'#skF_2')
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_113))))
      | ~ v1_funct_2(C_114,u1_struct_0('#skF_2'),u1_struct_0(B_113))
      | ~ v1_funct_1(C_114)
      | ~ l1_pre_topc(B_113)
      | ~ v2_pre_topc(B_113)
      | v2_struct_0(B_113)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_322])).

tff(c_334,plain,(
    ! [B_113,C_114,D_115] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_113),C_114,u1_struct_0(D_115)) = k2_tmap_1('#skF_2',B_113,C_114,D_115)
      | ~ m1_pre_topc(D_115,'#skF_2')
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_113))))
      | ~ v1_funct_2(C_114,u1_struct_0('#skF_3'),u1_struct_0(B_113))
      | ~ v1_funct_1(C_114)
      | ~ l1_pre_topc(B_113)
      | ~ v2_pre_topc(B_113)
      | v2_struct_0(B_113)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_184,c_184,c_326])).

tff(c_347,plain,(
    ! [B_118,C_119,D_120] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_118),C_119,u1_struct_0(D_120)) = k2_tmap_1('#skF_2',B_118,C_119,D_120)
      | ~ m1_pre_topc(D_120,'#skF_2')
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_118))))
      | ~ v1_funct_2(C_119,u1_struct_0('#skF_3'),u1_struct_0(B_118))
      | ~ v1_funct_1(C_119)
      | ~ l1_pre_topc(B_118)
      | ~ v2_pre_topc(B_118)
      | v2_struct_0(B_118) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_334])).

tff(c_349,plain,(
    ! [D_120] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_120)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_120)
      | ~ m1_pre_topc(D_120,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_209,c_347])).

tff(c_354,plain,(
    ! [D_120] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_120)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_120)
      | ~ m1_pre_topc(D_120,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_36,c_210,c_204,c_349])).

tff(c_359,plain,(
    ! [D_121] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_121)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_121)
      | ~ m1_pre_topc(D_121,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_354])).

tff(c_55,plain,(
    ! [C_56,A_57,B_58] :
      ( v1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_59,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_55])).

tff(c_60,plain,(
    ! [C_59,A_60,B_61] :
      ( v4_relat_1(C_59,A_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_64,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_60])).

tff(c_75,plain,(
    ! [B_66,A_67] :
      ( k7_relat_1(B_66,A_67) = B_66
      | ~ v4_relat_1(B_66,A_67)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_78,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_75])).

tff(c_81,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_78])).

tff(c_206,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_81])).

tff(c_365,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_206])).

tff(c_377,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_365])).

tff(c_28,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_205,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_28])).

tff(c_382,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_205])).

tff(c_391,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_320,c_382])).

tff(c_394,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_209,c_391])).

tff(c_396,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_321,c_394])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:51:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.35  
% 2.45/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.35  %$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.45/1.35  
% 2.45/1.35  %Foreground sorts:
% 2.45/1.35  
% 2.45/1.35  
% 2.45/1.35  %Background operators:
% 2.45/1.35  
% 2.45/1.35  
% 2.45/1.35  %Foreground operators:
% 2.45/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.45/1.35  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.45/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.45/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.35  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.45/1.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.45/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.45/1.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.45/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.45/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.45/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.45/1.35  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.45/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.45/1.35  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.45/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.45/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.45/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.45/1.35  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 2.45/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.35  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.45/1.35  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.45/1.35  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.45/1.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.45/1.35  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.45/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.45/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.45/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.45/1.35  
% 2.75/1.37  tff(f_154, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_tmap_1)).
% 2.75/1.37  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.75/1.37  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.75/1.37  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 2.75/1.37  tff(f_94, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 2.75/1.37  tff(f_63, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.75/1.37  tff(f_47, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.75/1.37  tff(f_121, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 2.75/1.37  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.75/1.37  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.75/1.37  tff(f_31, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.75/1.37  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.75/1.37  tff(c_12, plain, (![A_13]: (l1_struct_0(A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.75/1.37  tff(c_52, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.75/1.37  tff(c_36, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.75/1.37  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.75/1.37  tff(c_14, plain, (![A_14]: (m1_subset_1(u1_pre_topc(A_14), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_14)))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.75/1.37  tff(c_30, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.75/1.37  tff(c_90, plain, (![C_68, A_69, D_70, B_71]: (C_68=A_69 | g1_pre_topc(C_68, D_70)!=g1_pre_topc(A_69, B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(k1_zfmisc_1(A_69))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.75/1.37  tff(c_94, plain, (![C_68, D_70]: (u1_struct_0('#skF_2')=C_68 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_68, D_70) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_30, c_90])).
% 2.75/1.37  tff(c_152, plain, (~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_94])).
% 2.75/1.37  tff(c_161, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_152])).
% 2.75/1.37  tff(c_165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_161])).
% 2.75/1.37  tff(c_166, plain, (![C_68, D_70]: (u1_struct_0('#skF_2')=C_68 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_68, D_70))), inference(splitRight, [status(thm)], [c_94])).
% 2.75/1.37  tff(c_184, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_166])).
% 2.75/1.37  tff(c_34, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.75/1.37  tff(c_210, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_34])).
% 2.75/1.37  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.75/1.37  tff(c_209, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_32])).
% 2.75/1.37  tff(c_22, plain, (![F_27, A_22, B_23, D_25, C_24]: (r1_funct_2(A_22, B_23, C_24, D_25, F_27, F_27) | ~m1_subset_1(F_27, k1_zfmisc_1(k2_zfmisc_1(C_24, D_25))) | ~v1_funct_2(F_27, C_24, D_25) | ~m1_subset_1(F_27, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_2(F_27, A_22, B_23) | ~v1_funct_1(F_27) | v1_xboole_0(D_25) | v1_xboole_0(B_23))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.75/1.37  tff(c_260, plain, (![A_22, B_23]: (r1_funct_2(A_22, B_23, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_2('#skF_4', A_22, B_23) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_23))), inference(resolution, [status(thm)], [c_209, c_22])).
% 2.75/1.37  tff(c_274, plain, (![A_22, B_23]: (r1_funct_2(A_22, B_23, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_2('#skF_4', A_22, B_23) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_23))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_210, c_260])).
% 2.75/1.37  tff(c_306, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_274])).
% 2.75/1.37  tff(c_16, plain, (![A_15]: (~v1_xboole_0(u1_struct_0(A_15)) | ~l1_struct_0(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.75/1.37  tff(c_309, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_306, c_16])).
% 2.75/1.37  tff(c_312, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_309])).
% 2.75/1.37  tff(c_315, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_312])).
% 2.75/1.37  tff(c_319, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_315])).
% 2.75/1.37  tff(c_321, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_274])).
% 2.75/1.37  tff(c_320, plain, (![A_22, B_23]: (r1_funct_2(A_22, B_23, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_2('#skF_4', A_22, B_23) | v1_xboole_0(B_23))), inference(splitRight, [status(thm)], [c_274])).
% 2.75/1.37  tff(c_38, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.75/1.37  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.75/1.37  tff(c_104, plain, (![A_76, B_77, C_78, D_79]: (k2_partfun1(A_76, B_77, C_78, D_79)=k7_relat_1(C_78, D_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))) | ~v1_funct_1(C_78))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.75/1.37  tff(c_106, plain, (![D_79]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_79)=k7_relat_1('#skF_4', D_79) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_32, c_104])).
% 2.75/1.37  tff(c_109, plain, (![D_79]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_79)=k7_relat_1('#skF_4', D_79))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_106])).
% 2.75/1.37  tff(c_204, plain, (![D_79]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', D_79)=k7_relat_1('#skF_4', D_79))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_109])).
% 2.75/1.37  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.75/1.37  tff(c_44, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.75/1.37  tff(c_322, plain, (![A_112, B_113, C_114, D_115]: (k2_partfun1(u1_struct_0(A_112), u1_struct_0(B_113), C_114, u1_struct_0(D_115))=k2_tmap_1(A_112, B_113, C_114, D_115) | ~m1_pre_topc(D_115, A_112) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_112), u1_struct_0(B_113)))) | ~v1_funct_2(C_114, u1_struct_0(A_112), u1_struct_0(B_113)) | ~v1_funct_1(C_114) | ~l1_pre_topc(B_113) | ~v2_pre_topc(B_113) | v2_struct_0(B_113) | ~l1_pre_topc(A_112) | ~v2_pre_topc(A_112) | v2_struct_0(A_112))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.75/1.37  tff(c_326, plain, (![B_113, C_114, D_115]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_113), C_114, u1_struct_0(D_115))=k2_tmap_1('#skF_2', B_113, C_114, D_115) | ~m1_pre_topc(D_115, '#skF_2') | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_113)))) | ~v1_funct_2(C_114, u1_struct_0('#skF_2'), u1_struct_0(B_113)) | ~v1_funct_1(C_114) | ~l1_pre_topc(B_113) | ~v2_pre_topc(B_113) | v2_struct_0(B_113) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_184, c_322])).
% 2.75/1.37  tff(c_334, plain, (![B_113, C_114, D_115]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_113), C_114, u1_struct_0(D_115))=k2_tmap_1('#skF_2', B_113, C_114, D_115) | ~m1_pre_topc(D_115, '#skF_2') | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_113)))) | ~v1_funct_2(C_114, u1_struct_0('#skF_3'), u1_struct_0(B_113)) | ~v1_funct_1(C_114) | ~l1_pre_topc(B_113) | ~v2_pre_topc(B_113) | v2_struct_0(B_113) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_184, c_184, c_326])).
% 2.75/1.37  tff(c_347, plain, (![B_118, C_119, D_120]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_118), C_119, u1_struct_0(D_120))=k2_tmap_1('#skF_2', B_118, C_119, D_120) | ~m1_pre_topc(D_120, '#skF_2') | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_118)))) | ~v1_funct_2(C_119, u1_struct_0('#skF_3'), u1_struct_0(B_118)) | ~v1_funct_1(C_119) | ~l1_pre_topc(B_118) | ~v2_pre_topc(B_118) | v2_struct_0(B_118))), inference(negUnitSimplification, [status(thm)], [c_46, c_334])).
% 2.75/1.37  tff(c_349, plain, (![D_120]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_120))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_120) | ~m1_pre_topc(D_120, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_209, c_347])).
% 2.75/1.37  tff(c_354, plain, (![D_120]: (k7_relat_1('#skF_4', u1_struct_0(D_120))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_120) | ~m1_pre_topc(D_120, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_36, c_210, c_204, c_349])).
% 2.75/1.37  tff(c_359, plain, (![D_121]: (k7_relat_1('#skF_4', u1_struct_0(D_121))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_121) | ~m1_pre_topc(D_121, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_354])).
% 2.75/1.37  tff(c_55, plain, (![C_56, A_57, B_58]: (v1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.75/1.37  tff(c_59, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_55])).
% 2.75/1.37  tff(c_60, plain, (![C_59, A_60, B_61]: (v4_relat_1(C_59, A_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.75/1.37  tff(c_64, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_60])).
% 2.75/1.37  tff(c_75, plain, (![B_66, A_67]: (k7_relat_1(B_66, A_67)=B_66 | ~v4_relat_1(B_66, A_67) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.75/1.37  tff(c_78, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_75])).
% 2.75/1.37  tff(c_81, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_59, c_78])).
% 2.75/1.37  tff(c_206, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_184, c_81])).
% 2.75/1.37  tff(c_365, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_359, c_206])).
% 2.75/1.37  tff(c_377, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_365])).
% 2.75/1.37  tff(c_28, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.75/1.37  tff(c_205, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_28])).
% 2.75/1.37  tff(c_382, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_377, c_205])).
% 2.75/1.37  tff(c_391, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_320, c_382])).
% 2.75/1.37  tff(c_394, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_209, c_391])).
% 2.75/1.37  tff(c_396, plain, $false, inference(negUnitSimplification, [status(thm)], [c_321, c_394])).
% 2.75/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.37  
% 2.75/1.37  Inference rules
% 2.75/1.37  ----------------------
% 2.75/1.37  #Ref     : 8
% 2.75/1.37  #Sup     : 59
% 2.75/1.37  #Fact    : 0
% 2.75/1.37  #Define  : 0
% 2.75/1.37  #Split   : 5
% 2.75/1.37  #Chain   : 0
% 2.75/1.37  #Close   : 0
% 2.75/1.37  
% 2.75/1.37  Ordering : KBO
% 2.75/1.37  
% 2.75/1.37  Simplification rules
% 2.75/1.37  ----------------------
% 2.75/1.37  #Subsume      : 6
% 2.75/1.37  #Demod        : 71
% 2.75/1.37  #Tautology    : 38
% 2.75/1.37  #SimpNegUnit  : 9
% 2.75/1.37  #BackRed      : 11
% 2.75/1.37  
% 2.75/1.37  #Partial instantiations: 0
% 2.75/1.37  #Strategies tried      : 1
% 2.75/1.37  
% 2.75/1.37  Timing (in seconds)
% 2.75/1.37  ----------------------
% 2.75/1.37  Preprocessing        : 0.35
% 2.75/1.37  Parsing              : 0.19
% 2.75/1.37  CNF conversion       : 0.02
% 2.75/1.37  Main loop            : 0.25
% 2.75/1.37  Inferencing          : 0.09
% 2.75/1.37  Reduction            : 0.08
% 2.75/1.37  Demodulation         : 0.06
% 2.75/1.37  BG Simplification    : 0.02
% 2.75/1.37  Subsumption          : 0.04
% 2.75/1.37  Abstraction          : 0.01
% 2.75/1.38  MUC search           : 0.00
% 2.75/1.38  Cooper               : 0.00
% 2.75/1.38  Total                : 0.64
% 2.75/1.38  Index Insertion      : 0.00
% 2.75/1.38  Index Deletion       : 0.00
% 2.75/1.38  Index Matching       : 0.00
% 2.75/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
