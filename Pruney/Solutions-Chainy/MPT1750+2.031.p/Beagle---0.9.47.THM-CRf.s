%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:55 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 370 expanded)
%              Number of leaves         :   39 ( 135 expanded)
%              Depth                    :   17
%              Number of atoms          :  212 (1515 expanded)
%              Number of equality atoms :   36 ( 395 expanded)
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

tff(f_152,negated_conjecture,(
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

tff(f_92,axiom,(
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

tff(f_119,axiom,(
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

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_12,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_34,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_14,plain,(
    ! [A_14] :
      ( m1_subset_1(u1_pre_topc(A_14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_14))))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_88,plain,(
    ! [D_68,B_69,C_70,A_71] :
      ( D_68 = B_69
      | g1_pre_topc(C_70,D_68) != g1_pre_topc(A_71,B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(k1_zfmisc_1(A_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_92,plain,(
    ! [D_68,C_70] :
      ( u1_pre_topc('#skF_2') = D_68
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_70,D_68)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_88])).

tff(c_150,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_159,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_150])).

tff(c_163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_159])).

tff(c_165,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_97,plain,(
    ! [C_72,A_73,D_74,B_75] :
      ( C_72 = A_73
      | g1_pre_topc(C_72,D_74) != g1_pre_topc(A_73,B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(k1_zfmisc_1(A_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_101,plain,(
    ! [C_72,D_74] :
      ( u1_struct_0('#skF_2') = C_72
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_72,D_74)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_97])).

tff(c_190,plain,(
    ! [C_72,D_74] :
      ( u1_struct_0('#skF_2') = C_72
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_72,D_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_101])).

tff(c_193,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_190])).

tff(c_32,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_218,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_32])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_217,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_30])).

tff(c_277,plain,(
    ! [C_104,B_108,E_105,D_107,F_106,A_103] :
      ( r1_funct_2(A_103,B_108,C_104,D_107,E_105,E_105)
      | ~ m1_subset_1(F_106,k1_zfmisc_1(k2_zfmisc_1(C_104,D_107)))
      | ~ v1_funct_2(F_106,C_104,D_107)
      | ~ v1_funct_1(F_106)
      | ~ m1_subset_1(E_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_108)))
      | ~ v1_funct_2(E_105,A_103,B_108)
      | ~ v1_funct_1(E_105)
      | v1_xboole_0(D_107)
      | v1_xboole_0(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_279,plain,(
    ! [A_103,B_108,E_105] :
      ( r1_funct_2(A_103,B_108,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),E_105,E_105)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_108)))
      | ~ v1_funct_2(E_105,A_103,B_108)
      | ~ v1_funct_1(E_105)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_108) ) ),
    inference(resolution,[status(thm)],[c_217,c_277])).

tff(c_282,plain,(
    ! [A_103,B_108,E_105] :
      ( r1_funct_2(A_103,B_108,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),E_105,E_105)
      | ~ m1_subset_1(E_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_108)))
      | ~ v1_funct_2(E_105,A_103,B_108)
      | ~ v1_funct_1(E_105)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_218,c_279])).

tff(c_304,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_282])).

tff(c_16,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0(u1_struct_0(A_15))
      | ~ l1_struct_0(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_307,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_304,c_16])).

tff(c_310,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_307])).

tff(c_313,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_310])).

tff(c_317,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_313])).

tff(c_319,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_282])).

tff(c_318,plain,(
    ! [A_103,B_108,E_105] :
      ( r1_funct_2(A_103,B_108,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),E_105,E_105)
      | ~ m1_subset_1(E_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_108)))
      | ~ v1_funct_2(E_105,A_103,B_108)
      | ~ v1_funct_1(E_105)
      | v1_xboole_0(B_108) ) ),
    inference(splitRight,[status(thm)],[c_282])).

tff(c_36,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_102,plain,(
    ! [A_76,B_77,C_78,D_79] :
      ( k2_partfun1(A_76,B_77,C_78,D_79) = k7_relat_1(C_78,D_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77)))
      | ~ v1_funct_1(C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_104,plain,(
    ! [D_79] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_79) = k7_relat_1('#skF_4',D_79)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_102])).

tff(c_107,plain,(
    ! [D_79] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_79) = k7_relat_1('#skF_4',D_79) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_104])).

tff(c_213,plain,(
    ! [D_79] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',D_79) = k7_relat_1('#skF_4',D_79) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_107])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_320,plain,(
    ! [A_114,B_115,C_116,D_117] :
      ( k2_partfun1(u1_struct_0(A_114),u1_struct_0(B_115),C_116,u1_struct_0(D_117)) = k2_tmap_1(A_114,B_115,C_116,D_117)
      | ~ m1_pre_topc(D_117,A_114)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_114),u1_struct_0(B_115))))
      | ~ v1_funct_2(C_116,u1_struct_0(A_114),u1_struct_0(B_115))
      | ~ v1_funct_1(C_116)
      | ~ l1_pre_topc(B_115)
      | ~ v2_pre_topc(B_115)
      | v2_struct_0(B_115)
      | ~ l1_pre_topc(A_114)
      | ~ v2_pre_topc(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_324,plain,(
    ! [B_115,C_116,D_117] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_115),C_116,u1_struct_0(D_117)) = k2_tmap_1('#skF_2',B_115,C_116,D_117)
      | ~ m1_pre_topc(D_117,'#skF_2')
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_115))))
      | ~ v1_funct_2(C_116,u1_struct_0('#skF_2'),u1_struct_0(B_115))
      | ~ v1_funct_1(C_116)
      | ~ l1_pre_topc(B_115)
      | ~ v2_pre_topc(B_115)
      | v2_struct_0(B_115)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_320])).

tff(c_332,plain,(
    ! [B_115,C_116,D_117] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_115),C_116,u1_struct_0(D_117)) = k2_tmap_1('#skF_2',B_115,C_116,D_117)
      | ~ m1_pre_topc(D_117,'#skF_2')
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_115))))
      | ~ v1_funct_2(C_116,u1_struct_0('#skF_3'),u1_struct_0(B_115))
      | ~ v1_funct_1(C_116)
      | ~ l1_pre_topc(B_115)
      | ~ v2_pre_topc(B_115)
      | v2_struct_0(B_115)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_193,c_193,c_324])).

tff(c_338,plain,(
    ! [B_121,C_122,D_123] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_121),C_122,u1_struct_0(D_123)) = k2_tmap_1('#skF_2',B_121,C_122,D_123)
      | ~ m1_pre_topc(D_123,'#skF_2')
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_121))))
      | ~ v1_funct_2(C_122,u1_struct_0('#skF_3'),u1_struct_0(B_121))
      | ~ v1_funct_1(C_122)
      | ~ l1_pre_topc(B_121)
      | ~ v2_pre_topc(B_121)
      | v2_struct_0(B_121) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_332])).

tff(c_340,plain,(
    ! [D_123] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_123)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_123)
      | ~ m1_pre_topc(D_123,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_217,c_338])).

tff(c_345,plain,(
    ! [D_123] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_123)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_123)
      | ~ m1_pre_topc(D_123,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_34,c_218,c_213,c_340])).

tff(c_350,plain,(
    ! [D_124] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_124)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_124)
      | ~ m1_pre_topc(D_124,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_345])).

tff(c_53,plain,(
    ! [C_56,A_57,B_58] :
      ( v1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_57,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_53])).

tff(c_64,plain,(
    ! [C_64,A_65,B_66] :
      ( v4_relat_1(C_64,A_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_68,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_64])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k7_relat_1(B_2,A_1) = B_2
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_2])).

tff(c_78,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_75])).

tff(c_215,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_78])).

tff(c_356,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_215])).

tff(c_368,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_356])).

tff(c_26,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_214,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_26])).

tff(c_373,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_214])).

tff(c_382,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_318,c_373])).

tff(c_385,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_218,c_217,c_382])).

tff(c_387,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_319,c_385])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:04:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.40  
% 2.75/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.41  %$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.75/1.41  
% 2.75/1.41  %Foreground sorts:
% 2.75/1.41  
% 2.75/1.41  
% 2.75/1.41  %Background operators:
% 2.75/1.41  
% 2.75/1.41  
% 2.75/1.41  %Foreground operators:
% 2.75/1.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.75/1.41  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.75/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.75/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.41  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.75/1.41  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.75/1.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.75/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.75/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.75/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.75/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.75/1.41  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.75/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.75/1.41  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.75/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.75/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.75/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.75/1.41  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 2.75/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.41  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.75/1.41  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.75/1.41  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.75/1.41  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.75/1.41  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.75/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.75/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.75/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.75/1.41  
% 2.75/1.42  tff(f_152, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_tmap_1)).
% 2.75/1.42  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.75/1.42  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.75/1.42  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 2.75/1.42  tff(f_92, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => r1_funct_2(A, B, C, D, E, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r1_funct_2)).
% 2.75/1.42  tff(f_63, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.75/1.42  tff(f_47, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.75/1.42  tff(f_119, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 2.75/1.42  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.75/1.42  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.75/1.42  tff(f_31, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.75/1.42  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.75/1.42  tff(c_12, plain, (![A_13]: (l1_struct_0(A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.75/1.42  tff(c_50, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.75/1.42  tff(c_34, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.75/1.42  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.75/1.42  tff(c_14, plain, (![A_14]: (m1_subset_1(u1_pre_topc(A_14), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_14)))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.75/1.42  tff(c_28, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.75/1.42  tff(c_88, plain, (![D_68, B_69, C_70, A_71]: (D_68=B_69 | g1_pre_topc(C_70, D_68)!=g1_pre_topc(A_71, B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(k1_zfmisc_1(A_71))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.75/1.42  tff(c_92, plain, (![D_68, C_70]: (u1_pre_topc('#skF_2')=D_68 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_70, D_68) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_28, c_88])).
% 2.75/1.42  tff(c_150, plain, (~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_92])).
% 2.75/1.42  tff(c_159, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_150])).
% 2.75/1.42  tff(c_163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_159])).
% 2.75/1.42  tff(c_165, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_92])).
% 2.75/1.42  tff(c_97, plain, (![C_72, A_73, D_74, B_75]: (C_72=A_73 | g1_pre_topc(C_72, D_74)!=g1_pre_topc(A_73, B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(k1_zfmisc_1(A_73))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.75/1.42  tff(c_101, plain, (![C_72, D_74]: (u1_struct_0('#skF_2')=C_72 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_72, D_74) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_28, c_97])).
% 2.75/1.42  tff(c_190, plain, (![C_72, D_74]: (u1_struct_0('#skF_2')=C_72 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_72, D_74))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_101])).
% 2.75/1.42  tff(c_193, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_190])).
% 2.75/1.42  tff(c_32, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.75/1.42  tff(c_218, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_32])).
% 2.75/1.42  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.75/1.42  tff(c_217, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_30])).
% 2.75/1.42  tff(c_277, plain, (![C_104, B_108, E_105, D_107, F_106, A_103]: (r1_funct_2(A_103, B_108, C_104, D_107, E_105, E_105) | ~m1_subset_1(F_106, k1_zfmisc_1(k2_zfmisc_1(C_104, D_107))) | ~v1_funct_2(F_106, C_104, D_107) | ~v1_funct_1(F_106) | ~m1_subset_1(E_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_108))) | ~v1_funct_2(E_105, A_103, B_108) | ~v1_funct_1(E_105) | v1_xboole_0(D_107) | v1_xboole_0(B_108))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.75/1.42  tff(c_279, plain, (![A_103, B_108, E_105]: (r1_funct_2(A_103, B_108, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), E_105, E_105) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_108))) | ~v1_funct_2(E_105, A_103, B_108) | ~v1_funct_1(E_105) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_108))), inference(resolution, [status(thm)], [c_217, c_277])).
% 2.75/1.42  tff(c_282, plain, (![A_103, B_108, E_105]: (r1_funct_2(A_103, B_108, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), E_105, E_105) | ~m1_subset_1(E_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_108))) | ~v1_funct_2(E_105, A_103, B_108) | ~v1_funct_1(E_105) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_108))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_218, c_279])).
% 2.75/1.42  tff(c_304, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_282])).
% 2.75/1.42  tff(c_16, plain, (![A_15]: (~v1_xboole_0(u1_struct_0(A_15)) | ~l1_struct_0(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.75/1.42  tff(c_307, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_304, c_16])).
% 2.75/1.42  tff(c_310, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_307])).
% 2.75/1.42  tff(c_313, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_310])).
% 2.75/1.42  tff(c_317, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_313])).
% 2.75/1.42  tff(c_319, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_282])).
% 2.75/1.42  tff(c_318, plain, (![A_103, B_108, E_105]: (r1_funct_2(A_103, B_108, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), E_105, E_105) | ~m1_subset_1(E_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_108))) | ~v1_funct_2(E_105, A_103, B_108) | ~v1_funct_1(E_105) | v1_xboole_0(B_108))), inference(splitRight, [status(thm)], [c_282])).
% 2.75/1.42  tff(c_36, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.75/1.42  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.75/1.42  tff(c_102, plain, (![A_76, B_77, C_78, D_79]: (k2_partfun1(A_76, B_77, C_78, D_79)=k7_relat_1(C_78, D_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))) | ~v1_funct_1(C_78))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.75/1.42  tff(c_104, plain, (![D_79]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_79)=k7_relat_1('#skF_4', D_79) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_102])).
% 2.75/1.42  tff(c_107, plain, (![D_79]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_79)=k7_relat_1('#skF_4', D_79))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_104])).
% 2.75/1.42  tff(c_213, plain, (![D_79]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', D_79)=k7_relat_1('#skF_4', D_79))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_107])).
% 2.75/1.42  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.75/1.42  tff(c_42, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.75/1.42  tff(c_320, plain, (![A_114, B_115, C_116, D_117]: (k2_partfun1(u1_struct_0(A_114), u1_struct_0(B_115), C_116, u1_struct_0(D_117))=k2_tmap_1(A_114, B_115, C_116, D_117) | ~m1_pre_topc(D_117, A_114) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_114), u1_struct_0(B_115)))) | ~v1_funct_2(C_116, u1_struct_0(A_114), u1_struct_0(B_115)) | ~v1_funct_1(C_116) | ~l1_pre_topc(B_115) | ~v2_pre_topc(B_115) | v2_struct_0(B_115) | ~l1_pre_topc(A_114) | ~v2_pre_topc(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.75/1.42  tff(c_324, plain, (![B_115, C_116, D_117]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_115), C_116, u1_struct_0(D_117))=k2_tmap_1('#skF_2', B_115, C_116, D_117) | ~m1_pre_topc(D_117, '#skF_2') | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_115)))) | ~v1_funct_2(C_116, u1_struct_0('#skF_2'), u1_struct_0(B_115)) | ~v1_funct_1(C_116) | ~l1_pre_topc(B_115) | ~v2_pre_topc(B_115) | v2_struct_0(B_115) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_193, c_320])).
% 2.75/1.42  tff(c_332, plain, (![B_115, C_116, D_117]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_115), C_116, u1_struct_0(D_117))=k2_tmap_1('#skF_2', B_115, C_116, D_117) | ~m1_pre_topc(D_117, '#skF_2') | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_115)))) | ~v1_funct_2(C_116, u1_struct_0('#skF_3'), u1_struct_0(B_115)) | ~v1_funct_1(C_116) | ~l1_pre_topc(B_115) | ~v2_pre_topc(B_115) | v2_struct_0(B_115) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_193, c_193, c_324])).
% 2.75/1.42  tff(c_338, plain, (![B_121, C_122, D_123]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_121), C_122, u1_struct_0(D_123))=k2_tmap_1('#skF_2', B_121, C_122, D_123) | ~m1_pre_topc(D_123, '#skF_2') | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_121)))) | ~v1_funct_2(C_122, u1_struct_0('#skF_3'), u1_struct_0(B_121)) | ~v1_funct_1(C_122) | ~l1_pre_topc(B_121) | ~v2_pre_topc(B_121) | v2_struct_0(B_121))), inference(negUnitSimplification, [status(thm)], [c_44, c_332])).
% 2.75/1.42  tff(c_340, plain, (![D_123]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_123))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_123) | ~m1_pre_topc(D_123, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_217, c_338])).
% 2.75/1.42  tff(c_345, plain, (![D_123]: (k7_relat_1('#skF_4', u1_struct_0(D_123))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_123) | ~m1_pre_topc(D_123, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_34, c_218, c_213, c_340])).
% 2.75/1.42  tff(c_350, plain, (![D_124]: (k7_relat_1('#skF_4', u1_struct_0(D_124))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_124) | ~m1_pre_topc(D_124, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_345])).
% 2.75/1.42  tff(c_53, plain, (![C_56, A_57, B_58]: (v1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.75/1.42  tff(c_57, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_53])).
% 2.75/1.42  tff(c_64, plain, (![C_64, A_65, B_66]: (v4_relat_1(C_64, A_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.75/1.42  tff(c_68, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_64])).
% 2.75/1.42  tff(c_2, plain, (![B_2, A_1]: (k7_relat_1(B_2, A_1)=B_2 | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.75/1.42  tff(c_75, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_2])).
% 2.75/1.42  tff(c_78, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_57, c_75])).
% 2.75/1.42  tff(c_215, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_193, c_78])).
% 2.75/1.42  tff(c_356, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_350, c_215])).
% 2.75/1.42  tff(c_368, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_356])).
% 2.75/1.42  tff(c_26, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.75/1.42  tff(c_214, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_26])).
% 2.75/1.42  tff(c_373, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_368, c_214])).
% 2.75/1.42  tff(c_382, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_318, c_373])).
% 2.75/1.42  tff(c_385, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_218, c_217, c_382])).
% 2.75/1.42  tff(c_387, plain, $false, inference(negUnitSimplification, [status(thm)], [c_319, c_385])).
% 2.75/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.42  
% 2.75/1.42  Inference rules
% 2.75/1.42  ----------------------
% 2.75/1.42  #Ref     : 8
% 2.75/1.42  #Sup     : 58
% 2.75/1.42  #Fact    : 0
% 2.75/1.42  #Define  : 0
% 2.75/1.42  #Split   : 5
% 2.75/1.42  #Chain   : 0
% 2.75/1.42  #Close   : 0
% 2.75/1.42  
% 2.75/1.42  Ordering : KBO
% 2.75/1.42  
% 2.75/1.42  Simplification rules
% 2.75/1.42  ----------------------
% 2.75/1.42  #Subsume      : 6
% 2.75/1.42  #Demod        : 69
% 2.75/1.42  #Tautology    : 37
% 2.75/1.42  #SimpNegUnit  : 8
% 2.75/1.42  #BackRed      : 11
% 2.75/1.42  
% 2.75/1.43  #Partial instantiations: 0
% 2.75/1.43  #Strategies tried      : 1
% 2.75/1.43  
% 2.75/1.43  Timing (in seconds)
% 2.75/1.43  ----------------------
% 2.75/1.43  Preprocessing        : 0.34
% 2.75/1.43  Parsing              : 0.19
% 2.75/1.43  CNF conversion       : 0.03
% 2.75/1.43  Main loop            : 0.30
% 2.75/1.43  Inferencing          : 0.12
% 2.75/1.43  Reduction            : 0.09
% 2.75/1.43  Demodulation         : 0.06
% 2.75/1.43  BG Simplification    : 0.02
% 2.75/1.43  Subsumption          : 0.05
% 2.75/1.43  Abstraction          : 0.01
% 2.75/1.43  MUC search           : 0.00
% 2.75/1.43  Cooper               : 0.00
% 2.75/1.43  Total                : 0.69
% 2.75/1.43  Index Insertion      : 0.00
% 2.75/1.43  Index Deletion       : 0.00
% 2.75/1.43  Index Matching       : 0.00
% 2.75/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
