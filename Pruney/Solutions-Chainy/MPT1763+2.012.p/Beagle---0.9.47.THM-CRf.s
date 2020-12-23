%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:12 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 156 expanded)
%              Number of leaves         :   33 (  73 expanded)
%              Depth                    :   11
%              Number of atoms          :  151 ( 689 expanded)
%              Number of equality atoms :   18 (  34 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_137,negated_conjecture,(
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
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(C),u1_struct_0(B))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                   => r2_funct_2(u1_struct_0(C),u1_struct_0(B),D,k3_tmap_1(A,B,C,C,D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tmap_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_102,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => k3_tmap_1(A,B,C,D,E) = k2_partfun1(u1_struct_0(C),u1_struct_0(B),E,u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

tff(c_28,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_26,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_98,plain,(
    ! [A_82,B_83,D_84] :
      ( r2_funct_2(A_82,B_83,D_84,D_84)
      | ~ m1_subset_1(D_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83)))
      | ~ v1_funct_2(D_84,A_82,B_83)
      | ~ v1_funct_1(D_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_100,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_98])).

tff(c_103,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_100])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_30,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_46,plain,(
    ! [B_64,A_65] :
      ( l1_pre_topc(B_64)
      | ~ m1_pre_topc(B_64,A_65)
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_52,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_46])).

tff(c_56,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_52])).

tff(c_20,plain,(
    ! [A_51] :
      ( m1_pre_topc(A_51,A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_4,plain,(
    ! [C_5,A_3,B_4] :
      ( v1_relat_1(C_5)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_61,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_4])).

tff(c_62,plain,(
    ! [C_69,A_70,B_71] :
      ( v4_relat_1(C_69,A_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_66,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_62])).

tff(c_72,plain,(
    ! [B_75,A_76] :
      ( k7_relat_1(B_75,A_76) = B_75
      | ~ v4_relat_1(B_75,A_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_72])).

tff(c_78,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_75])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_36,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_83,plain,(
    ! [A_77,B_78,C_79,D_80] :
      ( k2_partfun1(A_77,B_78,C_79,D_80) = k7_relat_1(C_79,D_80)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78)))
      | ~ v1_funct_1(C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_85,plain,(
    ! [D_80] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',D_80) = k7_relat_1('#skF_4',D_80)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_83])).

tff(c_88,plain,(
    ! [D_80] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',D_80) = k7_relat_1('#skF_4',D_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_85])).

tff(c_111,plain,(
    ! [B_92,A_91,C_93,E_89,D_90] :
      ( k3_tmap_1(A_91,B_92,C_93,D_90,E_89) = k2_partfun1(u1_struct_0(C_93),u1_struct_0(B_92),E_89,u1_struct_0(D_90))
      | ~ m1_pre_topc(D_90,C_93)
      | ~ m1_subset_1(E_89,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_93),u1_struct_0(B_92))))
      | ~ v1_funct_2(E_89,u1_struct_0(C_93),u1_struct_0(B_92))
      | ~ v1_funct_1(E_89)
      | ~ m1_pre_topc(D_90,A_91)
      | ~ m1_pre_topc(C_93,A_91)
      | ~ l1_pre_topc(B_92)
      | ~ v2_pre_topc(B_92)
      | v2_struct_0(B_92)
      | ~ l1_pre_topc(A_91)
      | ~ v2_pre_topc(A_91)
      | v2_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_113,plain,(
    ! [A_91,D_90] :
      ( k3_tmap_1(A_91,'#skF_2','#skF_3',D_90,'#skF_4') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_90))
      | ~ m1_pre_topc(D_90,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc(D_90,A_91)
      | ~ m1_pre_topc('#skF_3',A_91)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_91)
      | ~ v2_pre_topc(A_91)
      | v2_struct_0(A_91) ) ),
    inference(resolution,[status(thm)],[c_24,c_111])).

tff(c_116,plain,(
    ! [D_90,A_91] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_90)) = k3_tmap_1(A_91,'#skF_2','#skF_3',D_90,'#skF_4')
      | ~ m1_pre_topc(D_90,'#skF_3')
      | ~ m1_pre_topc(D_90,A_91)
      | ~ m1_pre_topc('#skF_3',A_91)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_91)
      | ~ v2_pre_topc(A_91)
      | v2_struct_0(A_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_28,c_26,c_88,c_113])).

tff(c_118,plain,(
    ! [D_94,A_95] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_94)) = k3_tmap_1(A_95,'#skF_2','#skF_3',D_94,'#skF_4')
      | ~ m1_pre_topc(D_94,'#skF_3')
      | ~ m1_pre_topc(D_94,A_95)
      | ~ m1_pre_topc('#skF_3',A_95)
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_116])).

tff(c_122,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_118])).

tff(c_126,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_30,c_78,c_122])).

tff(c_127,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_126])).

tff(c_128,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_131,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_128])).

tff(c_135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_131])).

tff(c_136,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_22,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_150,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_22])).

tff(c_153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_150])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:11:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.27  
% 2.20/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.28  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.20/1.28  
% 2.20/1.28  %Foreground sorts:
% 2.20/1.28  
% 2.20/1.28  
% 2.20/1.28  %Background operators:
% 2.20/1.28  
% 2.20/1.28  
% 2.20/1.28  %Foreground operators:
% 2.20/1.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.20/1.28  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.20/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.20/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.28  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.20/1.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.20/1.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.20/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.20/1.28  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.20/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.20/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.20/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.20/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.20/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.28  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.20/1.28  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.20/1.28  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.20/1.28  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.20/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.20/1.28  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.20/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.28  
% 2.20/1.29  tff(f_137, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), D, k3_tmap_1(A, B, C, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tmap_1)).
% 2.20/1.29  tff(f_63, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 2.20/1.29  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.20/1.29  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 2.20/1.29  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.20/1.29  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.20/1.29  tff(f_31, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.20/1.29  tff(f_47, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.20/1.29  tff(f_102, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.20/1.29  tff(c_28, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.20/1.29  tff(c_26, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.20/1.29  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.20/1.29  tff(c_98, plain, (![A_82, B_83, D_84]: (r2_funct_2(A_82, B_83, D_84, D_84) | ~m1_subset_1(D_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))) | ~v1_funct_2(D_84, A_82, B_83) | ~v1_funct_1(D_84))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.20/1.29  tff(c_100, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_98])).
% 2.20/1.29  tff(c_103, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_100])).
% 2.20/1.29  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.20/1.29  tff(c_30, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.20/1.29  tff(c_46, plain, (![B_64, A_65]: (l1_pre_topc(B_64) | ~m1_pre_topc(B_64, A_65) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.20/1.29  tff(c_52, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_46])).
% 2.20/1.29  tff(c_56, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_52])).
% 2.20/1.29  tff(c_20, plain, (![A_51]: (m1_pre_topc(A_51, A_51) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.20/1.29  tff(c_44, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.20/1.29  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.20/1.29  tff(c_4, plain, (![C_5, A_3, B_4]: (v1_relat_1(C_5) | ~m1_subset_1(C_5, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.20/1.29  tff(c_61, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_4])).
% 2.20/1.29  tff(c_62, plain, (![C_69, A_70, B_71]: (v4_relat_1(C_69, A_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.20/1.29  tff(c_66, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_62])).
% 2.20/1.29  tff(c_72, plain, (![B_75, A_76]: (k7_relat_1(B_75, A_76)=B_75 | ~v4_relat_1(B_75, A_76) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.20/1.29  tff(c_75, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_72])).
% 2.20/1.29  tff(c_78, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_61, c_75])).
% 2.20/1.29  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.20/1.29  tff(c_36, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.20/1.29  tff(c_34, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.20/1.29  tff(c_83, plain, (![A_77, B_78, C_79, D_80]: (k2_partfun1(A_77, B_78, C_79, D_80)=k7_relat_1(C_79, D_80) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))) | ~v1_funct_1(C_79))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.20/1.29  tff(c_85, plain, (![D_80]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', D_80)=k7_relat_1('#skF_4', D_80) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_83])).
% 2.20/1.29  tff(c_88, plain, (![D_80]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', D_80)=k7_relat_1('#skF_4', D_80))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_85])).
% 2.20/1.29  tff(c_111, plain, (![B_92, A_91, C_93, E_89, D_90]: (k3_tmap_1(A_91, B_92, C_93, D_90, E_89)=k2_partfun1(u1_struct_0(C_93), u1_struct_0(B_92), E_89, u1_struct_0(D_90)) | ~m1_pre_topc(D_90, C_93) | ~m1_subset_1(E_89, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_93), u1_struct_0(B_92)))) | ~v1_funct_2(E_89, u1_struct_0(C_93), u1_struct_0(B_92)) | ~v1_funct_1(E_89) | ~m1_pre_topc(D_90, A_91) | ~m1_pre_topc(C_93, A_91) | ~l1_pre_topc(B_92) | ~v2_pre_topc(B_92) | v2_struct_0(B_92) | ~l1_pre_topc(A_91) | ~v2_pre_topc(A_91) | v2_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.20/1.29  tff(c_113, plain, (![A_91, D_90]: (k3_tmap_1(A_91, '#skF_2', '#skF_3', D_90, '#skF_4')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_90)) | ~m1_pre_topc(D_90, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc(D_90, A_91) | ~m1_pre_topc('#skF_3', A_91) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_91) | ~v2_pre_topc(A_91) | v2_struct_0(A_91))), inference(resolution, [status(thm)], [c_24, c_111])).
% 2.20/1.29  tff(c_116, plain, (![D_90, A_91]: (k7_relat_1('#skF_4', u1_struct_0(D_90))=k3_tmap_1(A_91, '#skF_2', '#skF_3', D_90, '#skF_4') | ~m1_pre_topc(D_90, '#skF_3') | ~m1_pre_topc(D_90, A_91) | ~m1_pre_topc('#skF_3', A_91) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_91) | ~v2_pre_topc(A_91) | v2_struct_0(A_91))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_28, c_26, c_88, c_113])).
% 2.20/1.29  tff(c_118, plain, (![D_94, A_95]: (k7_relat_1('#skF_4', u1_struct_0(D_94))=k3_tmap_1(A_95, '#skF_2', '#skF_3', D_94, '#skF_4') | ~m1_pre_topc(D_94, '#skF_3') | ~m1_pre_topc(D_94, A_95) | ~m1_pre_topc('#skF_3', A_95) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95) | v2_struct_0(A_95))), inference(negUnitSimplification, [status(thm)], [c_38, c_116])).
% 2.20/1.29  tff(c_122, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_118])).
% 2.20/1.29  tff(c_126, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_30, c_78, c_122])).
% 2.20/1.29  tff(c_127, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_44, c_126])).
% 2.20/1.29  tff(c_128, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_127])).
% 2.20/1.29  tff(c_131, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_128])).
% 2.20/1.29  tff(c_135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_131])).
% 2.20/1.29  tff(c_136, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_127])).
% 2.20/1.29  tff(c_22, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.20/1.29  tff(c_150, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_22])).
% 2.20/1.29  tff(c_153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_150])).
% 2.20/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.29  
% 2.20/1.29  Inference rules
% 2.20/1.29  ----------------------
% 2.20/1.29  #Ref     : 0
% 2.20/1.29  #Sup     : 19
% 2.20/1.29  #Fact    : 0
% 2.20/1.29  #Define  : 0
% 2.20/1.29  #Split   : 1
% 2.20/1.29  #Chain   : 0
% 2.20/1.29  #Close   : 0
% 2.20/1.29  
% 2.20/1.29  Ordering : KBO
% 2.20/1.29  
% 2.20/1.29  Simplification rules
% 2.20/1.29  ----------------------
% 2.20/1.29  #Subsume      : 0
% 2.20/1.29  #Demod        : 25
% 2.20/1.29  #Tautology    : 7
% 2.20/1.29  #SimpNegUnit  : 3
% 2.20/1.29  #BackRed      : 1
% 2.20/1.29  
% 2.20/1.29  #Partial instantiations: 0
% 2.20/1.29  #Strategies tried      : 1
% 2.20/1.29  
% 2.20/1.29  Timing (in seconds)
% 2.20/1.29  ----------------------
% 2.20/1.30  Preprocessing        : 0.35
% 2.20/1.30  Parsing              : 0.18
% 2.20/1.30  CNF conversion       : 0.03
% 2.20/1.30  Main loop            : 0.18
% 2.20/1.30  Inferencing          : 0.06
% 2.20/1.30  Reduction            : 0.06
% 2.20/1.30  Demodulation         : 0.04
% 2.20/1.30  BG Simplification    : 0.01
% 2.20/1.30  Subsumption          : 0.03
% 2.20/1.30  Abstraction          : 0.01
% 2.20/1.30  MUC search           : 0.00
% 2.20/1.30  Cooper               : 0.00
% 2.20/1.30  Total                : 0.56
% 2.20/1.30  Index Insertion      : 0.00
% 2.20/1.30  Index Deletion       : 0.00
% 2.20/1.30  Index Matching       : 0.00
% 2.20/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
