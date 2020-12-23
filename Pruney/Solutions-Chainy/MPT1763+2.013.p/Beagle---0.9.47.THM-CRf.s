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
% DateTime   : Thu Dec  3 10:27:12 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 164 expanded)
%              Number of leaves         :   33 (  76 expanded)
%              Depth                    :   11
%              Number of atoms          :  163 ( 740 expanded)
%              Number of equality atoms :   17 (  33 expanded)
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

tff(f_135,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tmap_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

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

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_100,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

tff(c_26,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_24,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_96,plain,(
    ! [A_82,B_83,C_84,D_85] :
      ( r2_funct_2(A_82,B_83,C_84,C_84)
      | ~ m1_subset_1(D_85,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83)))
      | ~ v1_funct_2(D_85,A_82,B_83)
      | ~ v1_funct_1(D_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83)))
      | ~ v1_funct_2(C_84,A_82,B_83)
      | ~ v1_funct_1(C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_98,plain,(
    ! [C_84] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_84,C_84)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_84,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_84) ) ),
    inference(resolution,[status(thm)],[c_22,c_96])).

tff(c_102,plain,(
    ! [C_86] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_86,C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_86,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_98])).

tff(c_104,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_102])).

tff(c_107,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_104])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_28,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_44,plain,(
    ! [B_64,A_65] :
      ( l1_pre_topc(B_64)
      | ~ m1_pre_topc(B_64,A_65)
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_50,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_44])).

tff(c_54,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_50])).

tff(c_18,plain,(
    ! [A_51] :
      ( m1_pre_topc(A_51,A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_40,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_4,plain,(
    ! [C_5,A_3,B_4] :
      ( v1_relat_1(C_5)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_59,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_4])).

tff(c_60,plain,(
    ! [C_69,A_70,B_71] :
      ( v4_relat_1(C_69,A_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_64,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_60])).

tff(c_70,plain,(
    ! [B_75,A_76] :
      ( k7_relat_1(B_75,A_76) = B_75
      | ~ v4_relat_1(B_75,A_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_73,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_70])).

tff(c_76,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_73])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_34,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_81,plain,(
    ! [A_77,B_78,C_79,D_80] :
      ( k2_partfun1(A_77,B_78,C_79,D_80) = k7_relat_1(C_79,D_80)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78)))
      | ~ v1_funct_1(C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_83,plain,(
    ! [D_80] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',D_80) = k7_relat_1('#skF_4',D_80)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_81])).

tff(c_86,plain,(
    ! [D_80] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',D_80) = k7_relat_1('#skF_4',D_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_83])).

tff(c_108,plain,(
    ! [D_88,E_87,C_91,A_89,B_90] :
      ( k3_tmap_1(A_89,B_90,C_91,D_88,E_87) = k2_partfun1(u1_struct_0(C_91),u1_struct_0(B_90),E_87,u1_struct_0(D_88))
      | ~ m1_pre_topc(D_88,C_91)
      | ~ m1_subset_1(E_87,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_91),u1_struct_0(B_90))))
      | ~ v1_funct_2(E_87,u1_struct_0(C_91),u1_struct_0(B_90))
      | ~ v1_funct_1(E_87)
      | ~ m1_pre_topc(D_88,A_89)
      | ~ m1_pre_topc(C_91,A_89)
      | ~ l1_pre_topc(B_90)
      | ~ v2_pre_topc(B_90)
      | v2_struct_0(B_90)
      | ~ l1_pre_topc(A_89)
      | ~ v2_pre_topc(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_110,plain,(
    ! [A_89,D_88] :
      ( k3_tmap_1(A_89,'#skF_2','#skF_3',D_88,'#skF_4') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_88))
      | ~ m1_pre_topc(D_88,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc(D_88,A_89)
      | ~ m1_pre_topc('#skF_3',A_89)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_89)
      | ~ v2_pre_topc(A_89)
      | v2_struct_0(A_89) ) ),
    inference(resolution,[status(thm)],[c_22,c_108])).

tff(c_113,plain,(
    ! [D_88,A_89] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_88)) = k3_tmap_1(A_89,'#skF_2','#skF_3',D_88,'#skF_4')
      | ~ m1_pre_topc(D_88,'#skF_3')
      | ~ m1_pre_topc(D_88,A_89)
      | ~ m1_pre_topc('#skF_3',A_89)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_89)
      | ~ v2_pre_topc(A_89)
      | v2_struct_0(A_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_24,c_86,c_110])).

tff(c_115,plain,(
    ! [D_92,A_93] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_92)) = k3_tmap_1(A_93,'#skF_2','#skF_3',D_92,'#skF_4')
      | ~ m1_pre_topc(D_92,'#skF_3')
      | ~ m1_pre_topc(D_92,A_93)
      | ~ m1_pre_topc('#skF_3',A_93)
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_113])).

tff(c_119,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_115])).

tff(c_123,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_28,c_76,c_119])).

tff(c_124,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_123])).

tff(c_125,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_128,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_125])).

tff(c_132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_128])).

tff(c_133,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_20,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_147,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_20])).

tff(c_150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_147])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:22:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.32  
% 1.93/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.32  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.93/1.32  
% 1.93/1.32  %Foreground sorts:
% 1.93/1.32  
% 1.93/1.32  
% 1.93/1.32  %Background operators:
% 1.93/1.32  
% 1.93/1.32  
% 1.93/1.32  %Foreground operators:
% 1.93/1.32  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.93/1.32  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 1.93/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.93/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.32  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.93/1.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.93/1.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.93/1.32  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.32  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.32  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.32  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.93/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.93/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.93/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.93/1.32  tff('#skF_4', type, '#skF_4': $i).
% 1.93/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.32  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 1.93/1.32  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 1.93/1.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.93/1.32  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.93/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.93/1.32  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 1.93/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.93/1.32  
% 2.26/1.34  tff(f_135, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), D, k3_tmap_1(A, B, C, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tmap_1)).
% 2.26/1.34  tff(f_61, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 2.26/1.34  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.26/1.34  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 2.26/1.34  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.26/1.34  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.26/1.34  tff(f_31, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.26/1.34  tff(f_47, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.26/1.34  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.26/1.34  tff(c_26, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.26/1.34  tff(c_24, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.26/1.34  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.26/1.34  tff(c_96, plain, (![A_82, B_83, C_84, D_85]: (r2_funct_2(A_82, B_83, C_84, C_84) | ~m1_subset_1(D_85, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))) | ~v1_funct_2(D_85, A_82, B_83) | ~v1_funct_1(D_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))) | ~v1_funct_2(C_84, A_82, B_83) | ~v1_funct_1(C_84))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.26/1.34  tff(c_98, plain, (![C_84]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_84, C_84) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_84, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_84))), inference(resolution, [status(thm)], [c_22, c_96])).
% 2.26/1.34  tff(c_102, plain, (![C_86]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_86, C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_86, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_86))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_98])).
% 2.26/1.34  tff(c_104, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_102])).
% 2.26/1.34  tff(c_107, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_104])).
% 2.26/1.34  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.26/1.34  tff(c_28, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.26/1.34  tff(c_44, plain, (![B_64, A_65]: (l1_pre_topc(B_64) | ~m1_pre_topc(B_64, A_65) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.26/1.34  tff(c_50, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_44])).
% 2.26/1.34  tff(c_54, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_50])).
% 2.26/1.34  tff(c_18, plain, (![A_51]: (m1_pre_topc(A_51, A_51) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.26/1.34  tff(c_42, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.26/1.34  tff(c_40, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.26/1.34  tff(c_4, plain, (![C_5, A_3, B_4]: (v1_relat_1(C_5) | ~m1_subset_1(C_5, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.26/1.34  tff(c_59, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_4])).
% 2.26/1.34  tff(c_60, plain, (![C_69, A_70, B_71]: (v4_relat_1(C_69, A_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.26/1.34  tff(c_64, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_60])).
% 2.26/1.34  tff(c_70, plain, (![B_75, A_76]: (k7_relat_1(B_75, A_76)=B_75 | ~v4_relat_1(B_75, A_76) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.26/1.34  tff(c_73, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_70])).
% 2.26/1.34  tff(c_76, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_59, c_73])).
% 2.26/1.34  tff(c_36, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.26/1.34  tff(c_34, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.26/1.34  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.26/1.34  tff(c_81, plain, (![A_77, B_78, C_79, D_80]: (k2_partfun1(A_77, B_78, C_79, D_80)=k7_relat_1(C_79, D_80) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))) | ~v1_funct_1(C_79))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.26/1.34  tff(c_83, plain, (![D_80]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', D_80)=k7_relat_1('#skF_4', D_80) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_22, c_81])).
% 2.26/1.34  tff(c_86, plain, (![D_80]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', D_80)=k7_relat_1('#skF_4', D_80))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_83])).
% 2.26/1.34  tff(c_108, plain, (![D_88, E_87, C_91, A_89, B_90]: (k3_tmap_1(A_89, B_90, C_91, D_88, E_87)=k2_partfun1(u1_struct_0(C_91), u1_struct_0(B_90), E_87, u1_struct_0(D_88)) | ~m1_pre_topc(D_88, C_91) | ~m1_subset_1(E_87, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_91), u1_struct_0(B_90)))) | ~v1_funct_2(E_87, u1_struct_0(C_91), u1_struct_0(B_90)) | ~v1_funct_1(E_87) | ~m1_pre_topc(D_88, A_89) | ~m1_pre_topc(C_91, A_89) | ~l1_pre_topc(B_90) | ~v2_pre_topc(B_90) | v2_struct_0(B_90) | ~l1_pre_topc(A_89) | ~v2_pre_topc(A_89) | v2_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.26/1.34  tff(c_110, plain, (![A_89, D_88]: (k3_tmap_1(A_89, '#skF_2', '#skF_3', D_88, '#skF_4')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_88)) | ~m1_pre_topc(D_88, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc(D_88, A_89) | ~m1_pre_topc('#skF_3', A_89) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_89) | ~v2_pre_topc(A_89) | v2_struct_0(A_89))), inference(resolution, [status(thm)], [c_22, c_108])).
% 2.26/1.34  tff(c_113, plain, (![D_88, A_89]: (k7_relat_1('#skF_4', u1_struct_0(D_88))=k3_tmap_1(A_89, '#skF_2', '#skF_3', D_88, '#skF_4') | ~m1_pre_topc(D_88, '#skF_3') | ~m1_pre_topc(D_88, A_89) | ~m1_pre_topc('#skF_3', A_89) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_89) | ~v2_pre_topc(A_89) | v2_struct_0(A_89))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_24, c_86, c_110])).
% 2.26/1.34  tff(c_115, plain, (![D_92, A_93]: (k7_relat_1('#skF_4', u1_struct_0(D_92))=k3_tmap_1(A_93, '#skF_2', '#skF_3', D_92, '#skF_4') | ~m1_pre_topc(D_92, '#skF_3') | ~m1_pre_topc(D_92, A_93) | ~m1_pre_topc('#skF_3', A_93) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93))), inference(negUnitSimplification, [status(thm)], [c_36, c_113])).
% 2.26/1.34  tff(c_119, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_115])).
% 2.26/1.34  tff(c_123, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_28, c_76, c_119])).
% 2.26/1.34  tff(c_124, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_42, c_123])).
% 2.26/1.34  tff(c_125, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_124])).
% 2.26/1.34  tff(c_128, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_18, c_125])).
% 2.26/1.34  tff(c_132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_128])).
% 2.26/1.34  tff(c_133, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_124])).
% 2.26/1.34  tff(c_20, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.26/1.34  tff(c_147, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_20])).
% 2.26/1.34  tff(c_150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_147])).
% 2.26/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.34  
% 2.26/1.34  Inference rules
% 2.26/1.34  ----------------------
% 2.26/1.34  #Ref     : 0
% 2.26/1.34  #Sup     : 19
% 2.26/1.34  #Fact    : 0
% 2.26/1.34  #Define  : 0
% 2.26/1.34  #Split   : 1
% 2.26/1.34  #Chain   : 0
% 2.26/1.34  #Close   : 0
% 2.26/1.34  
% 2.26/1.34  Ordering : KBO
% 2.26/1.34  
% 2.26/1.34  Simplification rules
% 2.26/1.34  ----------------------
% 2.26/1.34  #Subsume      : 0
% 2.26/1.34  #Demod        : 24
% 2.26/1.34  #Tautology    : 6
% 2.26/1.34  #SimpNegUnit  : 3
% 2.26/1.34  #BackRed      : 1
% 2.26/1.34  
% 2.26/1.34  #Partial instantiations: 0
% 2.26/1.34  #Strategies tried      : 1
% 2.26/1.34  
% 2.26/1.34  Timing (in seconds)
% 2.26/1.34  ----------------------
% 2.26/1.34  Preprocessing        : 0.35
% 2.26/1.34  Parsing              : 0.19
% 2.26/1.34  CNF conversion       : 0.03
% 2.26/1.35  Main loop            : 0.17
% 2.26/1.35  Inferencing          : 0.06
% 2.26/1.35  Reduction            : 0.05
% 2.26/1.35  Demodulation         : 0.04
% 2.26/1.35  BG Simplification    : 0.01
% 2.26/1.35  Subsumption          : 0.03
% 2.26/1.35  Abstraction          : 0.01
% 2.26/1.35  MUC search           : 0.00
% 2.26/1.35  Cooper               : 0.00
% 2.26/1.35  Total                : 0.55
% 2.26/1.35  Index Insertion      : 0.00
% 2.26/1.35  Index Deletion       : 0.00
% 2.26/1.35  Index Matching       : 0.00
% 2.26/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
