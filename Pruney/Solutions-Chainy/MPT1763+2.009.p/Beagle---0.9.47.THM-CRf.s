%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:12 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 164 expanded)
%              Number of leaves         :   36 (  77 expanded)
%              Depth                    :   11
%              Number of atoms          :  160 ( 707 expanded)
%              Number of equality atoms :   19 (  36 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
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

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_112,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

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

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_108,axiom,(
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

tff(c_32,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_30,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_113,plain,(
    ! [A_90,B_91,D_92] :
      ( r2_funct_2(A_90,B_91,D_92,D_92)
      | ~ m1_subset_1(D_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91)))
      | ~ v1_funct_2(D_92,A_90,B_91)
      | ~ v1_funct_1(D_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_115,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_113])).

tff(c_118,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_115])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_34,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_50,plain,(
    ! [B_66,A_67] :
      ( l1_pre_topc(B_66)
      | ~ m1_pre_topc(B_66,A_67)
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_56,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_50])).

tff(c_60,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_56])).

tff(c_24,plain,(
    ! [A_53] :
      ( m1_pre_topc(A_53,A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_8,plain,(
    ! [C_7,A_5,B_6] :
      ( v1_relat_1(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_65,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_8])).

tff(c_71,plain,(
    ! [C_74,A_75,B_76] :
      ( v4_relat_1(C_74,A_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_75,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_71])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_82,plain,(
    ! [B_81,A_82] :
      ( k7_relat_1(B_81,A_82) = B_81
      | ~ r1_tarski(k1_relat_1(B_81),A_82)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_87,plain,(
    ! [B_83,A_84] :
      ( k7_relat_1(B_83,A_84) = B_83
      | ~ v4_relat_1(B_83,A_84)
      | ~ v1_relat_1(B_83) ) ),
    inference(resolution,[status(thm)],[c_4,c_82])).

tff(c_90,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_75,c_87])).

tff(c_93,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_90])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_40,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_94,plain,(
    ! [A_85,B_86,C_87,D_88] :
      ( k2_partfun1(A_85,B_86,C_87,D_88) = k7_relat_1(C_87,D_88)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86)))
      | ~ v1_funct_1(C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_96,plain,(
    ! [D_88] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',D_88) = k7_relat_1('#skF_4',D_88)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_94])).

tff(c_99,plain,(
    ! [D_88] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',D_88) = k7_relat_1('#skF_4',D_88) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_96])).

tff(c_126,plain,(
    ! [A_98,E_100,B_99,C_101,D_97] :
      ( k3_tmap_1(A_98,B_99,C_101,D_97,E_100) = k2_partfun1(u1_struct_0(C_101),u1_struct_0(B_99),E_100,u1_struct_0(D_97))
      | ~ m1_pre_topc(D_97,C_101)
      | ~ m1_subset_1(E_100,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_101),u1_struct_0(B_99))))
      | ~ v1_funct_2(E_100,u1_struct_0(C_101),u1_struct_0(B_99))
      | ~ v1_funct_1(E_100)
      | ~ m1_pre_topc(D_97,A_98)
      | ~ m1_pre_topc(C_101,A_98)
      | ~ l1_pre_topc(B_99)
      | ~ v2_pre_topc(B_99)
      | v2_struct_0(B_99)
      | ~ l1_pre_topc(A_98)
      | ~ v2_pre_topc(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_128,plain,(
    ! [A_98,D_97] :
      ( k3_tmap_1(A_98,'#skF_2','#skF_3',D_97,'#skF_4') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_97))
      | ~ m1_pre_topc(D_97,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc(D_97,A_98)
      | ~ m1_pre_topc('#skF_3',A_98)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_98)
      | ~ v2_pre_topc(A_98)
      | v2_struct_0(A_98) ) ),
    inference(resolution,[status(thm)],[c_28,c_126])).

tff(c_131,plain,(
    ! [D_97,A_98] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_97)) = k3_tmap_1(A_98,'#skF_2','#skF_3',D_97,'#skF_4')
      | ~ m1_pre_topc(D_97,'#skF_3')
      | ~ m1_pre_topc(D_97,A_98)
      | ~ m1_pre_topc('#skF_3',A_98)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_98)
      | ~ v2_pre_topc(A_98)
      | v2_struct_0(A_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_30,c_99,c_128])).

tff(c_133,plain,(
    ! [D_102,A_103] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_102)) = k3_tmap_1(A_103,'#skF_2','#skF_3',D_102,'#skF_4')
      | ~ m1_pre_topc(D_102,'#skF_3')
      | ~ m1_pre_topc(D_102,A_103)
      | ~ m1_pre_topc('#skF_3',A_103)
      | ~ l1_pre_topc(A_103)
      | ~ v2_pre_topc(A_103)
      | v2_struct_0(A_103) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_131])).

tff(c_137,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_133])).

tff(c_141,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_34,c_93,c_137])).

tff(c_142,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_141])).

tff(c_143,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_146,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_143])).

tff(c_150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_146])).

tff(c_151,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_26,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_165,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_26])).

tff(c_168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_165])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:07:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.22  
% 2.18/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.22  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.18/1.22  
% 2.18/1.22  %Foreground sorts:
% 2.18/1.22  
% 2.18/1.22  
% 2.18/1.22  %Background operators:
% 2.18/1.22  
% 2.18/1.22  
% 2.18/1.22  %Foreground operators:
% 2.18/1.22  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.18/1.22  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.18/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.18/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.22  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.18/1.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.18/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.22  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.18/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.22  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.18/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.18/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.18/1.22  tff('#skF_4', type, '#skF_4': $i).
% 2.18/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.22  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.18/1.22  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.18/1.22  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.18/1.22  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.18/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.18/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.18/1.22  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.18/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.22  
% 2.27/1.24  tff(f_143, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), D, k3_tmap_1(A, B, C, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tmap_1)).
% 2.27/1.24  tff(f_69, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 2.27/1.24  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.27/1.24  tff(f_112, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 2.27/1.24  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.27/1.24  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.27/1.24  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.27/1.24  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.27/1.24  tff(f_53, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.27/1.24  tff(f_108, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.27/1.24  tff(c_32, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.27/1.24  tff(c_30, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.27/1.24  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.27/1.24  tff(c_113, plain, (![A_90, B_91, D_92]: (r2_funct_2(A_90, B_91, D_92, D_92) | ~m1_subset_1(D_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))) | ~v1_funct_2(D_92, A_90, B_91) | ~v1_funct_1(D_92))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.27/1.24  tff(c_115, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_113])).
% 2.27/1.24  tff(c_118, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_115])).
% 2.27/1.24  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.27/1.24  tff(c_34, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.27/1.24  tff(c_50, plain, (![B_66, A_67]: (l1_pre_topc(B_66) | ~m1_pre_topc(B_66, A_67) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.27/1.24  tff(c_56, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_50])).
% 2.27/1.24  tff(c_60, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_56])).
% 2.27/1.24  tff(c_24, plain, (![A_53]: (m1_pre_topc(A_53, A_53) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.27/1.24  tff(c_48, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.27/1.24  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.27/1.24  tff(c_8, plain, (![C_7, A_5, B_6]: (v1_relat_1(C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.27/1.24  tff(c_65, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_8])).
% 2.27/1.24  tff(c_71, plain, (![C_74, A_75, B_76]: (v4_relat_1(C_74, A_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.27/1.24  tff(c_75, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_71])).
% 2.27/1.24  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), A_1) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.27/1.24  tff(c_82, plain, (![B_81, A_82]: (k7_relat_1(B_81, A_82)=B_81 | ~r1_tarski(k1_relat_1(B_81), A_82) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.27/1.24  tff(c_87, plain, (![B_83, A_84]: (k7_relat_1(B_83, A_84)=B_83 | ~v4_relat_1(B_83, A_84) | ~v1_relat_1(B_83))), inference(resolution, [status(thm)], [c_4, c_82])).
% 2.27/1.24  tff(c_90, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_75, c_87])).
% 2.27/1.24  tff(c_93, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_65, c_90])).
% 2.27/1.24  tff(c_42, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.27/1.24  tff(c_40, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.27/1.24  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.27/1.24  tff(c_94, plain, (![A_85, B_86, C_87, D_88]: (k2_partfun1(A_85, B_86, C_87, D_88)=k7_relat_1(C_87, D_88) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))) | ~v1_funct_1(C_87))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.27/1.24  tff(c_96, plain, (![D_88]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', D_88)=k7_relat_1('#skF_4', D_88) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_94])).
% 2.27/1.24  tff(c_99, plain, (![D_88]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', D_88)=k7_relat_1('#skF_4', D_88))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_96])).
% 2.27/1.24  tff(c_126, plain, (![A_98, E_100, B_99, C_101, D_97]: (k3_tmap_1(A_98, B_99, C_101, D_97, E_100)=k2_partfun1(u1_struct_0(C_101), u1_struct_0(B_99), E_100, u1_struct_0(D_97)) | ~m1_pre_topc(D_97, C_101) | ~m1_subset_1(E_100, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_101), u1_struct_0(B_99)))) | ~v1_funct_2(E_100, u1_struct_0(C_101), u1_struct_0(B_99)) | ~v1_funct_1(E_100) | ~m1_pre_topc(D_97, A_98) | ~m1_pre_topc(C_101, A_98) | ~l1_pre_topc(B_99) | ~v2_pre_topc(B_99) | v2_struct_0(B_99) | ~l1_pre_topc(A_98) | ~v2_pre_topc(A_98) | v2_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.27/1.24  tff(c_128, plain, (![A_98, D_97]: (k3_tmap_1(A_98, '#skF_2', '#skF_3', D_97, '#skF_4')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_97)) | ~m1_pre_topc(D_97, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc(D_97, A_98) | ~m1_pre_topc('#skF_3', A_98) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_98) | ~v2_pre_topc(A_98) | v2_struct_0(A_98))), inference(resolution, [status(thm)], [c_28, c_126])).
% 2.27/1.24  tff(c_131, plain, (![D_97, A_98]: (k7_relat_1('#skF_4', u1_struct_0(D_97))=k3_tmap_1(A_98, '#skF_2', '#skF_3', D_97, '#skF_4') | ~m1_pre_topc(D_97, '#skF_3') | ~m1_pre_topc(D_97, A_98) | ~m1_pre_topc('#skF_3', A_98) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_98) | ~v2_pre_topc(A_98) | v2_struct_0(A_98))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_30, c_99, c_128])).
% 2.27/1.24  tff(c_133, plain, (![D_102, A_103]: (k7_relat_1('#skF_4', u1_struct_0(D_102))=k3_tmap_1(A_103, '#skF_2', '#skF_3', D_102, '#skF_4') | ~m1_pre_topc(D_102, '#skF_3') | ~m1_pre_topc(D_102, A_103) | ~m1_pre_topc('#skF_3', A_103) | ~l1_pre_topc(A_103) | ~v2_pre_topc(A_103) | v2_struct_0(A_103))), inference(negUnitSimplification, [status(thm)], [c_42, c_131])).
% 2.27/1.24  tff(c_137, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_133])).
% 2.27/1.24  tff(c_141, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_34, c_93, c_137])).
% 2.27/1.24  tff(c_142, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_48, c_141])).
% 2.27/1.24  tff(c_143, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_142])).
% 2.27/1.24  tff(c_146, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_24, c_143])).
% 2.27/1.24  tff(c_150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_146])).
% 2.27/1.24  tff(c_151, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_142])).
% 2.27/1.24  tff(c_26, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.27/1.24  tff(c_165, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_26])).
% 2.27/1.24  tff(c_168, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_165])).
% 2.27/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.24  
% 2.27/1.24  Inference rules
% 2.27/1.24  ----------------------
% 2.27/1.24  #Ref     : 0
% 2.27/1.24  #Sup     : 21
% 2.27/1.24  #Fact    : 0
% 2.27/1.24  #Define  : 0
% 2.27/1.24  #Split   : 1
% 2.27/1.24  #Chain   : 0
% 2.27/1.24  #Close   : 0
% 2.27/1.24  
% 2.27/1.24  Ordering : KBO
% 2.27/1.24  
% 2.27/1.24  Simplification rules
% 2.27/1.24  ----------------------
% 2.27/1.24  #Subsume      : 0
% 2.27/1.24  #Demod        : 25
% 2.27/1.24  #Tautology    : 8
% 2.27/1.24  #SimpNegUnit  : 3
% 2.27/1.24  #BackRed      : 1
% 2.27/1.24  
% 2.27/1.24  #Partial instantiations: 0
% 2.27/1.24  #Strategies tried      : 1
% 2.27/1.24  
% 2.27/1.24  Timing (in seconds)
% 2.27/1.24  ----------------------
% 2.27/1.24  Preprocessing        : 0.33
% 2.27/1.24  Parsing              : 0.18
% 2.27/1.24  CNF conversion       : 0.03
% 2.27/1.24  Main loop            : 0.17
% 2.27/1.24  Inferencing          : 0.06
% 2.27/1.24  Reduction            : 0.05
% 2.27/1.24  Demodulation         : 0.04
% 2.27/1.24  BG Simplification    : 0.01
% 2.27/1.24  Subsumption          : 0.03
% 2.27/1.24  Abstraction          : 0.01
% 2.27/1.24  MUC search           : 0.00
% 2.27/1.24  Cooper               : 0.00
% 2.27/1.24  Total                : 0.53
% 2.27/1.24  Index Insertion      : 0.00
% 2.27/1.24  Index Deletion       : 0.00
% 2.27/1.24  Index Matching       : 0.00
% 2.27/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
