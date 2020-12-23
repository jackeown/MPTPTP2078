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
% DateTime   : Thu Dec  3 10:27:13 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 170 expanded)
%              Number of leaves         :   37 (  79 expanded)
%              Depth                    :   11
%              Number of atoms          :  166 ( 719 expanded)
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

tff(f_148,negated_conjecture,(
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

tff(f_74,axiom,(
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

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_117,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_113,axiom,(
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

tff(c_34,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_32,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_118,plain,(
    ! [A_93,B_94,D_95] :
      ( r2_funct_2(A_93,B_94,D_95,D_95)
      | ~ m1_subset_1(D_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94)))
      | ~ v1_funct_2(D_95,A_93,B_94)
      | ~ v1_funct_1(D_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_120,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_118])).

tff(c_123,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_120])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_36,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_53,plain,(
    ! [B_70,A_71] :
      ( l1_pre_topc(B_70)
      | ~ m1_pre_topc(B_70,A_71)
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_59,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_53])).

tff(c_63,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_59])).

tff(c_26,plain,(
    ! [A_55] :
      ( m1_pre_topc(A_55,A_55)
      | ~ l1_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_64,plain,(
    ! [B_72,A_73] :
      ( v1_relat_1(B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_73))
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_67,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_30,c_64])).

tff(c_70,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_67])).

tff(c_77,plain,(
    ! [C_79,A_80,B_81] :
      ( v4_relat_1(C_79,A_80)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_81,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_77])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_87,plain,(
    ! [B_84,A_85] :
      ( k7_relat_1(B_84,A_85) = B_84
      | ~ r1_tarski(k1_relat_1(B_84),A_85)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_98,plain,(
    ! [B_90,A_91] :
      ( k7_relat_1(B_90,A_91) = B_90
      | ~ v4_relat_1(B_90,A_91)
      | ~ v1_relat_1(B_90) ) ),
    inference(resolution,[status(thm)],[c_6,c_87])).

tff(c_101,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_81,c_98])).

tff(c_104,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_101])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_92,plain,(
    ! [A_86,B_87,C_88,D_89] :
      ( k2_partfun1(A_86,B_87,C_88,D_89) = k7_relat_1(C_88,D_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ v1_funct_1(C_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_94,plain,(
    ! [D_89] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',D_89) = k7_relat_1('#skF_4',D_89)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_92])).

tff(c_97,plain,(
    ! [D_89] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',D_89) = k7_relat_1('#skF_4',D_89) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_94])).

tff(c_131,plain,(
    ! [C_103,A_102,D_104,E_100,B_101] :
      ( k3_tmap_1(A_102,B_101,C_103,D_104,E_100) = k2_partfun1(u1_struct_0(C_103),u1_struct_0(B_101),E_100,u1_struct_0(D_104))
      | ~ m1_pre_topc(D_104,C_103)
      | ~ m1_subset_1(E_100,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_103),u1_struct_0(B_101))))
      | ~ v1_funct_2(E_100,u1_struct_0(C_103),u1_struct_0(B_101))
      | ~ v1_funct_1(E_100)
      | ~ m1_pre_topc(D_104,A_102)
      | ~ m1_pre_topc(C_103,A_102)
      | ~ l1_pre_topc(B_101)
      | ~ v2_pre_topc(B_101)
      | v2_struct_0(B_101)
      | ~ l1_pre_topc(A_102)
      | ~ v2_pre_topc(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_133,plain,(
    ! [A_102,D_104] :
      ( k3_tmap_1(A_102,'#skF_2','#skF_3',D_104,'#skF_4') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_104))
      | ~ m1_pre_topc(D_104,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc(D_104,A_102)
      | ~ m1_pre_topc('#skF_3',A_102)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_102)
      | ~ v2_pre_topc(A_102)
      | v2_struct_0(A_102) ) ),
    inference(resolution,[status(thm)],[c_30,c_131])).

tff(c_136,plain,(
    ! [D_104,A_102] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_104)) = k3_tmap_1(A_102,'#skF_2','#skF_3',D_104,'#skF_4')
      | ~ m1_pre_topc(D_104,'#skF_3')
      | ~ m1_pre_topc(D_104,A_102)
      | ~ m1_pre_topc('#skF_3',A_102)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_102)
      | ~ v2_pre_topc(A_102)
      | v2_struct_0(A_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_34,c_32,c_97,c_133])).

tff(c_138,plain,(
    ! [D_105,A_106] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_105)) = k3_tmap_1(A_106,'#skF_2','#skF_3',D_105,'#skF_4')
      | ~ m1_pre_topc(D_105,'#skF_3')
      | ~ m1_pre_topc(D_105,A_106)
      | ~ m1_pre_topc('#skF_3',A_106)
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106)
      | v2_struct_0(A_106) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_136])).

tff(c_142,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_138])).

tff(c_146,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_36,c_104,c_142])).

tff(c_147,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_146])).

tff(c_148,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_151,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_148])).

tff(c_155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_151])).

tff(c_156,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_28,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_170,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_28])).

tff(c_173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_170])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:53:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.41  
% 2.42/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.41  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.42/1.41  
% 2.42/1.41  %Foreground sorts:
% 2.42/1.41  
% 2.42/1.41  
% 2.42/1.41  %Background operators:
% 2.42/1.41  
% 2.42/1.41  
% 2.42/1.41  %Foreground operators:
% 2.42/1.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.42/1.41  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.42/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.42/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.41  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.42/1.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.42/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.42/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.42/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.42/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.42/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.42/1.41  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.42/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.42/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.42/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.42/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.42/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.41  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.42/1.41  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.42/1.41  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.42/1.41  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.42/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.42/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.42/1.41  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.42/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.42/1.41  
% 2.42/1.43  tff(f_148, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), D, k3_tmap_1(A, B, C, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tmap_1)).
% 2.42/1.43  tff(f_74, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 2.42/1.43  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.42/1.43  tff(f_117, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 2.42/1.43  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.42/1.43  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.42/1.43  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.42/1.43  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.42/1.43  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 2.42/1.43  tff(f_58, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.42/1.43  tff(f_113, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.42/1.43  tff(c_34, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.42/1.43  tff(c_32, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.42/1.43  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.42/1.43  tff(c_118, plain, (![A_93, B_94, D_95]: (r2_funct_2(A_93, B_94, D_95, D_95) | ~m1_subset_1(D_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))) | ~v1_funct_2(D_95, A_93, B_94) | ~v1_funct_1(D_95))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.42/1.43  tff(c_120, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_118])).
% 2.42/1.43  tff(c_123, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_120])).
% 2.42/1.43  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.42/1.43  tff(c_36, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.42/1.43  tff(c_53, plain, (![B_70, A_71]: (l1_pre_topc(B_70) | ~m1_pre_topc(B_70, A_71) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.42/1.43  tff(c_59, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_53])).
% 2.42/1.43  tff(c_63, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_59])).
% 2.42/1.43  tff(c_26, plain, (![A_55]: (m1_pre_topc(A_55, A_55) | ~l1_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.42/1.43  tff(c_50, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.42/1.43  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.42/1.43  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.42/1.43  tff(c_64, plain, (![B_72, A_73]: (v1_relat_1(B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(A_73)) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.42/1.43  tff(c_67, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_30, c_64])).
% 2.42/1.43  tff(c_70, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_67])).
% 2.42/1.43  tff(c_77, plain, (![C_79, A_80, B_81]: (v4_relat_1(C_79, A_80) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.42/1.43  tff(c_81, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_77])).
% 2.42/1.43  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.42/1.43  tff(c_87, plain, (![B_84, A_85]: (k7_relat_1(B_84, A_85)=B_84 | ~r1_tarski(k1_relat_1(B_84), A_85) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.42/1.43  tff(c_98, plain, (![B_90, A_91]: (k7_relat_1(B_90, A_91)=B_90 | ~v4_relat_1(B_90, A_91) | ~v1_relat_1(B_90))), inference(resolution, [status(thm)], [c_6, c_87])).
% 2.42/1.43  tff(c_101, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_81, c_98])).
% 2.42/1.43  tff(c_104, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_101])).
% 2.42/1.43  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.42/1.43  tff(c_42, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.42/1.43  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.42/1.43  tff(c_92, plain, (![A_86, B_87, C_88, D_89]: (k2_partfun1(A_86, B_87, C_88, D_89)=k7_relat_1(C_88, D_89) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~v1_funct_1(C_88))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.42/1.43  tff(c_94, plain, (![D_89]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', D_89)=k7_relat_1('#skF_4', D_89) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_92])).
% 2.42/1.43  tff(c_97, plain, (![D_89]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', D_89)=k7_relat_1('#skF_4', D_89))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_94])).
% 2.42/1.43  tff(c_131, plain, (![C_103, A_102, D_104, E_100, B_101]: (k3_tmap_1(A_102, B_101, C_103, D_104, E_100)=k2_partfun1(u1_struct_0(C_103), u1_struct_0(B_101), E_100, u1_struct_0(D_104)) | ~m1_pre_topc(D_104, C_103) | ~m1_subset_1(E_100, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_103), u1_struct_0(B_101)))) | ~v1_funct_2(E_100, u1_struct_0(C_103), u1_struct_0(B_101)) | ~v1_funct_1(E_100) | ~m1_pre_topc(D_104, A_102) | ~m1_pre_topc(C_103, A_102) | ~l1_pre_topc(B_101) | ~v2_pre_topc(B_101) | v2_struct_0(B_101) | ~l1_pre_topc(A_102) | ~v2_pre_topc(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.42/1.43  tff(c_133, plain, (![A_102, D_104]: (k3_tmap_1(A_102, '#skF_2', '#skF_3', D_104, '#skF_4')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_104)) | ~m1_pre_topc(D_104, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc(D_104, A_102) | ~m1_pre_topc('#skF_3', A_102) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_102) | ~v2_pre_topc(A_102) | v2_struct_0(A_102))), inference(resolution, [status(thm)], [c_30, c_131])).
% 2.42/1.43  tff(c_136, plain, (![D_104, A_102]: (k7_relat_1('#skF_4', u1_struct_0(D_104))=k3_tmap_1(A_102, '#skF_2', '#skF_3', D_104, '#skF_4') | ~m1_pre_topc(D_104, '#skF_3') | ~m1_pre_topc(D_104, A_102) | ~m1_pre_topc('#skF_3', A_102) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_102) | ~v2_pre_topc(A_102) | v2_struct_0(A_102))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_34, c_32, c_97, c_133])).
% 2.42/1.43  tff(c_138, plain, (![D_105, A_106]: (k7_relat_1('#skF_4', u1_struct_0(D_105))=k3_tmap_1(A_106, '#skF_2', '#skF_3', D_105, '#skF_4') | ~m1_pre_topc(D_105, '#skF_3') | ~m1_pre_topc(D_105, A_106) | ~m1_pre_topc('#skF_3', A_106) | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106) | v2_struct_0(A_106))), inference(negUnitSimplification, [status(thm)], [c_44, c_136])).
% 2.42/1.43  tff(c_142, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_138])).
% 2.42/1.43  tff(c_146, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_36, c_104, c_142])).
% 2.42/1.43  tff(c_147, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_50, c_146])).
% 2.42/1.43  tff(c_148, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_147])).
% 2.42/1.43  tff(c_151, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_26, c_148])).
% 2.42/1.43  tff(c_155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_151])).
% 2.42/1.43  tff(c_156, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_147])).
% 2.42/1.43  tff(c_28, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.42/1.43  tff(c_170, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_28])).
% 2.42/1.43  tff(c_173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_123, c_170])).
% 2.42/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.43  
% 2.42/1.43  Inference rules
% 2.42/1.43  ----------------------
% 2.42/1.43  #Ref     : 0
% 2.42/1.43  #Sup     : 21
% 2.42/1.43  #Fact    : 0
% 2.42/1.43  #Define  : 0
% 2.42/1.43  #Split   : 1
% 2.42/1.43  #Chain   : 0
% 2.42/1.43  #Close   : 0
% 2.42/1.43  
% 2.42/1.43  Ordering : KBO
% 2.42/1.43  
% 2.42/1.43  Simplification rules
% 2.42/1.43  ----------------------
% 2.42/1.43  #Subsume      : 0
% 2.42/1.43  #Demod        : 26
% 2.42/1.43  #Tautology    : 8
% 2.42/1.43  #SimpNegUnit  : 3
% 2.42/1.43  #BackRed      : 1
% 2.42/1.43  
% 2.42/1.43  #Partial instantiations: 0
% 2.42/1.43  #Strategies tried      : 1
% 2.42/1.43  
% 2.42/1.43  Timing (in seconds)
% 2.42/1.43  ----------------------
% 2.42/1.43  Preprocessing        : 0.43
% 2.42/1.43  Parsing              : 0.21
% 2.42/1.43  CNF conversion       : 0.04
% 2.42/1.43  Main loop            : 0.17
% 2.42/1.43  Inferencing          : 0.06
% 2.42/1.43  Reduction            : 0.06
% 2.42/1.43  Demodulation         : 0.04
% 2.42/1.43  BG Simplification    : 0.02
% 2.42/1.43  Subsumption          : 0.03
% 2.42/1.43  Abstraction          : 0.01
% 2.42/1.43  MUC search           : 0.00
% 2.42/1.43  Cooper               : 0.00
% 2.42/1.43  Total                : 0.64
% 2.42/1.43  Index Insertion      : 0.00
% 2.42/1.43  Index Deletion       : 0.00
% 2.42/1.43  Index Matching       : 0.00
% 2.42/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
