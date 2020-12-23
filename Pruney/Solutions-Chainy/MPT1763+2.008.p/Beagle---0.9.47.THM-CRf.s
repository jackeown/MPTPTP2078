%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:12 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 112 expanded)
%              Number of leaves         :   34 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  168 ( 470 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_144,negated_conjecture,(
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

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_113,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_99,axiom,(
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

tff(c_32,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_30,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_148,plain,(
    ! [A_97,B_98,C_99,D_100] :
      ( r2_funct_2(A_97,B_98,C_99,C_99)
      | ~ m1_subset_1(D_100,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98)))
      | ~ v1_funct_2(D_100,A_97,B_98)
      | ~ v1_funct_1(D_100)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98)))
      | ~ v1_funct_2(C_99,A_97,B_98)
      | ~ v1_funct_1(C_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_150,plain,(
    ! [C_99] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_99,C_99)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_99,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_99) ) ),
    inference(resolution,[status(thm)],[c_28,c_148])).

tff(c_154,plain,(
    ! [C_101] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_101,C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_101,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_150])).

tff(c_156,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_154])).

tff(c_159,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_156])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_34,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_99,plain,(
    ! [B_87,C_88,A_89] :
      ( m1_pre_topc(B_87,C_88)
      | ~ r1_tarski(u1_struct_0(B_87),u1_struct_0(C_88))
      | ~ m1_pre_topc(C_88,A_89)
      | ~ m1_pre_topc(B_87,A_89)
      | ~ l1_pre_topc(A_89)
      | ~ v2_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_110,plain,(
    ! [B_93,A_94] :
      ( m1_pre_topc(B_93,B_93)
      | ~ m1_pre_topc(B_93,A_94)
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94) ) ),
    inference(resolution,[status(thm)],[c_6,c_99])).

tff(c_112,plain,
    ( m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_110])).

tff(c_115,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_112])).

tff(c_10,plain,(
    ! [C_7,A_5,B_6] :
      ( v1_relat_1(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_62,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_10])).

tff(c_64,plain,(
    ! [C_76,A_77,B_78] :
      ( v4_relat_1(C_76,A_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_68,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_64])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k7_relat_1(B_4,A_3) = B_4
      | ~ v4_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_71,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_8])).

tff(c_74,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_71])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_40,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_84,plain,(
    ! [A_82,B_83,C_84,D_85] :
      ( k2_partfun1(A_82,B_83,C_84,D_85) = k7_relat_1(C_84,D_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83)))
      | ~ v1_funct_1(C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_86,plain,(
    ! [D_85] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',D_85) = k7_relat_1('#skF_4',D_85)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_84])).

tff(c_89,plain,(
    ! [D_85] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',D_85) = k7_relat_1('#skF_4',D_85) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_86])).

tff(c_160,plain,(
    ! [C_102,D_103,E_106,A_104,B_105] :
      ( k3_tmap_1(A_104,B_105,C_102,D_103,E_106) = k2_partfun1(u1_struct_0(C_102),u1_struct_0(B_105),E_106,u1_struct_0(D_103))
      | ~ m1_pre_topc(D_103,C_102)
      | ~ m1_subset_1(E_106,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_102),u1_struct_0(B_105))))
      | ~ v1_funct_2(E_106,u1_struct_0(C_102),u1_struct_0(B_105))
      | ~ v1_funct_1(E_106)
      | ~ m1_pre_topc(D_103,A_104)
      | ~ m1_pre_topc(C_102,A_104)
      | ~ l1_pre_topc(B_105)
      | ~ v2_pre_topc(B_105)
      | v2_struct_0(B_105)
      | ~ l1_pre_topc(A_104)
      | ~ v2_pre_topc(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_162,plain,(
    ! [A_104,D_103] :
      ( k3_tmap_1(A_104,'#skF_2','#skF_3',D_103,'#skF_4') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_103))
      | ~ m1_pre_topc(D_103,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc(D_103,A_104)
      | ~ m1_pre_topc('#skF_3',A_104)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_104)
      | ~ v2_pre_topc(A_104)
      | v2_struct_0(A_104) ) ),
    inference(resolution,[status(thm)],[c_28,c_160])).

tff(c_165,plain,(
    ! [D_103,A_104] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_103)) = k3_tmap_1(A_104,'#skF_2','#skF_3',D_103,'#skF_4')
      | ~ m1_pre_topc(D_103,'#skF_3')
      | ~ m1_pre_topc(D_103,A_104)
      | ~ m1_pre_topc('#skF_3',A_104)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_104)
      | ~ v2_pre_topc(A_104)
      | v2_struct_0(A_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_30,c_89,c_162])).

tff(c_167,plain,(
    ! [D_107,A_108] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_107)) = k3_tmap_1(A_108,'#skF_2','#skF_3',D_107,'#skF_4')
      | ~ m1_pre_topc(D_107,'#skF_3')
      | ~ m1_pre_topc(D_107,A_108)
      | ~ m1_pre_topc('#skF_3',A_108)
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108)
      | v2_struct_0(A_108) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_165])).

tff(c_171,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_167])).

tff(c_178,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_34,c_115,c_74,c_171])).

tff(c_179,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_178])).

tff(c_26,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_180,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_26])).

tff(c_183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_180])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:32:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.26  
% 2.29/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.26  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.37/1.26  
% 2.37/1.26  %Foreground sorts:
% 2.37/1.26  
% 2.37/1.26  
% 2.37/1.26  %Background operators:
% 2.37/1.26  
% 2.37/1.26  
% 2.37/1.26  %Foreground operators:
% 2.37/1.26  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.37/1.26  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.37/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.37/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.26  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.37/1.26  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.37/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.37/1.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.37/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.37/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.37/1.26  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.37/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.37/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.37/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.37/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.37/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.26  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.37/1.26  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.37/1.26  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.37/1.26  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.37/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.37/1.26  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.37/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.37/1.26  
% 2.37/1.27  tff(f_144, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), D, k3_tmap_1(A, B, C, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tmap_1)).
% 2.37/1.27  tff(f_67, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 2.37/1.27  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.37/1.27  tff(f_113, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 2.37/1.27  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.37/1.27  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.37/1.27  tff(f_37, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.37/1.27  tff(f_53, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.37/1.27  tff(f_99, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.37/1.27  tff(c_32, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.37/1.27  tff(c_30, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.37/1.27  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.37/1.27  tff(c_148, plain, (![A_97, B_98, C_99, D_100]: (r2_funct_2(A_97, B_98, C_99, C_99) | ~m1_subset_1(D_100, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))) | ~v1_funct_2(D_100, A_97, B_98) | ~v1_funct_1(D_100) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))) | ~v1_funct_2(C_99, A_97, B_98) | ~v1_funct_1(C_99))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.37/1.27  tff(c_150, plain, (![C_99]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_99, C_99) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_99, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_99))), inference(resolution, [status(thm)], [c_28, c_148])).
% 2.37/1.27  tff(c_154, plain, (![C_101]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_101, C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_101, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_101))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_150])).
% 2.37/1.27  tff(c_156, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_154])).
% 2.37/1.27  tff(c_159, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_156])).
% 2.37/1.27  tff(c_48, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.37/1.27  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.37/1.27  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.37/1.27  tff(c_34, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.37/1.27  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.37/1.27  tff(c_99, plain, (![B_87, C_88, A_89]: (m1_pre_topc(B_87, C_88) | ~r1_tarski(u1_struct_0(B_87), u1_struct_0(C_88)) | ~m1_pre_topc(C_88, A_89) | ~m1_pre_topc(B_87, A_89) | ~l1_pre_topc(A_89) | ~v2_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.37/1.27  tff(c_110, plain, (![B_93, A_94]: (m1_pre_topc(B_93, B_93) | ~m1_pre_topc(B_93, A_94) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94))), inference(resolution, [status(thm)], [c_6, c_99])).
% 2.37/1.27  tff(c_112, plain, (m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_110])).
% 2.37/1.27  tff(c_115, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_112])).
% 2.37/1.27  tff(c_10, plain, (![C_7, A_5, B_6]: (v1_relat_1(C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.37/1.27  tff(c_62, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_10])).
% 2.37/1.27  tff(c_64, plain, (![C_76, A_77, B_78]: (v4_relat_1(C_76, A_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.37/1.27  tff(c_68, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_64])).
% 2.37/1.27  tff(c_8, plain, (![B_4, A_3]: (k7_relat_1(B_4, A_3)=B_4 | ~v4_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.37/1.27  tff(c_71, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_8])).
% 2.37/1.27  tff(c_74, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_71])).
% 2.37/1.27  tff(c_42, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.37/1.27  tff(c_40, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.37/1.27  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.37/1.27  tff(c_84, plain, (![A_82, B_83, C_84, D_85]: (k2_partfun1(A_82, B_83, C_84, D_85)=k7_relat_1(C_84, D_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))) | ~v1_funct_1(C_84))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.37/1.27  tff(c_86, plain, (![D_85]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', D_85)=k7_relat_1('#skF_4', D_85) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_84])).
% 2.37/1.27  tff(c_89, plain, (![D_85]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', D_85)=k7_relat_1('#skF_4', D_85))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_86])).
% 2.37/1.27  tff(c_160, plain, (![C_102, D_103, E_106, A_104, B_105]: (k3_tmap_1(A_104, B_105, C_102, D_103, E_106)=k2_partfun1(u1_struct_0(C_102), u1_struct_0(B_105), E_106, u1_struct_0(D_103)) | ~m1_pre_topc(D_103, C_102) | ~m1_subset_1(E_106, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_102), u1_struct_0(B_105)))) | ~v1_funct_2(E_106, u1_struct_0(C_102), u1_struct_0(B_105)) | ~v1_funct_1(E_106) | ~m1_pre_topc(D_103, A_104) | ~m1_pre_topc(C_102, A_104) | ~l1_pre_topc(B_105) | ~v2_pre_topc(B_105) | v2_struct_0(B_105) | ~l1_pre_topc(A_104) | ~v2_pre_topc(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.37/1.27  tff(c_162, plain, (![A_104, D_103]: (k3_tmap_1(A_104, '#skF_2', '#skF_3', D_103, '#skF_4')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_103)) | ~m1_pre_topc(D_103, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc(D_103, A_104) | ~m1_pre_topc('#skF_3', A_104) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_104) | ~v2_pre_topc(A_104) | v2_struct_0(A_104))), inference(resolution, [status(thm)], [c_28, c_160])).
% 2.37/1.27  tff(c_165, plain, (![D_103, A_104]: (k7_relat_1('#skF_4', u1_struct_0(D_103))=k3_tmap_1(A_104, '#skF_2', '#skF_3', D_103, '#skF_4') | ~m1_pre_topc(D_103, '#skF_3') | ~m1_pre_topc(D_103, A_104) | ~m1_pre_topc('#skF_3', A_104) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_104) | ~v2_pre_topc(A_104) | v2_struct_0(A_104))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_30, c_89, c_162])).
% 2.37/1.27  tff(c_167, plain, (![D_107, A_108]: (k7_relat_1('#skF_4', u1_struct_0(D_107))=k3_tmap_1(A_108, '#skF_2', '#skF_3', D_107, '#skF_4') | ~m1_pre_topc(D_107, '#skF_3') | ~m1_pre_topc(D_107, A_108) | ~m1_pre_topc('#skF_3', A_108) | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108) | v2_struct_0(A_108))), inference(negUnitSimplification, [status(thm)], [c_42, c_165])).
% 2.37/1.27  tff(c_171, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_167])).
% 2.37/1.27  tff(c_178, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_34, c_115, c_74, c_171])).
% 2.37/1.27  tff(c_179, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_48, c_178])).
% 2.37/1.27  tff(c_26, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.37/1.27  tff(c_180, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_26])).
% 2.37/1.27  tff(c_183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_159, c_180])).
% 2.37/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.27  
% 2.37/1.27  Inference rules
% 2.37/1.27  ----------------------
% 2.37/1.27  #Ref     : 0
% 2.37/1.27  #Sup     : 24
% 2.37/1.27  #Fact    : 0
% 2.37/1.27  #Define  : 0
% 2.37/1.27  #Split   : 1
% 2.37/1.27  #Chain   : 0
% 2.37/1.27  #Close   : 0
% 2.37/1.27  
% 2.37/1.27  Ordering : KBO
% 2.37/1.27  
% 2.37/1.27  Simplification rules
% 2.37/1.27  ----------------------
% 2.37/1.27  #Subsume      : 1
% 2.37/1.27  #Demod        : 31
% 2.37/1.27  #Tautology    : 10
% 2.37/1.27  #SimpNegUnit  : 3
% 2.37/1.27  #BackRed      : 1
% 2.37/1.27  
% 2.37/1.27  #Partial instantiations: 0
% 2.37/1.27  #Strategies tried      : 1
% 2.37/1.27  
% 2.37/1.27  Timing (in seconds)
% 2.37/1.27  ----------------------
% 2.37/1.28  Preprocessing        : 0.33
% 2.37/1.28  Parsing              : 0.18
% 2.37/1.28  CNF conversion       : 0.03
% 2.37/1.28  Main loop            : 0.18
% 2.37/1.28  Inferencing          : 0.06
% 2.37/1.28  Reduction            : 0.06
% 2.37/1.28  Demodulation         : 0.05
% 2.37/1.28  BG Simplification    : 0.01
% 2.37/1.28  Subsumption          : 0.03
% 2.37/1.28  Abstraction          : 0.01
% 2.37/1.28  MUC search           : 0.00
% 2.37/1.28  Cooper               : 0.00
% 2.37/1.28  Total                : 0.55
% 2.37/1.28  Index Insertion      : 0.00
% 2.37/1.28  Index Deletion       : 0.00
% 2.37/1.28  Index Matching       : 0.00
% 2.37/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
