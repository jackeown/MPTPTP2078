%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:13 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 107 expanded)
%              Number of leaves         :   35 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  162 ( 425 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :   19 (   4 average)
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

tff(f_151,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_120,axiom,(
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

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
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

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_106,axiom,(
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

tff(c_36,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_34,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_106,plain,(
    ! [A_90,B_91,D_92] :
      ( r2_funct_2(A_90,B_91,D_92,D_92)
      | ~ m1_subset_1(D_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91)))
      | ~ v1_funct_2(D_92,A_90,B_91)
      | ~ v1_funct_1(D_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_108,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_106])).

tff(c_111,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_108])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_50,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_38,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_139,plain,(
    ! [B_98,C_99,A_100] :
      ( m1_pre_topc(B_98,C_99)
      | ~ r1_tarski(u1_struct_0(B_98),u1_struct_0(C_99))
      | ~ m1_pre_topc(C_99,A_100)
      | ~ m1_pre_topc(B_98,A_100)
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_147,plain,(
    ! [B_101,A_102] :
      ( m1_pre_topc(B_101,B_101)
      | ~ m1_pre_topc(B_101,A_102)
      | ~ l1_pre_topc(A_102)
      | ~ v2_pre_topc(A_102) ) ),
    inference(resolution,[status(thm)],[c_6,c_139])).

tff(c_149,plain,
    ( m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_147])).

tff(c_152,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_149])).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_63,plain,(
    ! [B_75,A_76] :
      ( v1_relat_1(B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_76))
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_66,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_32,c_63])).

tff(c_69,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_66])).

tff(c_75,plain,(
    ! [C_80,A_81,B_82] :
      ( v4_relat_1(C_80,A_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_79,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_75])).

tff(c_80,plain,(
    ! [B_83,A_84] :
      ( k7_relat_1(B_83,A_84) = B_83
      | ~ v4_relat_1(B_83,A_84)
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_83,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_79,c_80])).

tff(c_86,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_83])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_44,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_91,plain,(
    ! [A_85,B_86,C_87,D_88] :
      ( k2_partfun1(A_85,B_86,C_87,D_88) = k7_relat_1(C_87,D_88)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86)))
      | ~ v1_funct_1(C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_93,plain,(
    ! [D_88] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',D_88) = k7_relat_1('#skF_4',D_88)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_91])).

tff(c_96,plain,(
    ! [D_88] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',D_88) = k7_relat_1('#skF_4',D_88) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_93])).

tff(c_168,plain,(
    ! [C_110,B_111,A_108,D_109,E_107] :
      ( k3_tmap_1(A_108,B_111,C_110,D_109,E_107) = k2_partfun1(u1_struct_0(C_110),u1_struct_0(B_111),E_107,u1_struct_0(D_109))
      | ~ m1_pre_topc(D_109,C_110)
      | ~ m1_subset_1(E_107,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_110),u1_struct_0(B_111))))
      | ~ v1_funct_2(E_107,u1_struct_0(C_110),u1_struct_0(B_111))
      | ~ v1_funct_1(E_107)
      | ~ m1_pre_topc(D_109,A_108)
      | ~ m1_pre_topc(C_110,A_108)
      | ~ l1_pre_topc(B_111)
      | ~ v2_pre_topc(B_111)
      | v2_struct_0(B_111)
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108)
      | v2_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_170,plain,(
    ! [A_108,D_109] :
      ( k3_tmap_1(A_108,'#skF_2','#skF_3',D_109,'#skF_4') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_109))
      | ~ m1_pre_topc(D_109,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc(D_109,A_108)
      | ~ m1_pre_topc('#skF_3',A_108)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108)
      | v2_struct_0(A_108) ) ),
    inference(resolution,[status(thm)],[c_32,c_168])).

tff(c_173,plain,(
    ! [D_109,A_108] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_109)) = k3_tmap_1(A_108,'#skF_2','#skF_3',D_109,'#skF_4')
      | ~ m1_pre_topc(D_109,'#skF_3')
      | ~ m1_pre_topc(D_109,A_108)
      | ~ m1_pre_topc('#skF_3',A_108)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108)
      | v2_struct_0(A_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_36,c_34,c_96,c_170])).

tff(c_175,plain,(
    ! [D_112,A_113] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_112)) = k3_tmap_1(A_113,'#skF_2','#skF_3',D_112,'#skF_4')
      | ~ m1_pre_topc(D_112,'#skF_3')
      | ~ m1_pre_topc(D_112,A_113)
      | ~ m1_pre_topc('#skF_3',A_113)
      | ~ l1_pre_topc(A_113)
      | ~ v2_pre_topc(A_113)
      | v2_struct_0(A_113) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_173])).

tff(c_179,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_175])).

tff(c_186,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_38,c_152,c_86,c_179])).

tff(c_187,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_186])).

tff(c_30,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_188,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_30])).

tff(c_191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_188])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:41:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.31  
% 2.37/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.31  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.37/1.31  
% 2.37/1.31  %Foreground sorts:
% 2.37/1.31  
% 2.37/1.31  
% 2.37/1.31  %Background operators:
% 2.37/1.31  
% 2.37/1.31  
% 2.37/1.31  %Foreground operators:
% 2.37/1.31  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.37/1.31  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.37/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.37/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.37/1.31  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.37/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.37/1.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.37/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.37/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.37/1.31  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.37/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.37/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.37/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.37/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.37/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.31  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.37/1.31  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.37/1.31  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.37/1.31  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.37/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.37/1.31  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.37/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.37/1.31  
% 2.37/1.32  tff(f_151, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), D, k3_tmap_1(A, B, C, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tmap_1)).
% 2.37/1.32  tff(f_74, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 2.37/1.32  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.37/1.32  tff(f_120, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 2.37/1.32  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.37/1.32  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.37/1.32  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.37/1.32  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.37/1.32  tff(f_58, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.37/1.32  tff(f_106, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.37/1.32  tff(c_36, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.37/1.32  tff(c_34, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.37/1.32  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.37/1.32  tff(c_106, plain, (![A_90, B_91, D_92]: (r2_funct_2(A_90, B_91, D_92, D_92) | ~m1_subset_1(D_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))) | ~v1_funct_2(D_92, A_90, B_91) | ~v1_funct_1(D_92))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.37/1.32  tff(c_108, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_106])).
% 2.37/1.32  tff(c_111, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_108])).
% 2.37/1.32  tff(c_52, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.37/1.32  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.37/1.32  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.37/1.32  tff(c_38, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.37/1.32  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.37/1.32  tff(c_139, plain, (![B_98, C_99, A_100]: (m1_pre_topc(B_98, C_99) | ~r1_tarski(u1_struct_0(B_98), u1_struct_0(C_99)) | ~m1_pre_topc(C_99, A_100) | ~m1_pre_topc(B_98, A_100) | ~l1_pre_topc(A_100) | ~v2_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.37/1.32  tff(c_147, plain, (![B_101, A_102]: (m1_pre_topc(B_101, B_101) | ~m1_pre_topc(B_101, A_102) | ~l1_pre_topc(A_102) | ~v2_pre_topc(A_102))), inference(resolution, [status(thm)], [c_6, c_139])).
% 2.37/1.32  tff(c_149, plain, (m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_147])).
% 2.37/1.32  tff(c_152, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_149])).
% 2.37/1.32  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.37/1.32  tff(c_63, plain, (![B_75, A_76]: (v1_relat_1(B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(A_76)) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.37/1.32  tff(c_66, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_32, c_63])).
% 2.37/1.32  tff(c_69, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_66])).
% 2.37/1.32  tff(c_75, plain, (![C_80, A_81, B_82]: (v4_relat_1(C_80, A_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.37/1.32  tff(c_79, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_75])).
% 2.37/1.32  tff(c_80, plain, (![B_83, A_84]: (k7_relat_1(B_83, A_84)=B_83 | ~v4_relat_1(B_83, A_84) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.37/1.32  tff(c_83, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_79, c_80])).
% 2.37/1.32  tff(c_86, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_69, c_83])).
% 2.37/1.32  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.37/1.32  tff(c_44, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.37/1.32  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.37/1.32  tff(c_91, plain, (![A_85, B_86, C_87, D_88]: (k2_partfun1(A_85, B_86, C_87, D_88)=k7_relat_1(C_87, D_88) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))) | ~v1_funct_1(C_87))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.37/1.32  tff(c_93, plain, (![D_88]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', D_88)=k7_relat_1('#skF_4', D_88) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_32, c_91])).
% 2.37/1.32  tff(c_96, plain, (![D_88]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', D_88)=k7_relat_1('#skF_4', D_88))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_93])).
% 2.37/1.32  tff(c_168, plain, (![C_110, B_111, A_108, D_109, E_107]: (k3_tmap_1(A_108, B_111, C_110, D_109, E_107)=k2_partfun1(u1_struct_0(C_110), u1_struct_0(B_111), E_107, u1_struct_0(D_109)) | ~m1_pre_topc(D_109, C_110) | ~m1_subset_1(E_107, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_110), u1_struct_0(B_111)))) | ~v1_funct_2(E_107, u1_struct_0(C_110), u1_struct_0(B_111)) | ~v1_funct_1(E_107) | ~m1_pre_topc(D_109, A_108) | ~m1_pre_topc(C_110, A_108) | ~l1_pre_topc(B_111) | ~v2_pre_topc(B_111) | v2_struct_0(B_111) | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108) | v2_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.37/1.32  tff(c_170, plain, (![A_108, D_109]: (k3_tmap_1(A_108, '#skF_2', '#skF_3', D_109, '#skF_4')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_109)) | ~m1_pre_topc(D_109, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc(D_109, A_108) | ~m1_pre_topc('#skF_3', A_108) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108) | v2_struct_0(A_108))), inference(resolution, [status(thm)], [c_32, c_168])).
% 2.37/1.32  tff(c_173, plain, (![D_109, A_108]: (k7_relat_1('#skF_4', u1_struct_0(D_109))=k3_tmap_1(A_108, '#skF_2', '#skF_3', D_109, '#skF_4') | ~m1_pre_topc(D_109, '#skF_3') | ~m1_pre_topc(D_109, A_108) | ~m1_pre_topc('#skF_3', A_108) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108) | v2_struct_0(A_108))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_36, c_34, c_96, c_170])).
% 2.37/1.32  tff(c_175, plain, (![D_112, A_113]: (k7_relat_1('#skF_4', u1_struct_0(D_112))=k3_tmap_1(A_113, '#skF_2', '#skF_3', D_112, '#skF_4') | ~m1_pre_topc(D_112, '#skF_3') | ~m1_pre_topc(D_112, A_113) | ~m1_pre_topc('#skF_3', A_113) | ~l1_pre_topc(A_113) | ~v2_pre_topc(A_113) | v2_struct_0(A_113))), inference(negUnitSimplification, [status(thm)], [c_46, c_173])).
% 2.37/1.32  tff(c_179, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_175])).
% 2.37/1.32  tff(c_186, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_38, c_152, c_86, c_179])).
% 2.37/1.32  tff(c_187, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_52, c_186])).
% 2.37/1.32  tff(c_30, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.37/1.32  tff(c_188, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_187, c_30])).
% 2.37/1.32  tff(c_191, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_111, c_188])).
% 2.37/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.32  
% 2.37/1.32  Inference rules
% 2.37/1.32  ----------------------
% 2.37/1.32  #Ref     : 0
% 2.37/1.32  #Sup     : 24
% 2.37/1.32  #Fact    : 0
% 2.37/1.32  #Define  : 0
% 2.37/1.32  #Split   : 1
% 2.37/1.32  #Chain   : 0
% 2.37/1.32  #Close   : 0
% 2.37/1.32  
% 2.37/1.32  Ordering : KBO
% 2.37/1.32  
% 2.37/1.32  Simplification rules
% 2.37/1.32  ----------------------
% 2.37/1.32  #Subsume      : 1
% 2.37/1.32  #Demod        : 31
% 2.37/1.32  #Tautology    : 11
% 2.37/1.32  #SimpNegUnit  : 3
% 2.37/1.32  #BackRed      : 1
% 2.37/1.32  
% 2.37/1.32  #Partial instantiations: 0
% 2.37/1.32  #Strategies tried      : 1
% 2.37/1.32  
% 2.37/1.32  Timing (in seconds)
% 2.37/1.32  ----------------------
% 2.37/1.33  Preprocessing        : 0.35
% 2.37/1.33  Parsing              : 0.18
% 2.55/1.33  CNF conversion       : 0.03
% 2.55/1.33  Main loop            : 0.20
% 2.55/1.33  Inferencing          : 0.07
% 2.55/1.33  Reduction            : 0.07
% 2.55/1.33  Demodulation         : 0.05
% 2.55/1.33  BG Simplification    : 0.01
% 2.55/1.33  Subsumption          : 0.04
% 2.55/1.33  Abstraction          : 0.01
% 2.55/1.33  MUC search           : 0.00
% 2.55/1.33  Cooper               : 0.00
% 2.55/1.33  Total                : 0.59
% 2.55/1.33  Index Insertion      : 0.00
% 2.55/1.33  Index Deletion       : 0.00
% 2.55/1.33  Index Matching       : 0.00
% 2.55/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
