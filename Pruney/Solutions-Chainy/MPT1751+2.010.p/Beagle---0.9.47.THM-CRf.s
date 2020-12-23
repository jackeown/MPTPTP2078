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
% DateTime   : Thu Dec  3 10:26:59 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 379 expanded)
%              Number of leaves         :   39 ( 160 expanded)
%              Depth                    :   14
%              Number of atoms          :  215 (1979 expanded)
%              Number of equality atoms :   30 ( 205 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_160,negated_conjecture,(
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
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                       => ( r1_tarski(E,u1_struct_0(C))
                         => k7_relset_1(u1_struct_0(B),u1_struct_0(A),D,E) = k7_relset_1(u1_struct_0(C),u1_struct_0(A),k2_tmap_1(B,A,D,C),E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_tmap_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_117,axiom,(
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

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_124,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r1_tarski(k7_relset_1(A,B,D,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_2)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( ~ v1_xboole_0(D)
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,A,D)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,D))) )
         => ( ( r1_tarski(B,A)
              & r1_tarski(k7_relset_1(A,D,E,B),C) )
           => ( v1_funct_1(k2_partfun1(A,D,E,B))
              & v1_funct_2(k2_partfun1(A,D,E,B),B,C)
              & m1_subset_1(k2_partfun1(A,D,E,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).

tff(f_90,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_42,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_32,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_73,plain,(
    ! [C_81,A_82,B_83] :
      ( v1_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_81,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_73])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_38,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_127,plain,(
    ! [A_103,B_104,C_105,D_106] :
      ( k2_partfun1(A_103,B_104,C_105,D_106) = k7_relat_1(C_105,D_106)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104)))
      | ~ v1_funct_1(C_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_129,plain,(
    ! [D_106] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_106) = k7_relat_1('#skF_4',D_106)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_127])).

tff(c_135,plain,(
    ! [D_106] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_106) = k7_relat_1('#skF_4',D_106) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_129])).

tff(c_318,plain,(
    ! [A_156,B_157,C_158,D_159] :
      ( k2_partfun1(u1_struct_0(A_156),u1_struct_0(B_157),C_158,u1_struct_0(D_159)) = k2_tmap_1(A_156,B_157,C_158,D_159)
      | ~ m1_pre_topc(D_159,A_156)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_156),u1_struct_0(B_157))))
      | ~ v1_funct_2(C_158,u1_struct_0(A_156),u1_struct_0(B_157))
      | ~ v1_funct_1(C_158)
      | ~ l1_pre_topc(B_157)
      | ~ v2_pre_topc(B_157)
      | v2_struct_0(B_157)
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_326,plain,(
    ! [D_159] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_159)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_159)
      | ~ m1_pre_topc(D_159,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36,c_318])).

tff(c_334,plain,(
    ! [D_159] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_159)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_159)
      | ~ m1_pre_topc(D_159,'#skF_2')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_54,c_52,c_40,c_38,c_135,c_326])).

tff(c_337,plain,(
    ! [D_160] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_160)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_160)
      | ~ m1_pre_topc(D_160,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_56,c_334])).

tff(c_6,plain,(
    ! [A_3,C_7,B_6] :
      ( k9_relat_1(k7_relat_1(A_3,C_7),B_6) = k9_relat_1(A_3,B_6)
      | ~ r1_tarski(B_6,C_7)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_355,plain,(
    ! [D_160,B_6] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_160),B_6) = k9_relat_1('#skF_4',B_6)
      | ~ r1_tarski(B_6,u1_struct_0(D_160))
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(D_160,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_6])).

tff(c_384,plain,(
    ! [D_167,B_168] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_167),B_168) = k9_relat_1('#skF_4',B_168)
      | ~ r1_tarski(B_168,u1_struct_0(D_167))
      | ~ m1_pre_topc(D_167,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_355])).

tff(c_400,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_384])).

tff(c_407,plain,(
    k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_400])).

tff(c_335,plain,(
    ! [D_159] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_159)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_159)
      | ~ m1_pre_topc(D_159,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_56,c_334])).

tff(c_89,plain,(
    ! [B_87,A_88] :
      ( m1_subset_1(u1_struct_0(B_87),k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m1_pre_topc(B_87,A_88)
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_93,plain,(
    ! [B_87,A_88] :
      ( r1_tarski(u1_struct_0(B_87),u1_struct_0(A_88))
      | ~ m1_pre_topc(B_87,A_88)
      | ~ l1_pre_topc(A_88) ) ),
    inference(resolution,[status(thm)],[c_89,c_2])).

tff(c_104,plain,(
    ! [A_94,B_95,C_96,D_97] :
      ( k7_relset_1(A_94,B_95,C_96,D_97) = k9_relat_1(C_96,D_97)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_110,plain,(
    ! [D_97] : k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_97) = k9_relat_1('#skF_4',D_97) ),
    inference(resolution,[status(thm)],[c_36,c_104])).

tff(c_152,plain,(
    ! [A_112,B_113,D_114,C_115] :
      ( r1_tarski(k7_relset_1(A_112,B_113,D_114,C_115),B_113)
      | ~ m1_subset_1(D_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113)))
      | ~ v1_funct_2(D_114,A_112,B_113)
      | ~ v1_funct_1(D_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_154,plain,(
    ! [C_115] :
      ( r1_tarski(k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',C_115),u1_struct_0('#skF_1'))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_152])).

tff(c_160,plain,(
    ! [C_115] : r1_tarski(k9_relat_1('#skF_4',C_115),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_110,c_154])).

tff(c_22,plain,(
    ! [A_29] :
      ( l1_struct_0(A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_163,plain,(
    ! [B_118,A_119,D_121,C_117,E_120] :
      ( v1_funct_1(k2_partfun1(A_119,D_121,E_120,B_118))
      | ~ r1_tarski(k7_relset_1(A_119,D_121,E_120,B_118),C_117)
      | ~ r1_tarski(B_118,A_119)
      | ~ m1_subset_1(E_120,k1_zfmisc_1(k2_zfmisc_1(A_119,D_121)))
      | ~ v1_funct_2(E_120,A_119,D_121)
      | ~ v1_funct_1(E_120)
      | v1_xboole_0(D_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_165,plain,(
    ! [D_97,C_117] :
      ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_97))
      | ~ r1_tarski(k9_relat_1('#skF_4',D_97),C_117)
      | ~ r1_tarski(D_97,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_163])).

tff(c_167,plain,(
    ! [D_97,C_117] :
      ( v1_funct_1(k7_relat_1('#skF_4',D_97))
      | ~ r1_tarski(k9_relat_1('#skF_4',D_97),C_117)
      | ~ r1_tarski(D_97,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_135,c_165])).

tff(c_168,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_24,plain,(
    ! [A_30] :
      ( ~ v1_xboole_0(u1_struct_0(A_30))
      | ~ l1_struct_0(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_171,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_168,c_24])).

tff(c_174,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_171])).

tff(c_177,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_174])).

tff(c_181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_177])).

tff(c_183,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_247,plain,(
    ! [D_149,E_148,C_145,B_146,A_147] :
      ( m1_subset_1(k2_partfun1(A_147,D_149,E_148,B_146),k1_zfmisc_1(k2_zfmisc_1(B_146,C_145)))
      | ~ r1_tarski(k7_relset_1(A_147,D_149,E_148,B_146),C_145)
      | ~ r1_tarski(B_146,A_147)
      | ~ m1_subset_1(E_148,k1_zfmisc_1(k2_zfmisc_1(A_147,D_149)))
      | ~ v1_funct_2(E_148,A_147,D_149)
      | ~ v1_funct_1(E_148)
      | v1_xboole_0(D_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_264,plain,(
    ! [D_106,C_145] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_106),k1_zfmisc_1(k2_zfmisc_1(D_106,C_145)))
      | ~ r1_tarski(k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_106),C_145)
      | ~ r1_tarski(D_106,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_247])).

tff(c_272,plain,(
    ! [D_106,C_145] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_106),k1_zfmisc_1(k2_zfmisc_1(D_106,C_145)))
      | ~ r1_tarski(k9_relat_1('#skF_4',D_106),C_145)
      | ~ r1_tarski(D_106,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_110,c_264])).

tff(c_274,plain,(
    ! [D_150,C_151] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_150),k1_zfmisc_1(k2_zfmisc_1(D_150,C_151)))
      | ~ r1_tarski(k9_relat_1('#skF_4',D_150),C_151)
      | ~ r1_tarski(D_150,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_272])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13,D_14] :
      ( k7_relset_1(A_11,B_12,C_13,D_14) = k9_relat_1(C_13,D_14)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_461,plain,(
    ! [D_182,C_183,D_184] :
      ( k7_relset_1(D_182,C_183,k7_relat_1('#skF_4',D_182),D_184) = k9_relat_1(k7_relat_1('#skF_4',D_182),D_184)
      | ~ r1_tarski(k9_relat_1('#skF_4',D_182),C_183)
      | ~ r1_tarski(D_182,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_274,c_10])).

tff(c_465,plain,(
    ! [C_185,D_186] :
      ( k7_relset_1(C_185,u1_struct_0('#skF_1'),k7_relat_1('#skF_4',C_185),D_186) = k9_relat_1(k7_relat_1('#skF_4',C_185),D_186)
      | ~ r1_tarski(C_185,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_160,c_461])).

tff(c_519,plain,(
    ! [D_197,D_198] :
      ( k7_relset_1(u1_struct_0(D_197),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4',D_197),D_198) = k9_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_197)),D_198)
      | ~ r1_tarski(u1_struct_0(D_197),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_197,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_465])).

tff(c_30,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_112,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_30])).

tff(c_532,plain,
    ( k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_519,c_112])).

tff(c_540,plain,
    ( k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_532])).

tff(c_542,plain,(
    ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_540])).

tff(c_545,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_93,c_542])).

tff(c_549,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_545])).

tff(c_550,plain,(
    k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_540])).

tff(c_597,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_550])).

tff(c_603,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_407,c_597])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:48:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.34/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.55  
% 3.34/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.56  %$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.34/1.56  
% 3.34/1.56  %Foreground sorts:
% 3.34/1.56  
% 3.34/1.56  
% 3.34/1.56  %Background operators:
% 3.34/1.56  
% 3.34/1.56  
% 3.34/1.56  %Foreground operators:
% 3.34/1.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.34/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.34/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.34/1.56  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.34/1.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.34/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.34/1.56  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.34/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.34/1.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.34/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.34/1.56  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.34/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.34/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.34/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.34/1.56  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.34/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.34/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.34/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.34/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.34/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.34/1.56  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.34/1.56  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.34/1.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.34/1.56  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.34/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.34/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.34/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.34/1.56  
% 3.34/1.58  tff(f_160, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (r1_tarski(E, u1_struct_0(C)) => (k7_relset_1(u1_struct_0(B), u1_struct_0(A), D, E) = k7_relset_1(u1_struct_0(C), u1_struct_0(A), k2_tmap_1(B, A, D, C), E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_tmap_1)).
% 3.34/1.58  tff(f_40, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.34/1.58  tff(f_50, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.34/1.58  tff(f_117, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.34/1.58  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 3.34/1.58  tff(f_124, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.34/1.58  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.34/1.58  tff(f_44, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.34/1.58  tff(f_78, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r1_tarski(k7_relset_1(A, B, D, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_funct_2)).
% 3.34/1.58  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.34/1.58  tff(f_70, axiom, (![A, B, C, D]: (~v1_xboole_0(D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, A, D)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, D)))) => ((r1_tarski(B, A) & r1_tarski(k7_relset_1(A, D, E, B), C)) => ((v1_funct_1(k2_partfun1(A, D, E, B)) & v1_funct_2(k2_partfun1(A, D, E, B), B, C)) & m1_subset_1(k2_partfun1(A, D, E, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_funct_2)).
% 3.34/1.58  tff(f_90, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.34/1.58  tff(c_42, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.34/1.58  tff(c_32, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.34/1.58  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.34/1.58  tff(c_73, plain, (![C_81, A_82, B_83]: (v1_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.34/1.58  tff(c_81, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_73])).
% 3.34/1.58  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.34/1.58  tff(c_56, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.34/1.58  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.34/1.58  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.34/1.58  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.34/1.58  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.34/1.58  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.34/1.58  tff(c_38, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.34/1.58  tff(c_127, plain, (![A_103, B_104, C_105, D_106]: (k2_partfun1(A_103, B_104, C_105, D_106)=k7_relat_1(C_105, D_106) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))) | ~v1_funct_1(C_105))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.34/1.58  tff(c_129, plain, (![D_106]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_106)=k7_relat_1('#skF_4', D_106) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_127])).
% 3.34/1.58  tff(c_135, plain, (![D_106]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_106)=k7_relat_1('#skF_4', D_106))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_129])).
% 3.34/1.58  tff(c_318, plain, (![A_156, B_157, C_158, D_159]: (k2_partfun1(u1_struct_0(A_156), u1_struct_0(B_157), C_158, u1_struct_0(D_159))=k2_tmap_1(A_156, B_157, C_158, D_159) | ~m1_pre_topc(D_159, A_156) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_156), u1_struct_0(B_157)))) | ~v1_funct_2(C_158, u1_struct_0(A_156), u1_struct_0(B_157)) | ~v1_funct_1(C_158) | ~l1_pre_topc(B_157) | ~v2_pre_topc(B_157) | v2_struct_0(B_157) | ~l1_pre_topc(A_156) | ~v2_pre_topc(A_156) | v2_struct_0(A_156))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.34/1.58  tff(c_326, plain, (![D_159]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_159))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_159) | ~m1_pre_topc(D_159, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_318])).
% 3.34/1.58  tff(c_334, plain, (![D_159]: (k7_relat_1('#skF_4', u1_struct_0(D_159))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_159) | ~m1_pre_topc(D_159, '#skF_2') | v2_struct_0('#skF_1') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_54, c_52, c_40, c_38, c_135, c_326])).
% 3.34/1.58  tff(c_337, plain, (![D_160]: (k7_relat_1('#skF_4', u1_struct_0(D_160))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_160) | ~m1_pre_topc(D_160, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_56, c_334])).
% 3.34/1.58  tff(c_6, plain, (![A_3, C_7, B_6]: (k9_relat_1(k7_relat_1(A_3, C_7), B_6)=k9_relat_1(A_3, B_6) | ~r1_tarski(B_6, C_7) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.34/1.58  tff(c_355, plain, (![D_160, B_6]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_160), B_6)=k9_relat_1('#skF_4', B_6) | ~r1_tarski(B_6, u1_struct_0(D_160)) | ~v1_relat_1('#skF_4') | ~m1_pre_topc(D_160, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_337, c_6])).
% 3.34/1.58  tff(c_384, plain, (![D_167, B_168]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_167), B_168)=k9_relat_1('#skF_4', B_168) | ~r1_tarski(B_168, u1_struct_0(D_167)) | ~m1_pre_topc(D_167, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_355])).
% 3.34/1.58  tff(c_400, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_384])).
% 3.34/1.58  tff(c_407, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_400])).
% 3.34/1.58  tff(c_335, plain, (![D_159]: (k7_relat_1('#skF_4', u1_struct_0(D_159))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_159) | ~m1_pre_topc(D_159, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_56, c_334])).
% 3.34/1.58  tff(c_89, plain, (![B_87, A_88]: (m1_subset_1(u1_struct_0(B_87), k1_zfmisc_1(u1_struct_0(A_88))) | ~m1_pre_topc(B_87, A_88) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.34/1.58  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.34/1.58  tff(c_93, plain, (![B_87, A_88]: (r1_tarski(u1_struct_0(B_87), u1_struct_0(A_88)) | ~m1_pre_topc(B_87, A_88) | ~l1_pre_topc(A_88))), inference(resolution, [status(thm)], [c_89, c_2])).
% 3.34/1.58  tff(c_104, plain, (![A_94, B_95, C_96, D_97]: (k7_relset_1(A_94, B_95, C_96, D_97)=k9_relat_1(C_96, D_97) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.34/1.58  tff(c_110, plain, (![D_97]: (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_97)=k9_relat_1('#skF_4', D_97))), inference(resolution, [status(thm)], [c_36, c_104])).
% 3.34/1.58  tff(c_152, plain, (![A_112, B_113, D_114, C_115]: (r1_tarski(k7_relset_1(A_112, B_113, D_114, C_115), B_113) | ~m1_subset_1(D_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))) | ~v1_funct_2(D_114, A_112, B_113) | ~v1_funct_1(D_114))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.34/1.58  tff(c_154, plain, (![C_115]: (r1_tarski(k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', C_115), u1_struct_0('#skF_1')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_152])).
% 3.34/1.58  tff(c_160, plain, (![C_115]: (r1_tarski(k9_relat_1('#skF_4', C_115), u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_110, c_154])).
% 3.34/1.58  tff(c_22, plain, (![A_29]: (l1_struct_0(A_29) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.34/1.58  tff(c_163, plain, (![B_118, A_119, D_121, C_117, E_120]: (v1_funct_1(k2_partfun1(A_119, D_121, E_120, B_118)) | ~r1_tarski(k7_relset_1(A_119, D_121, E_120, B_118), C_117) | ~r1_tarski(B_118, A_119) | ~m1_subset_1(E_120, k1_zfmisc_1(k2_zfmisc_1(A_119, D_121))) | ~v1_funct_2(E_120, A_119, D_121) | ~v1_funct_1(E_120) | v1_xboole_0(D_121))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.34/1.58  tff(c_165, plain, (![D_97, C_117]: (v1_funct_1(k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_97)) | ~r1_tarski(k9_relat_1('#skF_4', D_97), C_117) | ~r1_tarski(D_97, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_110, c_163])).
% 3.34/1.58  tff(c_167, plain, (![D_97, C_117]: (v1_funct_1(k7_relat_1('#skF_4', D_97)) | ~r1_tarski(k9_relat_1('#skF_4', D_97), C_117) | ~r1_tarski(D_97, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_135, c_165])).
% 3.34/1.58  tff(c_168, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_167])).
% 3.34/1.58  tff(c_24, plain, (![A_30]: (~v1_xboole_0(u1_struct_0(A_30)) | ~l1_struct_0(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.34/1.58  tff(c_171, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_168, c_24])).
% 3.34/1.58  tff(c_174, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_56, c_171])).
% 3.34/1.58  tff(c_177, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_174])).
% 3.34/1.58  tff(c_181, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_177])).
% 3.34/1.58  tff(c_183, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_167])).
% 3.34/1.58  tff(c_247, plain, (![D_149, E_148, C_145, B_146, A_147]: (m1_subset_1(k2_partfun1(A_147, D_149, E_148, B_146), k1_zfmisc_1(k2_zfmisc_1(B_146, C_145))) | ~r1_tarski(k7_relset_1(A_147, D_149, E_148, B_146), C_145) | ~r1_tarski(B_146, A_147) | ~m1_subset_1(E_148, k1_zfmisc_1(k2_zfmisc_1(A_147, D_149))) | ~v1_funct_2(E_148, A_147, D_149) | ~v1_funct_1(E_148) | v1_xboole_0(D_149))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.34/1.58  tff(c_264, plain, (![D_106, C_145]: (m1_subset_1(k7_relat_1('#skF_4', D_106), k1_zfmisc_1(k2_zfmisc_1(D_106, C_145))) | ~r1_tarski(k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_106), C_145) | ~r1_tarski(D_106, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_135, c_247])).
% 3.34/1.58  tff(c_272, plain, (![D_106, C_145]: (m1_subset_1(k7_relat_1('#skF_4', D_106), k1_zfmisc_1(k2_zfmisc_1(D_106, C_145))) | ~r1_tarski(k9_relat_1('#skF_4', D_106), C_145) | ~r1_tarski(D_106, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_110, c_264])).
% 3.34/1.58  tff(c_274, plain, (![D_150, C_151]: (m1_subset_1(k7_relat_1('#skF_4', D_150), k1_zfmisc_1(k2_zfmisc_1(D_150, C_151))) | ~r1_tarski(k9_relat_1('#skF_4', D_150), C_151) | ~r1_tarski(D_150, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_183, c_272])).
% 3.34/1.58  tff(c_10, plain, (![A_11, B_12, C_13, D_14]: (k7_relset_1(A_11, B_12, C_13, D_14)=k9_relat_1(C_13, D_14) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.34/1.58  tff(c_461, plain, (![D_182, C_183, D_184]: (k7_relset_1(D_182, C_183, k7_relat_1('#skF_4', D_182), D_184)=k9_relat_1(k7_relat_1('#skF_4', D_182), D_184) | ~r1_tarski(k9_relat_1('#skF_4', D_182), C_183) | ~r1_tarski(D_182, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_274, c_10])).
% 3.34/1.58  tff(c_465, plain, (![C_185, D_186]: (k7_relset_1(C_185, u1_struct_0('#skF_1'), k7_relat_1('#skF_4', C_185), D_186)=k9_relat_1(k7_relat_1('#skF_4', C_185), D_186) | ~r1_tarski(C_185, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_160, c_461])).
% 3.34/1.58  tff(c_519, plain, (![D_197, D_198]: (k7_relset_1(u1_struct_0(D_197), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_197), D_198)=k9_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_197)), D_198) | ~r1_tarski(u1_struct_0(D_197), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_197, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_335, c_465])).
% 3.34/1.58  tff(c_30, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.34/1.58  tff(c_112, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_30])).
% 3.34/1.58  tff(c_532, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_519, c_112])).
% 3.34/1.58  tff(c_540, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_532])).
% 3.34/1.58  tff(c_542, plain, (~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_540])).
% 3.34/1.58  tff(c_545, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_93, c_542])).
% 3.34/1.58  tff(c_549, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_545])).
% 3.34/1.58  tff(c_550, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_540])).
% 3.34/1.58  tff(c_597, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_335, c_550])).
% 3.34/1.58  tff(c_603, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_407, c_597])).
% 3.34/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.58  
% 3.34/1.58  Inference rules
% 3.34/1.58  ----------------------
% 3.34/1.58  #Ref     : 0
% 3.34/1.58  #Sup     : 120
% 3.34/1.58  #Fact    : 0
% 3.34/1.58  #Define  : 0
% 3.34/1.58  #Split   : 4
% 3.34/1.58  #Chain   : 0
% 3.34/1.58  #Close   : 0
% 3.34/1.58  
% 3.34/1.58  Ordering : KBO
% 3.34/1.58  
% 3.34/1.58  Simplification rules
% 3.34/1.58  ----------------------
% 3.34/1.58  #Subsume      : 14
% 3.34/1.58  #Demod        : 57
% 3.34/1.58  #Tautology    : 21
% 3.34/1.58  #SimpNegUnit  : 11
% 3.34/1.58  #BackRed      : 1
% 3.34/1.58  
% 3.34/1.58  #Partial instantiations: 0
% 3.34/1.58  #Strategies tried      : 1
% 3.34/1.58  
% 3.34/1.58  Timing (in seconds)
% 3.34/1.58  ----------------------
% 3.34/1.58  Preprocessing        : 0.37
% 3.34/1.58  Parsing              : 0.21
% 3.34/1.58  CNF conversion       : 0.03
% 3.34/1.58  Main loop            : 0.39
% 3.34/1.58  Inferencing          : 0.15
% 3.34/1.58  Reduction            : 0.11
% 3.34/1.58  Demodulation         : 0.08
% 3.34/1.58  BG Simplification    : 0.02
% 3.34/1.58  Subsumption          : 0.07
% 3.34/1.58  Abstraction          : 0.02
% 3.34/1.58  MUC search           : 0.00
% 3.34/1.58  Cooper               : 0.00
% 3.34/1.58  Total                : 0.80
% 3.34/1.58  Index Insertion      : 0.00
% 3.34/1.58  Index Deletion       : 0.00
% 3.34/1.58  Index Matching       : 0.00
% 3.34/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
