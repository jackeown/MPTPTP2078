%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:59 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 381 expanded)
%              Number of leaves         :   39 ( 161 expanded)
%              Depth                    :   14
%              Number of atoms          :  223 (2002 expanded)
%              Number of equality atoms :   30 ( 206 expanded)
%              Maximal formula depth    :   16 (   5 average)
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
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                       => ( r1_tarski(E,u1_struct_0(C))
                         => k7_relset_1(u1_struct_0(B),u1_struct_0(A),D,E) = k7_relset_1(u1_struct_0(C),u1_struct_0(A),k2_tmap_1(B,A,D,C),E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_tmap_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

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
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_117,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_131,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r1_tarski(k7_relset_1(A,B,D,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_2)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_66,axiom,(
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

tff(f_86,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_42,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_32,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_4,plain,(
    ! [C_8,A_6,B_7] :
      ( v1_relat_1(C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_64,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_4])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_38,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_88,plain,(
    ! [A_92,B_93,C_94,D_95] :
      ( k2_partfun1(A_92,B_93,C_94,D_95) = k7_relat_1(C_94,D_95)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93)))
      | ~ v1_funct_1(C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_90,plain,(
    ! [D_95] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_95) = k7_relat_1('#skF_4',D_95)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_88])).

tff(c_93,plain,(
    ! [D_95] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_95) = k7_relat_1('#skF_4',D_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_90])).

tff(c_224,plain,(
    ! [A_137,B_138,C_139,D_140] :
      ( k2_partfun1(u1_struct_0(A_137),u1_struct_0(B_138),C_139,u1_struct_0(D_140)) = k2_tmap_1(A_137,B_138,C_139,D_140)
      | ~ m1_pre_topc(D_140,A_137)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_137),u1_struct_0(B_138))))
      | ~ v1_funct_2(C_139,u1_struct_0(A_137),u1_struct_0(B_138))
      | ~ v1_funct_1(C_139)
      | ~ l1_pre_topc(B_138)
      | ~ v2_pre_topc(B_138)
      | v2_struct_0(B_138)
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_232,plain,(
    ! [D_140] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_140)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_140)
      | ~ m1_pre_topc(D_140,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36,c_224])).

tff(c_237,plain,(
    ! [D_140] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_140)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_140)
      | ~ m1_pre_topc(D_140,'#skF_2')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_54,c_52,c_40,c_38,c_93,c_232])).

tff(c_240,plain,(
    ! [D_142] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_142)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_142)
      | ~ m1_pre_topc(D_142,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_56,c_237])).

tff(c_2,plain,(
    ! [A_1,C_5,B_4] :
      ( k9_relat_1(k7_relat_1(A_1,C_5),B_4) = k9_relat_1(A_1,B_4)
      | ~ r1_tarski(B_4,C_5)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_258,plain,(
    ! [D_142,B_4] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_142),B_4) = k9_relat_1('#skF_4',B_4)
      | ~ r1_tarski(B_4,u1_struct_0(D_142))
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(D_142,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_2])).

tff(c_268,plain,(
    ! [D_145,B_146] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_145),B_146) = k9_relat_1('#skF_4',B_146)
      | ~ r1_tarski(B_146,u1_struct_0(D_145))
      | ~ m1_pre_topc(D_145,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_258])).

tff(c_280,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_268])).

tff(c_288,plain,(
    k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_280])).

tff(c_238,plain,(
    ! [D_140] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_140)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_140)
      | ~ m1_pre_topc(D_140,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_56,c_237])).

tff(c_24,plain,(
    ! [A_44] :
      ( m1_pre_topc(A_44,A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_104,plain,(
    ! [B_100,C_101,A_102] :
      ( r1_tarski(u1_struct_0(B_100),u1_struct_0(C_101))
      | ~ m1_pre_topc(B_100,C_101)
      | ~ m1_pre_topc(C_101,A_102)
      | ~ m1_pre_topc(B_100,A_102)
      | ~ l1_pre_topc(A_102)
      | ~ v2_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_109,plain,(
    ! [B_100,A_44] :
      ( r1_tarski(u1_struct_0(B_100),u1_struct_0(A_44))
      | ~ m1_pre_topc(B_100,A_44)
      | ~ v2_pre_topc(A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(resolution,[status(thm)],[c_24,c_104])).

tff(c_74,plain,(
    ! [A_87,B_88,C_89,D_90] :
      ( k7_relset_1(A_87,B_88,C_89,D_90) = k9_relat_1(C_89,D_90)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_77,plain,(
    ! [D_90] : k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_90) = k9_relat_1('#skF_4',D_90) ),
    inference(resolution,[status(thm)],[c_36,c_74])).

tff(c_121,plain,(
    ! [A_106,B_107,D_108,C_109] :
      ( r1_tarski(k7_relset_1(A_106,B_107,D_108,C_109),B_107)
      | ~ m1_subset_1(D_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107)))
      | ~ v1_funct_2(D_108,A_106,B_107)
      | ~ v1_funct_1(D_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_123,plain,(
    ! [C_109] :
      ( r1_tarski(k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',C_109),u1_struct_0('#skF_1'))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_121])).

tff(c_126,plain,(
    ! [C_109] : r1_tarski(k9_relat_1('#skF_4',C_109),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_77,c_123])).

tff(c_18,plain,(
    ! [A_27] :
      ( l1_struct_0(A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_128,plain,(
    ! [E_115,A_112,C_111,D_114,B_113] :
      ( v1_funct_1(k2_partfun1(A_112,D_114,E_115,B_113))
      | ~ r1_tarski(k7_relset_1(A_112,D_114,E_115,B_113),C_111)
      | ~ r1_tarski(B_113,A_112)
      | ~ m1_subset_1(E_115,k1_zfmisc_1(k2_zfmisc_1(A_112,D_114)))
      | ~ v1_funct_2(E_115,A_112,D_114)
      | ~ v1_funct_1(E_115)
      | v1_xboole_0(D_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_130,plain,(
    ! [D_90,C_111] :
      ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_90))
      | ~ r1_tarski(k9_relat_1('#skF_4',D_90),C_111)
      | ~ r1_tarski(D_90,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_128])).

tff(c_132,plain,(
    ! [D_90,C_111] :
      ( v1_funct_1(k7_relat_1('#skF_4',D_90))
      | ~ r1_tarski(k9_relat_1('#skF_4',D_90),C_111)
      | ~ r1_tarski(D_90,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_93,c_130])).

tff(c_133,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_20,plain,(
    ! [A_28] :
      ( ~ v1_xboole_0(u1_struct_0(A_28))
      | ~ l1_struct_0(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_136,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_133,c_20])).

tff(c_139,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_136])).

tff(c_142,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_139])).

tff(c_146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_142])).

tff(c_148,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_171,plain,(
    ! [D_130,B_129,A_128,E_131,C_127] :
      ( m1_subset_1(k2_partfun1(A_128,D_130,E_131,B_129),k1_zfmisc_1(k2_zfmisc_1(B_129,C_127)))
      | ~ r1_tarski(k7_relset_1(A_128,D_130,E_131,B_129),C_127)
      | ~ r1_tarski(B_129,A_128)
      | ~ m1_subset_1(E_131,k1_zfmisc_1(k2_zfmisc_1(A_128,D_130)))
      | ~ v1_funct_2(E_131,A_128,D_130)
      | ~ v1_funct_1(E_131)
      | v1_xboole_0(D_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_185,plain,(
    ! [D_95,C_127] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_95),k1_zfmisc_1(k2_zfmisc_1(D_95,C_127)))
      | ~ r1_tarski(k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_95),C_127)
      | ~ r1_tarski(D_95,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_171])).

tff(c_192,plain,(
    ! [D_95,C_127] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_95),k1_zfmisc_1(k2_zfmisc_1(D_95,C_127)))
      | ~ r1_tarski(k9_relat_1('#skF_4',D_95),C_127)
      | ~ r1_tarski(D_95,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_77,c_185])).

tff(c_194,plain,(
    ! [D_132,C_133] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_132),k1_zfmisc_1(k2_zfmisc_1(D_132,C_133)))
      | ~ r1_tarski(k9_relat_1('#skF_4',D_132),C_133)
      | ~ r1_tarski(D_132,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_192])).

tff(c_6,plain,(
    ! [A_9,B_10,C_11,D_12] :
      ( k7_relset_1(A_9,B_10,C_11,D_12) = k9_relat_1(C_11,D_12)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_309,plain,(
    ! [D_153,C_154,D_155] :
      ( k7_relset_1(D_153,C_154,k7_relat_1('#skF_4',D_153),D_155) = k9_relat_1(k7_relat_1('#skF_4',D_153),D_155)
      | ~ r1_tarski(k9_relat_1('#skF_4',D_153),C_154)
      | ~ r1_tarski(D_153,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_194,c_6])).

tff(c_313,plain,(
    ! [C_156,D_157] :
      ( k7_relset_1(C_156,u1_struct_0('#skF_1'),k7_relat_1('#skF_4',C_156),D_157) = k9_relat_1(k7_relat_1('#skF_4',C_156),D_157)
      | ~ r1_tarski(C_156,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_126,c_309])).

tff(c_418,plain,(
    ! [D_179,D_180] :
      ( k7_relset_1(u1_struct_0(D_179),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4',D_179),D_180) = k9_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_179)),D_180)
      | ~ r1_tarski(u1_struct_0(D_179),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_179,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_313])).

tff(c_30,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_78,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_30])).

tff(c_430,plain,
    ( k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_78])).

tff(c_439,plain,
    ( k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_430])).

tff(c_441,plain,(
    ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_439])).

tff(c_457,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_109,c_441])).

tff(c_461,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_42,c_457])).

tff(c_462,plain,(
    k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_439])).

tff(c_504,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_462])).

tff(c_510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_288,c_504])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.45  
% 2.78/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.45  %$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.78/1.45  
% 2.78/1.45  %Foreground sorts:
% 2.78/1.45  
% 2.78/1.45  
% 2.78/1.45  %Background operators:
% 2.78/1.45  
% 2.78/1.45  
% 2.78/1.45  %Foreground operators:
% 2.78/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.78/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.78/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.45  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.78/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.78/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.45  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.78/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.78/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.78/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.78/1.45  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.78/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.78/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.78/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.78/1.45  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.78/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.78/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.78/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.78/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.45  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.78/1.45  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.78/1.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.78/1.45  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.78/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.78/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.78/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.78/1.45  
% 2.78/1.47  tff(f_167, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (r1_tarski(E, u1_struct_0(C)) => (k7_relset_1(u1_struct_0(B), u1_struct_0(A), D, E) = k7_relset_1(u1_struct_0(C), u1_struct_0(A), k2_tmap_1(B, A, D, C), E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_tmap_1)).
% 2.78/1.47  tff(f_36, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.78/1.47  tff(f_46, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.78/1.47  tff(f_113, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 2.78/1.47  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 2.78/1.47  tff(f_117, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 2.78/1.47  tff(f_131, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 2.78/1.47  tff(f_40, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.78/1.47  tff(f_74, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r1_tarski(k7_relset_1(A, B, D, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_funct_2)).
% 2.78/1.47  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.78/1.47  tff(f_66, axiom, (![A, B, C, D]: (~v1_xboole_0(D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, A, D)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, D)))) => ((r1_tarski(B, A) & r1_tarski(k7_relset_1(A, D, E, B), C)) => ((v1_funct_1(k2_partfun1(A, D, E, B)) & v1_funct_2(k2_partfun1(A, D, E, B), B, C)) & m1_subset_1(k2_partfun1(A, D, E, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_funct_2)).
% 2.78/1.47  tff(f_86, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.78/1.47  tff(c_42, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.78/1.47  tff(c_32, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.78/1.47  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.78/1.47  tff(c_4, plain, (![C_8, A_6, B_7]: (v1_relat_1(C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.78/1.47  tff(c_64, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_4])).
% 2.78/1.47  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.78/1.47  tff(c_56, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.78/1.47  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.78/1.47  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.78/1.47  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.78/1.47  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.78/1.47  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.78/1.47  tff(c_38, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.78/1.47  tff(c_88, plain, (![A_92, B_93, C_94, D_95]: (k2_partfun1(A_92, B_93, C_94, D_95)=k7_relat_1(C_94, D_95) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))) | ~v1_funct_1(C_94))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.78/1.47  tff(c_90, plain, (![D_95]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_95)=k7_relat_1('#skF_4', D_95) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_88])).
% 2.78/1.47  tff(c_93, plain, (![D_95]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_95)=k7_relat_1('#skF_4', D_95))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_90])).
% 2.78/1.47  tff(c_224, plain, (![A_137, B_138, C_139, D_140]: (k2_partfun1(u1_struct_0(A_137), u1_struct_0(B_138), C_139, u1_struct_0(D_140))=k2_tmap_1(A_137, B_138, C_139, D_140) | ~m1_pre_topc(D_140, A_137) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_137), u1_struct_0(B_138)))) | ~v1_funct_2(C_139, u1_struct_0(A_137), u1_struct_0(B_138)) | ~v1_funct_1(C_139) | ~l1_pre_topc(B_138) | ~v2_pre_topc(B_138) | v2_struct_0(B_138) | ~l1_pre_topc(A_137) | ~v2_pre_topc(A_137) | v2_struct_0(A_137))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.47  tff(c_232, plain, (![D_140]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_140))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_140) | ~m1_pre_topc(D_140, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_224])).
% 2.78/1.47  tff(c_237, plain, (![D_140]: (k7_relat_1('#skF_4', u1_struct_0(D_140))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_140) | ~m1_pre_topc(D_140, '#skF_2') | v2_struct_0('#skF_1') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_54, c_52, c_40, c_38, c_93, c_232])).
% 2.78/1.47  tff(c_240, plain, (![D_142]: (k7_relat_1('#skF_4', u1_struct_0(D_142))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_142) | ~m1_pre_topc(D_142, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_56, c_237])).
% 2.78/1.47  tff(c_2, plain, (![A_1, C_5, B_4]: (k9_relat_1(k7_relat_1(A_1, C_5), B_4)=k9_relat_1(A_1, B_4) | ~r1_tarski(B_4, C_5) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.78/1.47  tff(c_258, plain, (![D_142, B_4]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_142), B_4)=k9_relat_1('#skF_4', B_4) | ~r1_tarski(B_4, u1_struct_0(D_142)) | ~v1_relat_1('#skF_4') | ~m1_pre_topc(D_142, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_240, c_2])).
% 2.78/1.47  tff(c_268, plain, (![D_145, B_146]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_145), B_146)=k9_relat_1('#skF_4', B_146) | ~r1_tarski(B_146, u1_struct_0(D_145)) | ~m1_pre_topc(D_145, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_258])).
% 2.78/1.47  tff(c_280, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_268])).
% 2.78/1.47  tff(c_288, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_280])).
% 2.78/1.47  tff(c_238, plain, (![D_140]: (k7_relat_1('#skF_4', u1_struct_0(D_140))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_140) | ~m1_pre_topc(D_140, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_56, c_237])).
% 2.78/1.47  tff(c_24, plain, (![A_44]: (m1_pre_topc(A_44, A_44) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.78/1.47  tff(c_104, plain, (![B_100, C_101, A_102]: (r1_tarski(u1_struct_0(B_100), u1_struct_0(C_101)) | ~m1_pre_topc(B_100, C_101) | ~m1_pre_topc(C_101, A_102) | ~m1_pre_topc(B_100, A_102) | ~l1_pre_topc(A_102) | ~v2_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.78/1.47  tff(c_109, plain, (![B_100, A_44]: (r1_tarski(u1_struct_0(B_100), u1_struct_0(A_44)) | ~m1_pre_topc(B_100, A_44) | ~v2_pre_topc(A_44) | ~l1_pre_topc(A_44))), inference(resolution, [status(thm)], [c_24, c_104])).
% 2.78/1.47  tff(c_74, plain, (![A_87, B_88, C_89, D_90]: (k7_relset_1(A_87, B_88, C_89, D_90)=k9_relat_1(C_89, D_90) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.78/1.47  tff(c_77, plain, (![D_90]: (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_90)=k9_relat_1('#skF_4', D_90))), inference(resolution, [status(thm)], [c_36, c_74])).
% 2.78/1.47  tff(c_121, plain, (![A_106, B_107, D_108, C_109]: (r1_tarski(k7_relset_1(A_106, B_107, D_108, C_109), B_107) | ~m1_subset_1(D_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))) | ~v1_funct_2(D_108, A_106, B_107) | ~v1_funct_1(D_108))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.78/1.47  tff(c_123, plain, (![C_109]: (r1_tarski(k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', C_109), u1_struct_0('#skF_1')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_121])).
% 2.78/1.47  tff(c_126, plain, (![C_109]: (r1_tarski(k9_relat_1('#skF_4', C_109), u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_77, c_123])).
% 2.78/1.47  tff(c_18, plain, (![A_27]: (l1_struct_0(A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.78/1.47  tff(c_128, plain, (![E_115, A_112, C_111, D_114, B_113]: (v1_funct_1(k2_partfun1(A_112, D_114, E_115, B_113)) | ~r1_tarski(k7_relset_1(A_112, D_114, E_115, B_113), C_111) | ~r1_tarski(B_113, A_112) | ~m1_subset_1(E_115, k1_zfmisc_1(k2_zfmisc_1(A_112, D_114))) | ~v1_funct_2(E_115, A_112, D_114) | ~v1_funct_1(E_115) | v1_xboole_0(D_114))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.78/1.47  tff(c_130, plain, (![D_90, C_111]: (v1_funct_1(k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_90)) | ~r1_tarski(k9_relat_1('#skF_4', D_90), C_111) | ~r1_tarski(D_90, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_77, c_128])).
% 2.78/1.47  tff(c_132, plain, (![D_90, C_111]: (v1_funct_1(k7_relat_1('#skF_4', D_90)) | ~r1_tarski(k9_relat_1('#skF_4', D_90), C_111) | ~r1_tarski(D_90, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_93, c_130])).
% 2.78/1.47  tff(c_133, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_132])).
% 2.78/1.47  tff(c_20, plain, (![A_28]: (~v1_xboole_0(u1_struct_0(A_28)) | ~l1_struct_0(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.78/1.47  tff(c_136, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_133, c_20])).
% 2.78/1.47  tff(c_139, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_56, c_136])).
% 2.78/1.47  tff(c_142, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_139])).
% 2.78/1.47  tff(c_146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_142])).
% 2.78/1.47  tff(c_148, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_132])).
% 2.78/1.47  tff(c_171, plain, (![D_130, B_129, A_128, E_131, C_127]: (m1_subset_1(k2_partfun1(A_128, D_130, E_131, B_129), k1_zfmisc_1(k2_zfmisc_1(B_129, C_127))) | ~r1_tarski(k7_relset_1(A_128, D_130, E_131, B_129), C_127) | ~r1_tarski(B_129, A_128) | ~m1_subset_1(E_131, k1_zfmisc_1(k2_zfmisc_1(A_128, D_130))) | ~v1_funct_2(E_131, A_128, D_130) | ~v1_funct_1(E_131) | v1_xboole_0(D_130))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.78/1.47  tff(c_185, plain, (![D_95, C_127]: (m1_subset_1(k7_relat_1('#skF_4', D_95), k1_zfmisc_1(k2_zfmisc_1(D_95, C_127))) | ~r1_tarski(k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_95), C_127) | ~r1_tarski(D_95, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_93, c_171])).
% 2.78/1.47  tff(c_192, plain, (![D_95, C_127]: (m1_subset_1(k7_relat_1('#skF_4', D_95), k1_zfmisc_1(k2_zfmisc_1(D_95, C_127))) | ~r1_tarski(k9_relat_1('#skF_4', D_95), C_127) | ~r1_tarski(D_95, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_77, c_185])).
% 2.78/1.47  tff(c_194, plain, (![D_132, C_133]: (m1_subset_1(k7_relat_1('#skF_4', D_132), k1_zfmisc_1(k2_zfmisc_1(D_132, C_133))) | ~r1_tarski(k9_relat_1('#skF_4', D_132), C_133) | ~r1_tarski(D_132, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_148, c_192])).
% 2.78/1.47  tff(c_6, plain, (![A_9, B_10, C_11, D_12]: (k7_relset_1(A_9, B_10, C_11, D_12)=k9_relat_1(C_11, D_12) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.78/1.47  tff(c_309, plain, (![D_153, C_154, D_155]: (k7_relset_1(D_153, C_154, k7_relat_1('#skF_4', D_153), D_155)=k9_relat_1(k7_relat_1('#skF_4', D_153), D_155) | ~r1_tarski(k9_relat_1('#skF_4', D_153), C_154) | ~r1_tarski(D_153, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_194, c_6])).
% 2.78/1.47  tff(c_313, plain, (![C_156, D_157]: (k7_relset_1(C_156, u1_struct_0('#skF_1'), k7_relat_1('#skF_4', C_156), D_157)=k9_relat_1(k7_relat_1('#skF_4', C_156), D_157) | ~r1_tarski(C_156, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_126, c_309])).
% 2.78/1.47  tff(c_418, plain, (![D_179, D_180]: (k7_relset_1(u1_struct_0(D_179), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_179), D_180)=k9_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_179)), D_180) | ~r1_tarski(u1_struct_0(D_179), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_179, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_238, c_313])).
% 2.78/1.47  tff(c_30, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.78/1.47  tff(c_78, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_30])).
% 2.78/1.47  tff(c_430, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_418, c_78])).
% 2.78/1.47  tff(c_439, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_430])).
% 2.78/1.47  tff(c_441, plain, (~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_439])).
% 2.78/1.47  tff(c_457, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_109, c_441])).
% 2.78/1.47  tff(c_461, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_42, c_457])).
% 2.78/1.47  tff(c_462, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_439])).
% 2.78/1.47  tff(c_504, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_238, c_462])).
% 2.78/1.47  tff(c_510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_288, c_504])).
% 2.78/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.47  
% 2.78/1.47  Inference rules
% 2.78/1.47  ----------------------
% 2.78/1.47  #Ref     : 0
% 2.78/1.47  #Sup     : 98
% 2.78/1.47  #Fact    : 0
% 2.78/1.47  #Define  : 0
% 2.78/1.47  #Split   : 3
% 2.78/1.47  #Chain   : 0
% 2.78/1.47  #Close   : 0
% 2.78/1.47  
% 2.78/1.47  Ordering : KBO
% 2.78/1.47  
% 2.78/1.47  Simplification rules
% 2.78/1.47  ----------------------
% 2.78/1.47  #Subsume      : 8
% 2.78/1.47  #Demod        : 62
% 2.78/1.47  #Tautology    : 27
% 2.78/1.47  #SimpNegUnit  : 17
% 2.78/1.47  #BackRed      : 1
% 2.78/1.47  
% 2.78/1.47  #Partial instantiations: 0
% 2.78/1.47  #Strategies tried      : 1
% 2.78/1.47  
% 2.78/1.47  Timing (in seconds)
% 2.78/1.47  ----------------------
% 3.12/1.47  Preprocessing        : 0.33
% 3.12/1.47  Parsing              : 0.17
% 3.12/1.47  CNF conversion       : 0.03
% 3.12/1.47  Main loop            : 0.33
% 3.12/1.47  Inferencing          : 0.13
% 3.13/1.47  Reduction            : 0.10
% 3.13/1.47  Demodulation         : 0.07
% 3.13/1.47  BG Simplification    : 0.02
% 3.13/1.47  Subsumption          : 0.06
% 3.13/1.47  Abstraction          : 0.02
% 3.13/1.47  MUC search           : 0.00
% 3.13/1.47  Cooper               : 0.00
% 3.13/1.47  Total                : 0.70
% 3.13/1.47  Index Insertion      : 0.00
% 3.13/1.47  Index Deletion       : 0.00
% 3.13/1.47  Index Matching       : 0.00
% 3.13/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
