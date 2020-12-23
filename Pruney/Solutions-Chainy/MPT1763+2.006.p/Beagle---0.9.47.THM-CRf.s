%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:11 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 116 expanded)
%              Number of leaves         :   36 (  60 expanded)
%              Depth                    :   10
%              Number of atoms          :  177 ( 479 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :   19 (   5 average)
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

tff(f_150,negated_conjecture,(
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

tff(f_73,axiom,(
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

tff(f_119,axiom,(
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

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_105,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_34,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_193,plain,(
    ! [A_109,B_110,C_111,D_112] :
      ( r2_funct_2(A_109,B_110,C_111,C_111)
      | ~ m1_subset_1(D_112,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110)))
      | ~ v1_funct_2(D_112,A_109,B_110)
      | ~ v1_funct_1(D_112)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110)))
      | ~ v1_funct_2(C_111,A_109,B_110)
      | ~ v1_funct_1(C_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_195,plain,(
    ! [C_111] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_111,C_111)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_111,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_111) ) ),
    inference(resolution,[status(thm)],[c_32,c_193])).

tff(c_213,plain,(
    ! [C_115] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_115,C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_115,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_195])).

tff(c_215,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_213])).

tff(c_218,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_215])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_50,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_38,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_185,plain,(
    ! [B_106,C_107,A_108] :
      ( m1_pre_topc(B_106,C_107)
      | ~ r1_tarski(u1_struct_0(B_106),u1_struct_0(C_107))
      | ~ m1_pre_topc(C_107,A_108)
      | ~ m1_pre_topc(B_106,A_108)
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_199,plain,(
    ! [B_113,A_114] :
      ( m1_pre_topc(B_113,B_113)
      | ~ m1_pre_topc(B_113,A_114)
      | ~ l1_pre_topc(A_114)
      | ~ v2_pre_topc(A_114) ) ),
    inference(resolution,[status(thm)],[c_6,c_185])).

tff(c_201,plain,
    ( m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_199])).

tff(c_204,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_201])).

tff(c_14,plain,(
    ! [C_9,A_7,B_8] :
      ( v1_relat_1(C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_66,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_14])).

tff(c_67,plain,(
    ! [C_76,A_77,B_78] :
      ( v4_relat_1(C_76,A_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_71,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_67])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k1_relat_1(B_4),A_3)
      | ~ v4_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_92,plain,(
    ! [B_87,A_88] :
      ( k7_relat_1(B_87,A_88) = B_87
      | ~ r1_tarski(k1_relat_1(B_87),A_88)
      | ~ v1_relat_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_117,plain,(
    ! [B_94,A_95] :
      ( k7_relat_1(B_94,A_95) = B_94
      | ~ v4_relat_1(B_94,A_95)
      | ~ v1_relat_1(B_94) ) ),
    inference(resolution,[status(thm)],[c_10,c_92])).

tff(c_123,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_71,c_117])).

tff(c_127,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_123])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_44,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_111,plain,(
    ! [A_90,B_91,C_92,D_93] :
      ( k2_partfun1(A_90,B_91,C_92,D_93) = k7_relat_1(C_92,D_93)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91)))
      | ~ v1_funct_1(C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_113,plain,(
    ! [D_93] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',D_93) = k7_relat_1('#skF_4',D_93)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_111])).

tff(c_116,plain,(
    ! [D_93] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',D_93) = k7_relat_1('#skF_4',D_93) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_113])).

tff(c_219,plain,(
    ! [A_117,E_116,B_120,C_119,D_118] :
      ( k3_tmap_1(A_117,B_120,C_119,D_118,E_116) = k2_partfun1(u1_struct_0(C_119),u1_struct_0(B_120),E_116,u1_struct_0(D_118))
      | ~ m1_pre_topc(D_118,C_119)
      | ~ m1_subset_1(E_116,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_119),u1_struct_0(B_120))))
      | ~ v1_funct_2(E_116,u1_struct_0(C_119),u1_struct_0(B_120))
      | ~ v1_funct_1(E_116)
      | ~ m1_pre_topc(D_118,A_117)
      | ~ m1_pre_topc(C_119,A_117)
      | ~ l1_pre_topc(B_120)
      | ~ v2_pre_topc(B_120)
      | v2_struct_0(B_120)
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117)
      | v2_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_221,plain,(
    ! [A_117,D_118] :
      ( k3_tmap_1(A_117,'#skF_2','#skF_3',D_118,'#skF_4') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_118))
      | ~ m1_pre_topc(D_118,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc(D_118,A_117)
      | ~ m1_pre_topc('#skF_3',A_117)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117)
      | v2_struct_0(A_117) ) ),
    inference(resolution,[status(thm)],[c_32,c_219])).

tff(c_224,plain,(
    ! [D_118,A_117] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_118)) = k3_tmap_1(A_117,'#skF_2','#skF_3',D_118,'#skF_4')
      | ~ m1_pre_topc(D_118,'#skF_3')
      | ~ m1_pre_topc(D_118,A_117)
      | ~ m1_pre_topc('#skF_3',A_117)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117)
      | v2_struct_0(A_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_36,c_34,c_116,c_221])).

tff(c_226,plain,(
    ! [D_121,A_122] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_121)) = k3_tmap_1(A_122,'#skF_2','#skF_3',D_121,'#skF_4')
      | ~ m1_pre_topc(D_121,'#skF_3')
      | ~ m1_pre_topc(D_121,A_122)
      | ~ m1_pre_topc('#skF_3',A_122)
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122)
      | v2_struct_0(A_122) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_224])).

tff(c_230,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_226])).

tff(c_237,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_38,c_204,c_127,c_230])).

tff(c_238,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_237])).

tff(c_30,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_239,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_30])).

tff(c_242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:55:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.31  
% 2.21/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.31  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.21/1.31  
% 2.21/1.31  %Foreground sorts:
% 2.21/1.31  
% 2.21/1.31  
% 2.21/1.31  %Background operators:
% 2.21/1.31  
% 2.21/1.31  
% 2.21/1.31  %Foreground operators:
% 2.21/1.31  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.21/1.31  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.21/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.21/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.21/1.31  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.21/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.21/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.31  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.21/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.21/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.21/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.21/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.21/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.31  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.21/1.31  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.21/1.31  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.21/1.31  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.21/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.21/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.21/1.31  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.21/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.21/1.31  
% 2.52/1.33  tff(f_150, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), D, k3_tmap_1(A, B, C, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tmap_1)).
% 2.52/1.33  tff(f_73, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 2.52/1.33  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.52/1.33  tff(f_119, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 2.52/1.33  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.52/1.33  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.52/1.33  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.52/1.33  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 2.52/1.33  tff(f_59, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.52/1.33  tff(f_105, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.52/1.33  tff(c_36, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.52/1.33  tff(c_34, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.52/1.33  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.52/1.33  tff(c_193, plain, (![A_109, B_110, C_111, D_112]: (r2_funct_2(A_109, B_110, C_111, C_111) | ~m1_subset_1(D_112, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))) | ~v1_funct_2(D_112, A_109, B_110) | ~v1_funct_1(D_112) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))) | ~v1_funct_2(C_111, A_109, B_110) | ~v1_funct_1(C_111))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.52/1.33  tff(c_195, plain, (![C_111]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_111, C_111) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_111, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_111))), inference(resolution, [status(thm)], [c_32, c_193])).
% 2.52/1.33  tff(c_213, plain, (![C_115]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_115, C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_115, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_115))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_195])).
% 2.52/1.33  tff(c_215, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_213])).
% 2.52/1.33  tff(c_218, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_215])).
% 2.52/1.33  tff(c_52, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.52/1.33  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.52/1.33  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.52/1.33  tff(c_38, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.52/1.33  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.52/1.33  tff(c_185, plain, (![B_106, C_107, A_108]: (m1_pre_topc(B_106, C_107) | ~r1_tarski(u1_struct_0(B_106), u1_struct_0(C_107)) | ~m1_pre_topc(C_107, A_108) | ~m1_pre_topc(B_106, A_108) | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.52/1.33  tff(c_199, plain, (![B_113, A_114]: (m1_pre_topc(B_113, B_113) | ~m1_pre_topc(B_113, A_114) | ~l1_pre_topc(A_114) | ~v2_pre_topc(A_114))), inference(resolution, [status(thm)], [c_6, c_185])).
% 2.52/1.33  tff(c_201, plain, (m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_199])).
% 2.52/1.33  tff(c_204, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_201])).
% 2.52/1.33  tff(c_14, plain, (![C_9, A_7, B_8]: (v1_relat_1(C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.52/1.33  tff(c_66, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_14])).
% 2.52/1.33  tff(c_67, plain, (![C_76, A_77, B_78]: (v4_relat_1(C_76, A_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.52/1.33  tff(c_71, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_67])).
% 2.52/1.33  tff(c_10, plain, (![B_4, A_3]: (r1_tarski(k1_relat_1(B_4), A_3) | ~v4_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.52/1.33  tff(c_92, plain, (![B_87, A_88]: (k7_relat_1(B_87, A_88)=B_87 | ~r1_tarski(k1_relat_1(B_87), A_88) | ~v1_relat_1(B_87))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.52/1.33  tff(c_117, plain, (![B_94, A_95]: (k7_relat_1(B_94, A_95)=B_94 | ~v4_relat_1(B_94, A_95) | ~v1_relat_1(B_94))), inference(resolution, [status(thm)], [c_10, c_92])).
% 2.52/1.33  tff(c_123, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_71, c_117])).
% 2.52/1.33  tff(c_127, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_123])).
% 2.52/1.33  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.52/1.33  tff(c_44, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.52/1.33  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.52/1.33  tff(c_111, plain, (![A_90, B_91, C_92, D_93]: (k2_partfun1(A_90, B_91, C_92, D_93)=k7_relat_1(C_92, D_93) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))) | ~v1_funct_1(C_92))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.52/1.33  tff(c_113, plain, (![D_93]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', D_93)=k7_relat_1('#skF_4', D_93) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_32, c_111])).
% 2.52/1.33  tff(c_116, plain, (![D_93]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', D_93)=k7_relat_1('#skF_4', D_93))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_113])).
% 2.52/1.33  tff(c_219, plain, (![A_117, E_116, B_120, C_119, D_118]: (k3_tmap_1(A_117, B_120, C_119, D_118, E_116)=k2_partfun1(u1_struct_0(C_119), u1_struct_0(B_120), E_116, u1_struct_0(D_118)) | ~m1_pre_topc(D_118, C_119) | ~m1_subset_1(E_116, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_119), u1_struct_0(B_120)))) | ~v1_funct_2(E_116, u1_struct_0(C_119), u1_struct_0(B_120)) | ~v1_funct_1(E_116) | ~m1_pre_topc(D_118, A_117) | ~m1_pre_topc(C_119, A_117) | ~l1_pre_topc(B_120) | ~v2_pre_topc(B_120) | v2_struct_0(B_120) | ~l1_pre_topc(A_117) | ~v2_pre_topc(A_117) | v2_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.52/1.33  tff(c_221, plain, (![A_117, D_118]: (k3_tmap_1(A_117, '#skF_2', '#skF_3', D_118, '#skF_4')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_118)) | ~m1_pre_topc(D_118, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc(D_118, A_117) | ~m1_pre_topc('#skF_3', A_117) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_117) | ~v2_pre_topc(A_117) | v2_struct_0(A_117))), inference(resolution, [status(thm)], [c_32, c_219])).
% 2.52/1.33  tff(c_224, plain, (![D_118, A_117]: (k7_relat_1('#skF_4', u1_struct_0(D_118))=k3_tmap_1(A_117, '#skF_2', '#skF_3', D_118, '#skF_4') | ~m1_pre_topc(D_118, '#skF_3') | ~m1_pre_topc(D_118, A_117) | ~m1_pre_topc('#skF_3', A_117) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_117) | ~v2_pre_topc(A_117) | v2_struct_0(A_117))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_36, c_34, c_116, c_221])).
% 2.52/1.33  tff(c_226, plain, (![D_121, A_122]: (k7_relat_1('#skF_4', u1_struct_0(D_121))=k3_tmap_1(A_122, '#skF_2', '#skF_3', D_121, '#skF_4') | ~m1_pre_topc(D_121, '#skF_3') | ~m1_pre_topc(D_121, A_122) | ~m1_pre_topc('#skF_3', A_122) | ~l1_pre_topc(A_122) | ~v2_pre_topc(A_122) | v2_struct_0(A_122))), inference(negUnitSimplification, [status(thm)], [c_46, c_224])).
% 2.52/1.33  tff(c_230, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_226])).
% 2.52/1.33  tff(c_237, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_38, c_204, c_127, c_230])).
% 2.52/1.33  tff(c_238, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_52, c_237])).
% 2.52/1.33  tff(c_30, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.52/1.33  tff(c_239, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_238, c_30])).
% 2.52/1.33  tff(c_242, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_218, c_239])).
% 2.52/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.33  
% 2.52/1.33  Inference rules
% 2.52/1.33  ----------------------
% 2.52/1.33  #Ref     : 0
% 2.52/1.33  #Sup     : 35
% 2.52/1.33  #Fact    : 0
% 2.52/1.33  #Define  : 0
% 2.52/1.33  #Split   : 1
% 2.52/1.33  #Chain   : 0
% 2.52/1.33  #Close   : 0
% 2.52/1.33  
% 2.52/1.33  Ordering : KBO
% 2.52/1.33  
% 2.52/1.33  Simplification rules
% 2.52/1.33  ----------------------
% 2.52/1.33  #Subsume      : 2
% 2.52/1.33  #Demod        : 29
% 2.52/1.33  #Tautology    : 15
% 2.52/1.33  #SimpNegUnit  : 3
% 2.52/1.33  #BackRed      : 1
% 2.52/1.33  
% 2.52/1.33  #Partial instantiations: 0
% 2.52/1.33  #Strategies tried      : 1
% 2.52/1.33  
% 2.52/1.33  Timing (in seconds)
% 2.52/1.33  ----------------------
% 2.52/1.33  Preprocessing        : 0.35
% 2.52/1.33  Parsing              : 0.19
% 2.52/1.33  CNF conversion       : 0.03
% 2.52/1.33  Main loop            : 0.21
% 2.52/1.33  Inferencing          : 0.07
% 2.52/1.33  Reduction            : 0.07
% 2.52/1.33  Demodulation         : 0.05
% 2.52/1.33  BG Simplification    : 0.02
% 2.52/1.33  Subsumption          : 0.04
% 2.52/1.33  Abstraction          : 0.01
% 2.52/1.33  MUC search           : 0.00
% 2.52/1.33  Cooper               : 0.00
% 2.52/1.33  Total                : 0.59
% 2.52/1.33  Index Insertion      : 0.00
% 2.52/1.33  Index Deletion       : 0.00
% 2.52/1.33  Index Matching       : 0.00
% 2.52/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
