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
% DateTime   : Thu Dec  3 10:27:12 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 119 expanded)
%              Number of leaves         :   37 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :  174 ( 476 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_146,negated_conjecture,(
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

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_115,axiom,(
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

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_101,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_32,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_250,plain,(
    ! [A_126,B_127,C_128,D_129] :
      ( r2_funct_2(A_126,B_127,C_128,C_128)
      | ~ m1_subset_1(D_129,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127)))
      | ~ v1_funct_2(D_129,A_126,B_127)
      | ~ v1_funct_1(D_129)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127)))
      | ~ v1_funct_2(C_128,A_126,B_127)
      | ~ v1_funct_1(C_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_252,plain,(
    ! [C_128] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_128,C_128)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_128,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_128) ) ),
    inference(resolution,[status(thm)],[c_30,c_250])).

tff(c_264,plain,(
    ! [C_130] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_130,C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_130,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_252])).

tff(c_266,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_264])).

tff(c_275,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_266])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_36,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_51,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_62,plain,(
    ! [A_72,B_73] :
      ( r1_tarski(A_72,B_73)
      | ~ m1_subset_1(A_72,k1_zfmisc_1(B_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_66,plain,(
    ! [A_2] : r1_tarski(A_2,A_2) ),
    inference(resolution,[status(thm)],[c_51,c_62])).

tff(c_228,plain,(
    ! [B_121,C_122,A_123] :
      ( m1_pre_topc(B_121,C_122)
      | ~ r1_tarski(u1_struct_0(B_121),u1_struct_0(C_122))
      | ~ m1_pre_topc(C_122,A_123)
      | ~ m1_pre_topc(B_121,A_123)
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_236,plain,(
    ! [B_124,A_125] :
      ( m1_pre_topc(B_124,B_124)
      | ~ m1_pre_topc(B_124,A_125)
      | ~ l1_pre_topc(A_125)
      | ~ v2_pre_topc(A_125) ) ),
    inference(resolution,[status(thm)],[c_66,c_228])).

tff(c_238,plain,
    ( m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_236])).

tff(c_241,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_238])).

tff(c_77,plain,(
    ! [C_77,A_78,B_79] :
      ( v1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_89,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_77])).

tff(c_105,plain,(
    ! [C_85,A_86,B_87] :
      ( v4_relat_1(C_85,A_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_117,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_105])).

tff(c_121,plain,(
    ! [B_90,A_91] :
      ( k7_relat_1(B_90,A_91) = B_90
      | ~ v4_relat_1(B_90,A_91)
      | ~ v1_relat_1(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_127,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_117,c_121])).

tff(c_133,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_127])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_187,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( k2_partfun1(A_105,B_106,C_107,D_108) = k7_relat_1(C_107,D_108)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106)))
      | ~ v1_funct_1(C_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_189,plain,(
    ! [D_108] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',D_108) = k7_relat_1('#skF_4',D_108)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_187])).

tff(c_198,plain,(
    ! [D_108] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',D_108) = k7_relat_1('#skF_4',D_108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_189])).

tff(c_315,plain,(
    ! [B_150,D_148,E_146,C_149,A_147] :
      ( k3_tmap_1(A_147,B_150,C_149,D_148,E_146) = k2_partfun1(u1_struct_0(C_149),u1_struct_0(B_150),E_146,u1_struct_0(D_148))
      | ~ m1_pre_topc(D_148,C_149)
      | ~ m1_subset_1(E_146,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_149),u1_struct_0(B_150))))
      | ~ v1_funct_2(E_146,u1_struct_0(C_149),u1_struct_0(B_150))
      | ~ v1_funct_1(E_146)
      | ~ m1_pre_topc(D_148,A_147)
      | ~ m1_pre_topc(C_149,A_147)
      | ~ l1_pre_topc(B_150)
      | ~ v2_pre_topc(B_150)
      | v2_struct_0(B_150)
      | ~ l1_pre_topc(A_147)
      | ~ v2_pre_topc(A_147)
      | v2_struct_0(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_317,plain,(
    ! [A_147,D_148] :
      ( k3_tmap_1(A_147,'#skF_2','#skF_3',D_148,'#skF_4') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_148))
      | ~ m1_pre_topc(D_148,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc(D_148,A_147)
      | ~ m1_pre_topc('#skF_3',A_147)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_147)
      | ~ v2_pre_topc(A_147)
      | v2_struct_0(A_147) ) ),
    inference(resolution,[status(thm)],[c_30,c_315])).

tff(c_326,plain,(
    ! [D_148,A_147] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_148)) = k3_tmap_1(A_147,'#skF_2','#skF_3',D_148,'#skF_4')
      | ~ m1_pre_topc(D_148,'#skF_3')
      | ~ m1_pre_topc(D_148,A_147)
      | ~ m1_pre_topc('#skF_3',A_147)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_147)
      | ~ v2_pre_topc(A_147)
      | v2_struct_0(A_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_34,c_32,c_198,c_317])).

tff(c_330,plain,(
    ! [D_151,A_152] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_151)) = k3_tmap_1(A_152,'#skF_2','#skF_3',D_151,'#skF_4')
      | ~ m1_pre_topc(D_151,'#skF_3')
      | ~ m1_pre_topc(D_151,A_152)
      | ~ m1_pre_topc('#skF_3',A_152)
      | ~ l1_pre_topc(A_152)
      | ~ v2_pre_topc(A_152)
      | v2_struct_0(A_152) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_326])).

tff(c_334,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_330])).

tff(c_341,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_36,c_241,c_133,c_334])).

tff(c_342,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_341])).

tff(c_28,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_343,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_28])).

tff(c_346,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_343])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:07:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.49  
% 2.63/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.49  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.63/1.49  
% 2.63/1.49  %Foreground sorts:
% 2.63/1.49  
% 2.63/1.49  
% 2.63/1.49  %Background operators:
% 2.63/1.49  
% 2.63/1.49  
% 2.63/1.49  %Foreground operators:
% 2.63/1.49  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.63/1.49  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.63/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.63/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.49  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.63/1.49  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.63/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.63/1.49  tff('#skF_2', type, '#skF_2': $i).
% 2.63/1.49  tff('#skF_3', type, '#skF_3': $i).
% 2.63/1.49  tff('#skF_1', type, '#skF_1': $i).
% 2.63/1.49  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.63/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.63/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.63/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.63/1.49  tff('#skF_4', type, '#skF_4': $i).
% 2.63/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.49  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.63/1.49  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.63/1.49  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.63/1.49  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.63/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.63/1.49  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.63/1.49  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.63/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.63/1.49  
% 2.63/1.51  tff(f_146, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), D, k3_tmap_1(A, B, C, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tmap_1)).
% 2.63/1.51  tff(f_69, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 2.63/1.51  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.63/1.51  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.63/1.51  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.63/1.51  tff(f_115, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 2.63/1.51  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.63/1.51  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.63/1.51  tff(f_39, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.63/1.51  tff(f_55, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.63/1.51  tff(f_101, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.63/1.51  tff(c_34, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.63/1.51  tff(c_32, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.63/1.51  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.63/1.51  tff(c_250, plain, (![A_126, B_127, C_128, D_129]: (r2_funct_2(A_126, B_127, C_128, C_128) | ~m1_subset_1(D_129, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))) | ~v1_funct_2(D_129, A_126, B_127) | ~v1_funct_1(D_129) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))) | ~v1_funct_2(C_128, A_126, B_127) | ~v1_funct_1(C_128))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.63/1.51  tff(c_252, plain, (![C_128]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_128, C_128) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_128, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_128))), inference(resolution, [status(thm)], [c_30, c_250])).
% 2.63/1.51  tff(c_264, plain, (![C_130]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_130, C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_130, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_130))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_252])).
% 2.63/1.51  tff(c_266, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_264])).
% 2.63/1.51  tff(c_275, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_266])).
% 2.63/1.51  tff(c_50, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.63/1.51  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.63/1.51  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.63/1.51  tff(c_36, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.63/1.51  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.63/1.51  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.63/1.51  tff(c_51, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 2.63/1.51  tff(c_62, plain, (![A_72, B_73]: (r1_tarski(A_72, B_73) | ~m1_subset_1(A_72, k1_zfmisc_1(B_73)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.63/1.51  tff(c_66, plain, (![A_2]: (r1_tarski(A_2, A_2))), inference(resolution, [status(thm)], [c_51, c_62])).
% 2.63/1.51  tff(c_228, plain, (![B_121, C_122, A_123]: (m1_pre_topc(B_121, C_122) | ~r1_tarski(u1_struct_0(B_121), u1_struct_0(C_122)) | ~m1_pre_topc(C_122, A_123) | ~m1_pre_topc(B_121, A_123) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.63/1.51  tff(c_236, plain, (![B_124, A_125]: (m1_pre_topc(B_124, B_124) | ~m1_pre_topc(B_124, A_125) | ~l1_pre_topc(A_125) | ~v2_pre_topc(A_125))), inference(resolution, [status(thm)], [c_66, c_228])).
% 2.63/1.51  tff(c_238, plain, (m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_236])).
% 2.63/1.51  tff(c_241, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_238])).
% 2.63/1.51  tff(c_77, plain, (![C_77, A_78, B_79]: (v1_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.63/1.51  tff(c_89, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_77])).
% 2.63/1.51  tff(c_105, plain, (![C_85, A_86, B_87]: (v4_relat_1(C_85, A_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.63/1.51  tff(c_117, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_105])).
% 2.63/1.51  tff(c_121, plain, (![B_90, A_91]: (k7_relat_1(B_90, A_91)=B_90 | ~v4_relat_1(B_90, A_91) | ~v1_relat_1(B_90))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.63/1.51  tff(c_127, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_117, c_121])).
% 2.63/1.51  tff(c_133, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_89, c_127])).
% 2.63/1.51  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.63/1.51  tff(c_42, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.63/1.51  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.63/1.51  tff(c_187, plain, (![A_105, B_106, C_107, D_108]: (k2_partfun1(A_105, B_106, C_107, D_108)=k7_relat_1(C_107, D_108) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))) | ~v1_funct_1(C_107))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.63/1.51  tff(c_189, plain, (![D_108]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', D_108)=k7_relat_1('#skF_4', D_108) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_187])).
% 2.63/1.51  tff(c_198, plain, (![D_108]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', D_108)=k7_relat_1('#skF_4', D_108))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_189])).
% 2.63/1.51  tff(c_315, plain, (![B_150, D_148, E_146, C_149, A_147]: (k3_tmap_1(A_147, B_150, C_149, D_148, E_146)=k2_partfun1(u1_struct_0(C_149), u1_struct_0(B_150), E_146, u1_struct_0(D_148)) | ~m1_pre_topc(D_148, C_149) | ~m1_subset_1(E_146, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_149), u1_struct_0(B_150)))) | ~v1_funct_2(E_146, u1_struct_0(C_149), u1_struct_0(B_150)) | ~v1_funct_1(E_146) | ~m1_pre_topc(D_148, A_147) | ~m1_pre_topc(C_149, A_147) | ~l1_pre_topc(B_150) | ~v2_pre_topc(B_150) | v2_struct_0(B_150) | ~l1_pre_topc(A_147) | ~v2_pre_topc(A_147) | v2_struct_0(A_147))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.63/1.51  tff(c_317, plain, (![A_147, D_148]: (k3_tmap_1(A_147, '#skF_2', '#skF_3', D_148, '#skF_4')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_148)) | ~m1_pre_topc(D_148, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc(D_148, A_147) | ~m1_pre_topc('#skF_3', A_147) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_147) | ~v2_pre_topc(A_147) | v2_struct_0(A_147))), inference(resolution, [status(thm)], [c_30, c_315])).
% 2.63/1.51  tff(c_326, plain, (![D_148, A_147]: (k7_relat_1('#skF_4', u1_struct_0(D_148))=k3_tmap_1(A_147, '#skF_2', '#skF_3', D_148, '#skF_4') | ~m1_pre_topc(D_148, '#skF_3') | ~m1_pre_topc(D_148, A_147) | ~m1_pre_topc('#skF_3', A_147) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_147) | ~v2_pre_topc(A_147) | v2_struct_0(A_147))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_34, c_32, c_198, c_317])).
% 2.63/1.51  tff(c_330, plain, (![D_151, A_152]: (k7_relat_1('#skF_4', u1_struct_0(D_151))=k3_tmap_1(A_152, '#skF_2', '#skF_3', D_151, '#skF_4') | ~m1_pre_topc(D_151, '#skF_3') | ~m1_pre_topc(D_151, A_152) | ~m1_pre_topc('#skF_3', A_152) | ~l1_pre_topc(A_152) | ~v2_pre_topc(A_152) | v2_struct_0(A_152))), inference(negUnitSimplification, [status(thm)], [c_44, c_326])).
% 2.63/1.51  tff(c_334, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_330])).
% 2.63/1.51  tff(c_341, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_36, c_241, c_133, c_334])).
% 2.63/1.51  tff(c_342, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_50, c_341])).
% 2.63/1.51  tff(c_28, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.63/1.51  tff(c_343, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_342, c_28])).
% 2.63/1.51  tff(c_346, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_275, c_343])).
% 2.63/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.51  
% 2.63/1.51  Inference rules
% 2.63/1.51  ----------------------
% 2.63/1.51  #Ref     : 0
% 2.63/1.51  #Sup     : 57
% 2.63/1.51  #Fact    : 0
% 2.63/1.51  #Define  : 0
% 2.63/1.51  #Split   : 2
% 2.63/1.51  #Chain   : 0
% 2.63/1.51  #Close   : 0
% 2.63/1.51  
% 2.63/1.51  Ordering : KBO
% 2.63/1.51  
% 2.63/1.51  Simplification rules
% 2.63/1.51  ----------------------
% 2.63/1.51  #Subsume      : 3
% 2.63/1.51  #Demod        : 43
% 2.63/1.51  #Tautology    : 20
% 2.63/1.51  #SimpNegUnit  : 3
% 2.63/1.51  #BackRed      : 1
% 2.63/1.51  
% 2.63/1.51  #Partial instantiations: 0
% 2.63/1.51  #Strategies tried      : 1
% 2.63/1.51  
% 2.63/1.51  Timing (in seconds)
% 2.63/1.51  ----------------------
% 2.63/1.51  Preprocessing        : 0.34
% 2.63/1.51  Parsing              : 0.18
% 2.63/1.51  CNF conversion       : 0.03
% 2.63/1.51  Main loop            : 0.27
% 2.63/1.51  Inferencing          : 0.10
% 2.63/1.51  Reduction            : 0.09
% 2.63/1.51  Demodulation         : 0.06
% 2.63/1.51  BG Simplification    : 0.02
% 2.63/1.51  Subsumption          : 0.05
% 2.63/1.51  Abstraction          : 0.02
% 2.63/1.51  MUC search           : 0.00
% 2.63/1.51  Cooper               : 0.00
% 2.63/1.51  Total                : 0.64
% 2.63/1.51  Index Insertion      : 0.00
% 2.63/1.51  Index Deletion       : 0.00
% 2.63/1.51  Index Matching       : 0.00
% 2.63/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
