%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:00 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 168 expanded)
%              Number of leaves         :   36 (  77 expanded)
%              Depth                    :   12
%              Number of atoms          :  185 ( 784 expanded)
%              Number of equality atoms :   26 (  61 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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
                  & m1_pre_topc(C,B) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(B),u1_struct_0(A))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                       => ( r1_tarski(E,u1_struct_0(C))
                         => k7_relset_1(u1_struct_0(B),u1_struct_0(A),D,E) = k7_relset_1(u1_struct_0(C),u1_struct_0(A),k2_tmap_1(B,A,D,C),E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tmap_1)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_89,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_107,axiom,(
    ! [A,B,C,D] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B))))
        & l1_struct_0(D) )
     => ( v1_funct_1(k2_tmap_1(A,B,C,D))
        & v1_funct_2(k2_tmap_1(A,B,C,D),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k2_tmap_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_36,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_53,plain,(
    ! [B_71,A_72] :
      ( l1_pre_topc(B_71)
      | ~ m1_pre_topc(B_71,A_72)
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_56,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_53])).

tff(c_59,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_56])).

tff(c_12,plain,(
    ! [A_19] :
      ( l1_struct_0(A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_60,plain,(
    ! [B_73,A_74] :
      ( v1_relat_1(B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_74))
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_63,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_30,c_60])).

tff(c_69,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_63])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_34,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_32,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_95,plain,(
    ! [A_83,B_84,C_85,D_86] :
      ( k2_partfun1(A_83,B_84,C_85,D_86) = k7_relat_1(C_85,D_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ v1_funct_1(C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_97,plain,(
    ! [D_86] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_86) = k7_relat_1('#skF_4',D_86)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_95])).

tff(c_100,plain,(
    ! [D_86] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_86) = k7_relat_1('#skF_4',D_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_97])).

tff(c_163,plain,(
    ! [A_102,B_103,C_104,D_105] :
      ( k2_partfun1(u1_struct_0(A_102),u1_struct_0(B_103),C_104,u1_struct_0(D_105)) = k2_tmap_1(A_102,B_103,C_104,D_105)
      | ~ m1_pre_topc(D_105,A_102)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_102),u1_struct_0(B_103))))
      | ~ v1_funct_2(C_104,u1_struct_0(A_102),u1_struct_0(B_103))
      | ~ v1_funct_1(C_104)
      | ~ l1_pre_topc(B_103)
      | ~ v2_pre_topc(B_103)
      | v2_struct_0(B_103)
      | ~ l1_pre_topc(A_102)
      | ~ v2_pre_topc(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_167,plain,(
    ! [D_105] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_105)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_105)
      | ~ m1_pre_topc(D_105,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_163])).

tff(c_171,plain,(
    ! [D_105] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_105)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_105)
      | ~ m1_pre_topc(D_105,'#skF_2')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_48,c_46,c_34,c_32,c_100,c_167])).

tff(c_173,plain,(
    ! [D_106] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_106)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_106)
      | ~ m1_pre_topc(D_106,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_50,c_171])).

tff(c_6,plain,(
    ! [A_6,C_10,B_9] :
      ( k9_relat_1(k7_relat_1(A_6,C_10),B_9) = k9_relat_1(A_6,B_9)
      | ~ r1_tarski(B_9,C_10)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_179,plain,(
    ! [D_106,B_9] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_106),B_9) = k9_relat_1('#skF_4',B_9)
      | ~ r1_tarski(B_9,u1_struct_0(D_106))
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(D_106,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_6])).

tff(c_187,plain,(
    ! [D_107,B_108] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_107),B_108) = k9_relat_1('#skF_4',B_108)
      | ~ r1_tarski(B_108,u1_struct_0(D_107))
      | ~ m1_pre_topc(D_107,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_179])).

tff(c_190,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_187])).

tff(c_193,plain,(
    k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_190])).

tff(c_110,plain,(
    ! [A_88,B_89,C_90,D_91] :
      ( v1_funct_1(k2_tmap_1(A_88,B_89,C_90,D_91))
      | ~ l1_struct_0(D_91)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_88),u1_struct_0(B_89))))
      | ~ v1_funct_2(C_90,u1_struct_0(A_88),u1_struct_0(B_89))
      | ~ v1_funct_1(C_90)
      | ~ l1_struct_0(B_89)
      | ~ l1_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_112,plain,(
    ! [D_91] :
      ( v1_funct_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_91))
      | ~ l1_struct_0(D_91)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_struct_0('#skF_1')
      | ~ l1_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_110])).

tff(c_115,plain,(
    ! [D_91] :
      ( v1_funct_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_91))
      | ~ l1_struct_0(D_91)
      | ~ l1_struct_0('#skF_1')
      | ~ l1_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_112])).

tff(c_116,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_119,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_116])).

tff(c_123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_119])).

tff(c_125,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_124,plain,(
    ! [D_91] :
      ( ~ l1_struct_0('#skF_1')
      | v1_funct_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_91))
      | ~ l1_struct_0(D_91) ) ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_126,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_129,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_126])).

tff(c_133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_129])).

tff(c_135,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_144,plain,(
    ! [A_98,B_99,C_100,D_101] :
      ( m1_subset_1(k2_tmap_1(A_98,B_99,C_100,D_101),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_101),u1_struct_0(B_99))))
      | ~ l1_struct_0(D_101)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_98),u1_struct_0(B_99))))
      | ~ v1_funct_2(C_100,u1_struct_0(A_98),u1_struct_0(B_99))
      | ~ v1_funct_1(C_100)
      | ~ l1_struct_0(B_99)
      | ~ l1_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_8,plain,(
    ! [A_11,B_12,C_13,D_14] :
      ( k7_relset_1(A_11,B_12,C_13,D_14) = k9_relat_1(C_13,D_14)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_208,plain,(
    ! [C_115,D_116,A_117,B_114,D_118] :
      ( k7_relset_1(u1_struct_0(D_116),u1_struct_0(B_114),k2_tmap_1(A_117,B_114,C_115,D_116),D_118) = k9_relat_1(k2_tmap_1(A_117,B_114,C_115,D_116),D_118)
      | ~ l1_struct_0(D_116)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_117),u1_struct_0(B_114))))
      | ~ v1_funct_2(C_115,u1_struct_0(A_117),u1_struct_0(B_114))
      | ~ v1_funct_1(C_115)
      | ~ l1_struct_0(B_114)
      | ~ l1_struct_0(A_117) ) ),
    inference(resolution,[status(thm)],[c_144,c_8])).

tff(c_212,plain,(
    ! [D_116,D_118] :
      ( k7_relset_1(u1_struct_0(D_116),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4',D_116),D_118) = k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_116),D_118)
      | ~ l1_struct_0(D_116)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_struct_0('#skF_1')
      | ~ l1_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_208])).

tff(c_217,plain,(
    ! [D_119,D_120] :
      ( k7_relset_1(u1_struct_0(D_119),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4',D_119),D_120) = k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_119),D_120)
      | ~ l1_struct_0(D_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_135,c_34,c_32,c_212])).

tff(c_81,plain,(
    ! [A_78,B_79,C_80,D_81] :
      ( k7_relset_1(A_78,B_79,C_80,D_81) = k9_relat_1(C_80,D_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_84,plain,(
    ! [D_81] : k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_81) = k9_relat_1('#skF_4',D_81) ),
    inference(resolution,[status(thm)],[c_30,c_81])).

tff(c_24,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_85,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_24])).

tff(c_223,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_85])).

tff(c_229,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_223])).

tff(c_233,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_229])).

tff(c_237,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_233])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.07  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.07/0.26  % Computer   : n013.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % DateTime   : Tue Dec  1 12:06:09 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.07/0.27  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.24  
% 2.44/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.24  %$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.44/1.24  
% 2.44/1.24  %Foreground sorts:
% 2.44/1.24  
% 2.44/1.24  
% 2.44/1.24  %Background operators:
% 2.44/1.24  
% 2.44/1.24  
% 2.44/1.24  %Foreground operators:
% 2.44/1.24  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.44/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.44/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.44/1.24  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.44/1.24  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.44/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.44/1.24  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.44/1.24  tff('#skF_5', type, '#skF_5': $i).
% 2.44/1.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.44/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.44/1.24  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.44/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.44/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.44/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.44/1.24  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.44/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.44/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.44/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.44/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.44/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.44/1.24  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.44/1.24  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.44/1.24  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.44/1.24  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.44/1.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.44/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.44/1.24  
% 2.55/1.26  tff(f_143, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (r1_tarski(E, u1_struct_0(C)) => (k7_relset_1(u1_struct_0(B), u1_struct_0(A), D, E) = k7_relset_1(u1_struct_0(C), u1_struct_0(A), k2_tmap_1(B, A, D, C), E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_tmap_1)).
% 2.55/1.26  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.55/1.26  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.55/1.26  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.55/1.26  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.55/1.26  tff(f_51, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.55/1.26  tff(f_89, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 2.55/1.26  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 2.55/1.26  tff(f_107, axiom, (![A, B, C, D]: ((((((l1_struct_0(A) & l1_struct_0(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & l1_struct_0(D)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 2.55/1.26  tff(f_45, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.55/1.26  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.55/1.26  tff(c_36, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.55/1.26  tff(c_53, plain, (![B_71, A_72]: (l1_pre_topc(B_71) | ~m1_pre_topc(B_71, A_72) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.55/1.26  tff(c_56, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_36, c_53])).
% 2.55/1.26  tff(c_59, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_56])).
% 2.55/1.26  tff(c_12, plain, (![A_19]: (l1_struct_0(A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.55/1.26  tff(c_26, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.55/1.26  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.55/1.26  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.55/1.26  tff(c_60, plain, (![B_73, A_74]: (v1_relat_1(B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_74)) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.55/1.26  tff(c_63, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_30, c_60])).
% 2.55/1.26  tff(c_69, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_63])).
% 2.55/1.26  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.55/1.26  tff(c_50, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.55/1.26  tff(c_42, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.55/1.26  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.55/1.26  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.55/1.26  tff(c_34, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.55/1.26  tff(c_32, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.55/1.26  tff(c_95, plain, (![A_83, B_84, C_85, D_86]: (k2_partfun1(A_83, B_84, C_85, D_86)=k7_relat_1(C_85, D_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~v1_funct_1(C_85))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.55/1.26  tff(c_97, plain, (![D_86]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_86)=k7_relat_1('#skF_4', D_86) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_95])).
% 2.55/1.26  tff(c_100, plain, (![D_86]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_86)=k7_relat_1('#skF_4', D_86))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_97])).
% 2.55/1.26  tff(c_163, plain, (![A_102, B_103, C_104, D_105]: (k2_partfun1(u1_struct_0(A_102), u1_struct_0(B_103), C_104, u1_struct_0(D_105))=k2_tmap_1(A_102, B_103, C_104, D_105) | ~m1_pre_topc(D_105, A_102) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_102), u1_struct_0(B_103)))) | ~v1_funct_2(C_104, u1_struct_0(A_102), u1_struct_0(B_103)) | ~v1_funct_1(C_104) | ~l1_pre_topc(B_103) | ~v2_pre_topc(B_103) | v2_struct_0(B_103) | ~l1_pre_topc(A_102) | ~v2_pre_topc(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.55/1.26  tff(c_167, plain, (![D_105]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_105))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_105) | ~m1_pre_topc(D_105, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_163])).
% 2.55/1.26  tff(c_171, plain, (![D_105]: (k7_relat_1('#skF_4', u1_struct_0(D_105))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_105) | ~m1_pre_topc(D_105, '#skF_2') | v2_struct_0('#skF_1') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_48, c_46, c_34, c_32, c_100, c_167])).
% 2.55/1.26  tff(c_173, plain, (![D_106]: (k7_relat_1('#skF_4', u1_struct_0(D_106))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_106) | ~m1_pre_topc(D_106, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_44, c_50, c_171])).
% 2.55/1.26  tff(c_6, plain, (![A_6, C_10, B_9]: (k9_relat_1(k7_relat_1(A_6, C_10), B_9)=k9_relat_1(A_6, B_9) | ~r1_tarski(B_9, C_10) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.55/1.26  tff(c_179, plain, (![D_106, B_9]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_106), B_9)=k9_relat_1('#skF_4', B_9) | ~r1_tarski(B_9, u1_struct_0(D_106)) | ~v1_relat_1('#skF_4') | ~m1_pre_topc(D_106, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_173, c_6])).
% 2.55/1.26  tff(c_187, plain, (![D_107, B_108]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_107), B_108)=k9_relat_1('#skF_4', B_108) | ~r1_tarski(B_108, u1_struct_0(D_107)) | ~m1_pre_topc(D_107, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_179])).
% 2.55/1.26  tff(c_190, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_187])).
% 2.55/1.26  tff(c_193, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_190])).
% 2.55/1.26  tff(c_110, plain, (![A_88, B_89, C_90, D_91]: (v1_funct_1(k2_tmap_1(A_88, B_89, C_90, D_91)) | ~l1_struct_0(D_91) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_88), u1_struct_0(B_89)))) | ~v1_funct_2(C_90, u1_struct_0(A_88), u1_struct_0(B_89)) | ~v1_funct_1(C_90) | ~l1_struct_0(B_89) | ~l1_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.55/1.26  tff(c_112, plain, (![D_91]: (v1_funct_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_91)) | ~l1_struct_0(D_91) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_struct_0('#skF_1') | ~l1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_110])).
% 2.55/1.26  tff(c_115, plain, (![D_91]: (v1_funct_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_91)) | ~l1_struct_0(D_91) | ~l1_struct_0('#skF_1') | ~l1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_112])).
% 2.55/1.26  tff(c_116, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_115])).
% 2.55/1.26  tff(c_119, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_116])).
% 2.55/1.26  tff(c_123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_119])).
% 2.55/1.26  tff(c_125, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_115])).
% 2.55/1.26  tff(c_124, plain, (![D_91]: (~l1_struct_0('#skF_1') | v1_funct_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_91)) | ~l1_struct_0(D_91))), inference(splitRight, [status(thm)], [c_115])).
% 2.55/1.26  tff(c_126, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_124])).
% 2.55/1.26  tff(c_129, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_126])).
% 2.55/1.26  tff(c_133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_129])).
% 2.55/1.26  tff(c_135, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_124])).
% 2.55/1.26  tff(c_144, plain, (![A_98, B_99, C_100, D_101]: (m1_subset_1(k2_tmap_1(A_98, B_99, C_100, D_101), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_101), u1_struct_0(B_99)))) | ~l1_struct_0(D_101) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_98), u1_struct_0(B_99)))) | ~v1_funct_2(C_100, u1_struct_0(A_98), u1_struct_0(B_99)) | ~v1_funct_1(C_100) | ~l1_struct_0(B_99) | ~l1_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.55/1.26  tff(c_8, plain, (![A_11, B_12, C_13, D_14]: (k7_relset_1(A_11, B_12, C_13, D_14)=k9_relat_1(C_13, D_14) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.55/1.26  tff(c_208, plain, (![C_115, D_116, A_117, B_114, D_118]: (k7_relset_1(u1_struct_0(D_116), u1_struct_0(B_114), k2_tmap_1(A_117, B_114, C_115, D_116), D_118)=k9_relat_1(k2_tmap_1(A_117, B_114, C_115, D_116), D_118) | ~l1_struct_0(D_116) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_117), u1_struct_0(B_114)))) | ~v1_funct_2(C_115, u1_struct_0(A_117), u1_struct_0(B_114)) | ~v1_funct_1(C_115) | ~l1_struct_0(B_114) | ~l1_struct_0(A_117))), inference(resolution, [status(thm)], [c_144, c_8])).
% 2.55/1.26  tff(c_212, plain, (![D_116, D_118]: (k7_relset_1(u1_struct_0(D_116), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_116), D_118)=k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_116), D_118) | ~l1_struct_0(D_116) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_struct_0('#skF_1') | ~l1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_208])).
% 2.55/1.26  tff(c_217, plain, (![D_119, D_120]: (k7_relset_1(u1_struct_0(D_119), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_119), D_120)=k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_119), D_120) | ~l1_struct_0(D_119))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_135, c_34, c_32, c_212])).
% 2.55/1.26  tff(c_81, plain, (![A_78, B_79, C_80, D_81]: (k7_relset_1(A_78, B_79, C_80, D_81)=k9_relat_1(C_80, D_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.55/1.26  tff(c_84, plain, (![D_81]: (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_81)=k9_relat_1('#skF_4', D_81))), inference(resolution, [status(thm)], [c_30, c_81])).
% 2.55/1.26  tff(c_24, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.55/1.26  tff(c_85, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_24])).
% 2.55/1.26  tff(c_223, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~l1_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_217, c_85])).
% 2.55/1.26  tff(c_229, plain, (~l1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_193, c_223])).
% 2.55/1.26  tff(c_233, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_12, c_229])).
% 2.55/1.26  tff(c_237, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_233])).
% 2.55/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.26  
% 2.55/1.26  Inference rules
% 2.55/1.26  ----------------------
% 2.55/1.26  #Ref     : 0
% 2.55/1.26  #Sup     : 36
% 2.55/1.26  #Fact    : 0
% 2.55/1.26  #Define  : 0
% 2.55/1.26  #Split   : 3
% 2.55/1.26  #Chain   : 0
% 2.55/1.26  #Close   : 0
% 2.55/1.26  
% 2.55/1.26  Ordering : KBO
% 2.55/1.26  
% 2.55/1.26  Simplification rules
% 2.55/1.26  ----------------------
% 2.55/1.26  #Subsume      : 0
% 2.55/1.26  #Demod        : 32
% 2.55/1.26  #Tautology    : 12
% 2.55/1.26  #SimpNegUnit  : 1
% 2.55/1.26  #BackRed      : 1
% 2.55/1.26  
% 2.55/1.26  #Partial instantiations: 0
% 2.55/1.26  #Strategies tried      : 1
% 2.55/1.26  
% 2.55/1.26  Timing (in seconds)
% 2.55/1.26  ----------------------
% 2.55/1.26  Preprocessing        : 0.35
% 2.55/1.26  Parsing              : 0.20
% 2.55/1.26  CNF conversion       : 0.03
% 2.55/1.26  Main loop            : 0.21
% 2.55/1.26  Inferencing          : 0.08
% 2.55/1.26  Reduction            : 0.07
% 2.55/1.26  Demodulation         : 0.05
% 2.55/1.26  BG Simplification    : 0.02
% 2.55/1.26  Subsumption          : 0.03
% 2.55/1.26  Abstraction          : 0.01
% 2.55/1.26  MUC search           : 0.00
% 2.55/1.26  Cooper               : 0.00
% 2.55/1.26  Total                : 0.60
% 2.55/1.26  Index Insertion      : 0.00
% 2.55/1.26  Index Deletion       : 0.00
% 2.55/1.26  Index Matching       : 0.00
% 2.55/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
