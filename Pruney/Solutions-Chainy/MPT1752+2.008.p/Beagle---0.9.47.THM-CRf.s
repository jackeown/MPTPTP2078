%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:01 EST 2020

% Result     : Theorem 20.86s
% Output     : CNFRefutation 20.86s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 456 expanded)
%              Number of leaves         :   43 ( 187 expanded)
%              Depth                    :   15
%              Number of atoms          :  230 (2089 expanded)
%              Number of equality atoms :   27 ( 187 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_154,negated_conjecture,(
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
                      & v1_funct_2(D,u1_struct_0(A),u1_struct_0(B))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                       => ( r1_tarski(k8_relset_1(u1_struct_0(A),u1_struct_0(B),D,E),u1_struct_0(C))
                         => k8_relset_1(u1_struct_0(A),u1_struct_0(B),D,E) = k8_relset_1(u1_struct_0(C),u1_struct_0(B),k2_tmap_1(A,B,D,C),E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tmap_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_118,axiom,(
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

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_91,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( r1_tarski(k10_relat_1(A,C),B)
         => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(c_14,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_8,plain,(
    ! [B_8,A_6] :
      ( v1_relat_1(B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_6))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_85,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_40,c_8])).

tff(c_91,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_85])).

tff(c_18,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k7_relat_1(B_16,A_15),B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_46,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_92,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_40,c_4])).

tff(c_115,plain,(
    ! [A_95,C_96,B_97] :
      ( r1_tarski(A_95,C_96)
      | ~ r1_tarski(B_97,C_96)
      | ~ r1_tarski(A_95,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_312,plain,(
    ! [A_136] :
      ( r1_tarski(A_136,k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_136,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_92,c_115])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_160,plain,(
    ! [C_101,B_102,A_103] :
      ( v5_relat_1(C_101,B_102)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_103,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_169,plain,(
    ! [A_4,B_102,A_103] :
      ( v5_relat_1(A_4,B_102)
      | ~ r1_tarski(A_4,k2_zfmisc_1(A_103,B_102)) ) ),
    inference(resolution,[status(thm)],[c_6,c_160])).

tff(c_329,plain,(
    ! [A_136] :
      ( v5_relat_1(A_136,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_136,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_312,c_169])).

tff(c_73,plain,(
    ! [B_85,A_86] :
      ( v1_relat_1(B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_86))
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_80,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(A_4)
      | ~ v1_relat_1(B_5)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_73])).

tff(c_327,plain,(
    ! [A_136] :
      ( v1_relat_1(A_136)
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_136,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_312,c_80])).

tff(c_335,plain,(
    ! [A_137] :
      ( v1_relat_1(A_137)
      | ~ r1_tarski(A_137,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_327])).

tff(c_347,plain,(
    ! [A_15] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_15))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_335])).

tff(c_352,plain,(
    ! [A_15] : v1_relat_1(k7_relat_1('#skF_4',A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_347])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_58,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_56,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_44,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_42,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_356,plain,(
    ! [A_141,B_142,C_143,D_144] :
      ( k2_partfun1(A_141,B_142,C_143,D_144) = k7_relat_1(C_143,D_144)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142)))
      | ~ v1_funct_1(C_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_360,plain,(
    ! [D_144] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',D_144) = k7_relat_1('#skF_4',D_144)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_356])).

tff(c_367,plain,(
    ! [D_144] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',D_144) = k7_relat_1('#skF_4',D_144) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_360])).

tff(c_513,plain,(
    ! [A_171,B_172,C_173,D_174] :
      ( k2_partfun1(u1_struct_0(A_171),u1_struct_0(B_172),C_173,u1_struct_0(D_174)) = k2_tmap_1(A_171,B_172,C_173,D_174)
      | ~ m1_pre_topc(D_174,A_171)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_171),u1_struct_0(B_172))))
      | ~ v1_funct_2(C_173,u1_struct_0(A_171),u1_struct_0(B_172))
      | ~ v1_funct_1(C_173)
      | ~ l1_pre_topc(B_172)
      | ~ v2_pre_topc(B_172)
      | v2_struct_0(B_172)
      | ~ l1_pre_topc(A_171)
      | ~ v2_pre_topc(A_171)
      | v2_struct_0(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_518,plain,(
    ! [D_174] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_174)) = k2_tmap_1('#skF_1','#skF_2','#skF_4',D_174)
      | ~ m1_pre_topc(D_174,'#skF_1')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_513])).

tff(c_525,plain,(
    ! [D_174] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_174)) = k2_tmap_1('#skF_1','#skF_2','#skF_4',D_174)
      | ~ m1_pre_topc(D_174,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_44,c_42,c_367,c_518])).

tff(c_526,plain,(
    ! [D_174] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_174)) = k2_tmap_1('#skF_1','#skF_2','#skF_4',D_174)
      | ~ m1_pre_topc(D_174,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_525])).

tff(c_16,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_14,A_13)),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_256,plain,(
    ! [C_126,A_127,B_128] :
      ( m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128)))
      | ~ r1_tarski(k2_relat_1(C_126),B_128)
      | ~ r1_tarski(k1_relat_1(C_126),A_127)
      | ~ v1_relat_1(C_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_928,plain,(
    ! [C_226,A_227,B_228] :
      ( r1_tarski(C_226,k2_zfmisc_1(A_227,B_228))
      | ~ r1_tarski(k2_relat_1(C_226),B_228)
      | ~ r1_tarski(k1_relat_1(C_226),A_227)
      | ~ v1_relat_1(C_226) ) ),
    inference(resolution,[status(thm)],[c_256,c_4])).

tff(c_1227,plain,(
    ! [B_255,A_256,A_257] :
      ( r1_tarski(B_255,k2_zfmisc_1(A_256,A_257))
      | ~ r1_tarski(k1_relat_1(B_255),A_256)
      | ~ v5_relat_1(B_255,A_257)
      | ~ v1_relat_1(B_255) ) ),
    inference(resolution,[status(thm)],[c_12,c_928])).

tff(c_4909,plain,(
    ! [B_578,A_579,A_580] :
      ( r1_tarski(k7_relat_1(B_578,A_579),k2_zfmisc_1(A_579,A_580))
      | ~ v5_relat_1(k7_relat_1(B_578,A_579),A_580)
      | ~ v1_relat_1(k7_relat_1(B_578,A_579))
      | ~ v1_relat_1(B_578) ) ),
    inference(resolution,[status(thm)],[c_16,c_1227])).

tff(c_4934,plain,(
    ! [D_174,A_580] :
      ( r1_tarski(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_174),k2_zfmisc_1(u1_struct_0(D_174),A_580))
      | ~ v5_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_174)),A_580)
      | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_174)))
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(D_174,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_526,c_4909])).

tff(c_7326,plain,(
    ! [D_708,A_709] :
      ( r1_tarski(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_708),k2_zfmisc_1(u1_struct_0(D_708),A_709))
      | ~ v5_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_708)),A_709)
      | ~ m1_pre_topc(D_708,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_352,c_4934])).

tff(c_7365,plain,(
    ! [D_710,A_711] :
      ( v5_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_710),A_711)
      | ~ v5_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_710)),A_711)
      | ~ m1_pre_topc(D_710,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_7326,c_169])).

tff(c_7408,plain,(
    ! [D_710] :
      ( v5_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_710),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_710,'#skF_1')
      | ~ r1_tarski(k7_relat_1('#skF_4',u1_struct_0(D_710)),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_329,c_7365])).

tff(c_541,plain,(
    ! [D_178] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_178)) = k2_tmap_1('#skF_1','#skF_2','#skF_4',D_178)
      | ~ m1_pre_topc(D_178,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_525])).

tff(c_555,plain,(
    ! [D_178] :
      ( v1_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_178))
      | ~ m1_pre_topc(D_178,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_352])).

tff(c_204,plain,(
    ! [A_113,B_114,C_115,D_116] :
      ( k8_relset_1(A_113,B_114,C_115,D_116) = k10_relat_1(C_115,D_116)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_210,plain,(
    ! [D_116] : k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',D_116) = k10_relat_1('#skF_4',D_116) ),
    inference(resolution,[status(thm)],[c_40,c_204])).

tff(c_36,plain,(
    r1_tarski(k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_238,plain,(
    r1_tarski(k10_relat_1('#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_36])).

tff(c_428,plain,(
    ! [A_156,B_157,C_158] :
      ( k10_relat_1(k7_relat_1(A_156,B_157),C_158) = k10_relat_1(A_156,C_158)
      | ~ r1_tarski(k10_relat_1(A_156,C_158),B_157)
      | ~ v1_funct_1(A_156)
      | ~ v1_relat_1(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_435,plain,
    ( k10_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') = k10_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_238,c_428])).

tff(c_443,plain,(
    k10_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') = k10_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_44,c_435])).

tff(c_553,plain,
    ( k10_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_5') = k10_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_443])).

tff(c_580,plain,(
    k10_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_5') = k10_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_553])).

tff(c_564,plain,(
    ! [D_178] :
      ( r1_tarski(k1_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_178)),u1_struct_0(D_178))
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(D_178,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_16])).

tff(c_586,plain,(
    ! [D_178] :
      ( r1_tarski(k1_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_178)),u1_struct_0(D_178))
      | ~ m1_pre_topc(D_178,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_564])).

tff(c_24,plain,(
    ! [A_20,B_21,C_22,D_23] :
      ( k8_relset_1(A_20,B_21,C_22,D_23) = k10_relat_1(C_22,D_23)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1211,plain,(
    ! [A_250,B_251,C_252,D_253] :
      ( k8_relset_1(A_250,B_251,C_252,D_253) = k10_relat_1(C_252,D_253)
      | ~ r1_tarski(k2_relat_1(C_252),B_251)
      | ~ r1_tarski(k1_relat_1(C_252),A_250)
      | ~ v1_relat_1(C_252) ) ),
    inference(resolution,[status(thm)],[c_256,c_24])).

tff(c_2437,plain,(
    ! [A_369,A_370,B_371,D_372] :
      ( k8_relset_1(A_369,A_370,B_371,D_372) = k10_relat_1(B_371,D_372)
      | ~ r1_tarski(k1_relat_1(B_371),A_369)
      | ~ v5_relat_1(B_371,A_370)
      | ~ v1_relat_1(B_371) ) ),
    inference(resolution,[status(thm)],[c_12,c_1211])).

tff(c_41725,plain,(
    ! [D_2127,A_2128,D_2129] :
      ( k8_relset_1(u1_struct_0(D_2127),A_2128,k2_tmap_1('#skF_1','#skF_2','#skF_4',D_2127),D_2129) = k10_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_2127),D_2129)
      | ~ v5_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_2127),A_2128)
      | ~ v1_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_2127))
      | ~ m1_pre_topc(D_2127,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_586,c_2437])).

tff(c_34,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_5') != k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_237,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_5') != k10_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_34])).

tff(c_41751,plain,
    ( k10_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_5') != k10_relat_1('#skF_4','#skF_5')
    | ~ v5_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_41725,c_237])).

tff(c_41779,plain,
    ( ~ v5_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_580,c_41751])).

tff(c_41783,plain,(
    ~ v1_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_41779])).

tff(c_41786,plain,(
    ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_555,c_41783])).

tff(c_41790,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_41786])).

tff(c_41791,plain,(
    ~ v5_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_41779])).

tff(c_41804,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ r1_tarski(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_7408,c_41791])).

tff(c_41825,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_41804])).

tff(c_41838,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_41825])).

tff(c_41844,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_41838])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.32  % Computer   : n023.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.32  % CPULimit   : 60
% 0.14/0.32  % DateTime   : Tue Dec  1 11:42:51 EST 2020
% 0.14/0.32  % CPUTime    : 
% 0.14/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.86/12.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.86/12.78  
% 20.86/12.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.86/12.78  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 20.86/12.78  
% 20.86/12.78  %Foreground sorts:
% 20.86/12.78  
% 20.86/12.78  
% 20.86/12.78  %Background operators:
% 20.86/12.78  
% 20.86/12.78  
% 20.86/12.78  %Foreground operators:
% 20.86/12.78  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 20.86/12.78  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 20.86/12.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.86/12.78  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 20.86/12.78  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 20.86/12.78  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 20.86/12.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.86/12.78  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 20.86/12.78  tff('#skF_5', type, '#skF_5': $i).
% 20.86/12.78  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 20.86/12.78  tff('#skF_2', type, '#skF_2': $i).
% 20.86/12.78  tff('#skF_3', type, '#skF_3': $i).
% 20.86/12.78  tff('#skF_1', type, '#skF_1': $i).
% 20.86/12.78  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 20.86/12.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 20.86/12.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.86/12.78  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 20.86/12.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 20.86/12.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 20.86/12.78  tff('#skF_4', type, '#skF_4': $i).
% 20.86/12.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.86/12.78  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 20.86/12.78  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 20.86/12.78  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 20.86/12.78  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 20.86/12.78  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 20.86/12.78  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 20.86/12.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 20.86/12.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 20.86/12.78  
% 20.86/12.80  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 20.86/12.80  tff(f_154, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (r1_tarski(k8_relset_1(u1_struct_0(A), u1_struct_0(B), D, E), u1_struct_0(C)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), D, E) = k8_relset_1(u1_struct_0(C), u1_struct_0(B), k2_tmap_1(A, B, D, C), E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tmap_1)).
% 20.86/12.80  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 20.86/12.80  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 20.86/12.80  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 20.86/12.80  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 20.86/12.80  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 20.86/12.80  tff(f_82, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 20.86/12.80  tff(f_118, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 20.86/12.80  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 20.86/12.80  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 20.86/12.80  tff(f_76, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 20.86/12.80  tff(f_68, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 20.86/12.80  tff(f_91, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 20.86/12.80  tff(c_14, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 20.86/12.80  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_154])).
% 20.86/12.80  tff(c_8, plain, (![B_8, A_6]: (v1_relat_1(B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_6)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 20.86/12.80  tff(c_85, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_40, c_8])).
% 20.86/12.80  tff(c_91, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_85])).
% 20.86/12.80  tff(c_18, plain, (![B_16, A_15]: (r1_tarski(k7_relat_1(B_16, A_15), B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 20.86/12.80  tff(c_46, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_154])).
% 20.86/12.80  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 20.86/12.80  tff(c_92, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_40, c_4])).
% 20.86/12.80  tff(c_115, plain, (![A_95, C_96, B_97]: (r1_tarski(A_95, C_96) | ~r1_tarski(B_97, C_96) | ~r1_tarski(A_95, B_97))), inference(cnfTransformation, [status(thm)], [f_31])).
% 20.86/12.80  tff(c_312, plain, (![A_136]: (r1_tarski(A_136, k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))) | ~r1_tarski(A_136, '#skF_4'))), inference(resolution, [status(thm)], [c_92, c_115])).
% 20.86/12.80  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 20.86/12.80  tff(c_160, plain, (![C_101, B_102, A_103]: (v5_relat_1(C_101, B_102) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_103, B_102))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 20.86/12.80  tff(c_169, plain, (![A_4, B_102, A_103]: (v5_relat_1(A_4, B_102) | ~r1_tarski(A_4, k2_zfmisc_1(A_103, B_102)))), inference(resolution, [status(thm)], [c_6, c_160])).
% 20.86/12.80  tff(c_329, plain, (![A_136]: (v5_relat_1(A_136, u1_struct_0('#skF_2')) | ~r1_tarski(A_136, '#skF_4'))), inference(resolution, [status(thm)], [c_312, c_169])).
% 20.86/12.80  tff(c_73, plain, (![B_85, A_86]: (v1_relat_1(B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(A_86)) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_42])).
% 20.86/12.80  tff(c_80, plain, (![A_4, B_5]: (v1_relat_1(A_4) | ~v1_relat_1(B_5) | ~r1_tarski(A_4, B_5))), inference(resolution, [status(thm)], [c_6, c_73])).
% 20.86/12.80  tff(c_327, plain, (![A_136]: (v1_relat_1(A_136) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))) | ~r1_tarski(A_136, '#skF_4'))), inference(resolution, [status(thm)], [c_312, c_80])).
% 20.86/12.80  tff(c_335, plain, (![A_137]: (v1_relat_1(A_137) | ~r1_tarski(A_137, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_327])).
% 20.86/12.80  tff(c_347, plain, (![A_15]: (v1_relat_1(k7_relat_1('#skF_4', A_15)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_335])).
% 20.86/12.80  tff(c_352, plain, (![A_15]: (v1_relat_1(k7_relat_1('#skF_4', A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_347])).
% 20.86/12.80  tff(c_60, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_154])).
% 20.86/12.80  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 20.86/12.80  tff(c_58, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_154])).
% 20.86/12.80  tff(c_56, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_154])).
% 20.86/12.80  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 20.86/12.80  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 20.86/12.80  tff(c_44, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_154])).
% 20.86/12.80  tff(c_42, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 20.86/12.80  tff(c_356, plain, (![A_141, B_142, C_143, D_144]: (k2_partfun1(A_141, B_142, C_143, D_144)=k7_relat_1(C_143, D_144) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))) | ~v1_funct_1(C_143))), inference(cnfTransformation, [status(thm)], [f_82])).
% 20.86/12.80  tff(c_360, plain, (![D_144]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', D_144)=k7_relat_1('#skF_4', D_144) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_356])).
% 20.86/12.80  tff(c_367, plain, (![D_144]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', D_144)=k7_relat_1('#skF_4', D_144))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_360])).
% 20.86/12.80  tff(c_513, plain, (![A_171, B_172, C_173, D_174]: (k2_partfun1(u1_struct_0(A_171), u1_struct_0(B_172), C_173, u1_struct_0(D_174))=k2_tmap_1(A_171, B_172, C_173, D_174) | ~m1_pre_topc(D_174, A_171) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_171), u1_struct_0(B_172)))) | ~v1_funct_2(C_173, u1_struct_0(A_171), u1_struct_0(B_172)) | ~v1_funct_1(C_173) | ~l1_pre_topc(B_172) | ~v2_pre_topc(B_172) | v2_struct_0(B_172) | ~l1_pre_topc(A_171) | ~v2_pre_topc(A_171) | v2_struct_0(A_171))), inference(cnfTransformation, [status(thm)], [f_118])).
% 20.86/12.80  tff(c_518, plain, (![D_174]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_174))=k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_174) | ~m1_pre_topc(D_174, '#skF_1') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_513])).
% 20.86/12.80  tff(c_525, plain, (![D_174]: (k7_relat_1('#skF_4', u1_struct_0(D_174))=k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_174) | ~m1_pre_topc(D_174, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_44, c_42, c_367, c_518])).
% 20.86/12.80  tff(c_526, plain, (![D_174]: (k7_relat_1('#skF_4', u1_struct_0(D_174))=k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_174) | ~m1_pre_topc(D_174, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_525])).
% 20.86/12.80  tff(c_16, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(k7_relat_1(B_14, A_13)), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 20.86/12.80  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 20.86/12.80  tff(c_256, plain, (![C_126, A_127, B_128]: (m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))) | ~r1_tarski(k2_relat_1(C_126), B_128) | ~r1_tarski(k1_relat_1(C_126), A_127) | ~v1_relat_1(C_126))), inference(cnfTransformation, [status(thm)], [f_76])).
% 20.86/12.80  tff(c_928, plain, (![C_226, A_227, B_228]: (r1_tarski(C_226, k2_zfmisc_1(A_227, B_228)) | ~r1_tarski(k2_relat_1(C_226), B_228) | ~r1_tarski(k1_relat_1(C_226), A_227) | ~v1_relat_1(C_226))), inference(resolution, [status(thm)], [c_256, c_4])).
% 20.86/12.80  tff(c_1227, plain, (![B_255, A_256, A_257]: (r1_tarski(B_255, k2_zfmisc_1(A_256, A_257)) | ~r1_tarski(k1_relat_1(B_255), A_256) | ~v5_relat_1(B_255, A_257) | ~v1_relat_1(B_255))), inference(resolution, [status(thm)], [c_12, c_928])).
% 20.86/12.80  tff(c_4909, plain, (![B_578, A_579, A_580]: (r1_tarski(k7_relat_1(B_578, A_579), k2_zfmisc_1(A_579, A_580)) | ~v5_relat_1(k7_relat_1(B_578, A_579), A_580) | ~v1_relat_1(k7_relat_1(B_578, A_579)) | ~v1_relat_1(B_578))), inference(resolution, [status(thm)], [c_16, c_1227])).
% 20.86/12.80  tff(c_4934, plain, (![D_174, A_580]: (r1_tarski(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_174), k2_zfmisc_1(u1_struct_0(D_174), A_580)) | ~v5_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_174)), A_580) | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_174))) | ~v1_relat_1('#skF_4') | ~m1_pre_topc(D_174, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_526, c_4909])).
% 20.86/12.80  tff(c_7326, plain, (![D_708, A_709]: (r1_tarski(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_708), k2_zfmisc_1(u1_struct_0(D_708), A_709)) | ~v5_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_708)), A_709) | ~m1_pre_topc(D_708, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_352, c_4934])).
% 20.86/12.80  tff(c_7365, plain, (![D_710, A_711]: (v5_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_710), A_711) | ~v5_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_710)), A_711) | ~m1_pre_topc(D_710, '#skF_1'))), inference(resolution, [status(thm)], [c_7326, c_169])).
% 20.86/12.80  tff(c_7408, plain, (![D_710]: (v5_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_710), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_710, '#skF_1') | ~r1_tarski(k7_relat_1('#skF_4', u1_struct_0(D_710)), '#skF_4'))), inference(resolution, [status(thm)], [c_329, c_7365])).
% 20.86/12.80  tff(c_541, plain, (![D_178]: (k7_relat_1('#skF_4', u1_struct_0(D_178))=k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_178) | ~m1_pre_topc(D_178, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_525])).
% 20.86/12.80  tff(c_555, plain, (![D_178]: (v1_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_178)) | ~m1_pre_topc(D_178, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_541, c_352])).
% 20.86/12.80  tff(c_204, plain, (![A_113, B_114, C_115, D_116]: (k8_relset_1(A_113, B_114, C_115, D_116)=k10_relat_1(C_115, D_116) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 20.86/12.80  tff(c_210, plain, (![D_116]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', D_116)=k10_relat_1('#skF_4', D_116))), inference(resolution, [status(thm)], [c_40, c_204])).
% 20.86/12.80  tff(c_36, plain, (r1_tarski(k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 20.86/12.80  tff(c_238, plain, (r1_tarski(k10_relat_1('#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_36])).
% 20.86/12.80  tff(c_428, plain, (![A_156, B_157, C_158]: (k10_relat_1(k7_relat_1(A_156, B_157), C_158)=k10_relat_1(A_156, C_158) | ~r1_tarski(k10_relat_1(A_156, C_158), B_157) | ~v1_funct_1(A_156) | ~v1_relat_1(A_156))), inference(cnfTransformation, [status(thm)], [f_91])).
% 20.86/12.80  tff(c_435, plain, (k10_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')=k10_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_238, c_428])).
% 20.86/12.80  tff(c_443, plain, (k10_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')=k10_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_44, c_435])).
% 20.86/12.80  tff(c_553, plain, (k10_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_5')=k10_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_541, c_443])).
% 20.86/12.80  tff(c_580, plain, (k10_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_5')=k10_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_553])).
% 20.86/12.80  tff(c_564, plain, (![D_178]: (r1_tarski(k1_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_178)), u1_struct_0(D_178)) | ~v1_relat_1('#skF_4') | ~m1_pre_topc(D_178, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_541, c_16])).
% 20.86/12.80  tff(c_586, plain, (![D_178]: (r1_tarski(k1_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_178)), u1_struct_0(D_178)) | ~m1_pre_topc(D_178, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_564])).
% 20.86/12.80  tff(c_24, plain, (![A_20, B_21, C_22, D_23]: (k8_relset_1(A_20, B_21, C_22, D_23)=k10_relat_1(C_22, D_23) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 20.86/12.80  tff(c_1211, plain, (![A_250, B_251, C_252, D_253]: (k8_relset_1(A_250, B_251, C_252, D_253)=k10_relat_1(C_252, D_253) | ~r1_tarski(k2_relat_1(C_252), B_251) | ~r1_tarski(k1_relat_1(C_252), A_250) | ~v1_relat_1(C_252))), inference(resolution, [status(thm)], [c_256, c_24])).
% 20.86/12.80  tff(c_2437, plain, (![A_369, A_370, B_371, D_372]: (k8_relset_1(A_369, A_370, B_371, D_372)=k10_relat_1(B_371, D_372) | ~r1_tarski(k1_relat_1(B_371), A_369) | ~v5_relat_1(B_371, A_370) | ~v1_relat_1(B_371))), inference(resolution, [status(thm)], [c_12, c_1211])).
% 20.86/12.80  tff(c_41725, plain, (![D_2127, A_2128, D_2129]: (k8_relset_1(u1_struct_0(D_2127), A_2128, k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_2127), D_2129)=k10_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_2127), D_2129) | ~v5_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_2127), A_2128) | ~v1_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_2127)) | ~m1_pre_topc(D_2127, '#skF_1'))), inference(resolution, [status(thm)], [c_586, c_2437])).
% 20.86/12.80  tff(c_34, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_5')!=k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 20.86/12.80  tff(c_237, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_5')!=k10_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_210, c_34])).
% 20.86/12.80  tff(c_41751, plain, (k10_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_5')!=k10_relat_1('#skF_4', '#skF_5') | ~v5_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')) | ~v1_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_41725, c_237])).
% 20.86/12.80  tff(c_41779, plain, (~v5_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')) | ~v1_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_580, c_41751])).
% 20.86/12.80  tff(c_41783, plain, (~v1_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_41779])).
% 20.86/12.80  tff(c_41786, plain, (~m1_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_555, c_41783])).
% 20.86/12.80  tff(c_41790, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_41786])).
% 20.86/12.80  tff(c_41791, plain, (~v5_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_41779])).
% 20.86/12.80  tff(c_41804, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~r1_tarski(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_4')), inference(resolution, [status(thm)], [c_7408, c_41791])).
% 20.86/12.80  tff(c_41825, plain, (~r1_tarski(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_41804])).
% 20.86/12.80  tff(c_41838, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_41825])).
% 20.86/12.80  tff(c_41844, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_41838])).
% 20.86/12.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.86/12.80  
% 20.86/12.80  Inference rules
% 20.86/12.80  ----------------------
% 20.86/12.80  #Ref     : 0
% 20.86/12.80  #Sup     : 10280
% 20.86/12.80  #Fact    : 0
% 20.86/12.80  #Define  : 0
% 20.86/12.80  #Split   : 25
% 20.86/12.80  #Chain   : 0
% 20.86/12.80  #Close   : 0
% 20.86/12.80  
% 20.86/12.80  Ordering : KBO
% 20.86/12.80  
% 20.86/12.80  Simplification rules
% 20.86/12.80  ----------------------
% 20.86/12.80  #Subsume      : 1473
% 20.86/12.80  #Demod        : 1870
% 20.86/12.80  #Tautology    : 641
% 20.86/12.80  #SimpNegUnit  : 295
% 20.86/12.80  #BackRed      : 2
% 20.86/12.80  
% 20.86/12.80  #Partial instantiations: 0
% 20.86/12.80  #Strategies tried      : 1
% 20.86/12.80  
% 20.86/12.80  Timing (in seconds)
% 20.86/12.80  ----------------------
% 20.86/12.81  Preprocessing        : 0.34
% 20.86/12.81  Parsing              : 0.18
% 21.14/12.81  CNF conversion       : 0.03
% 21.14/12.81  Main loop            : 11.73
% 21.14/12.81  Inferencing          : 2.23
% 21.14/12.81  Reduction            : 2.72
% 21.14/12.81  Demodulation         : 1.86
% 21.14/12.81  BG Simplification    : 0.23
% 21.14/12.81  Subsumption          : 5.89
% 21.14/12.81  Abstraction          : 0.38
% 21.14/12.81  MUC search           : 0.00
% 21.14/12.81  Cooper               : 0.00
% 21.14/12.81  Total                : 12.10
% 21.14/12.81  Index Insertion      : 0.00
% 21.14/12.81  Index Deletion       : 0.00
% 21.14/12.81  Index Matching       : 0.00
% 21.14/12.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
