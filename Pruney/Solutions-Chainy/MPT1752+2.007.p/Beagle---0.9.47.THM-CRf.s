%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:01 EST 2020

% Result     : Theorem 52.67s
% Output     : CNFRefutation 52.77s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 454 expanded)
%              Number of leaves         :   44 ( 185 expanded)
%              Depth                    :   15
%              Number of atoms          :  233 (2089 expanded)
%              Number of equality atoms :   30 ( 214 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_165,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tmap_1)).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_129,axiom,(
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

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_102,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( r1_tarski(k10_relat_1(A,C),B)
         => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(c_48,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_12,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_67,plain,(
    ! [B_88,A_89] :
      ( v1_relat_1(B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_89))
      | ~ v1_relat_1(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_70,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_42,c_67])).

tff(c_76,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_70])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_60,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_58,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_44,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_386,plain,(
    ! [A_154,B_155,C_156,D_157] :
      ( k2_partfun1(A_154,B_155,C_156,D_157) = k7_relat_1(C_156,D_157)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155)))
      | ~ v1_funct_1(C_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_390,plain,(
    ! [D_157] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',D_157) = k7_relat_1('#skF_4',D_157)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_386])).

tff(c_394,plain,(
    ! [D_157] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',D_157) = k7_relat_1('#skF_4',D_157) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_390])).

tff(c_634,plain,(
    ! [A_190,B_191,C_192,D_193] :
      ( k2_partfun1(u1_struct_0(A_190),u1_struct_0(B_191),C_192,u1_struct_0(D_193)) = k2_tmap_1(A_190,B_191,C_192,D_193)
      | ~ m1_pre_topc(D_193,A_190)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_190),u1_struct_0(B_191))))
      | ~ v1_funct_2(C_192,u1_struct_0(A_190),u1_struct_0(B_191))
      | ~ v1_funct_1(C_192)
      | ~ l1_pre_topc(B_191)
      | ~ v2_pre_topc(B_191)
      | v2_struct_0(B_191)
      | ~ l1_pre_topc(A_190)
      | ~ v2_pre_topc(A_190)
      | v2_struct_0(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_639,plain,(
    ! [D_193] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_193)) = k2_tmap_1('#skF_1','#skF_2','#skF_4',D_193)
      | ~ m1_pre_topc(D_193,'#skF_1')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_634])).

tff(c_643,plain,(
    ! [D_193] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_193)) = k2_tmap_1('#skF_1','#skF_2','#skF_4',D_193)
      | ~ m1_pre_topc(D_193,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_52,c_46,c_44,c_394,c_639])).

tff(c_645,plain,(
    ! [D_194] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_194)) = k2_tmap_1('#skF_1','#skF_2','#skF_4',D_194)
      | ~ m1_pre_topc(D_194,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_643])).

tff(c_20,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k7_relat_1(B_19,A_18),B_19)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_678,plain,(
    ! [D_194] :
      ( r1_tarski(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_194),'#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(D_194,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_645,c_20])).

tff(c_705,plain,(
    ! [D_194] :
      ( r1_tarski(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_194),'#skF_4')
      | ~ m1_pre_topc(D_194,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_678])).

tff(c_644,plain,(
    ! [D_193] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_193)) = k2_tmap_1('#skF_1','#skF_2','#skF_4',D_193)
      | ~ m1_pre_topc(D_193,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_643])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( v1_relat_1(k7_relat_1(A_9,B_10))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_174,plain,(
    ! [A_118,B_119,C_120,D_121] :
      ( k8_relset_1(A_118,B_119,C_120,D_121) = k10_relat_1(C_120,D_121)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_177,plain,(
    ! [D_121] : k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',D_121) = k10_relat_1('#skF_4',D_121) ),
    inference(resolution,[status(thm)],[c_42,c_174])).

tff(c_38,plain,(
    r1_tarski(k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_179,plain,(
    r1_tarski(k10_relat_1('#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_38])).

tff(c_523,plain,(
    ! [A_176,B_177,C_178] :
      ( k10_relat_1(k7_relat_1(A_176,B_177),C_178) = k10_relat_1(A_176,C_178)
      | ~ r1_tarski(k10_relat_1(A_176,C_178),B_177)
      | ~ v1_funct_1(A_176)
      | ~ v1_relat_1(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_526,plain,
    ( k10_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') = k10_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_179,c_523])).

tff(c_529,plain,(
    k10_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') = k10_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_46,c_526])).

tff(c_32,plain,(
    ! [A_34,B_37,C_38] :
      ( k10_relat_1(k7_relat_1(A_34,B_37),C_38) = k10_relat_1(A_34,C_38)
      | ~ r1_tarski(k10_relat_1(A_34,C_38),B_37)
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_533,plain,(
    ! [B_37] :
      ( k10_relat_1(k7_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),B_37),'#skF_5') = k10_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5')
      | ~ r1_tarski(k10_relat_1('#skF_4','#skF_5'),B_37)
      | ~ v1_funct_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')))
      | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_529,c_32])).

tff(c_536,plain,(
    ! [B_37] :
      ( k10_relat_1(k7_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),B_37),'#skF_5') = k10_relat_1('#skF_4','#skF_5')
      | ~ r1_tarski(k10_relat_1('#skF_4','#skF_5'),B_37)
      | ~ v1_funct_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')))
      | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_529,c_533])).

tff(c_25695,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_536])).

tff(c_25701,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_25695])).

tff(c_25707,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_25701])).

tff(c_25709,plain,(
    v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_536])).

tff(c_25712,plain,
    ( v1_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_644,c_25709])).

tff(c_25714,plain,(
    v1_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_25712])).

tff(c_93,plain,(
    ! [C_95,B_96,A_97] :
      ( v5_relat_1(C_95,B_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_97,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_97,plain,(
    v5_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_93])).

tff(c_14,plain,(
    ! [A_13,B_15] :
      ( r1_tarski(k2_relat_1(A_13),k2_relat_1(B_15))
      | ~ r1_tarski(A_13,B_15)
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_89,plain,(
    ! [B_93,A_94] :
      ( r1_tarski(k2_relat_1(B_93),A_94)
      | ~ v5_relat_1(B_93,A_94)
      | ~ v1_relat_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_158,plain,(
    ! [A_115,A_116,B_117] :
      ( r1_tarski(A_115,A_116)
      | ~ r1_tarski(A_115,k2_relat_1(B_117))
      | ~ v5_relat_1(B_117,A_116)
      | ~ v1_relat_1(B_117) ) ),
    inference(resolution,[status(thm)],[c_89,c_2])).

tff(c_404,plain,(
    ! [A_159,A_160,B_161] :
      ( r1_tarski(k2_relat_1(A_159),A_160)
      | ~ v5_relat_1(B_161,A_160)
      | ~ r1_tarski(A_159,B_161)
      | ~ v1_relat_1(B_161)
      | ~ v1_relat_1(A_159) ) ),
    inference(resolution,[status(thm)],[c_14,c_158])).

tff(c_408,plain,(
    ! [A_159] :
      ( r1_tarski(k2_relat_1(A_159),u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_159,'#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(A_159) ) ),
    inference(resolution,[status(thm)],[c_97,c_404])).

tff(c_413,plain,(
    ! [A_162] :
      ( r1_tarski(k2_relat_1(A_162),u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_162,'#skF_4')
      | ~ v1_relat_1(A_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_408])).

tff(c_6,plain,(
    ! [B_8,A_7] :
      ( v5_relat_1(B_8,A_7)
      | ~ r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_422,plain,(
    ! [A_162] :
      ( v5_relat_1(A_162,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_162,'#skF_4')
      | ~ v1_relat_1(A_162) ) ),
    inference(resolution,[status(thm)],[c_413,c_6])).

tff(c_651,plain,
    ( k10_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_5') = k10_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_645,c_529])).

tff(c_687,plain,(
    k10_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_5') = k10_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_651])).

tff(c_18,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_17,A_16)),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_675,plain,(
    ! [D_194] :
      ( r1_tarski(k1_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_194)),u1_struct_0(D_194))
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(D_194,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_645,c_18])).

tff(c_703,plain,(
    ! [D_194] :
      ( r1_tarski(k1_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_194)),u1_struct_0(D_194))
      | ~ m1_pre_topc(D_194,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_675])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v5_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_245,plain,(
    ! [C_129,A_130,B_131] :
      ( m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131)))
      | ~ r1_tarski(k2_relat_1(C_129),B_131)
      | ~ r1_tarski(k1_relat_1(C_129),A_130)
      | ~ v1_relat_1(C_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_26,plain,(
    ! [A_23,B_24,C_25,D_26] :
      ( k8_relset_1(A_23,B_24,C_25,D_26) = k10_relat_1(C_25,D_26)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_859,plain,(
    ! [A_205,B_206,C_207,D_208] :
      ( k8_relset_1(A_205,B_206,C_207,D_208) = k10_relat_1(C_207,D_208)
      | ~ r1_tarski(k2_relat_1(C_207),B_206)
      | ~ r1_tarski(k1_relat_1(C_207),A_205)
      | ~ v1_relat_1(C_207) ) ),
    inference(resolution,[status(thm)],[c_245,c_26])).

tff(c_1958,plain,(
    ! [A_295,A_296,B_297,D_298] :
      ( k8_relset_1(A_295,A_296,B_297,D_298) = k10_relat_1(B_297,D_298)
      | ~ r1_tarski(k1_relat_1(B_297),A_295)
      | ~ v5_relat_1(B_297,A_296)
      | ~ v1_relat_1(B_297) ) ),
    inference(resolution,[status(thm)],[c_8,c_859])).

tff(c_81515,plain,(
    ! [D_2844,A_2845,D_2846] :
      ( k8_relset_1(u1_struct_0(D_2844),A_2845,k2_tmap_1('#skF_1','#skF_2','#skF_4',D_2844),D_2846) = k10_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_2844),D_2846)
      | ~ v5_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_2844),A_2845)
      | ~ v1_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_2844))
      | ~ m1_pre_topc(D_2844,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_703,c_1958])).

tff(c_36,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_5') != k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_178,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_5') != k10_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_36])).

tff(c_81521,plain,
    ( k10_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_5') != k10_relat_1('#skF_4','#skF_5')
    | ~ v5_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_81515,c_178])).

tff(c_81527,plain,(
    ~ v5_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_25714,c_687,c_81521])).

tff(c_81534,plain,
    ( ~ r1_tarski(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_4')
    | ~ v1_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_422,c_81527])).

tff(c_81540,plain,(
    ~ r1_tarski(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25714,c_81534])).

tff(c_81543,plain,(
    ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_705,c_81540])).

tff(c_81547,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_81543])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:22:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 52.67/40.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 52.77/40.79  
% 52.77/40.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 52.77/40.80  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 52.77/40.80  
% 52.77/40.80  %Foreground sorts:
% 52.77/40.80  
% 52.77/40.80  
% 52.77/40.80  %Background operators:
% 52.77/40.80  
% 52.77/40.80  
% 52.77/40.80  %Foreground operators:
% 52.77/40.80  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 52.77/40.80  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 52.77/40.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 52.77/40.80  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 52.77/40.80  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 52.77/40.80  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 52.77/40.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 52.77/40.80  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 52.77/40.80  tff('#skF_5', type, '#skF_5': $i).
% 52.77/40.80  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 52.77/40.80  tff('#skF_2', type, '#skF_2': $i).
% 52.77/40.80  tff('#skF_3', type, '#skF_3': $i).
% 52.77/40.80  tff('#skF_1', type, '#skF_1': $i).
% 52.77/40.80  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 52.77/40.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 52.77/40.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 52.77/40.80  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 52.77/40.80  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 52.77/40.80  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 52.77/40.80  tff('#skF_4', type, '#skF_4': $i).
% 52.77/40.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 52.77/40.80  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 52.77/40.80  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 52.77/40.80  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 52.77/40.80  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 52.77/40.80  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 52.77/40.80  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 52.77/40.80  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 52.77/40.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 52.77/40.80  
% 52.77/40.82  tff(f_165, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (r1_tarski(k8_relset_1(u1_struct_0(A), u1_struct_0(B), D, E), u1_struct_0(C)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), D, E) = k8_relset_1(u1_struct_0(C), u1_struct_0(B), k2_tmap_1(A, B, D, C), E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tmap_1)).
% 52.77/40.82  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 52.77/40.82  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 52.77/40.82  tff(f_93, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 52.77/40.82  tff(f_129, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 52.77/40.82  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 52.77/40.82  tff(f_48, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 52.77/40.82  tff(f_79, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 52.77/40.82  tff(f_102, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 52.77/40.82  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 52.77/40.82  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 52.77/40.82  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 52.77/40.82  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 52.77/40.82  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 52.77/40.82  tff(f_87, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 52.77/40.82  tff(c_48, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_165])).
% 52.77/40.82  tff(c_12, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 52.77/40.82  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_165])).
% 52.77/40.82  tff(c_67, plain, (![B_88, A_89]: (v1_relat_1(B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(A_89)) | ~v1_relat_1(A_89))), inference(cnfTransformation, [status(thm)], [f_38])).
% 52.77/40.82  tff(c_70, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_42, c_67])).
% 52.77/40.82  tff(c_76, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_70])).
% 52.77/40.82  tff(c_62, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_165])).
% 52.77/40.82  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 52.77/40.82  tff(c_60, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_165])).
% 52.77/40.82  tff(c_58, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_165])).
% 52.77/40.82  tff(c_54, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 52.77/40.82  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 52.77/40.82  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_165])).
% 52.77/40.82  tff(c_44, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 52.77/40.82  tff(c_386, plain, (![A_154, B_155, C_156, D_157]: (k2_partfun1(A_154, B_155, C_156, D_157)=k7_relat_1(C_156, D_157) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))) | ~v1_funct_1(C_156))), inference(cnfTransformation, [status(thm)], [f_93])).
% 52.77/40.82  tff(c_390, plain, (![D_157]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', D_157)=k7_relat_1('#skF_4', D_157) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_386])).
% 52.77/40.82  tff(c_394, plain, (![D_157]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', D_157)=k7_relat_1('#skF_4', D_157))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_390])).
% 52.77/40.82  tff(c_634, plain, (![A_190, B_191, C_192, D_193]: (k2_partfun1(u1_struct_0(A_190), u1_struct_0(B_191), C_192, u1_struct_0(D_193))=k2_tmap_1(A_190, B_191, C_192, D_193) | ~m1_pre_topc(D_193, A_190) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_190), u1_struct_0(B_191)))) | ~v1_funct_2(C_192, u1_struct_0(A_190), u1_struct_0(B_191)) | ~v1_funct_1(C_192) | ~l1_pre_topc(B_191) | ~v2_pre_topc(B_191) | v2_struct_0(B_191) | ~l1_pre_topc(A_190) | ~v2_pre_topc(A_190) | v2_struct_0(A_190))), inference(cnfTransformation, [status(thm)], [f_129])).
% 52.77/40.82  tff(c_639, plain, (![D_193]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_193))=k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_193) | ~m1_pre_topc(D_193, '#skF_1') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_634])).
% 52.77/40.82  tff(c_643, plain, (![D_193]: (k7_relat_1('#skF_4', u1_struct_0(D_193))=k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_193) | ~m1_pre_topc(D_193, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_52, c_46, c_44, c_394, c_639])).
% 52.77/40.82  tff(c_645, plain, (![D_194]: (k7_relat_1('#skF_4', u1_struct_0(D_194))=k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_194) | ~m1_pre_topc(D_194, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_643])).
% 52.77/40.82  tff(c_20, plain, (![B_19, A_18]: (r1_tarski(k7_relat_1(B_19, A_18), B_19) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 52.77/40.82  tff(c_678, plain, (![D_194]: (r1_tarski(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_194), '#skF_4') | ~v1_relat_1('#skF_4') | ~m1_pre_topc(D_194, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_645, c_20])).
% 52.77/40.82  tff(c_705, plain, (![D_194]: (r1_tarski(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_194), '#skF_4') | ~m1_pre_topc(D_194, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_678])).
% 52.77/40.82  tff(c_644, plain, (![D_193]: (k7_relat_1('#skF_4', u1_struct_0(D_193))=k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_193) | ~m1_pre_topc(D_193, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_643])).
% 52.77/40.82  tff(c_10, plain, (![A_9, B_10]: (v1_relat_1(k7_relat_1(A_9, B_10)) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 52.77/40.82  tff(c_174, plain, (![A_118, B_119, C_120, D_121]: (k8_relset_1(A_118, B_119, C_120, D_121)=k10_relat_1(C_120, D_121) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 52.77/40.82  tff(c_177, plain, (![D_121]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', D_121)=k10_relat_1('#skF_4', D_121))), inference(resolution, [status(thm)], [c_42, c_174])).
% 52.77/40.82  tff(c_38, plain, (r1_tarski(k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 52.77/40.82  tff(c_179, plain, (r1_tarski(k10_relat_1('#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_38])).
% 52.77/40.82  tff(c_523, plain, (![A_176, B_177, C_178]: (k10_relat_1(k7_relat_1(A_176, B_177), C_178)=k10_relat_1(A_176, C_178) | ~r1_tarski(k10_relat_1(A_176, C_178), B_177) | ~v1_funct_1(A_176) | ~v1_relat_1(A_176))), inference(cnfTransformation, [status(thm)], [f_102])).
% 52.77/40.82  tff(c_526, plain, (k10_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')=k10_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_179, c_523])).
% 52.77/40.82  tff(c_529, plain, (k10_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')=k10_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_46, c_526])).
% 52.77/40.82  tff(c_32, plain, (![A_34, B_37, C_38]: (k10_relat_1(k7_relat_1(A_34, B_37), C_38)=k10_relat_1(A_34, C_38) | ~r1_tarski(k10_relat_1(A_34, C_38), B_37) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_102])).
% 52.77/40.82  tff(c_533, plain, (![B_37]: (k10_relat_1(k7_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), B_37), '#skF_5')=k10_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5') | ~r1_tarski(k10_relat_1('#skF_4', '#skF_5'), B_37) | ~v1_funct_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3'))) | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_529, c_32])).
% 52.77/40.82  tff(c_536, plain, (![B_37]: (k10_relat_1(k7_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), B_37), '#skF_5')=k10_relat_1('#skF_4', '#skF_5') | ~r1_tarski(k10_relat_1('#skF_4', '#skF_5'), B_37) | ~v1_funct_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3'))) | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_529, c_533])).
% 52.77/40.82  tff(c_25695, plain, (~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_536])).
% 52.77/40.82  tff(c_25701, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_25695])).
% 52.77/40.82  tff(c_25707, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_25701])).
% 52.77/40.82  tff(c_25709, plain, (v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_536])).
% 52.77/40.82  tff(c_25712, plain, (v1_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_644, c_25709])).
% 52.77/40.82  tff(c_25714, plain, (v1_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_25712])).
% 52.77/40.82  tff(c_93, plain, (![C_95, B_96, A_97]: (v5_relat_1(C_95, B_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_97, B_96))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 52.77/40.82  tff(c_97, plain, (v5_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_93])).
% 52.77/40.82  tff(c_14, plain, (![A_13, B_15]: (r1_tarski(k2_relat_1(A_13), k2_relat_1(B_15)) | ~r1_tarski(A_13, B_15) | ~v1_relat_1(B_15) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 52.77/40.82  tff(c_89, plain, (![B_93, A_94]: (r1_tarski(k2_relat_1(B_93), A_94) | ~v5_relat_1(B_93, A_94) | ~v1_relat_1(B_93))), inference(cnfTransformation, [status(thm)], [f_44])).
% 52.77/40.82  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 52.77/40.82  tff(c_158, plain, (![A_115, A_116, B_117]: (r1_tarski(A_115, A_116) | ~r1_tarski(A_115, k2_relat_1(B_117)) | ~v5_relat_1(B_117, A_116) | ~v1_relat_1(B_117))), inference(resolution, [status(thm)], [c_89, c_2])).
% 52.77/40.82  tff(c_404, plain, (![A_159, A_160, B_161]: (r1_tarski(k2_relat_1(A_159), A_160) | ~v5_relat_1(B_161, A_160) | ~r1_tarski(A_159, B_161) | ~v1_relat_1(B_161) | ~v1_relat_1(A_159))), inference(resolution, [status(thm)], [c_14, c_158])).
% 52.77/40.82  tff(c_408, plain, (![A_159]: (r1_tarski(k2_relat_1(A_159), u1_struct_0('#skF_2')) | ~r1_tarski(A_159, '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(A_159))), inference(resolution, [status(thm)], [c_97, c_404])).
% 52.77/40.82  tff(c_413, plain, (![A_162]: (r1_tarski(k2_relat_1(A_162), u1_struct_0('#skF_2')) | ~r1_tarski(A_162, '#skF_4') | ~v1_relat_1(A_162))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_408])).
% 52.77/40.82  tff(c_6, plain, (![B_8, A_7]: (v5_relat_1(B_8, A_7) | ~r1_tarski(k2_relat_1(B_8), A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 52.77/40.82  tff(c_422, plain, (![A_162]: (v5_relat_1(A_162, u1_struct_0('#skF_2')) | ~r1_tarski(A_162, '#skF_4') | ~v1_relat_1(A_162))), inference(resolution, [status(thm)], [c_413, c_6])).
% 52.77/40.82  tff(c_651, plain, (k10_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_5')=k10_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_645, c_529])).
% 52.77/40.82  tff(c_687, plain, (k10_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_5')=k10_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_651])).
% 52.77/40.82  tff(c_18, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(k7_relat_1(B_17, A_16)), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 52.77/40.82  tff(c_675, plain, (![D_194]: (r1_tarski(k1_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_194)), u1_struct_0(D_194)) | ~v1_relat_1('#skF_4') | ~m1_pre_topc(D_194, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_645, c_18])).
% 52.77/40.82  tff(c_703, plain, (![D_194]: (r1_tarski(k1_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_194)), u1_struct_0(D_194)) | ~m1_pre_topc(D_194, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_675])).
% 52.77/40.82  tff(c_8, plain, (![B_8, A_7]: (r1_tarski(k2_relat_1(B_8), A_7) | ~v5_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 52.77/40.82  tff(c_245, plain, (![C_129, A_130, B_131]: (m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))) | ~r1_tarski(k2_relat_1(C_129), B_131) | ~r1_tarski(k1_relat_1(C_129), A_130) | ~v1_relat_1(C_129))), inference(cnfTransformation, [status(thm)], [f_87])).
% 52.77/40.82  tff(c_26, plain, (![A_23, B_24, C_25, D_26]: (k8_relset_1(A_23, B_24, C_25, D_26)=k10_relat_1(C_25, D_26) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 52.77/40.82  tff(c_859, plain, (![A_205, B_206, C_207, D_208]: (k8_relset_1(A_205, B_206, C_207, D_208)=k10_relat_1(C_207, D_208) | ~r1_tarski(k2_relat_1(C_207), B_206) | ~r1_tarski(k1_relat_1(C_207), A_205) | ~v1_relat_1(C_207))), inference(resolution, [status(thm)], [c_245, c_26])).
% 52.77/40.82  tff(c_1958, plain, (![A_295, A_296, B_297, D_298]: (k8_relset_1(A_295, A_296, B_297, D_298)=k10_relat_1(B_297, D_298) | ~r1_tarski(k1_relat_1(B_297), A_295) | ~v5_relat_1(B_297, A_296) | ~v1_relat_1(B_297))), inference(resolution, [status(thm)], [c_8, c_859])).
% 52.77/40.82  tff(c_81515, plain, (![D_2844, A_2845, D_2846]: (k8_relset_1(u1_struct_0(D_2844), A_2845, k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_2844), D_2846)=k10_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_2844), D_2846) | ~v5_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_2844), A_2845) | ~v1_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_2844)) | ~m1_pre_topc(D_2844, '#skF_1'))), inference(resolution, [status(thm)], [c_703, c_1958])).
% 52.77/40.82  tff(c_36, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_5')!=k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_165])).
% 52.77/40.82  tff(c_178, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_5')!=k10_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_177, c_36])).
% 52.77/40.82  tff(c_81521, plain, (k10_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_5')!=k10_relat_1('#skF_4', '#skF_5') | ~v5_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')) | ~v1_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_81515, c_178])).
% 52.77/40.82  tff(c_81527, plain, (~v5_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_25714, c_687, c_81521])).
% 52.77/40.82  tff(c_81534, plain, (~r1_tarski(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_4') | ~v1_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_422, c_81527])).
% 52.77/40.82  tff(c_81540, plain, (~r1_tarski(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_25714, c_81534])).
% 52.77/40.82  tff(c_81543, plain, (~m1_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_705, c_81540])).
% 52.77/40.82  tff(c_81547, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_81543])).
% 52.77/40.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 52.77/40.82  
% 52.77/40.82  Inference rules
% 52.77/40.82  ----------------------
% 52.77/40.82  #Ref     : 0
% 52.77/40.82  #Sup     : 20834
% 52.77/40.82  #Fact    : 0
% 52.77/40.82  #Define  : 0
% 52.77/40.82  #Split   : 12
% 52.77/40.82  #Chain   : 0
% 52.77/40.82  #Close   : 0
% 52.77/40.82  
% 52.77/40.82  Ordering : KBO
% 52.77/40.82  
% 52.77/40.82  Simplification rules
% 52.77/40.82  ----------------------
% 52.77/40.82  #Subsume      : 2731
% 52.77/40.82  #Demod        : 1027
% 52.77/40.82  #Tautology    : 108
% 52.77/40.82  #SimpNegUnit  : 5
% 52.77/40.82  #BackRed      : 2
% 52.77/40.82  
% 52.77/40.82  #Partial instantiations: 0
% 52.77/40.82  #Strategies tried      : 1
% 52.77/40.82  
% 52.77/40.82  Timing (in seconds)
% 52.77/40.82  ----------------------
% 52.77/40.82  Preprocessing        : 0.35
% 52.77/40.82  Parsing              : 0.19
% 52.77/40.82  CNF conversion       : 0.03
% 52.77/40.82  Main loop            : 39.69
% 52.77/40.82  Inferencing          : 3.15
% 52.77/40.82  Reduction            : 4.78
% 52.77/40.82  Demodulation         : 3.44
% 52.77/40.82  BG Simplification    : 0.43
% 52.77/40.82  Subsumption          : 29.61
% 52.77/40.82  Abstraction          : 0.72
% 52.77/40.82  MUC search           : 0.00
% 52.77/40.82  Cooper               : 0.00
% 52.77/40.82  Total                : 40.08
% 52.77/40.82  Index Insertion      : 0.00
% 52.77/40.82  Index Deletion       : 0.00
% 52.77/40.82  Index Matching       : 0.00
% 52.77/40.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
