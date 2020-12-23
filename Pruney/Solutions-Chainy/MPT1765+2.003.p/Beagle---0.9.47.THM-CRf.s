%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:15 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 305 expanded)
%              Number of leaves         :   45 ( 136 expanded)
%              Depth                    :   13
%              Number of atoms          :  196 (1893 expanded)
%              Number of equality atoms :   38 ( 171 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k8_relset_1 > k2_partfun1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_161,negated_conjecture,(
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
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                       => ( m1_pre_topc(C,D)
                         => ! [F] :
                              ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(B)))
                             => ( r1_tarski(k8_relset_1(u1_struct_0(D),u1_struct_0(B),E,F),u1_struct_0(C))
                               => k8_relset_1(u1_struct_0(D),u1_struct_0(B),E,F) = k8_relset_1(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,E),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tmap_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

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

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v5_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc22_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_117,plain,(
    ! [C_133,B_134,A_135] :
      ( v5_relat_1(C_133,B_134)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_135,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_121,plain,(
    v5_relat_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_117])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_64,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_62,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_48,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_40,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_52,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_58,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_56,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_44,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_323,plain,(
    ! [A_163,B_164,C_165,D_166] :
      ( k2_partfun1(A_163,B_164,C_165,D_166) = k7_relat_1(C_165,D_166)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164)))
      | ~ v1_funct_1(C_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_325,plain,(
    ! [D_166] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_166) = k7_relat_1('#skF_5',D_166)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_42,c_323])).

tff(c_328,plain,(
    ! [D_166] : k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_166) = k7_relat_1('#skF_5',D_166) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_325])).

tff(c_432,plain,(
    ! [B_183,A_182,C_184,E_186,D_185] :
      ( k3_tmap_1(A_182,B_183,C_184,D_185,E_186) = k2_partfun1(u1_struct_0(C_184),u1_struct_0(B_183),E_186,u1_struct_0(D_185))
      | ~ m1_pre_topc(D_185,C_184)
      | ~ m1_subset_1(E_186,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_184),u1_struct_0(B_183))))
      | ~ v1_funct_2(E_186,u1_struct_0(C_184),u1_struct_0(B_183))
      | ~ v1_funct_1(E_186)
      | ~ m1_pre_topc(D_185,A_182)
      | ~ m1_pre_topc(C_184,A_182)
      | ~ l1_pre_topc(B_183)
      | ~ v2_pre_topc(B_183)
      | v2_struct_0(B_183)
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182)
      | v2_struct_0(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_437,plain,(
    ! [A_182,D_185] :
      ( k3_tmap_1(A_182,'#skF_2','#skF_4',D_185,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_185))
      | ~ m1_pre_topc(D_185,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_185,A_182)
      | ~ m1_pre_topc('#skF_4',A_182)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182)
      | v2_struct_0(A_182) ) ),
    inference(resolution,[status(thm)],[c_42,c_432])).

tff(c_441,plain,(
    ! [D_185,A_182] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_185)) = k3_tmap_1(A_182,'#skF_2','#skF_4',D_185,'#skF_5')
      | ~ m1_pre_topc(D_185,'#skF_4')
      | ~ m1_pre_topc(D_185,A_182)
      | ~ m1_pre_topc('#skF_4',A_182)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182)
      | v2_struct_0(A_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_46,c_44,c_328,c_437])).

tff(c_468,plain,(
    ! [D_194,A_195] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_194)) = k3_tmap_1(A_195,'#skF_2','#skF_4',D_194,'#skF_5')
      | ~ m1_pre_topc(D_194,'#skF_4')
      | ~ m1_pre_topc(D_194,A_195)
      | ~ m1_pre_topc('#skF_4',A_195)
      | ~ l1_pre_topc(A_195)
      | ~ v2_pre_topc(A_195)
      | v2_struct_0(A_195) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_441])).

tff(c_470,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_468])).

tff(c_477,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_48,c_40,c_470])).

tff(c_478,plain,(
    k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_477])).

tff(c_112,plain,(
    ! [C_130,A_131,B_132] :
      ( v1_relat_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_116,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_112])).

tff(c_192,plain,(
    ! [A_150,C_151,B_152] :
      ( k3_xboole_0(A_150,k10_relat_1(C_151,B_152)) = k10_relat_1(k7_relat_1(C_151,A_150),B_152)
      | ~ v1_relat_1(C_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_202,plain,(
    ! [C_151,B_152,A_150] :
      ( k3_xboole_0(k10_relat_1(C_151,B_152),A_150) = k10_relat_1(k7_relat_1(C_151,A_150),B_152)
      | ~ v1_relat_1(C_151) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_2])).

tff(c_303,plain,(
    ! [A_158,B_159,C_160,D_161] :
      ( k8_relset_1(A_158,B_159,C_160,D_161) = k10_relat_1(C_160,D_161)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_306,plain,(
    ! [D_161] : k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_161) = k10_relat_1('#skF_5',D_161) ),
    inference(resolution,[status(thm)],[c_42,c_303])).

tff(c_36,plain,(
    r1_tarski(k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_111,plain,(
    k3_xboole_0(k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6'),u1_struct_0('#skF_3')) = k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_4])).

tff(c_307,plain,(
    k3_xboole_0(k10_relat_1('#skF_5','#skF_6'),u1_struct_0('#skF_3')) = k10_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_306,c_111])).

tff(c_342,plain,
    ( k10_relat_1(k7_relat_1('#skF_5',u1_struct_0('#skF_3')),'#skF_6') = k10_relat_1('#skF_5','#skF_6')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_307])).

tff(c_354,plain,(
    k10_relat_1(k7_relat_1('#skF_5',u1_struct_0('#skF_3')),'#skF_6') = k10_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_342])).

tff(c_487,plain,(
    k10_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') = k10_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_354])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k7_relat_1(A_7,B_8))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_505,plain,
    ( v1_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_478,c_10])).

tff(c_518,plain,(
    v1_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_505])).

tff(c_16,plain,(
    ! [C_16,A_14,B_15] :
      ( v5_relat_1(k7_relat_1(C_16,A_14),B_15)
      | ~ v5_relat_1(C_16,B_15)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_10,A_9)),A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_tarski(k2_relat_1(B_6),A_5)
      | ~ v5_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_384,plain,(
    ! [C_167,A_168,B_169] :
      ( m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169)))
      | ~ r1_tarski(k2_relat_1(C_167),B_169)
      | ~ r1_tarski(k1_relat_1(C_167),A_168)
      | ~ v1_relat_1(C_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_26,plain,(
    ! [A_23,B_24,C_25,D_26] :
      ( k8_relset_1(A_23,B_24,C_25,D_26) = k10_relat_1(C_25,D_26)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_555,plain,(
    ! [A_197,B_198,C_199,D_200] :
      ( k8_relset_1(A_197,B_198,C_199,D_200) = k10_relat_1(C_199,D_200)
      | ~ r1_tarski(k2_relat_1(C_199),B_198)
      | ~ r1_tarski(k1_relat_1(C_199),A_197)
      | ~ v1_relat_1(C_199) ) ),
    inference(resolution,[status(thm)],[c_384,c_26])).

tff(c_623,plain,(
    ! [A_203,A_204,B_205,D_206] :
      ( k8_relset_1(A_203,A_204,B_205,D_206) = k10_relat_1(B_205,D_206)
      | ~ r1_tarski(k1_relat_1(B_205),A_203)
      | ~ v5_relat_1(B_205,A_204)
      | ~ v1_relat_1(B_205) ) ),
    inference(resolution,[status(thm)],[c_8,c_555])).

tff(c_1020,plain,(
    ! [A_245,A_246,B_247,D_248] :
      ( k8_relset_1(A_245,A_246,k7_relat_1(B_247,A_245),D_248) = k10_relat_1(k7_relat_1(B_247,A_245),D_248)
      | ~ v5_relat_1(k7_relat_1(B_247,A_245),A_246)
      | ~ v1_relat_1(k7_relat_1(B_247,A_245))
      | ~ v1_relat_1(B_247) ) ),
    inference(resolution,[status(thm)],[c_12,c_623])).

tff(c_1028,plain,(
    ! [A_249,B_250,C_251,D_252] :
      ( k8_relset_1(A_249,B_250,k7_relat_1(C_251,A_249),D_252) = k10_relat_1(k7_relat_1(C_251,A_249),D_252)
      | ~ v1_relat_1(k7_relat_1(C_251,A_249))
      | ~ v5_relat_1(C_251,B_250)
      | ~ v1_relat_1(C_251) ) ),
    inference(resolution,[status(thm)],[c_16,c_1020])).

tff(c_1030,plain,(
    ! [B_250,D_252] :
      ( k8_relset_1(u1_struct_0('#skF_3'),B_250,k7_relat_1('#skF_5',u1_struct_0('#skF_3')),D_252) = k10_relat_1(k7_relat_1('#skF_5',u1_struct_0('#skF_3')),D_252)
      | ~ v1_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'))
      | ~ v5_relat_1('#skF_5',B_250)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_478,c_1028])).

tff(c_1050,plain,(
    ! [B_257,D_258] :
      ( k8_relset_1(u1_struct_0('#skF_3'),B_257,k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),D_258) = k10_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),D_258)
      | ~ v5_relat_1('#skF_5',B_257) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_518,c_478,c_478,c_1030])).

tff(c_34,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_308,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k10_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_34])).

tff(c_1056,plain,
    ( k10_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k10_relat_1('#skF_5','#skF_6')
    | ~ v5_relat_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1050,c_308])).

tff(c_1063,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_487,c_1056])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:25:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.59/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.60  
% 3.59/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.61  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k8_relset_1 > k2_partfun1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.59/1.61  
% 3.59/1.61  %Foreground sorts:
% 3.59/1.61  
% 3.59/1.61  
% 3.59/1.61  %Background operators:
% 3.59/1.61  
% 3.59/1.61  
% 3.59/1.61  %Foreground operators:
% 3.59/1.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.59/1.61  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.59/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.59/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.59/1.61  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.59/1.61  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.59/1.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.59/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.59/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.59/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.59/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.59/1.61  tff('#skF_6', type, '#skF_6': $i).
% 3.59/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.59/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.59/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.59/1.61  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.59/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.59/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.59/1.61  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.59/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.59/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.59/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.59/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.59/1.61  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.59/1.61  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.59/1.61  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.59/1.61  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.59/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.59/1.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.59/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.59/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.59/1.61  
% 3.59/1.62  tff(f_161, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(B))) => (r1_tarski(k8_relset_1(u1_struct_0(D), u1_struct_0(B), E, F), u1_struct_0(C)) => (k8_relset_1(u1_struct_0(D), u1_struct_0(B), E, F) = k8_relset_1(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, E), F)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tmap_1)).
% 3.59/1.62  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.59/1.62  tff(f_85, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.59/1.62  tff(f_117, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 3.59/1.62  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.59/1.62  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 3.59/1.62  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.59/1.62  tff(f_71, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.59/1.62  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.59/1.62  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.59/1.62  tff(f_57, axiom, (![A, B, C]: ((v1_relat_1(C) & v5_relat_1(C, B)) => (v1_relat_1(k7_relat_1(C, A)) & v5_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc22_relat_1)).
% 3.59/1.62  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 3.59/1.62  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.59/1.62  tff(f_79, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 3.59/1.62  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.59/1.62  tff(c_117, plain, (![C_133, B_134, A_135]: (v5_relat_1(C_133, B_134) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_135, B_134))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.59/1.62  tff(c_121, plain, (v5_relat_1('#skF_5', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_117])).
% 3.59/1.62  tff(c_66, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.59/1.62  tff(c_64, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.59/1.62  tff(c_62, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.59/1.62  tff(c_48, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.59/1.62  tff(c_40, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.59/1.62  tff(c_52, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.59/1.62  tff(c_60, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.59/1.62  tff(c_58, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.59/1.62  tff(c_56, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.59/1.62  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.59/1.62  tff(c_44, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.59/1.62  tff(c_323, plain, (![A_163, B_164, C_165, D_166]: (k2_partfun1(A_163, B_164, C_165, D_166)=k7_relat_1(C_165, D_166) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_163, B_164))) | ~v1_funct_1(C_165))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.59/1.62  tff(c_325, plain, (![D_166]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_166)=k7_relat_1('#skF_5', D_166) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_42, c_323])).
% 3.59/1.62  tff(c_328, plain, (![D_166]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_166)=k7_relat_1('#skF_5', D_166))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_325])).
% 3.59/1.62  tff(c_432, plain, (![B_183, A_182, C_184, E_186, D_185]: (k3_tmap_1(A_182, B_183, C_184, D_185, E_186)=k2_partfun1(u1_struct_0(C_184), u1_struct_0(B_183), E_186, u1_struct_0(D_185)) | ~m1_pre_topc(D_185, C_184) | ~m1_subset_1(E_186, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_184), u1_struct_0(B_183)))) | ~v1_funct_2(E_186, u1_struct_0(C_184), u1_struct_0(B_183)) | ~v1_funct_1(E_186) | ~m1_pre_topc(D_185, A_182) | ~m1_pre_topc(C_184, A_182) | ~l1_pre_topc(B_183) | ~v2_pre_topc(B_183) | v2_struct_0(B_183) | ~l1_pre_topc(A_182) | ~v2_pre_topc(A_182) | v2_struct_0(A_182))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.59/1.62  tff(c_437, plain, (![A_182, D_185]: (k3_tmap_1(A_182, '#skF_2', '#skF_4', D_185, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_185)) | ~m1_pre_topc(D_185, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_185, A_182) | ~m1_pre_topc('#skF_4', A_182) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_182) | ~v2_pre_topc(A_182) | v2_struct_0(A_182))), inference(resolution, [status(thm)], [c_42, c_432])).
% 3.59/1.62  tff(c_441, plain, (![D_185, A_182]: (k7_relat_1('#skF_5', u1_struct_0(D_185))=k3_tmap_1(A_182, '#skF_2', '#skF_4', D_185, '#skF_5') | ~m1_pre_topc(D_185, '#skF_4') | ~m1_pre_topc(D_185, A_182) | ~m1_pre_topc('#skF_4', A_182) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_182) | ~v2_pre_topc(A_182) | v2_struct_0(A_182))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_46, c_44, c_328, c_437])).
% 3.59/1.62  tff(c_468, plain, (![D_194, A_195]: (k7_relat_1('#skF_5', u1_struct_0(D_194))=k3_tmap_1(A_195, '#skF_2', '#skF_4', D_194, '#skF_5') | ~m1_pre_topc(D_194, '#skF_4') | ~m1_pre_topc(D_194, A_195) | ~m1_pre_topc('#skF_4', A_195) | ~l1_pre_topc(A_195) | ~v2_pre_topc(A_195) | v2_struct_0(A_195))), inference(negUnitSimplification, [status(thm)], [c_60, c_441])).
% 3.59/1.62  tff(c_470, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_468])).
% 3.59/1.62  tff(c_477, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_48, c_40, c_470])).
% 3.59/1.62  tff(c_478, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_66, c_477])).
% 3.59/1.62  tff(c_112, plain, (![C_130, A_131, B_132]: (v1_relat_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.59/1.62  tff(c_116, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_112])).
% 3.59/1.62  tff(c_192, plain, (![A_150, C_151, B_152]: (k3_xboole_0(A_150, k10_relat_1(C_151, B_152))=k10_relat_1(k7_relat_1(C_151, A_150), B_152) | ~v1_relat_1(C_151))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.59/1.62  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.59/1.62  tff(c_202, plain, (![C_151, B_152, A_150]: (k3_xboole_0(k10_relat_1(C_151, B_152), A_150)=k10_relat_1(k7_relat_1(C_151, A_150), B_152) | ~v1_relat_1(C_151))), inference(superposition, [status(thm), theory('equality')], [c_192, c_2])).
% 3.59/1.62  tff(c_303, plain, (![A_158, B_159, C_160, D_161]: (k8_relset_1(A_158, B_159, C_160, D_161)=k10_relat_1(C_160, D_161) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.59/1.62  tff(c_306, plain, (![D_161]: (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_161)=k10_relat_1('#skF_5', D_161))), inference(resolution, [status(thm)], [c_42, c_303])).
% 3.59/1.62  tff(c_36, plain, (r1_tarski(k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.59/1.62  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.59/1.62  tff(c_111, plain, (k3_xboole_0(k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6'), u1_struct_0('#skF_3'))=k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_36, c_4])).
% 3.59/1.62  tff(c_307, plain, (k3_xboole_0(k10_relat_1('#skF_5', '#skF_6'), u1_struct_0('#skF_3'))=k10_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_306, c_306, c_111])).
% 3.59/1.62  tff(c_342, plain, (k10_relat_1(k7_relat_1('#skF_5', u1_struct_0('#skF_3')), '#skF_6')=k10_relat_1('#skF_5', '#skF_6') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_202, c_307])).
% 3.59/1.62  tff(c_354, plain, (k10_relat_1(k7_relat_1('#skF_5', u1_struct_0('#skF_3')), '#skF_6')=k10_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_342])).
% 3.59/1.62  tff(c_487, plain, (k10_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')=k10_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_478, c_354])).
% 3.59/1.62  tff(c_10, plain, (![A_7, B_8]: (v1_relat_1(k7_relat_1(A_7, B_8)) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.59/1.62  tff(c_505, plain, (v1_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')) | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_478, c_10])).
% 3.59/1.62  tff(c_518, plain, (v1_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_505])).
% 3.59/1.62  tff(c_16, plain, (![C_16, A_14, B_15]: (v5_relat_1(k7_relat_1(C_16, A_14), B_15) | ~v5_relat_1(C_16, B_15) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.59/1.62  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(k7_relat_1(B_10, A_9)), A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.59/1.62  tff(c_8, plain, (![B_6, A_5]: (r1_tarski(k2_relat_1(B_6), A_5) | ~v5_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.59/1.62  tff(c_384, plain, (![C_167, A_168, B_169]: (m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))) | ~r1_tarski(k2_relat_1(C_167), B_169) | ~r1_tarski(k1_relat_1(C_167), A_168) | ~v1_relat_1(C_167))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.59/1.62  tff(c_26, plain, (![A_23, B_24, C_25, D_26]: (k8_relset_1(A_23, B_24, C_25, D_26)=k10_relat_1(C_25, D_26) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.59/1.62  tff(c_555, plain, (![A_197, B_198, C_199, D_200]: (k8_relset_1(A_197, B_198, C_199, D_200)=k10_relat_1(C_199, D_200) | ~r1_tarski(k2_relat_1(C_199), B_198) | ~r1_tarski(k1_relat_1(C_199), A_197) | ~v1_relat_1(C_199))), inference(resolution, [status(thm)], [c_384, c_26])).
% 3.59/1.62  tff(c_623, plain, (![A_203, A_204, B_205, D_206]: (k8_relset_1(A_203, A_204, B_205, D_206)=k10_relat_1(B_205, D_206) | ~r1_tarski(k1_relat_1(B_205), A_203) | ~v5_relat_1(B_205, A_204) | ~v1_relat_1(B_205))), inference(resolution, [status(thm)], [c_8, c_555])).
% 3.59/1.62  tff(c_1020, plain, (![A_245, A_246, B_247, D_248]: (k8_relset_1(A_245, A_246, k7_relat_1(B_247, A_245), D_248)=k10_relat_1(k7_relat_1(B_247, A_245), D_248) | ~v5_relat_1(k7_relat_1(B_247, A_245), A_246) | ~v1_relat_1(k7_relat_1(B_247, A_245)) | ~v1_relat_1(B_247))), inference(resolution, [status(thm)], [c_12, c_623])).
% 3.59/1.62  tff(c_1028, plain, (![A_249, B_250, C_251, D_252]: (k8_relset_1(A_249, B_250, k7_relat_1(C_251, A_249), D_252)=k10_relat_1(k7_relat_1(C_251, A_249), D_252) | ~v1_relat_1(k7_relat_1(C_251, A_249)) | ~v5_relat_1(C_251, B_250) | ~v1_relat_1(C_251))), inference(resolution, [status(thm)], [c_16, c_1020])).
% 3.59/1.62  tff(c_1030, plain, (![B_250, D_252]: (k8_relset_1(u1_struct_0('#skF_3'), B_250, k7_relat_1('#skF_5', u1_struct_0('#skF_3')), D_252)=k10_relat_1(k7_relat_1('#skF_5', u1_struct_0('#skF_3')), D_252) | ~v1_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')) | ~v5_relat_1('#skF_5', B_250) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_478, c_1028])).
% 3.59/1.62  tff(c_1050, plain, (![B_257, D_258]: (k8_relset_1(u1_struct_0('#skF_3'), B_257, k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), D_258)=k10_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), D_258) | ~v5_relat_1('#skF_5', B_257))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_518, c_478, c_478, c_1030])).
% 3.59/1.62  tff(c_34, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.59/1.62  tff(c_308, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k10_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_306, c_34])).
% 3.59/1.62  tff(c_1056, plain, (k10_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k10_relat_1('#skF_5', '#skF_6') | ~v5_relat_1('#skF_5', u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1050, c_308])).
% 3.59/1.62  tff(c_1063, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121, c_487, c_1056])).
% 3.59/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.62  
% 3.59/1.62  Inference rules
% 3.59/1.62  ----------------------
% 3.59/1.62  #Ref     : 0
% 3.59/1.62  #Sup     : 231
% 3.59/1.62  #Fact    : 0
% 3.59/1.62  #Define  : 0
% 3.59/1.62  #Split   : 2
% 3.59/1.62  #Chain   : 0
% 3.59/1.62  #Close   : 0
% 3.59/1.62  
% 3.59/1.62  Ordering : KBO
% 3.59/1.62  
% 3.59/1.62  Simplification rules
% 3.59/1.62  ----------------------
% 3.59/1.62  #Subsume      : 53
% 3.59/1.62  #Demod        : 186
% 3.59/1.62  #Tautology    : 84
% 3.59/1.62  #SimpNegUnit  : 14
% 3.59/1.62  #BackRed      : 5
% 3.59/1.62  
% 3.59/1.62  #Partial instantiations: 0
% 3.59/1.62  #Strategies tried      : 1
% 3.59/1.62  
% 3.59/1.62  Timing (in seconds)
% 3.59/1.62  ----------------------
% 3.59/1.63  Preprocessing        : 0.37
% 3.59/1.63  Parsing              : 0.19
% 3.59/1.63  CNF conversion       : 0.04
% 3.59/1.63  Main loop            : 0.48
% 3.59/1.63  Inferencing          : 0.18
% 3.59/1.63  Reduction            : 0.17
% 3.59/1.63  Demodulation         : 0.12
% 3.59/1.63  BG Simplification    : 0.03
% 3.59/1.63  Subsumption          : 0.08
% 3.59/1.63  Abstraction          : 0.03
% 3.59/1.63  MUC search           : 0.00
% 3.59/1.63  Cooper               : 0.00
% 3.59/1.63  Total                : 0.89
% 3.59/1.63  Index Insertion      : 0.00
% 3.59/1.63  Index Deletion       : 0.00
% 3.59/1.63  Index Matching       : 0.00
% 3.59/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
