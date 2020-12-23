%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:00 EST 2020

% Result     : Theorem 9.01s
% Output     : CNFRefutation 9.19s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 202 expanded)
%              Number of leaves         :   45 (  90 expanded)
%              Depth                    :   15
%              Number of atoms          :  193 ( 649 expanded)
%              Number of equality atoms :   38 ( 102 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

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
                      & v1_funct_2(D,u1_struct_0(A),u1_struct_0(B))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                       => ( r1_tarski(k8_relset_1(u1_struct_0(A),u1_struct_0(B),D,E),u1_struct_0(C))
                         => k8_relset_1(u1_struct_0(A),u1_struct_0(B),D,E) = k8_relset_1(u1_struct_0(C),u1_struct_0(B),k2_tmap_1(A,B,D,C),E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tmap_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_114,axiom,(
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

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_126,plain,(
    ! [C_95,B_96,A_97] :
      ( v5_relat_1(C_95,B_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_97,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_130,plain,(
    v5_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_126])).

tff(c_20,plain,(
    ! [C_21,A_19,B_20] :
      ( v1_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_100,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_20])).

tff(c_18,plain,(
    ! [A_16,C_18,B_17] :
      ( k3_xboole_0(A_16,k10_relat_1(C_18,B_17)) = k10_relat_1(k7_relat_1(C_18,A_16),B_17)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_250,plain,(
    ! [A_113,B_114,C_115,D_116] :
      ( k8_relset_1(A_113,B_114,C_115,D_116) = k10_relat_1(C_115,D_116)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_253,plain,(
    ! [D_116] : k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',D_116) = k10_relat_1('#skF_4',D_116) ),
    inference(resolution,[status(thm)],[c_40,c_250])).

tff(c_36,plain,(
    r1_tarski(k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_255,plain,(
    r1_tarski(k10_relat_1('#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_36])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_271,plain,(
    k3_xboole_0(k10_relat_1('#skF_4','#skF_5'),u1_struct_0('#skF_3')) = k10_relat_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_255,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_287,plain,(
    k3_xboole_0(u1_struct_0('#skF_3'),k10_relat_1('#skF_4','#skF_5')) = k10_relat_1('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_2])).

tff(c_307,plain,
    ( k10_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') = k10_relat_1('#skF_4','#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_287])).

tff(c_313,plain,(
    k10_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') = k10_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_307])).

tff(c_46,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_58,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_56,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_44,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_42,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_317,plain,(
    ! [A_119,B_120,C_121,D_122] :
      ( k2_partfun1(A_119,B_120,C_121,D_122) = k7_relat_1(C_121,D_122)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120)))
      | ~ v1_funct_1(C_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_319,plain,(
    ! [D_122] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',D_122) = k7_relat_1('#skF_4',D_122)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_317])).

tff(c_322,plain,(
    ! [D_122] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',D_122) = k7_relat_1('#skF_4',D_122) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_319])).

tff(c_543,plain,(
    ! [A_148,B_149,C_150,D_151] :
      ( k2_partfun1(u1_struct_0(A_148),u1_struct_0(B_149),C_150,u1_struct_0(D_151)) = k2_tmap_1(A_148,B_149,C_150,D_151)
      | ~ m1_pre_topc(D_151,A_148)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_148),u1_struct_0(B_149))))
      | ~ v1_funct_2(C_150,u1_struct_0(A_148),u1_struct_0(B_149))
      | ~ v1_funct_1(C_150)
      | ~ l1_pre_topc(B_149)
      | ~ v2_pre_topc(B_149)
      | v2_struct_0(B_149)
      | ~ l1_pre_topc(A_148)
      | ~ v2_pre_topc(A_148)
      | v2_struct_0(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_548,plain,(
    ! [D_151] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_151)) = k2_tmap_1('#skF_1','#skF_2','#skF_4',D_151)
      | ~ m1_pre_topc(D_151,'#skF_1')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_543])).

tff(c_552,plain,(
    ! [D_151] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_151)) = k2_tmap_1('#skF_1','#skF_2','#skF_4',D_151)
      | ~ m1_pre_topc(D_151,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_44,c_42,c_322,c_548])).

tff(c_553,plain,(
    ! [D_151] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_151)) = k2_tmap_1('#skF_1','#skF_2','#skF_4',D_151)
      | ~ m1_pre_topc(D_151,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_552])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( v1_relat_1(k7_relat_1(A_10,B_11))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_219,plain,(
    ! [A_110,C_111,B_112] :
      ( k3_xboole_0(A_110,k10_relat_1(C_111,B_112)) = k10_relat_1(k7_relat_1(C_111,A_110),B_112)
      | ~ v1_relat_1(C_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_349,plain,(
    ! [C_125,B_126,A_127] :
      ( k3_xboole_0(k10_relat_1(C_125,B_126),A_127) = k10_relat_1(k7_relat_1(C_125,A_127),B_126)
      | ~ v1_relat_1(C_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_2])).

tff(c_375,plain,(
    ! [A_127] :
      ( k10_relat_1(k7_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),A_127),'#skF_5') = k3_xboole_0(k10_relat_1('#skF_4','#skF_5'),A_127)
      | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_349])).

tff(c_3260,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_375])).

tff(c_3266,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_3260])).

tff(c_3272,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_3266])).

tff(c_3274,plain,(
    v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_375])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_15,A_14)),k2_relat_1(B_15))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v5_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_141,plain,(
    ! [A_100,C_101,B_102] :
      ( r1_tarski(A_100,C_101)
      | ~ r1_tarski(B_102,C_101)
      | ~ r1_tarski(A_100,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_436,plain,(
    ! [A_134,A_135,B_136] :
      ( r1_tarski(A_134,A_135)
      | ~ r1_tarski(A_134,k2_relat_1(B_136))
      | ~ v5_relat_1(B_136,A_135)
      | ~ v1_relat_1(B_136) ) ),
    inference(resolution,[status(thm)],[c_10,c_141])).

tff(c_448,plain,(
    ! [B_137,A_138,A_139] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_137,A_138)),A_139)
      | ~ v5_relat_1(B_137,A_139)
      | ~ v1_relat_1(B_137) ) ),
    inference(resolution,[status(thm)],[c_16,c_436])).

tff(c_8,plain,(
    ! [B_9,A_8] :
      ( v5_relat_1(B_9,A_8)
      | ~ r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_477,plain,(
    ! [B_137,A_138,A_139] :
      ( v5_relat_1(k7_relat_1(B_137,A_138),A_139)
      | ~ v1_relat_1(k7_relat_1(B_137,A_138))
      | ~ v5_relat_1(B_137,A_139)
      | ~ v1_relat_1(B_137) ) ),
    inference(resolution,[status(thm)],[c_448,c_8])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_13,A_12)),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_417,plain,(
    ! [C_131,A_132,B_133] :
      ( m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133)))
      | ~ r1_tarski(k2_relat_1(C_131),B_133)
      | ~ r1_tarski(k1_relat_1(C_131),A_132)
      | ~ v1_relat_1(C_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_26,plain,(
    ! [A_25,B_26,C_27,D_28] :
      ( k8_relset_1(A_25,B_26,C_27,D_28) = k10_relat_1(C_27,D_28)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_743,plain,(
    ! [A_168,B_169,C_170,D_171] :
      ( k8_relset_1(A_168,B_169,C_170,D_171) = k10_relat_1(C_170,D_171)
      | ~ r1_tarski(k2_relat_1(C_170),B_169)
      | ~ r1_tarski(k1_relat_1(C_170),A_168)
      | ~ v1_relat_1(C_170) ) ),
    inference(resolution,[status(thm)],[c_417,c_26])).

tff(c_1651,plain,(
    ! [A_246,A_247,B_248,D_249] :
      ( k8_relset_1(A_246,A_247,B_248,D_249) = k10_relat_1(B_248,D_249)
      | ~ r1_tarski(k1_relat_1(B_248),A_246)
      | ~ v5_relat_1(B_248,A_247)
      | ~ v1_relat_1(B_248) ) ),
    inference(resolution,[status(thm)],[c_10,c_743])).

tff(c_7268,plain,(
    ! [A_652,A_653,B_654,D_655] :
      ( k8_relset_1(A_652,A_653,k7_relat_1(B_654,A_652),D_655) = k10_relat_1(k7_relat_1(B_654,A_652),D_655)
      | ~ v5_relat_1(k7_relat_1(B_654,A_652),A_653)
      | ~ v1_relat_1(k7_relat_1(B_654,A_652))
      | ~ v1_relat_1(B_654) ) ),
    inference(resolution,[status(thm)],[c_14,c_1651])).

tff(c_7298,plain,(
    ! [A_656,A_657,B_658,D_659] :
      ( k8_relset_1(A_656,A_657,k7_relat_1(B_658,A_656),D_659) = k10_relat_1(k7_relat_1(B_658,A_656),D_659)
      | ~ v1_relat_1(k7_relat_1(B_658,A_656))
      | ~ v5_relat_1(B_658,A_657)
      | ~ v1_relat_1(B_658) ) ),
    inference(resolution,[status(thm)],[c_477,c_7268])).

tff(c_7300,plain,(
    ! [A_657,D_659] :
      ( k8_relset_1(u1_struct_0('#skF_3'),A_657,k7_relat_1('#skF_4',u1_struct_0('#skF_3')),D_659) = k10_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),D_659)
      | ~ v5_relat_1('#skF_4',A_657)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3274,c_7298])).

tff(c_7334,plain,(
    ! [A_664,D_665] :
      ( k8_relset_1(u1_struct_0('#skF_3'),A_664,k7_relat_1('#skF_4',u1_struct_0('#skF_3')),D_665) = k10_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),D_665)
      | ~ v5_relat_1('#skF_4',A_664) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_7300])).

tff(c_7358,plain,(
    ! [A_664,D_665] :
      ( k8_relset_1(u1_struct_0('#skF_3'),A_664,k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),D_665) = k10_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),D_665)
      | ~ v5_relat_1('#skF_4',A_664)
      | ~ m1_pre_topc('#skF_3','#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_7334])).

tff(c_7395,plain,(
    ! [A_669,D_670] :
      ( k8_relset_1(u1_struct_0('#skF_3'),A_669,k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),D_670) = k10_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),D_670)
      | ~ v5_relat_1('#skF_4',A_669) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_7358])).

tff(c_34,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_5') != k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_254,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_5') != k10_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_34])).

tff(c_7401,plain,
    ( k10_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k10_relat_1('#skF_4','#skF_5')
    | ~ v5_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7395,c_254])).

tff(c_7408,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_313,c_7401])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:36:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.01/3.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.01/3.16  
% 9.01/3.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.01/3.16  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.01/3.16  
% 9.01/3.16  %Foreground sorts:
% 9.01/3.16  
% 9.01/3.16  
% 9.01/3.16  %Background operators:
% 9.01/3.16  
% 9.01/3.16  
% 9.01/3.16  %Foreground operators:
% 9.01/3.16  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.01/3.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.01/3.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.01/3.16  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.01/3.16  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 9.01/3.16  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.01/3.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.01/3.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.01/3.16  tff('#skF_5', type, '#skF_5': $i).
% 9.01/3.16  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.01/3.16  tff('#skF_2', type, '#skF_2': $i).
% 9.01/3.16  tff('#skF_3', type, '#skF_3': $i).
% 9.01/3.16  tff('#skF_1', type, '#skF_1': $i).
% 9.01/3.16  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.01/3.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.01/3.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.01/3.16  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 9.01/3.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.01/3.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.01/3.16  tff('#skF_4', type, '#skF_4': $i).
% 9.01/3.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.01/3.16  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 9.01/3.16  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 9.01/3.16  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.01/3.16  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.01/3.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.01/3.16  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 9.01/3.16  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.01/3.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.01/3.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.01/3.16  
% 9.19/3.18  tff(f_150, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (r1_tarski(k8_relset_1(u1_struct_0(A), u1_struct_0(B), D, E), u1_struct_0(C)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), D, E) = k8_relset_1(u1_struct_0(C), u1_struct_0(B), k2_tmap_1(A, B, D, C), E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tmap_1)).
% 9.19/3.18  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.19/3.18  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.19/3.18  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 9.19/3.18  tff(f_73, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 9.19/3.18  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.19/3.18  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.19/3.18  tff(f_87, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 9.19/3.18  tff(f_114, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 9.19/3.18  tff(f_47, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 9.19/3.18  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_relat_1)).
% 9.19/3.18  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 9.19/3.18  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 9.19/3.18  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 9.19/3.18  tff(f_81, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 9.19/3.18  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_150])).
% 9.19/3.18  tff(c_126, plain, (![C_95, B_96, A_97]: (v5_relat_1(C_95, B_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_97, B_96))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.19/3.18  tff(c_130, plain, (v5_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_126])).
% 9.19/3.18  tff(c_20, plain, (![C_21, A_19, B_20]: (v1_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.19/3.18  tff(c_100, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_20])).
% 9.19/3.18  tff(c_18, plain, (![A_16, C_18, B_17]: (k3_xboole_0(A_16, k10_relat_1(C_18, B_17))=k10_relat_1(k7_relat_1(C_18, A_16), B_17) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.19/3.18  tff(c_250, plain, (![A_113, B_114, C_115, D_116]: (k8_relset_1(A_113, B_114, C_115, D_116)=k10_relat_1(C_115, D_116) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.19/3.18  tff(c_253, plain, (![D_116]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', D_116)=k10_relat_1('#skF_4', D_116))), inference(resolution, [status(thm)], [c_40, c_250])).
% 9.19/3.18  tff(c_36, plain, (r1_tarski(k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 9.19/3.18  tff(c_255, plain, (r1_tarski(k10_relat_1('#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_253, c_36])).
% 9.19/3.18  tff(c_6, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.19/3.18  tff(c_271, plain, (k3_xboole_0(k10_relat_1('#skF_4', '#skF_5'), u1_struct_0('#skF_3'))=k10_relat_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_255, c_6])).
% 9.19/3.18  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.19/3.18  tff(c_287, plain, (k3_xboole_0(u1_struct_0('#skF_3'), k10_relat_1('#skF_4', '#skF_5'))=k10_relat_1('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_271, c_2])).
% 9.19/3.18  tff(c_307, plain, (k10_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')=k10_relat_1('#skF_4', '#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18, c_287])).
% 9.19/3.18  tff(c_313, plain, (k10_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')=k10_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_307])).
% 9.19/3.18  tff(c_46, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 9.19/3.18  tff(c_60, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 9.19/3.18  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 9.19/3.18  tff(c_58, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 9.19/3.18  tff(c_56, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 9.19/3.18  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 9.19/3.18  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 9.19/3.18  tff(c_44, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_150])).
% 9.19/3.18  tff(c_42, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 9.19/3.18  tff(c_317, plain, (![A_119, B_120, C_121, D_122]: (k2_partfun1(A_119, B_120, C_121, D_122)=k7_relat_1(C_121, D_122) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))) | ~v1_funct_1(C_121))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.19/3.18  tff(c_319, plain, (![D_122]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', D_122)=k7_relat_1('#skF_4', D_122) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_317])).
% 9.19/3.18  tff(c_322, plain, (![D_122]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', D_122)=k7_relat_1('#skF_4', D_122))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_319])).
% 9.19/3.18  tff(c_543, plain, (![A_148, B_149, C_150, D_151]: (k2_partfun1(u1_struct_0(A_148), u1_struct_0(B_149), C_150, u1_struct_0(D_151))=k2_tmap_1(A_148, B_149, C_150, D_151) | ~m1_pre_topc(D_151, A_148) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_148), u1_struct_0(B_149)))) | ~v1_funct_2(C_150, u1_struct_0(A_148), u1_struct_0(B_149)) | ~v1_funct_1(C_150) | ~l1_pre_topc(B_149) | ~v2_pre_topc(B_149) | v2_struct_0(B_149) | ~l1_pre_topc(A_148) | ~v2_pre_topc(A_148) | v2_struct_0(A_148))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.19/3.18  tff(c_548, plain, (![D_151]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_151))=k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_151) | ~m1_pre_topc(D_151, '#skF_1') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_543])).
% 9.19/3.18  tff(c_552, plain, (![D_151]: (k7_relat_1('#skF_4', u1_struct_0(D_151))=k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_151) | ~m1_pre_topc(D_151, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_44, c_42, c_322, c_548])).
% 9.19/3.18  tff(c_553, plain, (![D_151]: (k7_relat_1('#skF_4', u1_struct_0(D_151))=k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_151) | ~m1_pre_topc(D_151, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_552])).
% 9.19/3.18  tff(c_12, plain, (![A_10, B_11]: (v1_relat_1(k7_relat_1(A_10, B_11)) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.19/3.18  tff(c_219, plain, (![A_110, C_111, B_112]: (k3_xboole_0(A_110, k10_relat_1(C_111, B_112))=k10_relat_1(k7_relat_1(C_111, A_110), B_112) | ~v1_relat_1(C_111))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.19/3.18  tff(c_349, plain, (![C_125, B_126, A_127]: (k3_xboole_0(k10_relat_1(C_125, B_126), A_127)=k10_relat_1(k7_relat_1(C_125, A_127), B_126) | ~v1_relat_1(C_125))), inference(superposition, [status(thm), theory('equality')], [c_219, c_2])).
% 9.19/3.18  tff(c_375, plain, (![A_127]: (k10_relat_1(k7_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), A_127), '#skF_5')=k3_xboole_0(k10_relat_1('#skF_4', '#skF_5'), A_127) | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_313, c_349])).
% 9.19/3.18  tff(c_3260, plain, (~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_375])).
% 9.19/3.18  tff(c_3266, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_3260])).
% 9.19/3.18  tff(c_3272, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_3266])).
% 9.19/3.18  tff(c_3274, plain, (v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_375])).
% 9.19/3.18  tff(c_16, plain, (![B_15, A_14]: (r1_tarski(k2_relat_1(k7_relat_1(B_15, A_14)), k2_relat_1(B_15)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.19/3.18  tff(c_10, plain, (![B_9, A_8]: (r1_tarski(k2_relat_1(B_9), A_8) | ~v5_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.19/3.18  tff(c_141, plain, (![A_100, C_101, B_102]: (r1_tarski(A_100, C_101) | ~r1_tarski(B_102, C_101) | ~r1_tarski(A_100, B_102))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.19/3.18  tff(c_436, plain, (![A_134, A_135, B_136]: (r1_tarski(A_134, A_135) | ~r1_tarski(A_134, k2_relat_1(B_136)) | ~v5_relat_1(B_136, A_135) | ~v1_relat_1(B_136))), inference(resolution, [status(thm)], [c_10, c_141])).
% 9.19/3.18  tff(c_448, plain, (![B_137, A_138, A_139]: (r1_tarski(k2_relat_1(k7_relat_1(B_137, A_138)), A_139) | ~v5_relat_1(B_137, A_139) | ~v1_relat_1(B_137))), inference(resolution, [status(thm)], [c_16, c_436])).
% 9.19/3.18  tff(c_8, plain, (![B_9, A_8]: (v5_relat_1(B_9, A_8) | ~r1_tarski(k2_relat_1(B_9), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.19/3.18  tff(c_477, plain, (![B_137, A_138, A_139]: (v5_relat_1(k7_relat_1(B_137, A_138), A_139) | ~v1_relat_1(k7_relat_1(B_137, A_138)) | ~v5_relat_1(B_137, A_139) | ~v1_relat_1(B_137))), inference(resolution, [status(thm)], [c_448, c_8])).
% 9.19/3.18  tff(c_14, plain, (![B_13, A_12]: (r1_tarski(k1_relat_1(k7_relat_1(B_13, A_12)), A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.19/3.18  tff(c_417, plain, (![C_131, A_132, B_133]: (m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))) | ~r1_tarski(k2_relat_1(C_131), B_133) | ~r1_tarski(k1_relat_1(C_131), A_132) | ~v1_relat_1(C_131))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.19/3.18  tff(c_26, plain, (![A_25, B_26, C_27, D_28]: (k8_relset_1(A_25, B_26, C_27, D_28)=k10_relat_1(C_27, D_28) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.19/3.18  tff(c_743, plain, (![A_168, B_169, C_170, D_171]: (k8_relset_1(A_168, B_169, C_170, D_171)=k10_relat_1(C_170, D_171) | ~r1_tarski(k2_relat_1(C_170), B_169) | ~r1_tarski(k1_relat_1(C_170), A_168) | ~v1_relat_1(C_170))), inference(resolution, [status(thm)], [c_417, c_26])).
% 9.19/3.18  tff(c_1651, plain, (![A_246, A_247, B_248, D_249]: (k8_relset_1(A_246, A_247, B_248, D_249)=k10_relat_1(B_248, D_249) | ~r1_tarski(k1_relat_1(B_248), A_246) | ~v5_relat_1(B_248, A_247) | ~v1_relat_1(B_248))), inference(resolution, [status(thm)], [c_10, c_743])).
% 9.19/3.18  tff(c_7268, plain, (![A_652, A_653, B_654, D_655]: (k8_relset_1(A_652, A_653, k7_relat_1(B_654, A_652), D_655)=k10_relat_1(k7_relat_1(B_654, A_652), D_655) | ~v5_relat_1(k7_relat_1(B_654, A_652), A_653) | ~v1_relat_1(k7_relat_1(B_654, A_652)) | ~v1_relat_1(B_654))), inference(resolution, [status(thm)], [c_14, c_1651])).
% 9.19/3.18  tff(c_7298, plain, (![A_656, A_657, B_658, D_659]: (k8_relset_1(A_656, A_657, k7_relat_1(B_658, A_656), D_659)=k10_relat_1(k7_relat_1(B_658, A_656), D_659) | ~v1_relat_1(k7_relat_1(B_658, A_656)) | ~v5_relat_1(B_658, A_657) | ~v1_relat_1(B_658))), inference(resolution, [status(thm)], [c_477, c_7268])).
% 9.19/3.18  tff(c_7300, plain, (![A_657, D_659]: (k8_relset_1(u1_struct_0('#skF_3'), A_657, k7_relat_1('#skF_4', u1_struct_0('#skF_3')), D_659)=k10_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), D_659) | ~v5_relat_1('#skF_4', A_657) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_3274, c_7298])).
% 9.19/3.18  tff(c_7334, plain, (![A_664, D_665]: (k8_relset_1(u1_struct_0('#skF_3'), A_664, k7_relat_1('#skF_4', u1_struct_0('#skF_3')), D_665)=k10_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), D_665) | ~v5_relat_1('#skF_4', A_664))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_7300])).
% 9.19/3.18  tff(c_7358, plain, (![A_664, D_665]: (k8_relset_1(u1_struct_0('#skF_3'), A_664, k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), D_665)=k10_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), D_665) | ~v5_relat_1('#skF_4', A_664) | ~m1_pre_topc('#skF_3', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_553, c_7334])).
% 9.19/3.18  tff(c_7395, plain, (![A_669, D_670]: (k8_relset_1(u1_struct_0('#skF_3'), A_669, k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), D_670)=k10_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), D_670) | ~v5_relat_1('#skF_4', A_669))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_7358])).
% 9.19/3.18  tff(c_34, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_5')!=k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 9.19/3.18  tff(c_254, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_5')!=k10_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_253, c_34])).
% 9.19/3.18  tff(c_7401, plain, (k10_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k10_relat_1('#skF_4', '#skF_5') | ~v5_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_7395, c_254])).
% 9.19/3.18  tff(c_7408, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_313, c_7401])).
% 9.19/3.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.19/3.18  
% 9.19/3.18  Inference rules
% 9.19/3.18  ----------------------
% 9.19/3.18  #Ref     : 0
% 9.19/3.18  #Sup     : 1784
% 9.19/3.18  #Fact    : 0
% 9.19/3.18  #Define  : 0
% 9.19/3.18  #Split   : 3
% 9.19/3.18  #Chain   : 0
% 9.19/3.18  #Close   : 0
% 9.19/3.18  
% 9.19/3.18  Ordering : KBO
% 9.19/3.18  
% 9.19/3.18  Simplification rules
% 9.19/3.18  ----------------------
% 9.19/3.18  #Subsume      : 290
% 9.19/3.18  #Demod        : 320
% 9.19/3.18  #Tautology    : 191
% 9.19/3.18  #SimpNegUnit  : 3
% 9.19/3.18  #BackRed      : 2
% 9.19/3.18  
% 9.19/3.18  #Partial instantiations: 0
% 9.19/3.18  #Strategies tried      : 1
% 9.19/3.18  
% 9.19/3.18  Timing (in seconds)
% 9.19/3.18  ----------------------
% 9.19/3.19  Preprocessing        : 0.37
% 9.19/3.19  Parsing              : 0.19
% 9.19/3.19  CNF conversion       : 0.03
% 9.19/3.19  Main loop            : 2.02
% 9.19/3.19  Inferencing          : 0.63
% 9.19/3.19  Reduction            : 0.54
% 9.19/3.19  Demodulation         : 0.37
% 9.19/3.19  BG Simplification    : 0.08
% 9.19/3.19  Subsumption          : 0.62
% 9.19/3.19  Abstraction          : 0.12
% 9.19/3.19  MUC search           : 0.00
% 9.19/3.19  Cooper               : 0.00
% 9.19/3.19  Total                : 2.43
% 9.19/3.19  Index Insertion      : 0.00
% 9.19/3.19  Index Deletion       : 0.00
% 9.19/3.19  Index Matching       : 0.00
% 9.19/3.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
