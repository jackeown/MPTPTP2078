%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:15 EST 2020

% Result     : Theorem 45.65s
% Output     : CNFRefutation 45.83s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 407 expanded)
%              Number of leaves         :   48 ( 175 expanded)
%              Depth                    :   13
%              Number of atoms          :  217 (2580 expanded)
%              Number of equality atoms :   36 ( 218 expanded)
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

tff(f_60,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_172,negated_conjecture,(
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

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_128,axiom,(
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

tff(f_82,axiom,(
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

tff(f_72,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(c_20,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_141,plain,(
    ! [B_142,A_143] :
      ( v1_relat_1(B_142)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(A_143))
      | ~ v1_relat_1(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_147,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_48,c_141])).

tff(c_154,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_147])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_70,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_68,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_54,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_46,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_58,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_64,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_62,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_50,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_668,plain,(
    ! [A_214,B_215,C_216,D_217] :
      ( k2_partfun1(A_214,B_215,C_216,D_217) = k7_relat_1(C_216,D_217)
      | ~ m1_subset_1(C_216,k1_zfmisc_1(k2_zfmisc_1(A_214,B_215)))
      | ~ v1_funct_1(C_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_675,plain,(
    ! [D_217] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_217) = k7_relat_1('#skF_5',D_217)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_668])).

tff(c_680,plain,(
    ! [D_217] : k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_217) = k7_relat_1('#skF_5',D_217) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_675])).

tff(c_782,plain,(
    ! [D_231,C_230,A_229,B_228,E_232] :
      ( k3_tmap_1(A_229,B_228,C_230,D_231,E_232) = k2_partfun1(u1_struct_0(C_230),u1_struct_0(B_228),E_232,u1_struct_0(D_231))
      | ~ m1_pre_topc(D_231,C_230)
      | ~ m1_subset_1(E_232,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_230),u1_struct_0(B_228))))
      | ~ v1_funct_2(E_232,u1_struct_0(C_230),u1_struct_0(B_228))
      | ~ v1_funct_1(E_232)
      | ~ m1_pre_topc(D_231,A_229)
      | ~ m1_pre_topc(C_230,A_229)
      | ~ l1_pre_topc(B_228)
      | ~ v2_pre_topc(B_228)
      | v2_struct_0(B_228)
      | ~ l1_pre_topc(A_229)
      | ~ v2_pre_topc(A_229)
      | v2_struct_0(A_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_790,plain,(
    ! [A_229,D_231] :
      ( k3_tmap_1(A_229,'#skF_2','#skF_4',D_231,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_231))
      | ~ m1_pre_topc(D_231,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_231,A_229)
      | ~ m1_pre_topc('#skF_4',A_229)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_229)
      | ~ v2_pre_topc(A_229)
      | v2_struct_0(A_229) ) ),
    inference(resolution,[status(thm)],[c_48,c_782])).

tff(c_795,plain,(
    ! [D_231,A_229] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_231)) = k3_tmap_1(A_229,'#skF_2','#skF_4',D_231,'#skF_5')
      | ~ m1_pre_topc(D_231,'#skF_4')
      | ~ m1_pre_topc(D_231,A_229)
      | ~ m1_pre_topc('#skF_4',A_229)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_229)
      | ~ v2_pre_topc(A_229)
      | v2_struct_0(A_229) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_52,c_50,c_680,c_790])).

tff(c_849,plain,(
    ! [D_238,A_239] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_238)) = k3_tmap_1(A_239,'#skF_2','#skF_4',D_238,'#skF_5')
      | ~ m1_pre_topc(D_238,'#skF_4')
      | ~ m1_pre_topc(D_238,A_239)
      | ~ m1_pre_topc('#skF_4',A_239)
      | ~ l1_pre_topc(A_239)
      | ~ v2_pre_topc(A_239)
      | v2_struct_0(A_239) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_795])).

tff(c_855,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_849])).

tff(c_866,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_54,c_46,c_855])).

tff(c_867,plain,(
    k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_866])).

tff(c_508,plain,(
    ! [A_194,B_195,C_196,D_197] :
      ( k8_relset_1(A_194,B_195,C_196,D_197) = k10_relat_1(C_196,D_197)
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(A_194,B_195))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_515,plain,(
    ! [D_197] : k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_197) = k10_relat_1('#skF_5',D_197) ),
    inference(resolution,[status(thm)],[c_48,c_508])).

tff(c_42,plain,(
    r1_tarski(k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_518,plain,(
    r1_tarski(k10_relat_1('#skF_5','#skF_6'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_515,c_42])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_538,plain,(
    k3_xboole_0(k10_relat_1('#skF_5','#skF_6'),u1_struct_0('#skF_3')) = k10_relat_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_518,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_394,plain,(
    ! [A_181,C_182,B_183] :
      ( k3_xboole_0(A_181,k10_relat_1(C_182,B_183)) = k10_relat_1(k7_relat_1(C_182,A_181),B_183)
      | ~ v1_relat_1(C_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_946,plain,(
    ! [C_240,B_241,B_242] :
      ( k3_xboole_0(k10_relat_1(C_240,B_241),B_242) = k10_relat_1(k7_relat_1(C_240,B_242),B_241)
      | ~ v1_relat_1(C_240) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_394])).

tff(c_984,plain,
    ( k10_relat_1(k7_relat_1('#skF_5',u1_struct_0('#skF_3')),'#skF_6') = k10_relat_1('#skF_5','#skF_6')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_538,c_946])).

tff(c_1010,plain,(
    k10_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') = k10_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_867,c_984])).

tff(c_24,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k7_relat_1(B_22,A_21),B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_889,plain,
    ( r1_tarski(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_867,c_24])).

tff(c_906,plain,(
    r1_tarski(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_889])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( v1_relat_1(k7_relat_1(A_15,B_16))
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_892,plain,
    ( v1_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_867,c_18])).

tff(c_908,plain,(
    v1_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_892])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_117,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_48,c_8])).

tff(c_242,plain,(
    ! [A_161,C_162,B_163] :
      ( r1_tarski(A_161,C_162)
      | ~ r1_tarski(B_163,C_162)
      | ~ r1_tarski(A_161,B_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_442,plain,(
    ! [A_186] :
      ( r1_tarski(A_186,k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_186,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_117,c_242])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_203,plain,(
    ! [C_150,B_151,A_152] :
      ( v5_relat_1(C_150,B_151)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_152,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_211,plain,(
    ! [A_8,B_151,A_152] :
      ( v5_relat_1(A_8,B_151)
      | ~ r1_tarski(A_8,k2_zfmisc_1(A_152,B_151)) ) ),
    inference(resolution,[status(thm)],[c_10,c_203])).

tff(c_463,plain,(
    ! [A_186] :
      ( v5_relat_1(A_186,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_186,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_442,c_211])).

tff(c_22,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_20,A_19)),A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k2_relat_1(B_14),A_13)
      | ~ v5_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_587,plain,(
    ! [C_200,A_201,B_202] :
      ( m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_201,B_202)))
      | ~ r1_tarski(k2_relat_1(C_200),B_202)
      | ~ r1_tarski(k1_relat_1(C_200),A_201)
      | ~ v1_relat_1(C_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_32,plain,(
    ! [A_29,B_30,C_31,D_32] :
      ( k8_relset_1(A_29,B_30,C_31,D_32) = k10_relat_1(C_31,D_32)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1926,plain,(
    ! [A_319,B_320,C_321,D_322] :
      ( k8_relset_1(A_319,B_320,C_321,D_322) = k10_relat_1(C_321,D_322)
      | ~ r1_tarski(k2_relat_1(C_321),B_320)
      | ~ r1_tarski(k1_relat_1(C_321),A_319)
      | ~ v1_relat_1(C_321) ) ),
    inference(resolution,[status(thm)],[c_587,c_32])).

tff(c_3331,plain,(
    ! [A_437,A_438,B_439,D_440] :
      ( k8_relset_1(A_437,A_438,B_439,D_440) = k10_relat_1(B_439,D_440)
      | ~ r1_tarski(k1_relat_1(B_439),A_437)
      | ~ v5_relat_1(B_439,A_438)
      | ~ v1_relat_1(B_439) ) ),
    inference(resolution,[status(thm)],[c_16,c_1926])).

tff(c_24509,plain,(
    ! [A_1138,A_1139,B_1140,D_1141] :
      ( k8_relset_1(A_1138,A_1139,k7_relat_1(B_1140,A_1138),D_1141) = k10_relat_1(k7_relat_1(B_1140,A_1138),D_1141)
      | ~ v5_relat_1(k7_relat_1(B_1140,A_1138),A_1139)
      | ~ v1_relat_1(k7_relat_1(B_1140,A_1138))
      | ~ v1_relat_1(B_1140) ) ),
    inference(resolution,[status(thm)],[c_22,c_3331])).

tff(c_100901,plain,(
    ! [A_3052,B_3053,D_3054] :
      ( k8_relset_1(A_3052,u1_struct_0('#skF_2'),k7_relat_1(B_3053,A_3052),D_3054) = k10_relat_1(k7_relat_1(B_3053,A_3052),D_3054)
      | ~ v1_relat_1(k7_relat_1(B_3053,A_3052))
      | ~ v1_relat_1(B_3053)
      | ~ r1_tarski(k7_relat_1(B_3053,A_3052),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_463,c_24509])).

tff(c_101020,plain,(
    ! [D_3054] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),D_3054) = k10_relat_1(k7_relat_1('#skF_5',u1_struct_0('#skF_3')),D_3054)
      | ~ v1_relat_1(k7_relat_1('#skF_5',u1_struct_0('#skF_3')))
      | ~ v1_relat_1('#skF_5')
      | ~ r1_tarski(k7_relat_1('#skF_5',u1_struct_0('#skF_3')),'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_867,c_100901])).

tff(c_101060,plain,(
    ! [D_3054] : k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),D_3054) = k10_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),D_3054) ),
    inference(demodulation,[status(thm),theory(equality)],[c_906,c_867,c_154,c_908,c_867,c_867,c_101020])).

tff(c_40,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_517,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k10_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_515,c_40])).

tff(c_101061,plain,(
    k10_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k10_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101060,c_517])).

tff(c_101064,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1010,c_101061])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:34:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 45.65/32.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 45.65/32.57  
% 45.65/32.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 45.65/32.58  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k8_relset_1 > k2_partfun1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 45.65/32.58  
% 45.65/32.58  %Foreground sorts:
% 45.65/32.58  
% 45.65/32.58  
% 45.65/32.58  %Background operators:
% 45.65/32.58  
% 45.65/32.58  
% 45.65/32.58  %Foreground operators:
% 45.65/32.58  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 45.65/32.58  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 45.65/32.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 45.65/32.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 45.65/32.58  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 45.65/32.58  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 45.65/32.58  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 45.65/32.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 45.65/32.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 45.65/32.58  tff('#skF_5', type, '#skF_5': $i).
% 45.65/32.58  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 45.65/32.58  tff('#skF_6', type, '#skF_6': $i).
% 45.65/32.58  tff('#skF_2', type, '#skF_2': $i).
% 45.65/32.58  tff('#skF_3', type, '#skF_3': $i).
% 45.65/32.58  tff('#skF_1', type, '#skF_1': $i).
% 45.65/32.58  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 45.65/32.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 45.65/32.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 45.65/32.58  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 45.65/32.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 45.65/32.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 45.65/32.58  tff('#skF_4', type, '#skF_4': $i).
% 45.65/32.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 45.65/32.58  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 45.65/32.58  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 45.65/32.58  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 45.65/32.58  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 45.65/32.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 45.65/32.58  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 45.65/32.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 45.65/32.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 45.65/32.58  
% 45.83/32.59  tff(f_60, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 45.83/32.59  tff(f_172, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(B))) => (r1_tarski(k8_relset_1(u1_struct_0(D), u1_struct_0(B), E, F), u1_struct_0(C)) => (k8_relset_1(u1_struct_0(D), u1_struct_0(B), E, F) = k8_relset_1(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, E), F)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tmap_1)).
% 45.83/32.59  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 45.83/32.59  tff(f_96, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 45.83/32.59  tff(f_128, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 45.83/32.59  tff(f_82, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 45.83/32.59  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 45.83/32.59  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 45.83/32.59  tff(f_72, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 45.83/32.59  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 45.83/32.59  tff(f_58, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 45.83/32.59  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 45.83/32.59  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 45.83/32.59  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 45.83/32.59  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 45.83/32.59  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 45.83/32.59  tff(f_90, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 45.83/32.59  tff(c_20, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 45.83/32.59  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_172])).
% 45.83/32.59  tff(c_141, plain, (![B_142, A_143]: (v1_relat_1(B_142) | ~m1_subset_1(B_142, k1_zfmisc_1(A_143)) | ~v1_relat_1(A_143))), inference(cnfTransformation, [status(thm)], [f_48])).
% 45.83/32.59  tff(c_147, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_48, c_141])).
% 45.83/32.59  tff(c_154, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_147])).
% 45.83/32.59  tff(c_72, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_172])).
% 45.83/32.59  tff(c_70, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_172])).
% 45.83/32.59  tff(c_68, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_172])).
% 45.83/32.59  tff(c_54, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_172])).
% 45.83/32.59  tff(c_46, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_172])).
% 45.83/32.59  tff(c_58, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_172])).
% 45.83/32.59  tff(c_66, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_172])).
% 45.83/32.59  tff(c_64, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_172])).
% 45.83/32.59  tff(c_62, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_172])).
% 45.83/32.59  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_172])).
% 45.83/32.59  tff(c_50, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_172])).
% 45.83/32.59  tff(c_668, plain, (![A_214, B_215, C_216, D_217]: (k2_partfun1(A_214, B_215, C_216, D_217)=k7_relat_1(C_216, D_217) | ~m1_subset_1(C_216, k1_zfmisc_1(k2_zfmisc_1(A_214, B_215))) | ~v1_funct_1(C_216))), inference(cnfTransformation, [status(thm)], [f_96])).
% 45.83/32.59  tff(c_675, plain, (![D_217]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_217)=k7_relat_1('#skF_5', D_217) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_48, c_668])).
% 45.83/32.59  tff(c_680, plain, (![D_217]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_217)=k7_relat_1('#skF_5', D_217))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_675])).
% 45.83/32.59  tff(c_782, plain, (![D_231, C_230, A_229, B_228, E_232]: (k3_tmap_1(A_229, B_228, C_230, D_231, E_232)=k2_partfun1(u1_struct_0(C_230), u1_struct_0(B_228), E_232, u1_struct_0(D_231)) | ~m1_pre_topc(D_231, C_230) | ~m1_subset_1(E_232, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_230), u1_struct_0(B_228)))) | ~v1_funct_2(E_232, u1_struct_0(C_230), u1_struct_0(B_228)) | ~v1_funct_1(E_232) | ~m1_pre_topc(D_231, A_229) | ~m1_pre_topc(C_230, A_229) | ~l1_pre_topc(B_228) | ~v2_pre_topc(B_228) | v2_struct_0(B_228) | ~l1_pre_topc(A_229) | ~v2_pre_topc(A_229) | v2_struct_0(A_229))), inference(cnfTransformation, [status(thm)], [f_128])).
% 45.83/32.59  tff(c_790, plain, (![A_229, D_231]: (k3_tmap_1(A_229, '#skF_2', '#skF_4', D_231, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_231)) | ~m1_pre_topc(D_231, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_231, A_229) | ~m1_pre_topc('#skF_4', A_229) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_229) | ~v2_pre_topc(A_229) | v2_struct_0(A_229))), inference(resolution, [status(thm)], [c_48, c_782])).
% 45.83/32.59  tff(c_795, plain, (![D_231, A_229]: (k7_relat_1('#skF_5', u1_struct_0(D_231))=k3_tmap_1(A_229, '#skF_2', '#skF_4', D_231, '#skF_5') | ~m1_pre_topc(D_231, '#skF_4') | ~m1_pre_topc(D_231, A_229) | ~m1_pre_topc('#skF_4', A_229) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_229) | ~v2_pre_topc(A_229) | v2_struct_0(A_229))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_52, c_50, c_680, c_790])).
% 45.83/32.59  tff(c_849, plain, (![D_238, A_239]: (k7_relat_1('#skF_5', u1_struct_0(D_238))=k3_tmap_1(A_239, '#skF_2', '#skF_4', D_238, '#skF_5') | ~m1_pre_topc(D_238, '#skF_4') | ~m1_pre_topc(D_238, A_239) | ~m1_pre_topc('#skF_4', A_239) | ~l1_pre_topc(A_239) | ~v2_pre_topc(A_239) | v2_struct_0(A_239))), inference(negUnitSimplification, [status(thm)], [c_66, c_795])).
% 45.83/32.59  tff(c_855, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_58, c_849])).
% 45.83/32.59  tff(c_866, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_54, c_46, c_855])).
% 45.83/32.59  tff(c_867, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_72, c_866])).
% 45.83/32.59  tff(c_508, plain, (![A_194, B_195, C_196, D_197]: (k8_relset_1(A_194, B_195, C_196, D_197)=k10_relat_1(C_196, D_197) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(A_194, B_195))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 45.83/32.59  tff(c_515, plain, (![D_197]: (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_197)=k10_relat_1('#skF_5', D_197))), inference(resolution, [status(thm)], [c_48, c_508])).
% 45.83/32.59  tff(c_42, plain, (r1_tarski(k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_172])).
% 45.83/32.59  tff(c_518, plain, (r1_tarski(k10_relat_1('#skF_5', '#skF_6'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_515, c_42])).
% 45.83/32.59  tff(c_6, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 45.83/32.59  tff(c_538, plain, (k3_xboole_0(k10_relat_1('#skF_5', '#skF_6'), u1_struct_0('#skF_3'))=k10_relat_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_518, c_6])).
% 45.83/32.59  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 45.83/32.59  tff(c_394, plain, (![A_181, C_182, B_183]: (k3_xboole_0(A_181, k10_relat_1(C_182, B_183))=k10_relat_1(k7_relat_1(C_182, A_181), B_183) | ~v1_relat_1(C_182))), inference(cnfTransformation, [status(thm)], [f_72])).
% 45.83/32.59  tff(c_946, plain, (![C_240, B_241, B_242]: (k3_xboole_0(k10_relat_1(C_240, B_241), B_242)=k10_relat_1(k7_relat_1(C_240, B_242), B_241) | ~v1_relat_1(C_240))), inference(superposition, [status(thm), theory('equality')], [c_2, c_394])).
% 45.83/32.59  tff(c_984, plain, (k10_relat_1(k7_relat_1('#skF_5', u1_struct_0('#skF_3')), '#skF_6')=k10_relat_1('#skF_5', '#skF_6') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_538, c_946])).
% 45.83/32.59  tff(c_1010, plain, (k10_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')=k10_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_867, c_984])).
% 45.83/32.59  tff(c_24, plain, (![B_22, A_21]: (r1_tarski(k7_relat_1(B_22, A_21), B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_68])).
% 45.83/32.59  tff(c_889, plain, (r1_tarski(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_867, c_24])).
% 45.83/32.59  tff(c_906, plain, (r1_tarski(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_889])).
% 45.83/32.59  tff(c_18, plain, (![A_15, B_16]: (v1_relat_1(k7_relat_1(A_15, B_16)) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 45.83/32.59  tff(c_892, plain, (v1_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')) | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_867, c_18])).
% 45.83/32.59  tff(c_908, plain, (v1_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_892])).
% 45.83/32.59  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 45.83/32.59  tff(c_117, plain, (r1_tarski('#skF_5', k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_48, c_8])).
% 45.83/32.59  tff(c_242, plain, (![A_161, C_162, B_163]: (r1_tarski(A_161, C_162) | ~r1_tarski(B_163, C_162) | ~r1_tarski(A_161, B_163))), inference(cnfTransformation, [status(thm)], [f_33])).
% 45.83/32.59  tff(c_442, plain, (![A_186]: (r1_tarski(A_186, k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))) | ~r1_tarski(A_186, '#skF_5'))), inference(resolution, [status(thm)], [c_117, c_242])).
% 45.83/32.59  tff(c_10, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 45.83/32.59  tff(c_203, plain, (![C_150, B_151, A_152]: (v5_relat_1(C_150, B_151) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_152, B_151))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 45.83/32.59  tff(c_211, plain, (![A_8, B_151, A_152]: (v5_relat_1(A_8, B_151) | ~r1_tarski(A_8, k2_zfmisc_1(A_152, B_151)))), inference(resolution, [status(thm)], [c_10, c_203])).
% 45.83/32.59  tff(c_463, plain, (![A_186]: (v5_relat_1(A_186, u1_struct_0('#skF_2')) | ~r1_tarski(A_186, '#skF_5'))), inference(resolution, [status(thm)], [c_442, c_211])).
% 45.83/32.59  tff(c_22, plain, (![B_20, A_19]: (r1_tarski(k1_relat_1(k7_relat_1(B_20, A_19)), A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_64])).
% 45.83/32.59  tff(c_16, plain, (![B_14, A_13]: (r1_tarski(k2_relat_1(B_14), A_13) | ~v5_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 45.83/32.59  tff(c_587, plain, (![C_200, A_201, B_202]: (m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_201, B_202))) | ~r1_tarski(k2_relat_1(C_200), B_202) | ~r1_tarski(k1_relat_1(C_200), A_201) | ~v1_relat_1(C_200))), inference(cnfTransformation, [status(thm)], [f_90])).
% 45.83/32.59  tff(c_32, plain, (![A_29, B_30, C_31, D_32]: (k8_relset_1(A_29, B_30, C_31, D_32)=k10_relat_1(C_31, D_32) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 45.83/32.59  tff(c_1926, plain, (![A_319, B_320, C_321, D_322]: (k8_relset_1(A_319, B_320, C_321, D_322)=k10_relat_1(C_321, D_322) | ~r1_tarski(k2_relat_1(C_321), B_320) | ~r1_tarski(k1_relat_1(C_321), A_319) | ~v1_relat_1(C_321))), inference(resolution, [status(thm)], [c_587, c_32])).
% 45.83/32.59  tff(c_3331, plain, (![A_437, A_438, B_439, D_440]: (k8_relset_1(A_437, A_438, B_439, D_440)=k10_relat_1(B_439, D_440) | ~r1_tarski(k1_relat_1(B_439), A_437) | ~v5_relat_1(B_439, A_438) | ~v1_relat_1(B_439))), inference(resolution, [status(thm)], [c_16, c_1926])).
% 45.83/32.59  tff(c_24509, plain, (![A_1138, A_1139, B_1140, D_1141]: (k8_relset_1(A_1138, A_1139, k7_relat_1(B_1140, A_1138), D_1141)=k10_relat_1(k7_relat_1(B_1140, A_1138), D_1141) | ~v5_relat_1(k7_relat_1(B_1140, A_1138), A_1139) | ~v1_relat_1(k7_relat_1(B_1140, A_1138)) | ~v1_relat_1(B_1140))), inference(resolution, [status(thm)], [c_22, c_3331])).
% 45.83/32.59  tff(c_100901, plain, (![A_3052, B_3053, D_3054]: (k8_relset_1(A_3052, u1_struct_0('#skF_2'), k7_relat_1(B_3053, A_3052), D_3054)=k10_relat_1(k7_relat_1(B_3053, A_3052), D_3054) | ~v1_relat_1(k7_relat_1(B_3053, A_3052)) | ~v1_relat_1(B_3053) | ~r1_tarski(k7_relat_1(B_3053, A_3052), '#skF_5'))), inference(resolution, [status(thm)], [c_463, c_24509])).
% 45.83/32.59  tff(c_101020, plain, (![D_3054]: (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), D_3054)=k10_relat_1(k7_relat_1('#skF_5', u1_struct_0('#skF_3')), D_3054) | ~v1_relat_1(k7_relat_1('#skF_5', u1_struct_0('#skF_3'))) | ~v1_relat_1('#skF_5') | ~r1_tarski(k7_relat_1('#skF_5', u1_struct_0('#skF_3')), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_867, c_100901])).
% 45.83/32.59  tff(c_101060, plain, (![D_3054]: (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), D_3054)=k10_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), D_3054))), inference(demodulation, [status(thm), theory('equality')], [c_906, c_867, c_154, c_908, c_867, c_867, c_101020])).
% 45.83/32.59  tff(c_40, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_172])).
% 45.83/32.59  tff(c_517, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k10_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_515, c_40])).
% 45.83/32.59  tff(c_101061, plain, (k10_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k10_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_101060, c_517])).
% 45.83/32.59  tff(c_101064, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1010, c_101061])).
% 45.83/32.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 45.83/32.59  
% 45.83/32.59  Inference rules
% 45.83/32.59  ----------------------
% 45.83/32.59  #Ref     : 0
% 45.83/32.59  #Sup     : 22412
% 45.83/32.59  #Fact    : 0
% 45.83/32.59  #Define  : 0
% 45.83/32.59  #Split   : 46
% 45.83/32.59  #Chain   : 0
% 45.83/32.59  #Close   : 0
% 45.83/32.60  
% 45.83/32.60  Ordering : KBO
% 45.83/32.60  
% 45.83/32.60  Simplification rules
% 45.83/32.60  ----------------------
% 45.83/32.60  #Subsume      : 4073
% 45.83/32.60  #Demod        : 14682
% 45.83/32.60  #Tautology    : 3587
% 45.83/32.60  #SimpNegUnit  : 1106
% 45.83/32.60  #BackRed      : 23
% 45.83/32.60  
% 45.83/32.60  #Partial instantiations: 0
% 45.83/32.60  #Strategies tried      : 1
% 45.83/32.60  
% 45.83/32.60  Timing (in seconds)
% 45.83/32.60  ----------------------
% 45.83/32.60  Preprocessing        : 0.38
% 45.83/32.60  Parsing              : 0.21
% 45.83/32.60  CNF conversion       : 0.04
% 45.83/32.60  Main loop            : 31.39
% 45.83/32.60  Inferencing          : 5.72
% 45.83/32.60  Reduction            : 11.36
% 45.83/32.60  Demodulation         : 9.05
% 45.83/32.60  BG Simplification    : 0.66
% 45.83/32.60  Subsumption          : 11.81
% 45.83/32.60  Abstraction          : 1.30
% 45.83/32.60  MUC search           : 0.00
% 45.83/32.60  Cooper               : 0.00
% 45.83/32.60  Total                : 31.82
% 45.83/32.60  Index Insertion      : 0.00
% 45.83/32.60  Index Deletion       : 0.00
% 45.83/32.60  Index Matching       : 0.00
% 45.87/32.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
