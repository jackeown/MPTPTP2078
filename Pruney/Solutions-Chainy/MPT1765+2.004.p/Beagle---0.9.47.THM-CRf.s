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
% DateTime   : Thu Dec  3 10:27:15 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 127 expanded)
%              Number of leaves         :   33 (  65 expanded)
%              Depth                    :   11
%              Number of atoms          :  199 ( 733 expanded)
%              Number of equality atoms :   29 (  63 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k8_relset_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

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

tff(f_39,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_80,axiom,(
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

tff(f_29,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_33,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( r1_tarski(k10_relat_1(A,C),B)
         => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_110,axiom,(
    ! [A,B,C,D,E] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & m1_pre_topc(C,A)
        & m1_pre_topc(D,A)
        & v1_funct_1(E)
        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
     => ( v1_funct_1(k3_tmap_1(A,B,C,D,E))
        & v1_funct_2(k3_tmap_1(A,B,C,D,E),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k3_tmap_1(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_32,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_36,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_24,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_30,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_28,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_71,plain,(
    ! [A_118,B_119,C_120,D_121] :
      ( k2_partfun1(A_118,B_119,C_120,D_121) = k7_relat_1(C_120,D_121)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119)))
      | ~ v1_funct_1(C_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_73,plain,(
    ! [D_121] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_121) = k7_relat_1('#skF_5',D_121)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_26,c_71])).

tff(c_76,plain,(
    ! [D_121] : k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_121) = k7_relat_1('#skF_5',D_121) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_73])).

tff(c_361,plain,(
    ! [D_227,C_230,A_229,B_228,E_231] :
      ( k3_tmap_1(A_229,B_228,C_230,D_227,E_231) = k2_partfun1(u1_struct_0(C_230),u1_struct_0(B_228),E_231,u1_struct_0(D_227))
      | ~ m1_pre_topc(D_227,C_230)
      | ~ m1_subset_1(E_231,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_230),u1_struct_0(B_228))))
      | ~ v1_funct_2(E_231,u1_struct_0(C_230),u1_struct_0(B_228))
      | ~ v1_funct_1(E_231)
      | ~ m1_pre_topc(D_227,A_229)
      | ~ m1_pre_topc(C_230,A_229)
      | ~ l1_pre_topc(B_228)
      | ~ v2_pre_topc(B_228)
      | v2_struct_0(B_228)
      | ~ l1_pre_topc(A_229)
      | ~ v2_pre_topc(A_229)
      | v2_struct_0(A_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_365,plain,(
    ! [A_229,D_227] :
      ( k3_tmap_1(A_229,'#skF_2','#skF_4',D_227,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_227))
      | ~ m1_pre_topc(D_227,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_227,A_229)
      | ~ m1_pre_topc('#skF_4',A_229)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_229)
      | ~ v2_pre_topc(A_229)
      | v2_struct_0(A_229) ) ),
    inference(resolution,[status(thm)],[c_26,c_361])).

tff(c_369,plain,(
    ! [D_227,A_229] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_227)) = k3_tmap_1(A_229,'#skF_2','#skF_4',D_227,'#skF_5')
      | ~ m1_pre_topc(D_227,'#skF_4')
      | ~ m1_pre_topc(D_227,A_229)
      | ~ m1_pre_topc('#skF_4',A_229)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_229)
      | ~ v2_pre_topc(A_229)
      | v2_struct_0(A_229) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_30,c_28,c_76,c_365])).

tff(c_371,plain,(
    ! [D_232,A_233] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_232)) = k3_tmap_1(A_233,'#skF_2','#skF_4',D_232,'#skF_5')
      | ~ m1_pre_topc(D_232,'#skF_4')
      | ~ m1_pre_topc(D_232,A_233)
      | ~ m1_pre_topc('#skF_4',A_233)
      | ~ l1_pre_topc(A_233)
      | ~ v2_pre_topc(A_233)
      | v2_struct_0(A_233) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_369])).

tff(c_377,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_371])).

tff(c_388,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_32,c_24,c_377])).

tff(c_389,plain,(
    k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_388])).

tff(c_2,plain,(
    ! [C_3,A_1,B_2] :
      ( v1_relat_1(C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_55,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_2])).

tff(c_56,plain,(
    ! [A_113,B_114,C_115,D_116] :
      ( k8_relset_1(A_113,B_114,C_115,D_116) = k10_relat_1(C_115,D_116)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_59,plain,(
    ! [D_116] : k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_116) = k10_relat_1('#skF_5',D_116) ),
    inference(resolution,[status(thm)],[c_26,c_56])).

tff(c_20,plain,(
    r1_tarski(k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_61,plain,(
    r1_tarski(k10_relat_1('#skF_5','#skF_6'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_20])).

tff(c_86,plain,(
    ! [A_123,B_124,C_125] :
      ( k10_relat_1(k7_relat_1(A_123,B_124),C_125) = k10_relat_1(A_123,C_125)
      | ~ r1_tarski(k10_relat_1(A_123,C_125),B_124)
      | ~ v1_funct_1(A_123)
      | ~ v1_relat_1(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_89,plain,
    ( k10_relat_1(k7_relat_1('#skF_5',u1_struct_0('#skF_3')),'#skF_6') = k10_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_61,c_86])).

tff(c_92,plain,(
    k10_relat_1(k7_relat_1('#skF_5',u1_struct_0('#skF_3')),'#skF_6') = k10_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_30,c_89])).

tff(c_394,plain,(
    k10_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') = k10_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_389,c_92])).

tff(c_333,plain,(
    ! [E_219,D_215,A_217,B_216,C_218] :
      ( m1_subset_1(k3_tmap_1(A_217,B_216,C_218,D_215,E_219),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_215),u1_struct_0(B_216))))
      | ~ m1_subset_1(E_219,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_218),u1_struct_0(B_216))))
      | ~ v1_funct_2(E_219,u1_struct_0(C_218),u1_struct_0(B_216))
      | ~ v1_funct_1(E_219)
      | ~ m1_pre_topc(D_215,A_217)
      | ~ m1_pre_topc(C_218,A_217)
      | ~ l1_pre_topc(B_216)
      | ~ v2_pre_topc(B_216)
      | v2_struct_0(B_216)
      | ~ l1_pre_topc(A_217)
      | ~ v2_pre_topc(A_217)
      | v2_struct_0(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6,D_7] :
      ( k8_relset_1(A_4,B_5,C_6,D_7) = k10_relat_1(C_6,D_7)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(A_4,B_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_409,plain,(
    ! [D_239,B_234,C_237,E_236,D_235,A_238] :
      ( k8_relset_1(u1_struct_0(D_235),u1_struct_0(B_234),k3_tmap_1(A_238,B_234,C_237,D_235,E_236),D_239) = k10_relat_1(k3_tmap_1(A_238,B_234,C_237,D_235,E_236),D_239)
      | ~ m1_subset_1(E_236,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_237),u1_struct_0(B_234))))
      | ~ v1_funct_2(E_236,u1_struct_0(C_237),u1_struct_0(B_234))
      | ~ v1_funct_1(E_236)
      | ~ m1_pre_topc(D_235,A_238)
      | ~ m1_pre_topc(C_237,A_238)
      | ~ l1_pre_topc(B_234)
      | ~ v2_pre_topc(B_234)
      | v2_struct_0(B_234)
      | ~ l1_pre_topc(A_238)
      | ~ v2_pre_topc(A_238)
      | v2_struct_0(A_238) ) ),
    inference(resolution,[status(thm)],[c_333,c_4])).

tff(c_413,plain,(
    ! [D_235,A_238,D_239] :
      ( k8_relset_1(u1_struct_0(D_235),u1_struct_0('#skF_2'),k3_tmap_1(A_238,'#skF_2','#skF_4',D_235,'#skF_5'),D_239) = k10_relat_1(k3_tmap_1(A_238,'#skF_2','#skF_4',D_235,'#skF_5'),D_239)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_235,A_238)
      | ~ m1_pre_topc('#skF_4',A_238)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_238)
      | ~ v2_pre_topc(A_238)
      | v2_struct_0(A_238) ) ),
    inference(resolution,[status(thm)],[c_26,c_409])).

tff(c_417,plain,(
    ! [D_235,A_238,D_239] :
      ( k8_relset_1(u1_struct_0(D_235),u1_struct_0('#skF_2'),k3_tmap_1(A_238,'#skF_2','#skF_4',D_235,'#skF_5'),D_239) = k10_relat_1(k3_tmap_1(A_238,'#skF_2','#skF_4',D_235,'#skF_5'),D_239)
      | ~ m1_pre_topc(D_235,A_238)
      | ~ m1_pre_topc('#skF_4',A_238)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_238)
      | ~ v2_pre_topc(A_238)
      | v2_struct_0(A_238) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_30,c_28,c_413])).

tff(c_432,plain,(
    ! [D_241,A_242,D_243] :
      ( k8_relset_1(u1_struct_0(D_241),u1_struct_0('#skF_2'),k3_tmap_1(A_242,'#skF_2','#skF_4',D_241,'#skF_5'),D_243) = k10_relat_1(k3_tmap_1(A_242,'#skF_2','#skF_4',D_241,'#skF_5'),D_243)
      | ~ m1_pre_topc(D_241,A_242)
      | ~ m1_pre_topc('#skF_4',A_242)
      | ~ l1_pre_topc(A_242)
      | ~ v2_pre_topc(A_242)
      | v2_struct_0(A_242) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_417])).

tff(c_18,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_60,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k10_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_18])).

tff(c_438,plain,
    ( k10_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k10_relat_1('#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_60])).

tff(c_444,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_32,c_36,c_394,c_438])).

tff(c_446,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_444])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:49:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.43  
% 2.87/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.44  %$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k8_relset_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.19/1.44  
% 3.19/1.44  %Foreground sorts:
% 3.19/1.44  
% 3.19/1.44  
% 3.19/1.44  %Background operators:
% 3.19/1.44  
% 3.19/1.44  
% 3.19/1.44  %Foreground operators:
% 3.19/1.44  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.19/1.44  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.19/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.19/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.19/1.44  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.19/1.44  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.19/1.44  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.19/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.19/1.44  tff('#skF_5', type, '#skF_5': $i).
% 3.19/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.19/1.44  tff('#skF_6', type, '#skF_6': $i).
% 3.19/1.44  tff('#skF_2', type, '#skF_2': $i).
% 3.19/1.44  tff('#skF_3', type, '#skF_3': $i).
% 3.19/1.44  tff('#skF_1', type, '#skF_1': $i).
% 3.19/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.19/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.19/1.44  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.19/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.19/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.19/1.44  tff('#skF_4', type, '#skF_4': $i).
% 3.19/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.19/1.44  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.19/1.44  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.19/1.44  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.19/1.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.19/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.19/1.44  
% 3.19/1.45  tff(f_154, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(B))) => (r1_tarski(k8_relset_1(u1_struct_0(D), u1_struct_0(B), E, F), u1_struct_0(C)) => (k8_relset_1(u1_struct_0(D), u1_struct_0(B), E, F) = k8_relset_1(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, E), F)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tmap_1)).
% 3.19/1.45  tff(f_39, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.19/1.45  tff(f_80, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 3.19/1.45  tff(f_29, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.19/1.45  tff(f_33, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.19/1.45  tff(f_48, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 3.19/1.45  tff(f_110, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 3.19/1.45  tff(c_50, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.19/1.45  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.19/1.45  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.19/1.45  tff(c_32, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.19/1.45  tff(c_36, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.19/1.45  tff(c_24, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.19/1.45  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.19/1.45  tff(c_42, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.19/1.45  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.19/1.45  tff(c_30, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.19/1.45  tff(c_28, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.19/1.45  tff(c_26, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.19/1.45  tff(c_71, plain, (![A_118, B_119, C_120, D_121]: (k2_partfun1(A_118, B_119, C_120, D_121)=k7_relat_1(C_120, D_121) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))) | ~v1_funct_1(C_120))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.19/1.45  tff(c_73, plain, (![D_121]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_121)=k7_relat_1('#skF_5', D_121) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_26, c_71])).
% 3.19/1.45  tff(c_76, plain, (![D_121]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_121)=k7_relat_1('#skF_5', D_121))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_73])).
% 3.19/1.45  tff(c_361, plain, (![D_227, C_230, A_229, B_228, E_231]: (k3_tmap_1(A_229, B_228, C_230, D_227, E_231)=k2_partfun1(u1_struct_0(C_230), u1_struct_0(B_228), E_231, u1_struct_0(D_227)) | ~m1_pre_topc(D_227, C_230) | ~m1_subset_1(E_231, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_230), u1_struct_0(B_228)))) | ~v1_funct_2(E_231, u1_struct_0(C_230), u1_struct_0(B_228)) | ~v1_funct_1(E_231) | ~m1_pre_topc(D_227, A_229) | ~m1_pre_topc(C_230, A_229) | ~l1_pre_topc(B_228) | ~v2_pre_topc(B_228) | v2_struct_0(B_228) | ~l1_pre_topc(A_229) | ~v2_pre_topc(A_229) | v2_struct_0(A_229))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.19/1.45  tff(c_365, plain, (![A_229, D_227]: (k3_tmap_1(A_229, '#skF_2', '#skF_4', D_227, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_227)) | ~m1_pre_topc(D_227, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_227, A_229) | ~m1_pre_topc('#skF_4', A_229) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_229) | ~v2_pre_topc(A_229) | v2_struct_0(A_229))), inference(resolution, [status(thm)], [c_26, c_361])).
% 3.19/1.45  tff(c_369, plain, (![D_227, A_229]: (k7_relat_1('#skF_5', u1_struct_0(D_227))=k3_tmap_1(A_229, '#skF_2', '#skF_4', D_227, '#skF_5') | ~m1_pre_topc(D_227, '#skF_4') | ~m1_pre_topc(D_227, A_229) | ~m1_pre_topc('#skF_4', A_229) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_229) | ~v2_pre_topc(A_229) | v2_struct_0(A_229))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_30, c_28, c_76, c_365])).
% 3.19/1.45  tff(c_371, plain, (![D_232, A_233]: (k7_relat_1('#skF_5', u1_struct_0(D_232))=k3_tmap_1(A_233, '#skF_2', '#skF_4', D_232, '#skF_5') | ~m1_pre_topc(D_232, '#skF_4') | ~m1_pre_topc(D_232, A_233) | ~m1_pre_topc('#skF_4', A_233) | ~l1_pre_topc(A_233) | ~v2_pre_topc(A_233) | v2_struct_0(A_233))), inference(negUnitSimplification, [status(thm)], [c_44, c_369])).
% 3.19/1.45  tff(c_377, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_371])).
% 3.19/1.45  tff(c_388, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_32, c_24, c_377])).
% 3.19/1.45  tff(c_389, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_50, c_388])).
% 3.19/1.45  tff(c_2, plain, (![C_3, A_1, B_2]: (v1_relat_1(C_3) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.19/1.45  tff(c_55, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_26, c_2])).
% 3.19/1.45  tff(c_56, plain, (![A_113, B_114, C_115, D_116]: (k8_relset_1(A_113, B_114, C_115, D_116)=k10_relat_1(C_115, D_116) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.19/1.45  tff(c_59, plain, (![D_116]: (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_116)=k10_relat_1('#skF_5', D_116))), inference(resolution, [status(thm)], [c_26, c_56])).
% 3.19/1.45  tff(c_20, plain, (r1_tarski(k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.19/1.45  tff(c_61, plain, (r1_tarski(k10_relat_1('#skF_5', '#skF_6'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_20])).
% 3.19/1.45  tff(c_86, plain, (![A_123, B_124, C_125]: (k10_relat_1(k7_relat_1(A_123, B_124), C_125)=k10_relat_1(A_123, C_125) | ~r1_tarski(k10_relat_1(A_123, C_125), B_124) | ~v1_funct_1(A_123) | ~v1_relat_1(A_123))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.19/1.45  tff(c_89, plain, (k10_relat_1(k7_relat_1('#skF_5', u1_struct_0('#skF_3')), '#skF_6')=k10_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_61, c_86])).
% 3.19/1.45  tff(c_92, plain, (k10_relat_1(k7_relat_1('#skF_5', u1_struct_0('#skF_3')), '#skF_6')=k10_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_30, c_89])).
% 3.19/1.45  tff(c_394, plain, (k10_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')=k10_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_389, c_92])).
% 3.19/1.45  tff(c_333, plain, (![E_219, D_215, A_217, B_216, C_218]: (m1_subset_1(k3_tmap_1(A_217, B_216, C_218, D_215, E_219), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_215), u1_struct_0(B_216)))) | ~m1_subset_1(E_219, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_218), u1_struct_0(B_216)))) | ~v1_funct_2(E_219, u1_struct_0(C_218), u1_struct_0(B_216)) | ~v1_funct_1(E_219) | ~m1_pre_topc(D_215, A_217) | ~m1_pre_topc(C_218, A_217) | ~l1_pre_topc(B_216) | ~v2_pre_topc(B_216) | v2_struct_0(B_216) | ~l1_pre_topc(A_217) | ~v2_pre_topc(A_217) | v2_struct_0(A_217))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.19/1.45  tff(c_4, plain, (![A_4, B_5, C_6, D_7]: (k8_relset_1(A_4, B_5, C_6, D_7)=k10_relat_1(C_6, D_7) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(A_4, B_5))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.19/1.45  tff(c_409, plain, (![D_239, B_234, C_237, E_236, D_235, A_238]: (k8_relset_1(u1_struct_0(D_235), u1_struct_0(B_234), k3_tmap_1(A_238, B_234, C_237, D_235, E_236), D_239)=k10_relat_1(k3_tmap_1(A_238, B_234, C_237, D_235, E_236), D_239) | ~m1_subset_1(E_236, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_237), u1_struct_0(B_234)))) | ~v1_funct_2(E_236, u1_struct_0(C_237), u1_struct_0(B_234)) | ~v1_funct_1(E_236) | ~m1_pre_topc(D_235, A_238) | ~m1_pre_topc(C_237, A_238) | ~l1_pre_topc(B_234) | ~v2_pre_topc(B_234) | v2_struct_0(B_234) | ~l1_pre_topc(A_238) | ~v2_pre_topc(A_238) | v2_struct_0(A_238))), inference(resolution, [status(thm)], [c_333, c_4])).
% 3.19/1.45  tff(c_413, plain, (![D_235, A_238, D_239]: (k8_relset_1(u1_struct_0(D_235), u1_struct_0('#skF_2'), k3_tmap_1(A_238, '#skF_2', '#skF_4', D_235, '#skF_5'), D_239)=k10_relat_1(k3_tmap_1(A_238, '#skF_2', '#skF_4', D_235, '#skF_5'), D_239) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_235, A_238) | ~m1_pre_topc('#skF_4', A_238) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_238) | ~v2_pre_topc(A_238) | v2_struct_0(A_238))), inference(resolution, [status(thm)], [c_26, c_409])).
% 3.19/1.45  tff(c_417, plain, (![D_235, A_238, D_239]: (k8_relset_1(u1_struct_0(D_235), u1_struct_0('#skF_2'), k3_tmap_1(A_238, '#skF_2', '#skF_4', D_235, '#skF_5'), D_239)=k10_relat_1(k3_tmap_1(A_238, '#skF_2', '#skF_4', D_235, '#skF_5'), D_239) | ~m1_pre_topc(D_235, A_238) | ~m1_pre_topc('#skF_4', A_238) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_238) | ~v2_pre_topc(A_238) | v2_struct_0(A_238))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_30, c_28, c_413])).
% 3.19/1.45  tff(c_432, plain, (![D_241, A_242, D_243]: (k8_relset_1(u1_struct_0(D_241), u1_struct_0('#skF_2'), k3_tmap_1(A_242, '#skF_2', '#skF_4', D_241, '#skF_5'), D_243)=k10_relat_1(k3_tmap_1(A_242, '#skF_2', '#skF_4', D_241, '#skF_5'), D_243) | ~m1_pre_topc(D_241, A_242) | ~m1_pre_topc('#skF_4', A_242) | ~l1_pre_topc(A_242) | ~v2_pre_topc(A_242) | v2_struct_0(A_242))), inference(negUnitSimplification, [status(thm)], [c_44, c_417])).
% 3.19/1.45  tff(c_18, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.19/1.45  tff(c_60, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k10_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_18])).
% 3.19/1.45  tff(c_438, plain, (k10_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k10_relat_1('#skF_5', '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_432, c_60])).
% 3.19/1.45  tff(c_444, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_32, c_36, c_394, c_438])).
% 3.19/1.45  tff(c_446, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_444])).
% 3.19/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.45  
% 3.19/1.45  Inference rules
% 3.19/1.45  ----------------------
% 3.19/1.45  #Ref     : 0
% 3.19/1.45  #Sup     : 80
% 3.19/1.45  #Fact    : 0
% 3.19/1.45  #Define  : 0
% 3.19/1.45  #Split   : 4
% 3.19/1.45  #Chain   : 0
% 3.19/1.45  #Close   : 0
% 3.19/1.45  
% 3.19/1.45  Ordering : KBO
% 3.19/1.45  
% 3.19/1.45  Simplification rules
% 3.19/1.45  ----------------------
% 3.19/1.45  #Subsume      : 1
% 3.19/1.45  #Demod        : 119
% 3.19/1.45  #Tautology    : 21
% 3.19/1.45  #SimpNegUnit  : 26
% 3.19/1.45  #BackRed      : 12
% 3.19/1.45  
% 3.19/1.45  #Partial instantiations: 0
% 3.19/1.45  #Strategies tried      : 1
% 3.19/1.45  
% 3.19/1.45  Timing (in seconds)
% 3.19/1.45  ----------------------
% 3.19/1.46  Preprocessing        : 0.35
% 3.19/1.46  Parsing              : 0.18
% 3.19/1.46  CNF conversion       : 0.04
% 3.19/1.46  Main loop            : 0.35
% 3.19/1.46  Inferencing          : 0.13
% 3.19/1.46  Reduction            : 0.10
% 3.19/1.46  Demodulation         : 0.08
% 3.19/1.46  BG Simplification    : 0.02
% 3.19/1.46  Subsumption          : 0.07
% 3.19/1.46  Abstraction          : 0.02
% 3.19/1.46  MUC search           : 0.00
% 3.19/1.46  Cooper               : 0.00
% 3.19/1.46  Total                : 0.74
% 3.19/1.46  Index Insertion      : 0.00
% 3.19/1.46  Index Deletion       : 0.00
% 3.19/1.46  Index Matching       : 0.00
% 3.19/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
