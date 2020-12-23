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
% DateTime   : Thu Dec  3 10:27:15 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 130 expanded)
%              Number of leaves         :   34 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :  205 ( 739 expanded)
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

tff(f_159,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_85,axiom,(
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

tff(f_38,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( r1_tarski(k10_relat_1(A,C),B)
         => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_115,axiom,(
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

tff(c_52,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_50,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_34,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_38,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_26,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_44,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_32,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_30,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_80,plain,(
    ! [A_121,B_122,C_123,D_124] :
      ( k2_partfun1(A_121,B_122,C_123,D_124) = k7_relat_1(C_123,D_124)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122)))
      | ~ v1_funct_1(C_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_82,plain,(
    ! [D_124] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_124) = k7_relat_1('#skF_5',D_124)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_80])).

tff(c_85,plain,(
    ! [D_124] : k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_124) = k7_relat_1('#skF_5',D_124) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_82])).

tff(c_376,plain,(
    ! [D_231,C_230,E_234,B_233,A_232] :
      ( k3_tmap_1(A_232,B_233,C_230,D_231,E_234) = k2_partfun1(u1_struct_0(C_230),u1_struct_0(B_233),E_234,u1_struct_0(D_231))
      | ~ m1_pre_topc(D_231,C_230)
      | ~ m1_subset_1(E_234,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_230),u1_struct_0(B_233))))
      | ~ v1_funct_2(E_234,u1_struct_0(C_230),u1_struct_0(B_233))
      | ~ v1_funct_1(E_234)
      | ~ m1_pre_topc(D_231,A_232)
      | ~ m1_pre_topc(C_230,A_232)
      | ~ l1_pre_topc(B_233)
      | ~ v2_pre_topc(B_233)
      | v2_struct_0(B_233)
      | ~ l1_pre_topc(A_232)
      | ~ v2_pre_topc(A_232)
      | v2_struct_0(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_380,plain,(
    ! [A_232,D_231] :
      ( k3_tmap_1(A_232,'#skF_2','#skF_4',D_231,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_231))
      | ~ m1_pre_topc(D_231,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_231,A_232)
      | ~ m1_pre_topc('#skF_4',A_232)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_232)
      | ~ v2_pre_topc(A_232)
      | v2_struct_0(A_232) ) ),
    inference(resolution,[status(thm)],[c_28,c_376])).

tff(c_384,plain,(
    ! [D_231,A_232] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_231)) = k3_tmap_1(A_232,'#skF_2','#skF_4',D_231,'#skF_5')
      | ~ m1_pre_topc(D_231,'#skF_4')
      | ~ m1_pre_topc(D_231,A_232)
      | ~ m1_pre_topc('#skF_4',A_232)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_232)
      | ~ v2_pre_topc(A_232)
      | v2_struct_0(A_232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_32,c_30,c_85,c_380])).

tff(c_386,plain,(
    ! [D_235,A_236] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_235)) = k3_tmap_1(A_236,'#skF_2','#skF_4',D_235,'#skF_5')
      | ~ m1_pre_topc(D_235,'#skF_4')
      | ~ m1_pre_topc(D_235,A_236)
      | ~ m1_pre_topc('#skF_4',A_236)
      | ~ l1_pre_topc(A_236)
      | ~ v2_pre_topc(A_236)
      | v2_struct_0(A_236) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_384])).

tff(c_392,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_386])).

tff(c_403,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_34,c_26,c_392])).

tff(c_404,plain,(
    k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_403])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_28,c_2])).

tff(c_65,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_62])).

tff(c_66,plain,(
    ! [A_116,B_117,C_118,D_119] :
      ( k8_relset_1(A_116,B_117,C_118,D_119) = k10_relat_1(C_118,D_119)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_69,plain,(
    ! [D_119] : k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_119) = k10_relat_1('#skF_5',D_119) ),
    inference(resolution,[status(thm)],[c_28,c_66])).

tff(c_22,plain,(
    r1_tarski(k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_70,plain,(
    r1_tarski(k10_relat_1('#skF_5','#skF_6'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_22])).

tff(c_86,plain,(
    ! [A_125,B_126,C_127] :
      ( k10_relat_1(k7_relat_1(A_125,B_126),C_127) = k10_relat_1(A_125,C_127)
      | ~ r1_tarski(k10_relat_1(A_125,C_127),B_126)
      | ~ v1_funct_1(A_125)
      | ~ v1_relat_1(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_89,plain,
    ( k10_relat_1(k7_relat_1('#skF_5',u1_struct_0('#skF_3')),'#skF_6') = k10_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_86])).

tff(c_92,plain,(
    k10_relat_1(k7_relat_1('#skF_5',u1_struct_0('#skF_3')),'#skF_6') = k10_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_32,c_89])).

tff(c_409,plain,(
    k10_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') = k10_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_92])).

tff(c_346,plain,(
    ! [B_221,E_218,C_220,D_222,A_219] :
      ( m1_subset_1(k3_tmap_1(A_219,B_221,C_220,D_222,E_218),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_222),u1_struct_0(B_221))))
      | ~ m1_subset_1(E_218,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_220),u1_struct_0(B_221))))
      | ~ v1_funct_2(E_218,u1_struct_0(C_220),u1_struct_0(B_221))
      | ~ v1_funct_1(E_218)
      | ~ m1_pre_topc(D_222,A_219)
      | ~ m1_pre_topc(C_220,A_219)
      | ~ l1_pre_topc(B_221)
      | ~ v2_pre_topc(B_221)
      | v2_struct_0(B_221)
      | ~ l1_pre_topc(A_219)
      | ~ v2_pre_topc(A_219)
      | v2_struct_0(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8,D_9] :
      ( k8_relset_1(A_6,B_7,C_8,D_9) = k10_relat_1(C_8,D_9)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_424,plain,(
    ! [E_241,D_239,D_238,B_242,A_237,C_240] :
      ( k8_relset_1(u1_struct_0(D_238),u1_struct_0(B_242),k3_tmap_1(A_237,B_242,C_240,D_238,E_241),D_239) = k10_relat_1(k3_tmap_1(A_237,B_242,C_240,D_238,E_241),D_239)
      | ~ m1_subset_1(E_241,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_240),u1_struct_0(B_242))))
      | ~ v1_funct_2(E_241,u1_struct_0(C_240),u1_struct_0(B_242))
      | ~ v1_funct_1(E_241)
      | ~ m1_pre_topc(D_238,A_237)
      | ~ m1_pre_topc(C_240,A_237)
      | ~ l1_pre_topc(B_242)
      | ~ v2_pre_topc(B_242)
      | v2_struct_0(B_242)
      | ~ l1_pre_topc(A_237)
      | ~ v2_pre_topc(A_237)
      | v2_struct_0(A_237) ) ),
    inference(resolution,[status(thm)],[c_346,c_6])).

tff(c_428,plain,(
    ! [D_238,A_237,D_239] :
      ( k8_relset_1(u1_struct_0(D_238),u1_struct_0('#skF_2'),k3_tmap_1(A_237,'#skF_2','#skF_4',D_238,'#skF_5'),D_239) = k10_relat_1(k3_tmap_1(A_237,'#skF_2','#skF_4',D_238,'#skF_5'),D_239)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_238,A_237)
      | ~ m1_pre_topc('#skF_4',A_237)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_237)
      | ~ v2_pre_topc(A_237)
      | v2_struct_0(A_237) ) ),
    inference(resolution,[status(thm)],[c_28,c_424])).

tff(c_432,plain,(
    ! [D_238,A_237,D_239] :
      ( k8_relset_1(u1_struct_0(D_238),u1_struct_0('#skF_2'),k3_tmap_1(A_237,'#skF_2','#skF_4',D_238,'#skF_5'),D_239) = k10_relat_1(k3_tmap_1(A_237,'#skF_2','#skF_4',D_238,'#skF_5'),D_239)
      | ~ m1_pre_topc(D_238,A_237)
      | ~ m1_pre_topc('#skF_4',A_237)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_237)
      | ~ v2_pre_topc(A_237)
      | v2_struct_0(A_237) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_32,c_30,c_428])).

tff(c_447,plain,(
    ! [D_244,A_245,D_246] :
      ( k8_relset_1(u1_struct_0(D_244),u1_struct_0('#skF_2'),k3_tmap_1(A_245,'#skF_2','#skF_4',D_244,'#skF_5'),D_246) = k10_relat_1(k3_tmap_1(A_245,'#skF_2','#skF_4',D_244,'#skF_5'),D_246)
      | ~ m1_pre_topc(D_244,A_245)
      | ~ m1_pre_topc('#skF_4',A_245)
      | ~ l1_pre_topc(A_245)
      | ~ v2_pre_topc(A_245)
      | v2_struct_0(A_245) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_432])).

tff(c_20,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_110,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k10_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_20])).

tff(c_453,plain,
    ( k10_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k10_relat_1('#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_447,c_110])).

tff(c_459,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_34,c_38,c_409,c_453])).

tff(c_461,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_459])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:21:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.52  
% 3.11/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.53  %$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k8_relset_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.11/1.53  
% 3.11/1.53  %Foreground sorts:
% 3.11/1.53  
% 3.11/1.53  
% 3.11/1.53  %Background operators:
% 3.11/1.53  
% 3.11/1.53  
% 3.11/1.53  %Foreground operators:
% 3.11/1.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.11/1.53  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.11/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.11/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.53  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.11/1.53  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.11/1.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.11/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.11/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.11/1.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.11/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.11/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.11/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.11/1.53  tff('#skF_1', type, '#skF_1': $i).
% 3.11/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.11/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.53  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.11/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.11/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.11/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.11/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.53  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.11/1.53  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.11/1.53  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.11/1.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.11/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.11/1.53  
% 3.32/1.54  tff(f_159, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(B))) => (r1_tarski(k8_relset_1(u1_struct_0(D), u1_struct_0(B), E, F), u1_struct_0(C)) => (k8_relset_1(u1_struct_0(D), u1_struct_0(B), E, F) = k8_relset_1(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, E), F)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tmap_1)).
% 3.32/1.54  tff(f_44, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.32/1.54  tff(f_85, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 3.32/1.54  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.32/1.54  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.32/1.54  tff(f_38, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.32/1.54  tff(f_53, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 3.32/1.54  tff(f_115, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 3.32/1.54  tff(c_52, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.32/1.54  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.32/1.54  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.32/1.54  tff(c_34, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.32/1.54  tff(c_38, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.32/1.54  tff(c_26, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.32/1.54  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.32/1.54  tff(c_44, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.32/1.54  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.32/1.54  tff(c_32, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.32/1.54  tff(c_30, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.32/1.54  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.32/1.54  tff(c_80, plain, (![A_121, B_122, C_123, D_124]: (k2_partfun1(A_121, B_122, C_123, D_124)=k7_relat_1(C_123, D_124) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))) | ~v1_funct_1(C_123))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.32/1.54  tff(c_82, plain, (![D_124]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_124)=k7_relat_1('#skF_5', D_124) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_28, c_80])).
% 3.32/1.54  tff(c_85, plain, (![D_124]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_124)=k7_relat_1('#skF_5', D_124))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_82])).
% 3.32/1.54  tff(c_376, plain, (![D_231, C_230, E_234, B_233, A_232]: (k3_tmap_1(A_232, B_233, C_230, D_231, E_234)=k2_partfun1(u1_struct_0(C_230), u1_struct_0(B_233), E_234, u1_struct_0(D_231)) | ~m1_pre_topc(D_231, C_230) | ~m1_subset_1(E_234, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_230), u1_struct_0(B_233)))) | ~v1_funct_2(E_234, u1_struct_0(C_230), u1_struct_0(B_233)) | ~v1_funct_1(E_234) | ~m1_pre_topc(D_231, A_232) | ~m1_pre_topc(C_230, A_232) | ~l1_pre_topc(B_233) | ~v2_pre_topc(B_233) | v2_struct_0(B_233) | ~l1_pre_topc(A_232) | ~v2_pre_topc(A_232) | v2_struct_0(A_232))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.32/1.54  tff(c_380, plain, (![A_232, D_231]: (k3_tmap_1(A_232, '#skF_2', '#skF_4', D_231, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_231)) | ~m1_pre_topc(D_231, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_231, A_232) | ~m1_pre_topc('#skF_4', A_232) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_232) | ~v2_pre_topc(A_232) | v2_struct_0(A_232))), inference(resolution, [status(thm)], [c_28, c_376])).
% 3.32/1.54  tff(c_384, plain, (![D_231, A_232]: (k7_relat_1('#skF_5', u1_struct_0(D_231))=k3_tmap_1(A_232, '#skF_2', '#skF_4', D_231, '#skF_5') | ~m1_pre_topc(D_231, '#skF_4') | ~m1_pre_topc(D_231, A_232) | ~m1_pre_topc('#skF_4', A_232) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_232) | ~v2_pre_topc(A_232) | v2_struct_0(A_232))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_32, c_30, c_85, c_380])).
% 3.32/1.54  tff(c_386, plain, (![D_235, A_236]: (k7_relat_1('#skF_5', u1_struct_0(D_235))=k3_tmap_1(A_236, '#skF_2', '#skF_4', D_235, '#skF_5') | ~m1_pre_topc(D_235, '#skF_4') | ~m1_pre_topc(D_235, A_236) | ~m1_pre_topc('#skF_4', A_236) | ~l1_pre_topc(A_236) | ~v2_pre_topc(A_236) | v2_struct_0(A_236))), inference(negUnitSimplification, [status(thm)], [c_46, c_384])).
% 3.32/1.54  tff(c_392, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_386])).
% 3.32/1.54  tff(c_403, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_34, c_26, c_392])).
% 3.32/1.54  tff(c_404, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_403])).
% 3.32/1.54  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.32/1.54  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.32/1.54  tff(c_62, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_28, c_2])).
% 3.32/1.54  tff(c_65, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_62])).
% 3.32/1.54  tff(c_66, plain, (![A_116, B_117, C_118, D_119]: (k8_relset_1(A_116, B_117, C_118, D_119)=k10_relat_1(C_118, D_119) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.32/1.54  tff(c_69, plain, (![D_119]: (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_119)=k10_relat_1('#skF_5', D_119))), inference(resolution, [status(thm)], [c_28, c_66])).
% 3.32/1.54  tff(c_22, plain, (r1_tarski(k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.32/1.54  tff(c_70, plain, (r1_tarski(k10_relat_1('#skF_5', '#skF_6'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_22])).
% 3.32/1.54  tff(c_86, plain, (![A_125, B_126, C_127]: (k10_relat_1(k7_relat_1(A_125, B_126), C_127)=k10_relat_1(A_125, C_127) | ~r1_tarski(k10_relat_1(A_125, C_127), B_126) | ~v1_funct_1(A_125) | ~v1_relat_1(A_125))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.32/1.54  tff(c_89, plain, (k10_relat_1(k7_relat_1('#skF_5', u1_struct_0('#skF_3')), '#skF_6')=k10_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_70, c_86])).
% 3.32/1.54  tff(c_92, plain, (k10_relat_1(k7_relat_1('#skF_5', u1_struct_0('#skF_3')), '#skF_6')=k10_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_32, c_89])).
% 3.32/1.54  tff(c_409, plain, (k10_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')=k10_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_404, c_92])).
% 3.32/1.54  tff(c_346, plain, (![B_221, E_218, C_220, D_222, A_219]: (m1_subset_1(k3_tmap_1(A_219, B_221, C_220, D_222, E_218), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_222), u1_struct_0(B_221)))) | ~m1_subset_1(E_218, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_220), u1_struct_0(B_221)))) | ~v1_funct_2(E_218, u1_struct_0(C_220), u1_struct_0(B_221)) | ~v1_funct_1(E_218) | ~m1_pre_topc(D_222, A_219) | ~m1_pre_topc(C_220, A_219) | ~l1_pre_topc(B_221) | ~v2_pre_topc(B_221) | v2_struct_0(B_221) | ~l1_pre_topc(A_219) | ~v2_pre_topc(A_219) | v2_struct_0(A_219))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.32/1.54  tff(c_6, plain, (![A_6, B_7, C_8, D_9]: (k8_relset_1(A_6, B_7, C_8, D_9)=k10_relat_1(C_8, D_9) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.32/1.54  tff(c_424, plain, (![E_241, D_239, D_238, B_242, A_237, C_240]: (k8_relset_1(u1_struct_0(D_238), u1_struct_0(B_242), k3_tmap_1(A_237, B_242, C_240, D_238, E_241), D_239)=k10_relat_1(k3_tmap_1(A_237, B_242, C_240, D_238, E_241), D_239) | ~m1_subset_1(E_241, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_240), u1_struct_0(B_242)))) | ~v1_funct_2(E_241, u1_struct_0(C_240), u1_struct_0(B_242)) | ~v1_funct_1(E_241) | ~m1_pre_topc(D_238, A_237) | ~m1_pre_topc(C_240, A_237) | ~l1_pre_topc(B_242) | ~v2_pre_topc(B_242) | v2_struct_0(B_242) | ~l1_pre_topc(A_237) | ~v2_pre_topc(A_237) | v2_struct_0(A_237))), inference(resolution, [status(thm)], [c_346, c_6])).
% 3.32/1.54  tff(c_428, plain, (![D_238, A_237, D_239]: (k8_relset_1(u1_struct_0(D_238), u1_struct_0('#skF_2'), k3_tmap_1(A_237, '#skF_2', '#skF_4', D_238, '#skF_5'), D_239)=k10_relat_1(k3_tmap_1(A_237, '#skF_2', '#skF_4', D_238, '#skF_5'), D_239) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_238, A_237) | ~m1_pre_topc('#skF_4', A_237) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_237) | ~v2_pre_topc(A_237) | v2_struct_0(A_237))), inference(resolution, [status(thm)], [c_28, c_424])).
% 3.32/1.54  tff(c_432, plain, (![D_238, A_237, D_239]: (k8_relset_1(u1_struct_0(D_238), u1_struct_0('#skF_2'), k3_tmap_1(A_237, '#skF_2', '#skF_4', D_238, '#skF_5'), D_239)=k10_relat_1(k3_tmap_1(A_237, '#skF_2', '#skF_4', D_238, '#skF_5'), D_239) | ~m1_pre_topc(D_238, A_237) | ~m1_pre_topc('#skF_4', A_237) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_237) | ~v2_pre_topc(A_237) | v2_struct_0(A_237))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_32, c_30, c_428])).
% 3.32/1.54  tff(c_447, plain, (![D_244, A_245, D_246]: (k8_relset_1(u1_struct_0(D_244), u1_struct_0('#skF_2'), k3_tmap_1(A_245, '#skF_2', '#skF_4', D_244, '#skF_5'), D_246)=k10_relat_1(k3_tmap_1(A_245, '#skF_2', '#skF_4', D_244, '#skF_5'), D_246) | ~m1_pre_topc(D_244, A_245) | ~m1_pre_topc('#skF_4', A_245) | ~l1_pre_topc(A_245) | ~v2_pre_topc(A_245) | v2_struct_0(A_245))), inference(negUnitSimplification, [status(thm)], [c_46, c_432])).
% 3.32/1.54  tff(c_20, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.32/1.54  tff(c_110, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k10_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_20])).
% 3.32/1.54  tff(c_453, plain, (k10_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k10_relat_1('#skF_5', '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_447, c_110])).
% 3.32/1.54  tff(c_459, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_34, c_38, c_409, c_453])).
% 3.32/1.54  tff(c_461, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_459])).
% 3.32/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.54  
% 3.32/1.54  Inference rules
% 3.32/1.54  ----------------------
% 3.32/1.54  #Ref     : 0
% 3.32/1.54  #Sup     : 81
% 3.32/1.54  #Fact    : 0
% 3.32/1.54  #Define  : 0
% 3.32/1.54  #Split   : 4
% 3.32/1.54  #Chain   : 0
% 3.32/1.54  #Close   : 0
% 3.32/1.54  
% 3.32/1.54  Ordering : KBO
% 3.32/1.54  
% 3.32/1.54  Simplification rules
% 3.32/1.54  ----------------------
% 3.32/1.54  #Subsume      : 1
% 3.32/1.54  #Demod        : 123
% 3.32/1.54  #Tautology    : 21
% 3.32/1.54  #SimpNegUnit  : 26
% 3.32/1.54  #BackRed      : 11
% 3.32/1.54  
% 3.32/1.54  #Partial instantiations: 0
% 3.32/1.54  #Strategies tried      : 1
% 3.32/1.54  
% 3.32/1.54  Timing (in seconds)
% 3.32/1.54  ----------------------
% 3.37/1.55  Preprocessing        : 0.38
% 3.37/1.55  Parsing              : 0.20
% 3.37/1.55  CNF conversion       : 0.04
% 3.37/1.55  Main loop            : 0.34
% 3.37/1.55  Inferencing          : 0.13
% 3.37/1.55  Reduction            : 0.10
% 3.37/1.55  Demodulation         : 0.07
% 3.37/1.55  BG Simplification    : 0.02
% 3.37/1.55  Subsumption          : 0.06
% 3.37/1.55  Abstraction          : 0.02
% 3.37/1.55  MUC search           : 0.00
% 3.37/1.55  Cooper               : 0.00
% 3.37/1.55  Total                : 0.75
% 3.37/1.55  Index Insertion      : 0.00
% 3.37/1.55  Index Deletion       : 0.00
% 3.37/1.55  Index Matching       : 0.00
% 3.37/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
