%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:58 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 328 expanded)
%              Number of leaves         :   40 ( 141 expanded)
%              Depth                    :   13
%              Number of atoms          :  205 (1727 expanded)
%              Number of equality atoms :   39 ( 198 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

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

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_47,axiom,(
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
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_123,axiom,(
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

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(C,A)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | ( v1_funct_1(k2_partfun1(A,B,D,C))
            & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
            & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_78,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_48,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_38,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_6,plain,(
    ! [C_8,A_6,B_7] :
      ( v1_relat_1(C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_70,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_6])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_60,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_58,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_44,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_94,plain,(
    ! [A_86,B_87,C_88,D_89] :
      ( k2_partfun1(A_86,B_87,C_88,D_89) = k7_relat_1(C_88,D_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ v1_funct_1(C_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_96,plain,(
    ! [D_89] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_89) = k7_relat_1('#skF_4',D_89)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_94])).

tff(c_99,plain,(
    ! [D_89] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_89) = k7_relat_1('#skF_4',D_89) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_96])).

tff(c_290,plain,(
    ! [A_128,B_129,C_130,D_131] :
      ( k2_partfun1(u1_struct_0(A_128),u1_struct_0(B_129),C_130,u1_struct_0(D_131)) = k2_tmap_1(A_128,B_129,C_130,D_131)
      | ~ m1_pre_topc(D_131,A_128)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_128),u1_struct_0(B_129))))
      | ~ v1_funct_2(C_130,u1_struct_0(A_128),u1_struct_0(B_129))
      | ~ v1_funct_1(C_130)
      | ~ l1_pre_topc(B_129)
      | ~ v2_pre_topc(B_129)
      | v2_struct_0(B_129)
      | ~ l1_pre_topc(A_128)
      | ~ v2_pre_topc(A_128)
      | v2_struct_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_301,plain,(
    ! [D_131] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_131)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_131)
      | ~ m1_pre_topc(D_131,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_290])).

tff(c_310,plain,(
    ! [D_131] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_131)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_131)
      | ~ m1_pre_topc(D_131,'#skF_2')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_60,c_58,c_46,c_44,c_99,c_301])).

tff(c_321,plain,(
    ! [D_134] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_134)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_134)
      | ~ m1_pre_topc(D_134,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_62,c_310])).

tff(c_4,plain,(
    ! [A_1,C_5,B_4] :
      ( k9_relat_1(k7_relat_1(A_1,C_5),B_4) = k9_relat_1(A_1,B_4)
      | ~ r1_tarski(B_4,C_5)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_339,plain,(
    ! [D_134,B_4] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_134),B_4) = k9_relat_1('#skF_4',B_4)
      | ~ r1_tarski(B_4,u1_struct_0(D_134))
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(D_134,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_4])).

tff(c_365,plain,(
    ! [D_139,B_140] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_139),B_140) = k9_relat_1('#skF_4',B_140)
      | ~ r1_tarski(B_140,u1_struct_0(D_139))
      | ~ m1_pre_topc(D_139,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_339])).

tff(c_374,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_365])).

tff(c_381,plain,(
    k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_374])).

tff(c_311,plain,(
    ! [D_131] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_131)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_131)
      | ~ m1_pre_topc(D_131,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_62,c_310])).

tff(c_30,plain,(
    ! [A_38] :
      ( m1_pre_topc(A_38,A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_110,plain,(
    ! [B_94,C_95,A_96] :
      ( r1_tarski(u1_struct_0(B_94),u1_struct_0(C_95))
      | ~ m1_pre_topc(B_94,C_95)
      | ~ m1_pre_topc(C_95,A_96)
      | ~ m1_pre_topc(B_94,A_96)
      | ~ l1_pre_topc(A_96)
      | ~ v2_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_115,plain,(
    ! [B_94,A_38] :
      ( r1_tarski(u1_struct_0(B_94),u1_struct_0(A_38))
      | ~ m1_pre_topc(B_94,A_38)
      | ~ v2_pre_topc(A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(resolution,[status(thm)],[c_30,c_110])).

tff(c_24,plain,(
    ! [A_21] :
      ( l1_struct_0(A_21)
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_128,plain,(
    ! [B_103,A_104,D_105,C_106] :
      ( k1_xboole_0 = B_103
      | v1_funct_1(k2_partfun1(A_104,B_103,D_105,C_106))
      | ~ r1_tarski(C_106,A_104)
      | ~ m1_subset_1(D_105,k1_zfmisc_1(k2_zfmisc_1(A_104,B_103)))
      | ~ v1_funct_2(D_105,A_104,B_103)
      | ~ v1_funct_1(D_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_130,plain,(
    ! [C_106] :
      ( u1_struct_0('#skF_1') = k1_xboole_0
      | v1_funct_1(k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',C_106))
      | ~ r1_tarski(C_106,u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_128])).

tff(c_133,plain,(
    ! [C_106] :
      ( u1_struct_0('#skF_1') = k1_xboole_0
      | v1_funct_1(k7_relat_1('#skF_4',C_106))
      | ~ r1_tarski(C_106,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_99,c_130])).

tff(c_134,plain,(
    u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_26,plain,(
    ! [A_22] :
      ( ~ v1_xboole_0(u1_struct_0(A_22))
      | ~ l1_struct_0(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_156,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_26])).

tff(c_162,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_156])).

tff(c_163,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_162])).

tff(c_167,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_163])).

tff(c_171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_167])).

tff(c_173,plain,(
    u1_struct_0('#skF_1') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_222,plain,(
    ! [B_123,A_124,D_125,C_126] :
      ( k1_xboole_0 = B_123
      | m1_subset_1(k2_partfun1(A_124,B_123,D_125,C_126),k1_zfmisc_1(k2_zfmisc_1(C_126,B_123)))
      | ~ r1_tarski(C_126,A_124)
      | ~ m1_subset_1(D_125,k1_zfmisc_1(k2_zfmisc_1(A_124,B_123)))
      | ~ v1_funct_2(D_125,A_124,B_123)
      | ~ v1_funct_1(D_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_245,plain,(
    ! [D_89] :
      ( u1_struct_0('#skF_1') = k1_xboole_0
      | m1_subset_1(k7_relat_1('#skF_4',D_89),k1_zfmisc_1(k2_zfmisc_1(D_89,u1_struct_0('#skF_1'))))
      | ~ r1_tarski(D_89,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_222])).

tff(c_255,plain,(
    ! [D_89] :
      ( u1_struct_0('#skF_1') = k1_xboole_0
      | m1_subset_1(k7_relat_1('#skF_4',D_89),k1_zfmisc_1(k2_zfmisc_1(D_89,u1_struct_0('#skF_1'))))
      | ~ r1_tarski(D_89,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_245])).

tff(c_257,plain,(
    ! [D_127] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_127),k1_zfmisc_1(k2_zfmisc_1(D_127,u1_struct_0('#skF_1'))))
      | ~ r1_tarski(D_127,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_255])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11,D_12] :
      ( k7_relset_1(A_9,B_10,C_11,D_12) = k9_relat_1(C_11,D_12)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_386,plain,(
    ! [D_141,D_142] :
      ( k7_relset_1(D_141,u1_struct_0('#skF_1'),k7_relat_1('#skF_4',D_141),D_142) = k9_relat_1(k7_relat_1('#skF_4',D_141),D_142)
      | ~ r1_tarski(D_141,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_257,c_8])).

tff(c_528,plain,(
    ! [D_158,D_159] :
      ( k7_relset_1(u1_struct_0(D_158),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4',D_158),D_159) = k9_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_158)),D_159)
      | ~ r1_tarski(u1_struct_0(D_158),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_158,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_386])).

tff(c_80,plain,(
    ! [A_81,B_82,C_83,D_84] :
      ( k7_relset_1(A_81,B_82,C_83,D_84) = k9_relat_1(C_83,D_84)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_83,plain,(
    ! [D_84] : k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_84) = k9_relat_1('#skF_4',D_84) ),
    inference(resolution,[status(thm)],[c_42,c_80])).

tff(c_36,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_84,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_36])).

tff(c_534,plain,
    ( k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_528,c_84])).

tff(c_540,plain,
    ( k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_534])).

tff(c_555,plain,(
    ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_540])).

tff(c_558,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_115,c_555])).

tff(c_562,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_54,c_48,c_558])).

tff(c_563,plain,(
    k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_540])).

tff(c_613,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_563])).

tff(c_619,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_381,c_613])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:27:17 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.46  
% 3.14/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.46  %$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.14/1.46  
% 3.14/1.46  %Foreground sorts:
% 3.14/1.46  
% 3.14/1.46  
% 3.14/1.46  %Background operators:
% 3.14/1.46  
% 3.14/1.46  
% 3.14/1.46  %Foreground operators:
% 3.14/1.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.14/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.14/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.46  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.14/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.14/1.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.14/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.46  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.14/1.46  tff('#skF_5', type, '#skF_5': $i).
% 3.14/1.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.14/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.14/1.46  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.14/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.14/1.46  tff('#skF_1', type, '#skF_1': $i).
% 3.14/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.14/1.46  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.14/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.14/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.14/1.46  tff('#skF_4', type, '#skF_4': $i).
% 3.14/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.46  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.14/1.46  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.14/1.46  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.14/1.46  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.14/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.14/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.14/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.14/1.46  
% 3.28/1.48  tff(f_159, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (r1_tarski(E, u1_struct_0(C)) => (k7_relset_1(u1_struct_0(B), u1_struct_0(A), D, E) = k7_relset_1(u1_struct_0(C), u1_struct_0(A), k2_tmap_1(B, A, D, C), E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_tmap_1)).
% 3.28/1.48  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.28/1.48  tff(f_47, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.28/1.48  tff(f_105, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.28/1.48  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 3.28/1.48  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 3.28/1.48  tff(f_123, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 3.28/1.48  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.28/1.48  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.28/1.48  tff(f_66, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 3.28/1.48  tff(f_78, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.28/1.48  tff(f_41, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.28/1.48  tff(c_48, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.28/1.48  tff(c_38, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.28/1.48  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.28/1.48  tff(c_6, plain, (![C_8, A_6, B_7]: (v1_relat_1(C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.28/1.48  tff(c_70, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_6])).
% 3.28/1.48  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.28/1.48  tff(c_62, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.28/1.48  tff(c_54, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.28/1.48  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.28/1.48  tff(c_60, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.28/1.48  tff(c_58, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.28/1.48  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.28/1.48  tff(c_44, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.28/1.48  tff(c_94, plain, (![A_86, B_87, C_88, D_89]: (k2_partfun1(A_86, B_87, C_88, D_89)=k7_relat_1(C_88, D_89) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~v1_funct_1(C_88))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.28/1.48  tff(c_96, plain, (![D_89]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_89)=k7_relat_1('#skF_4', D_89) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_94])).
% 3.28/1.48  tff(c_99, plain, (![D_89]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_89)=k7_relat_1('#skF_4', D_89))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_96])).
% 3.28/1.48  tff(c_290, plain, (![A_128, B_129, C_130, D_131]: (k2_partfun1(u1_struct_0(A_128), u1_struct_0(B_129), C_130, u1_struct_0(D_131))=k2_tmap_1(A_128, B_129, C_130, D_131) | ~m1_pre_topc(D_131, A_128) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_128), u1_struct_0(B_129)))) | ~v1_funct_2(C_130, u1_struct_0(A_128), u1_struct_0(B_129)) | ~v1_funct_1(C_130) | ~l1_pre_topc(B_129) | ~v2_pre_topc(B_129) | v2_struct_0(B_129) | ~l1_pre_topc(A_128) | ~v2_pre_topc(A_128) | v2_struct_0(A_128))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.28/1.48  tff(c_301, plain, (![D_131]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_131))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_131) | ~m1_pre_topc(D_131, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_290])).
% 3.28/1.48  tff(c_310, plain, (![D_131]: (k7_relat_1('#skF_4', u1_struct_0(D_131))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_131) | ~m1_pre_topc(D_131, '#skF_2') | v2_struct_0('#skF_1') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_60, c_58, c_46, c_44, c_99, c_301])).
% 3.28/1.48  tff(c_321, plain, (![D_134]: (k7_relat_1('#skF_4', u1_struct_0(D_134))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_134) | ~m1_pre_topc(D_134, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_62, c_310])).
% 3.28/1.48  tff(c_4, plain, (![A_1, C_5, B_4]: (k9_relat_1(k7_relat_1(A_1, C_5), B_4)=k9_relat_1(A_1, B_4) | ~r1_tarski(B_4, C_5) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.28/1.48  tff(c_339, plain, (![D_134, B_4]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_134), B_4)=k9_relat_1('#skF_4', B_4) | ~r1_tarski(B_4, u1_struct_0(D_134)) | ~v1_relat_1('#skF_4') | ~m1_pre_topc(D_134, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_321, c_4])).
% 3.28/1.48  tff(c_365, plain, (![D_139, B_140]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_139), B_140)=k9_relat_1('#skF_4', B_140) | ~r1_tarski(B_140, u1_struct_0(D_139)) | ~m1_pre_topc(D_139, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_339])).
% 3.28/1.48  tff(c_374, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_365])).
% 3.28/1.48  tff(c_381, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_374])).
% 3.28/1.48  tff(c_311, plain, (![D_131]: (k7_relat_1('#skF_4', u1_struct_0(D_131))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_131) | ~m1_pre_topc(D_131, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_62, c_310])).
% 3.28/1.48  tff(c_30, plain, (![A_38]: (m1_pre_topc(A_38, A_38) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.28/1.48  tff(c_110, plain, (![B_94, C_95, A_96]: (r1_tarski(u1_struct_0(B_94), u1_struct_0(C_95)) | ~m1_pre_topc(B_94, C_95) | ~m1_pre_topc(C_95, A_96) | ~m1_pre_topc(B_94, A_96) | ~l1_pre_topc(A_96) | ~v2_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.28/1.48  tff(c_115, plain, (![B_94, A_38]: (r1_tarski(u1_struct_0(B_94), u1_struct_0(A_38)) | ~m1_pre_topc(B_94, A_38) | ~v2_pre_topc(A_38) | ~l1_pre_topc(A_38))), inference(resolution, [status(thm)], [c_30, c_110])).
% 3.28/1.48  tff(c_24, plain, (![A_21]: (l1_struct_0(A_21) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.28/1.48  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.28/1.48  tff(c_128, plain, (![B_103, A_104, D_105, C_106]: (k1_xboole_0=B_103 | v1_funct_1(k2_partfun1(A_104, B_103, D_105, C_106)) | ~r1_tarski(C_106, A_104) | ~m1_subset_1(D_105, k1_zfmisc_1(k2_zfmisc_1(A_104, B_103))) | ~v1_funct_2(D_105, A_104, B_103) | ~v1_funct_1(D_105))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.28/1.48  tff(c_130, plain, (![C_106]: (u1_struct_0('#skF_1')=k1_xboole_0 | v1_funct_1(k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', C_106)) | ~r1_tarski(C_106, u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_128])).
% 3.28/1.48  tff(c_133, plain, (![C_106]: (u1_struct_0('#skF_1')=k1_xboole_0 | v1_funct_1(k7_relat_1('#skF_4', C_106)) | ~r1_tarski(C_106, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_99, c_130])).
% 3.28/1.48  tff(c_134, plain, (u1_struct_0('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_133])).
% 3.28/1.48  tff(c_26, plain, (![A_22]: (~v1_xboole_0(u1_struct_0(A_22)) | ~l1_struct_0(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.28/1.48  tff(c_156, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_134, c_26])).
% 3.28/1.48  tff(c_162, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_156])).
% 3.28/1.48  tff(c_163, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_62, c_162])).
% 3.28/1.48  tff(c_167, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_163])).
% 3.28/1.48  tff(c_171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_167])).
% 3.28/1.48  tff(c_173, plain, (u1_struct_0('#skF_1')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_133])).
% 3.28/1.48  tff(c_222, plain, (![B_123, A_124, D_125, C_126]: (k1_xboole_0=B_123 | m1_subset_1(k2_partfun1(A_124, B_123, D_125, C_126), k1_zfmisc_1(k2_zfmisc_1(C_126, B_123))) | ~r1_tarski(C_126, A_124) | ~m1_subset_1(D_125, k1_zfmisc_1(k2_zfmisc_1(A_124, B_123))) | ~v1_funct_2(D_125, A_124, B_123) | ~v1_funct_1(D_125))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.28/1.48  tff(c_245, plain, (![D_89]: (u1_struct_0('#skF_1')=k1_xboole_0 | m1_subset_1(k7_relat_1('#skF_4', D_89), k1_zfmisc_1(k2_zfmisc_1(D_89, u1_struct_0('#skF_1')))) | ~r1_tarski(D_89, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_99, c_222])).
% 3.28/1.48  tff(c_255, plain, (![D_89]: (u1_struct_0('#skF_1')=k1_xboole_0 | m1_subset_1(k7_relat_1('#skF_4', D_89), k1_zfmisc_1(k2_zfmisc_1(D_89, u1_struct_0('#skF_1')))) | ~r1_tarski(D_89, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_245])).
% 3.28/1.48  tff(c_257, plain, (![D_127]: (m1_subset_1(k7_relat_1('#skF_4', D_127), k1_zfmisc_1(k2_zfmisc_1(D_127, u1_struct_0('#skF_1')))) | ~r1_tarski(D_127, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_173, c_255])).
% 3.28/1.48  tff(c_8, plain, (![A_9, B_10, C_11, D_12]: (k7_relset_1(A_9, B_10, C_11, D_12)=k9_relat_1(C_11, D_12) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.28/1.48  tff(c_386, plain, (![D_141, D_142]: (k7_relset_1(D_141, u1_struct_0('#skF_1'), k7_relat_1('#skF_4', D_141), D_142)=k9_relat_1(k7_relat_1('#skF_4', D_141), D_142) | ~r1_tarski(D_141, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_257, c_8])).
% 3.28/1.48  tff(c_528, plain, (![D_158, D_159]: (k7_relset_1(u1_struct_0(D_158), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_158), D_159)=k9_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_158)), D_159) | ~r1_tarski(u1_struct_0(D_158), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_158, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_311, c_386])).
% 3.28/1.48  tff(c_80, plain, (![A_81, B_82, C_83, D_84]: (k7_relset_1(A_81, B_82, C_83, D_84)=k9_relat_1(C_83, D_84) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.28/1.48  tff(c_83, plain, (![D_84]: (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_84)=k9_relat_1('#skF_4', D_84))), inference(resolution, [status(thm)], [c_42, c_80])).
% 3.28/1.48  tff(c_36, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.28/1.48  tff(c_84, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_36])).
% 3.28/1.48  tff(c_534, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_528, c_84])).
% 3.28/1.48  tff(c_540, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_534])).
% 3.28/1.48  tff(c_555, plain, (~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_540])).
% 3.28/1.48  tff(c_558, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_115, c_555])).
% 3.28/1.48  tff(c_562, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_54, c_48, c_558])).
% 3.28/1.48  tff(c_563, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_540])).
% 3.28/1.48  tff(c_613, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_311, c_563])).
% 3.28/1.48  tff(c_619, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_381, c_613])).
% 3.28/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.48  
% 3.28/1.48  Inference rules
% 3.28/1.48  ----------------------
% 3.28/1.48  #Ref     : 0
% 3.28/1.48  #Sup     : 122
% 3.28/1.48  #Fact    : 0
% 3.28/1.48  #Define  : 0
% 3.28/1.48  #Split   : 2
% 3.28/1.48  #Chain   : 0
% 3.28/1.48  #Close   : 0
% 3.28/1.48  
% 3.28/1.48  Ordering : KBO
% 3.28/1.48  
% 3.28/1.48  Simplification rules
% 3.28/1.48  ----------------------
% 3.28/1.48  #Subsume      : 3
% 3.28/1.48  #Demod        : 56
% 3.28/1.48  #Tautology    : 33
% 3.28/1.48  #SimpNegUnit  : 17
% 3.28/1.48  #BackRed      : 6
% 3.28/1.48  
% 3.28/1.48  #Partial instantiations: 0
% 3.28/1.48  #Strategies tried      : 1
% 3.28/1.48  
% 3.28/1.48  Timing (in seconds)
% 3.28/1.48  ----------------------
% 3.28/1.49  Preprocessing        : 0.36
% 3.28/1.49  Parsing              : 0.19
% 3.28/1.49  CNF conversion       : 0.03
% 3.28/1.49  Main loop            : 0.37
% 3.28/1.49  Inferencing          : 0.13
% 3.28/1.49  Reduction            : 0.11
% 3.28/1.49  Demodulation         : 0.08
% 3.28/1.49  BG Simplification    : 0.03
% 3.28/1.49  Subsumption          : 0.07
% 3.28/1.49  Abstraction          : 0.02
% 3.28/1.49  MUC search           : 0.00
% 3.28/1.49  Cooper               : 0.00
% 3.28/1.49  Total                : 0.76
% 3.28/1.49  Index Insertion      : 0.00
% 3.28/1.49  Index Deletion       : 0.00
% 3.28/1.49  Index Matching       : 0.00
% 3.28/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
