%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:51 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :  123 (2823 expanded)
%              Number of leaves         :   45 ( 996 expanded)
%              Depth                    :   24
%              Number of atoms          :  284 (12958 expanded)
%              Number of equality atoms :   27 ( 753 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

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

tff(r1_funct_2,type,(
    r1_funct_2: ( $i * $i * $i * $i * $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_195,negated_conjecture,(
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
                   => ( g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                     => r1_funct_2(u1_struct_0(B),u1_struct_0(A),u1_struct_0(C),u1_struct_0(A),D,k2_tmap_1(B,A,D,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_tmap_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_148,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_162,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_117,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(B)
        & ~ v1_xboole_0(D)
        & v1_funct_1(E)
        & v1_funct_2(E,A,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,C,D)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => r1_funct_2(A,B,C,D,E,E) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).

tff(f_81,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_144,axiom,(
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

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(c_62,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_20,plain,(
    ! [A_18] :
      ( l1_struct_0(A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_56,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_52,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_72,plain,(
    ! [B_73,A_74] :
      ( l1_pre_topc(B_73)
      | ~ m1_pre_topc(B_73,A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_78,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_72])).

tff(c_82,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_78])).

tff(c_44,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_149,plain,(
    ! [A_93,B_94] :
      ( m1_pre_topc(A_93,g1_pre_topc(u1_struct_0(B_94),u1_pre_topc(B_94)))
      | ~ m1_pre_topc(A_93,B_94)
      | ~ l1_pre_topc(B_94)
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_165,plain,(
    ! [A_93] :
      ( m1_pre_topc(A_93,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_93,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_149])).

tff(c_210,plain,(
    ! [A_102] :
      ( m1_pre_topc(A_102,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_102,'#skF_2')
      | ~ l1_pre_topc(A_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_165])).

tff(c_26,plain,(
    ! [B_25,A_23] :
      ( m1_pre_topc(B_25,A_23)
      | ~ m1_pre_topc(B_25,g1_pre_topc(u1_struct_0(A_23),u1_pre_topc(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_216,plain,(
    ! [A_102] :
      ( m1_pre_topc(A_102,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc(A_102,'#skF_2')
      | ~ l1_pre_topc(A_102) ) ),
    inference(resolution,[status(thm)],[c_210,c_26])).

tff(c_229,plain,(
    ! [A_103] :
      ( m1_pre_topc(A_103,'#skF_3')
      | ~ m1_pre_topc(A_103,'#skF_2')
      | ~ l1_pre_topc(A_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_216])).

tff(c_239,plain,
    ( m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_229])).

tff(c_246,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_239])).

tff(c_36,plain,(
    ! [A_50] :
      ( m1_pre_topc(A_50,A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_236,plain,
    ( m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_229])).

tff(c_243,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_236])).

tff(c_58,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_99,plain,(
    ! [B_80,A_81] :
      ( v2_pre_topc(B_80)
      | ~ m1_pre_topc(B_80,A_81)
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_105,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_99])).

tff(c_109,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_105])).

tff(c_327,plain,(
    ! [B_106,C_107,A_108] :
      ( r1_tarski(u1_struct_0(B_106),u1_struct_0(C_107))
      | ~ m1_pre_topc(B_106,C_107)
      | ~ m1_pre_topc(C_107,A_108)
      | ~ m1_pre_topc(B_106,A_108)
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_333,plain,(
    ! [B_106] :
      ( r1_tarski(u1_struct_0(B_106),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_106,'#skF_2')
      | ~ m1_pre_topc(B_106,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_243,c_327])).

tff(c_350,plain,(
    ! [B_106] :
      ( r1_tarski(u1_struct_0(B_106),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_106,'#skF_2')
      | ~ m1_pre_topc(B_106,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_82,c_333])).

tff(c_331,plain,(
    ! [B_106] :
      ( r1_tarski(u1_struct_0(B_106),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_106,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_246,c_327])).

tff(c_360,plain,(
    ! [B_109] :
      ( r1_tarski(u1_struct_0(B_109),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_109,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_82,c_331])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_368,plain,(
    ! [B_111] :
      ( u1_struct_0(B_111) = u1_struct_0('#skF_3')
      | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0(B_111))
      | ~ m1_pre_topc(B_111,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_360,c_2])).

tff(c_372,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_350,c_368])).

tff(c_383,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_52,c_243,c_372])).

tff(c_48,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_399,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_48])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_398,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_46])).

tff(c_576,plain,(
    ! [E_122,B_119,A_120,F_121,D_118,C_123] :
      ( r1_funct_2(A_120,B_119,C_123,D_118,E_122,E_122)
      | ~ m1_subset_1(F_121,k1_zfmisc_1(k2_zfmisc_1(C_123,D_118)))
      | ~ v1_funct_2(F_121,C_123,D_118)
      | ~ v1_funct_1(F_121)
      | ~ m1_subset_1(E_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_119)))
      | ~ v1_funct_2(E_122,A_120,B_119)
      | ~ v1_funct_1(E_122)
      | v1_xboole_0(D_118)
      | v1_xboole_0(B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_578,plain,(
    ! [A_120,B_119,E_122] :
      ( r1_funct_2(A_120,B_119,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),E_122,E_122)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_119)))
      | ~ v1_funct_2(E_122,A_120,B_119)
      | ~ v1_funct_1(E_122)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_119) ) ),
    inference(resolution,[status(thm)],[c_398,c_576])).

tff(c_581,plain,(
    ! [A_120,B_119,E_122] :
      ( r1_funct_2(A_120,B_119,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),E_122,E_122)
      | ~ m1_subset_1(E_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_119)))
      | ~ v1_funct_2(E_122,A_120,B_119)
      | ~ v1_funct_1(E_122)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_399,c_578])).

tff(c_1450,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_581])).

tff(c_24,plain,(
    ! [A_22] :
      ( ~ v1_xboole_0(u1_struct_0(A_22))
      | ~ l1_struct_0(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1453,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1450,c_24])).

tff(c_1456,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1453])).

tff(c_1459,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_1456])).

tff(c_1463,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1459])).

tff(c_1465,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_581])).

tff(c_1651,plain,(
    ! [A_185,B_186,E_187] :
      ( r1_funct_2(A_185,B_186,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),E_187,E_187)
      | ~ m1_subset_1(E_187,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186)))
      | ~ v1_funct_2(E_187,A_185,B_186)
      | ~ v1_funct_1(E_187)
      | v1_xboole_0(B_186) ) ),
    inference(splitRight,[status(thm)],[c_581])).

tff(c_64,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_174,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( k2_partfun1(A_95,B_96,C_97,D_98) = k7_relat_1(C_97,D_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96)))
      | ~ v1_funct_1(C_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_176,plain,(
    ! [D_98] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_98) = k7_relat_1('#skF_4',D_98)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_46,c_174])).

tff(c_179,plain,(
    ! [D_98] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_98) = k7_relat_1('#skF_4',D_98) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_176])).

tff(c_393,plain,(
    ! [D_98] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',D_98) = k7_relat_1('#skF_4',D_98) ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_179])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_670,plain,(
    ! [A_129,B_130,C_131,D_132] :
      ( k2_partfun1(u1_struct_0(A_129),u1_struct_0(B_130),C_131,u1_struct_0(D_132)) = k2_tmap_1(A_129,B_130,C_131,D_132)
      | ~ m1_pre_topc(D_132,A_129)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_129),u1_struct_0(B_130))))
      | ~ v1_funct_2(C_131,u1_struct_0(A_129),u1_struct_0(B_130))
      | ~ v1_funct_1(C_131)
      | ~ l1_pre_topc(B_130)
      | ~ v2_pre_topc(B_130)
      | v2_struct_0(B_130)
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129)
      | v2_struct_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_674,plain,(
    ! [B_130,C_131,D_132] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_130),C_131,u1_struct_0(D_132)) = k2_tmap_1('#skF_2',B_130,C_131,D_132)
      | ~ m1_pre_topc(D_132,'#skF_2')
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_130))))
      | ~ v1_funct_2(C_131,u1_struct_0('#skF_2'),u1_struct_0(B_130))
      | ~ v1_funct_1(C_131)
      | ~ l1_pre_topc(B_130)
      | ~ v2_pre_topc(B_130)
      | v2_struct_0(B_130)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_670])).

tff(c_682,plain,(
    ! [B_130,C_131,D_132] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_130),C_131,u1_struct_0(D_132)) = k2_tmap_1('#skF_2',B_130,C_131,D_132)
      | ~ m1_pre_topc(D_132,'#skF_2')
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_130))))
      | ~ v1_funct_2(C_131,u1_struct_0('#skF_3'),u1_struct_0(B_130))
      | ~ v1_funct_1(C_131)
      | ~ l1_pre_topc(B_130)
      | ~ v2_pre_topc(B_130)
      | v2_struct_0(B_130)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_383,c_383,c_674])).

tff(c_716,plain,(
    ! [B_134,C_135,D_136] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_134),C_135,u1_struct_0(D_136)) = k2_tmap_1('#skF_2',B_134,C_135,D_136)
      | ~ m1_pre_topc(D_136,'#skF_2')
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_134))))
      | ~ v1_funct_2(C_135,u1_struct_0('#skF_3'),u1_struct_0(B_134))
      | ~ v1_funct_1(C_135)
      | ~ l1_pre_topc(B_134)
      | ~ v2_pre_topc(B_134)
      | v2_struct_0(B_134) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_682])).

tff(c_718,plain,(
    ! [D_136] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_136)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_136)
      | ~ m1_pre_topc(D_136,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_398,c_716])).

tff(c_723,plain,(
    ! [D_136] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_136)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_136)
      | ~ m1_pre_topc(D_136,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_50,c_399,c_393,c_718])).

tff(c_732,plain,(
    ! [D_137] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_137)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_137)
      | ~ m1_pre_topc(D_137,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_723])).

tff(c_90,plain,(
    ! [C_77,A_78,B_79] :
      ( v1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_94,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_90])).

tff(c_116,plain,(
    ! [C_87,A_88,B_89] :
      ( v4_relat_1(C_87,A_88)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_120,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_116])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k7_relat_1(B_4,A_3) = B_4
      | ~ v4_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_123,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_120,c_8])).

tff(c_126,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_123])).

tff(c_395,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_126])).

tff(c_741,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_732,c_395])).

tff(c_756,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_741])).

tff(c_42,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_394,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_42])).

tff(c_762,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_756,c_394])).

tff(c_1654,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1651,c_762])).

tff(c_1657,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_399,c_398,c_1654])).

tff(c_1659,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1465,c_1657])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:43:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.60/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.57  
% 3.60/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.57  %$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.60/1.57  
% 3.60/1.57  %Foreground sorts:
% 3.60/1.57  
% 3.60/1.57  
% 3.60/1.57  %Background operators:
% 3.60/1.57  
% 3.60/1.57  
% 3.60/1.57  %Foreground operators:
% 3.60/1.57  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.60/1.57  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.60/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.60/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.60/1.57  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.60/1.57  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.60/1.57  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.60/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.60/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.60/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.60/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.60/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.60/1.57  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.60/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.60/1.57  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.60/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.60/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.60/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.60/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.60/1.57  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 3.60/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.60/1.57  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.60/1.57  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.60/1.57  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.60/1.57  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.60/1.57  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.60/1.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.60/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.60/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.60/1.57  
% 3.80/1.59  tff(f_195, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_tmap_1)).
% 3.80/1.59  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.80/1.59  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.80/1.59  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 3.80/1.59  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 3.80/1.59  tff(f_148, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 3.80/1.59  tff(f_62, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.80/1.59  tff(f_162, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 3.80/1.59  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.80/1.59  tff(f_117, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => r1_funct_2(A, B, C, D, E, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r1_funct_2)).
% 3.80/1.59  tff(f_81, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.80/1.59  tff(f_53, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.80/1.59  tff(f_144, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.80/1.59  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.80/1.59  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.80/1.59  tff(f_37, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.80/1.59  tff(c_62, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.80/1.59  tff(c_20, plain, (![A_18]: (l1_struct_0(A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.80/1.59  tff(c_66, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.80/1.59  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.80/1.59  tff(c_56, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.80/1.59  tff(c_52, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.80/1.59  tff(c_72, plain, (![B_73, A_74]: (l1_pre_topc(B_73) | ~m1_pre_topc(B_73, A_74) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.80/1.59  tff(c_78, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_72])).
% 3.80/1.59  tff(c_82, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_78])).
% 3.80/1.59  tff(c_44, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.80/1.59  tff(c_149, plain, (![A_93, B_94]: (m1_pre_topc(A_93, g1_pre_topc(u1_struct_0(B_94), u1_pre_topc(B_94))) | ~m1_pre_topc(A_93, B_94) | ~l1_pre_topc(B_94) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.80/1.59  tff(c_165, plain, (![A_93]: (m1_pre_topc(A_93, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_93, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_93))), inference(superposition, [status(thm), theory('equality')], [c_44, c_149])).
% 3.80/1.59  tff(c_210, plain, (![A_102]: (m1_pre_topc(A_102, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_102, '#skF_2') | ~l1_pre_topc(A_102))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_165])).
% 3.80/1.59  tff(c_26, plain, (![B_25, A_23]: (m1_pre_topc(B_25, A_23) | ~m1_pre_topc(B_25, g1_pre_topc(u1_struct_0(A_23), u1_pre_topc(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.80/1.59  tff(c_216, plain, (![A_102]: (m1_pre_topc(A_102, '#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(A_102, '#skF_2') | ~l1_pre_topc(A_102))), inference(resolution, [status(thm)], [c_210, c_26])).
% 3.80/1.59  tff(c_229, plain, (![A_103]: (m1_pre_topc(A_103, '#skF_3') | ~m1_pre_topc(A_103, '#skF_2') | ~l1_pre_topc(A_103))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_216])).
% 3.80/1.59  tff(c_239, plain, (m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_52, c_229])).
% 3.80/1.59  tff(c_246, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_239])).
% 3.80/1.59  tff(c_36, plain, (![A_50]: (m1_pre_topc(A_50, A_50) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.80/1.59  tff(c_236, plain, (m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_36, c_229])).
% 3.80/1.59  tff(c_243, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_236])).
% 3.80/1.59  tff(c_58, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.80/1.59  tff(c_99, plain, (![B_80, A_81]: (v2_pre_topc(B_80) | ~m1_pre_topc(B_80, A_81) | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.80/1.59  tff(c_105, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_99])).
% 3.80/1.59  tff(c_109, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_105])).
% 3.80/1.59  tff(c_327, plain, (![B_106, C_107, A_108]: (r1_tarski(u1_struct_0(B_106), u1_struct_0(C_107)) | ~m1_pre_topc(B_106, C_107) | ~m1_pre_topc(C_107, A_108) | ~m1_pre_topc(B_106, A_108) | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.80/1.59  tff(c_333, plain, (![B_106]: (r1_tarski(u1_struct_0(B_106), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_106, '#skF_2') | ~m1_pre_topc(B_106, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_243, c_327])).
% 3.80/1.59  tff(c_350, plain, (![B_106]: (r1_tarski(u1_struct_0(B_106), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_106, '#skF_2') | ~m1_pre_topc(B_106, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_82, c_333])).
% 3.80/1.59  tff(c_331, plain, (![B_106]: (r1_tarski(u1_struct_0(B_106), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_106, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_246, c_327])).
% 3.80/1.59  tff(c_360, plain, (![B_109]: (r1_tarski(u1_struct_0(B_109), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_109, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_82, c_331])).
% 3.80/1.59  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.80/1.59  tff(c_368, plain, (![B_111]: (u1_struct_0(B_111)=u1_struct_0('#skF_3') | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0(B_111)) | ~m1_pre_topc(B_111, '#skF_3'))), inference(resolution, [status(thm)], [c_360, c_2])).
% 3.80/1.59  tff(c_372, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_350, c_368])).
% 3.80/1.59  tff(c_383, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_246, c_52, c_243, c_372])).
% 3.80/1.59  tff(c_48, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.80/1.59  tff(c_399, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_383, c_48])).
% 3.80/1.59  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.80/1.59  tff(c_398, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_383, c_46])).
% 3.80/1.59  tff(c_576, plain, (![E_122, B_119, A_120, F_121, D_118, C_123]: (r1_funct_2(A_120, B_119, C_123, D_118, E_122, E_122) | ~m1_subset_1(F_121, k1_zfmisc_1(k2_zfmisc_1(C_123, D_118))) | ~v1_funct_2(F_121, C_123, D_118) | ~v1_funct_1(F_121) | ~m1_subset_1(E_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_119))) | ~v1_funct_2(E_122, A_120, B_119) | ~v1_funct_1(E_122) | v1_xboole_0(D_118) | v1_xboole_0(B_119))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.80/1.59  tff(c_578, plain, (![A_120, B_119, E_122]: (r1_funct_2(A_120, B_119, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), E_122, E_122) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_119))) | ~v1_funct_2(E_122, A_120, B_119) | ~v1_funct_1(E_122) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_119))), inference(resolution, [status(thm)], [c_398, c_576])).
% 3.80/1.59  tff(c_581, plain, (![A_120, B_119, E_122]: (r1_funct_2(A_120, B_119, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), E_122, E_122) | ~m1_subset_1(E_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_119))) | ~v1_funct_2(E_122, A_120, B_119) | ~v1_funct_1(E_122) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_119))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_399, c_578])).
% 3.80/1.59  tff(c_1450, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_581])).
% 3.80/1.59  tff(c_24, plain, (![A_22]: (~v1_xboole_0(u1_struct_0(A_22)) | ~l1_struct_0(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.80/1.59  tff(c_1453, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1450, c_24])).
% 3.80/1.59  tff(c_1456, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_66, c_1453])).
% 3.80/1.59  tff(c_1459, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_1456])).
% 3.80/1.59  tff(c_1463, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_1459])).
% 3.80/1.59  tff(c_1465, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_581])).
% 3.80/1.59  tff(c_1651, plain, (![A_185, B_186, E_187]: (r1_funct_2(A_185, B_186, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), E_187, E_187) | ~m1_subset_1(E_187, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))) | ~v1_funct_2(E_187, A_185, B_186) | ~v1_funct_1(E_187) | v1_xboole_0(B_186))), inference(splitRight, [status(thm)], [c_581])).
% 3.80/1.59  tff(c_64, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.80/1.59  tff(c_174, plain, (![A_95, B_96, C_97, D_98]: (k2_partfun1(A_95, B_96, C_97, D_98)=k7_relat_1(C_97, D_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))) | ~v1_funct_1(C_97))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.80/1.59  tff(c_176, plain, (![D_98]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_98)=k7_relat_1('#skF_4', D_98) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_46, c_174])).
% 3.80/1.59  tff(c_179, plain, (![D_98]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_98)=k7_relat_1('#skF_4', D_98))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_176])).
% 3.80/1.59  tff(c_393, plain, (![D_98]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', D_98)=k7_relat_1('#skF_4', D_98))), inference(demodulation, [status(thm), theory('equality')], [c_383, c_179])).
% 3.80/1.59  tff(c_60, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.80/1.59  tff(c_670, plain, (![A_129, B_130, C_131, D_132]: (k2_partfun1(u1_struct_0(A_129), u1_struct_0(B_130), C_131, u1_struct_0(D_132))=k2_tmap_1(A_129, B_130, C_131, D_132) | ~m1_pre_topc(D_132, A_129) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_129), u1_struct_0(B_130)))) | ~v1_funct_2(C_131, u1_struct_0(A_129), u1_struct_0(B_130)) | ~v1_funct_1(C_131) | ~l1_pre_topc(B_130) | ~v2_pre_topc(B_130) | v2_struct_0(B_130) | ~l1_pre_topc(A_129) | ~v2_pre_topc(A_129) | v2_struct_0(A_129))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.80/1.59  tff(c_674, plain, (![B_130, C_131, D_132]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_130), C_131, u1_struct_0(D_132))=k2_tmap_1('#skF_2', B_130, C_131, D_132) | ~m1_pre_topc(D_132, '#skF_2') | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_130)))) | ~v1_funct_2(C_131, u1_struct_0('#skF_2'), u1_struct_0(B_130)) | ~v1_funct_1(C_131) | ~l1_pre_topc(B_130) | ~v2_pre_topc(B_130) | v2_struct_0(B_130) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_383, c_670])).
% 3.80/1.59  tff(c_682, plain, (![B_130, C_131, D_132]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_130), C_131, u1_struct_0(D_132))=k2_tmap_1('#skF_2', B_130, C_131, D_132) | ~m1_pre_topc(D_132, '#skF_2') | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_130)))) | ~v1_funct_2(C_131, u1_struct_0('#skF_3'), u1_struct_0(B_130)) | ~v1_funct_1(C_131) | ~l1_pre_topc(B_130) | ~v2_pre_topc(B_130) | v2_struct_0(B_130) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_383, c_383, c_674])).
% 3.80/1.59  tff(c_716, plain, (![B_134, C_135, D_136]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_134), C_135, u1_struct_0(D_136))=k2_tmap_1('#skF_2', B_134, C_135, D_136) | ~m1_pre_topc(D_136, '#skF_2') | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_134)))) | ~v1_funct_2(C_135, u1_struct_0('#skF_3'), u1_struct_0(B_134)) | ~v1_funct_1(C_135) | ~l1_pre_topc(B_134) | ~v2_pre_topc(B_134) | v2_struct_0(B_134))), inference(negUnitSimplification, [status(thm)], [c_60, c_682])).
% 3.80/1.59  tff(c_718, plain, (![D_136]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_136))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_136) | ~m1_pre_topc(D_136, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_398, c_716])).
% 3.80/1.59  tff(c_723, plain, (![D_136]: (k7_relat_1('#skF_4', u1_struct_0(D_136))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_136) | ~m1_pre_topc(D_136, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_50, c_399, c_393, c_718])).
% 3.80/1.59  tff(c_732, plain, (![D_137]: (k7_relat_1('#skF_4', u1_struct_0(D_137))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_137) | ~m1_pre_topc(D_137, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_66, c_723])).
% 3.80/1.59  tff(c_90, plain, (![C_77, A_78, B_79]: (v1_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.80/1.59  tff(c_94, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_90])).
% 3.80/1.59  tff(c_116, plain, (![C_87, A_88, B_89]: (v4_relat_1(C_87, A_88) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.80/1.59  tff(c_120, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_46, c_116])).
% 3.80/1.59  tff(c_8, plain, (![B_4, A_3]: (k7_relat_1(B_4, A_3)=B_4 | ~v4_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.80/1.59  tff(c_123, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_120, c_8])).
% 3.80/1.59  tff(c_126, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_123])).
% 3.80/1.59  tff(c_395, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_383, c_126])).
% 3.80/1.59  tff(c_741, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_732, c_395])).
% 3.80/1.59  tff(c_756, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_741])).
% 3.80/1.59  tff(c_42, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.80/1.59  tff(c_394, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_383, c_42])).
% 3.80/1.59  tff(c_762, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_756, c_394])).
% 3.80/1.59  tff(c_1654, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_1651, c_762])).
% 3.80/1.59  tff(c_1657, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_399, c_398, c_1654])).
% 3.80/1.59  tff(c_1659, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1465, c_1657])).
% 3.80/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/1.59  
% 3.80/1.59  Inference rules
% 3.80/1.59  ----------------------
% 3.80/1.59  #Ref     : 0
% 3.80/1.59  #Sup     : 308
% 3.80/1.59  #Fact    : 0
% 3.80/1.59  #Define  : 0
% 3.80/1.59  #Split   : 3
% 3.80/1.59  #Chain   : 0
% 3.80/1.60  #Close   : 0
% 3.80/1.60  
% 3.80/1.60  Ordering : KBO
% 3.80/1.60  
% 3.80/1.60  Simplification rules
% 3.80/1.60  ----------------------
% 3.80/1.60  #Subsume      : 83
% 3.80/1.60  #Demod        : 484
% 3.80/1.60  #Tautology    : 144
% 3.80/1.60  #SimpNegUnit  : 10
% 3.80/1.60  #BackRed      : 9
% 3.80/1.60  
% 3.80/1.60  #Partial instantiations: 0
% 3.80/1.60  #Strategies tried      : 1
% 3.80/1.60  
% 3.80/1.60  Timing (in seconds)
% 3.80/1.60  ----------------------
% 3.80/1.60  Preprocessing        : 0.34
% 3.80/1.60  Parsing              : 0.18
% 3.80/1.60  CNF conversion       : 0.03
% 3.80/1.60  Main loop            : 0.49
% 3.80/1.60  Inferencing          : 0.16
% 3.80/1.60  Reduction            : 0.17
% 3.80/1.60  Demodulation         : 0.12
% 3.80/1.60  BG Simplification    : 0.02
% 3.80/1.60  Subsumption          : 0.11
% 3.80/1.60  Abstraction          : 0.02
% 3.80/1.60  MUC search           : 0.00
% 3.80/1.60  Cooper               : 0.00
% 3.80/1.60  Total                : 0.87
% 3.80/1.60  Index Insertion      : 0.00
% 3.80/1.60  Index Deletion       : 0.00
% 3.80/1.60  Index Matching       : 0.00
% 3.80/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
