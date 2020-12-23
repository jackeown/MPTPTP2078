%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:51 EST 2020

% Result     : Theorem 4.90s
% Output     : CNFRefutation 5.28s
% Verified   : 
% Statistics : Number of formulae       :  152 (1341 expanded)
%              Number of leaves         :   49 ( 461 expanded)
%              Depth                    :   23
%              Number of atoms          :  340 (5246 expanded)
%              Number of equality atoms :   32 ( 497 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_219,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_tmap_1)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_103,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_141,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(B)
        & ~ v1_xboole_0(D)
        & v1_funct_1(E)
        & v1_funct_2(E,A,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,C,D)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( r1_funct_2(A,B,C,D,E,F)
      <=> E = F ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_172,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_119,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_186,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_168,axiom,(
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

tff(c_72,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_28,plain,(
    ! [A_24] :
      ( l1_struct_0(A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_10,plain,(
    ! [C_7,A_5,B_6] :
      ( v1_relat_1(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_97,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_10])).

tff(c_125,plain,(
    ! [C_91,A_92,B_93] :
      ( v4_relat_1(C_91,A_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_129,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_56,c_125])).

tff(c_146,plain,(
    ! [B_98,A_99] :
      ( k1_relat_1(B_98) = A_99
      | ~ v1_partfun1(B_98,A_99)
      | ~ v4_relat_1(B_98,A_99)
      | ~ v1_relat_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_149,plain,
    ( u1_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_129,c_146])).

tff(c_152,plain,
    ( u1_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_149])).

tff(c_153,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_58,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_350,plain,(
    ! [C_116,A_117,B_118] :
      ( v1_partfun1(C_116,A_117)
      | ~ v1_funct_2(C_116,A_117,B_118)
      | ~ v1_funct_1(C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118)))
      | v1_xboole_0(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_353,plain,
    ( v1_partfun1('#skF_4',u1_struct_0('#skF_2'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_56,c_350])).

tff(c_356,plain,
    ( v1_partfun1('#skF_4',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_353])).

tff(c_357,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_356])).

tff(c_32,plain,(
    ! [A_28] :
      ( ~ v1_xboole_0(u1_struct_0(A_28))
      | ~ l1_struct_0(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_360,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_357,c_32])).

tff(c_363,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_360])).

tff(c_366,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_363])).

tff(c_370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_366])).

tff(c_371,plain,(
    u1_struct_0('#skF_2') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_377,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_58])).

tff(c_376,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_56])).

tff(c_821,plain,(
    ! [C_152,D_153,A_150,F_151,B_154] :
      ( r1_funct_2(A_150,B_154,C_152,D_153,F_151,F_151)
      | ~ m1_subset_1(F_151,k1_zfmisc_1(k2_zfmisc_1(C_152,D_153)))
      | ~ v1_funct_2(F_151,C_152,D_153)
      | ~ m1_subset_1(F_151,k1_zfmisc_1(k2_zfmisc_1(A_150,B_154)))
      | ~ v1_funct_2(F_151,A_150,B_154)
      | ~ v1_funct_1(F_151)
      | v1_xboole_0(D_153)
      | v1_xboole_0(B_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_823,plain,(
    ! [A_150,B_154] :
      ( r1_funct_2(A_150,B_154,k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_150,B_154)))
      | ~ v1_funct_2('#skF_4',A_150,B_154)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_154) ) ),
    inference(resolution,[status(thm)],[c_376,c_821])).

tff(c_826,plain,(
    ! [A_150,B_154] :
      ( r1_funct_2(A_150,B_154,k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_150,B_154)))
      | ~ v1_funct_2('#skF_4',A_150,B_154)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_377,c_823])).

tff(c_3124,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_826])).

tff(c_3127,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_3124,c_32])).

tff(c_3130,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_3127])).

tff(c_3133,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_3130])).

tff(c_3137,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3133])).

tff(c_3139,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_826])).

tff(c_3233,plain,(
    ! [A_275,B_276] :
      ( r1_funct_2(A_275,B_276,k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_275,B_276)))
      | ~ v1_funct_2('#skF_4',A_275,B_276)
      | v1_xboole_0(B_276) ) ),
    inference(splitRight,[status(thm)],[c_826])).

tff(c_62,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_68,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_66,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_114,plain,(
    ! [B_89,A_90] :
      ( v2_pre_topc(B_89)
      | ~ m1_pre_topc(B_89,A_90)
      | ~ l1_pre_topc(A_90)
      | ~ v2_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_120,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_114])).

tff(c_124,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_120])).

tff(c_82,plain,(
    ! [B_79,A_80] :
      ( l1_pre_topc(B_79)
      | ~ m1_pre_topc(B_79,A_80)
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_88,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_82])).

tff(c_92,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_88])).

tff(c_46,plain,(
    ! [A_56] :
      ( m1_pre_topc(A_56,A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_451,plain,(
    ! [A_122,B_123] :
      ( m1_pre_topc(A_122,g1_pre_topc(u1_struct_0(B_123),u1_pre_topc(B_123)))
      | ~ m1_pre_topc(A_122,B_123)
      | ~ l1_pre_topc(B_123)
      | ~ l1_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_466,plain,(
    ! [A_122] :
      ( m1_pre_topc(A_122,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')))
      | ~ m1_pre_topc(A_122,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_451])).

tff(c_518,plain,(
    ! [A_128] :
      ( m1_pre_topc(A_128,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')))
      | ~ m1_pre_topc(A_128,'#skF_2')
      | ~ l1_pre_topc(A_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_466])).

tff(c_54,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_375,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_54])).

tff(c_34,plain,(
    ! [B_31,A_29] :
      ( m1_pre_topc(B_31,A_29)
      | ~ m1_pre_topc(B_31,g1_pre_topc(u1_struct_0(A_29),u1_pre_topc(A_29)))
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_439,plain,(
    ! [B_31] :
      ( m1_pre_topc(B_31,'#skF_3')
      | ~ m1_pre_topc(B_31,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_34])).

tff(c_443,plain,(
    ! [B_31] :
      ( m1_pre_topc(B_31,'#skF_3')
      | ~ m1_pre_topc(B_31,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_439])).

tff(c_535,plain,(
    ! [A_129] :
      ( m1_pre_topc(A_129,'#skF_3')
      | ~ m1_pre_topc(A_129,'#skF_2')
      | ~ l1_pre_topc(A_129) ) ),
    inference(resolution,[status(thm)],[c_518,c_443])).

tff(c_542,plain,
    ( m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_535])).

tff(c_549,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_542])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_671,plain,(
    ! [B_140,C_141,A_142] :
      ( m1_pre_topc(B_140,C_141)
      | ~ r1_tarski(u1_struct_0(B_140),u1_struct_0(C_141))
      | ~ m1_pre_topc(C_141,A_142)
      | ~ m1_pre_topc(B_140,A_142)
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_742,plain,(
    ! [B_147,A_148] :
      ( m1_pre_topc(B_147,B_147)
      | ~ m1_pre_topc(B_147,A_148)
      | ~ l1_pre_topc(A_148)
      | ~ v2_pre_topc(A_148) ) ),
    inference(resolution,[status(thm)],[c_6,c_671])).

tff(c_748,plain,
    ( m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_549,c_742])).

tff(c_767,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_92,c_748])).

tff(c_48,plain,(
    ! [B_61,C_63,A_57] :
      ( r1_tarski(u1_struct_0(B_61),u1_struct_0(C_63))
      | ~ m1_pre_topc(B_61,C_63)
      | ~ m1_pre_topc(C_63,A_57)
      | ~ m1_pre_topc(B_61,A_57)
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_781,plain,(
    ! [B_61] :
      ( r1_tarski(u1_struct_0(B_61),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_61,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_767,c_48])).

tff(c_806,plain,(
    ! [B_149] :
      ( r1_tarski(u1_struct_0(B_149),k1_relat_1('#skF_4'))
      | ~ m1_pre_topc(B_149,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_371,c_781])).

tff(c_545,plain,
    ( m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_535])).

tff(c_552,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_545])).

tff(c_680,plain,(
    ! [B_143,C_144,A_145] :
      ( r1_tarski(u1_struct_0(B_143),u1_struct_0(C_144))
      | ~ m1_pre_topc(B_143,C_144)
      | ~ m1_pre_topc(C_144,A_145)
      | ~ m1_pre_topc(B_143,A_145)
      | ~ l1_pre_topc(A_145)
      | ~ v2_pre_topc(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_684,plain,(
    ! [B_143] :
      ( r1_tarski(u1_struct_0(B_143),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_143,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_552,c_680])).

tff(c_716,plain,(
    ! [B_146] :
      ( r1_tarski(u1_struct_0(B_146),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_146,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_92,c_684])).

tff(c_723,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_716])).

tff(c_727,plain,(
    r1_tarski(k1_relat_1('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_723])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_736,plain,
    ( u1_struct_0('#skF_3') = k1_relat_1('#skF_4')
    | ~ r1_tarski(u1_struct_0('#skF_3'),k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_727,c_2])).

tff(c_741,plain,(
    ~ r1_tarski(u1_struct_0('#skF_3'),k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_736])).

tff(c_809,plain,(
    ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_806,c_741])).

tff(c_818,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_809])).

tff(c_819,plain,(
    u1_struct_0('#skF_3') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_736])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k7_relat_1(B_4,A_3) = B_4
      | ~ r1_tarski(k1_relat_1(B_4),A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_730,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_727,c_8])).

tff(c_735,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_730])).

tff(c_827,plain,(
    k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_819,c_735])).

tff(c_74,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_589,plain,(
    ! [A_130,B_131,C_132,D_133] :
      ( k2_partfun1(A_130,B_131,C_132,D_133) = k7_relat_1(C_132,D_133)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131)))
      | ~ v1_funct_1(C_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_591,plain,(
    ! [D_133] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',D_133) = k7_relat_1('#skF_4',D_133)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_376,c_589])).

tff(c_594,plain,(
    ! [D_133] : k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',D_133) = k7_relat_1('#skF_4',D_133) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_591])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_1078,plain,(
    ! [A_172,B_173,C_174,D_175] :
      ( k2_partfun1(u1_struct_0(A_172),u1_struct_0(B_173),C_174,u1_struct_0(D_175)) = k2_tmap_1(A_172,B_173,C_174,D_175)
      | ~ m1_pre_topc(D_175,A_172)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_172),u1_struct_0(B_173))))
      | ~ v1_funct_2(C_174,u1_struct_0(A_172),u1_struct_0(B_173))
      | ~ v1_funct_1(C_174)
      | ~ l1_pre_topc(B_173)
      | ~ v2_pre_topc(B_173)
      | v2_struct_0(B_173)
      | ~ l1_pre_topc(A_172)
      | ~ v2_pre_topc(A_172)
      | v2_struct_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_1084,plain,(
    ! [B_173,C_174,D_175] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_173),C_174,u1_struct_0(D_175)) = k2_tmap_1('#skF_2',B_173,C_174,D_175)
      | ~ m1_pre_topc(D_175,'#skF_2')
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_173))))
      | ~ v1_funct_2(C_174,u1_struct_0('#skF_2'),u1_struct_0(B_173))
      | ~ v1_funct_1(C_174)
      | ~ l1_pre_topc(B_173)
      | ~ v2_pre_topc(B_173)
      | v2_struct_0(B_173)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_1078])).

tff(c_1094,plain,(
    ! [B_173,C_174,D_175] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0(B_173),C_174,u1_struct_0(D_175)) = k2_tmap_1('#skF_2',B_173,C_174,D_175)
      | ~ m1_pre_topc(D_175,'#skF_2')
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_173))))
      | ~ v1_funct_2(C_174,k1_relat_1('#skF_4'),u1_struct_0(B_173))
      | ~ v1_funct_1(C_174)
      | ~ l1_pre_topc(B_173)
      | ~ v2_pre_topc(B_173)
      | v2_struct_0(B_173)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_371,c_371,c_1084])).

tff(c_1160,plain,(
    ! [B_179,C_180,D_181] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0(B_179),C_180,u1_struct_0(D_181)) = k2_tmap_1('#skF_2',B_179,C_180,D_181)
      | ~ m1_pre_topc(D_181,'#skF_2')
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_179))))
      | ~ v1_funct_2(C_180,k1_relat_1('#skF_4'),u1_struct_0(B_179))
      | ~ v1_funct_1(C_180)
      | ~ l1_pre_topc(B_179)
      | ~ v2_pre_topc(B_179)
      | v2_struct_0(B_179) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1094])).

tff(c_1164,plain,(
    ! [D_181] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_181)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_181)
      | ~ m1_pre_topc(D_181,'#skF_2')
      | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_376,c_1160])).

tff(c_1172,plain,(
    ! [D_181] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_181)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_181)
      | ~ m1_pre_topc(D_181,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_60,c_377,c_594,c_1164])).

tff(c_1177,plain,(
    ! [D_182] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_182)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_182)
      | ~ m1_pre_topc(D_182,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1172])).

tff(c_1192,plain,
    ( k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_819,c_1177])).

tff(c_1199,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_827,c_1192])).

tff(c_52,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_373,plain,(
    ~ r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_52])).

tff(c_830,plain,(
    ~ r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_819,c_373])).

tff(c_1206,plain,(
    ~ r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1199,c_830])).

tff(c_3236,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_3233,c_1206])).

tff(c_3241,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_376,c_3236])).

tff(c_3243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3139,c_3241])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:43:25 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.90/1.88  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.90/1.90  
% 4.90/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.90/1.90  %$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.90/1.90  
% 4.90/1.90  %Foreground sorts:
% 4.90/1.90  
% 4.90/1.90  
% 4.90/1.90  %Background operators:
% 4.90/1.90  
% 4.90/1.90  
% 4.90/1.90  %Foreground operators:
% 4.90/1.90  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.90/1.90  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.90/1.90  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.90/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.90/1.90  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.90/1.90  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.90/1.90  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.90/1.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.90/1.90  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.90/1.90  tff('#skF_2', type, '#skF_2': $i).
% 4.90/1.90  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.90/1.90  tff('#skF_3', type, '#skF_3': $i).
% 4.90/1.90  tff('#skF_1', type, '#skF_1': $i).
% 4.90/1.90  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.90/1.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.90/1.90  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.90/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.90/1.90  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.90/1.90  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.90/1.90  tff('#skF_4', type, '#skF_4': $i).
% 4.90/1.90  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 4.90/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.90/1.90  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.90/1.90  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 4.90/1.90  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.90/1.90  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.90/1.90  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 4.90/1.90  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.90/1.90  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.90/1.90  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.90/1.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.90/1.90  
% 5.28/1.92  tff(f_219, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_tmap_1)).
% 5.28/1.92  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.28/1.92  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.28/1.92  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.28/1.92  tff(f_69, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 5.28/1.92  tff(f_61, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 5.28/1.92  tff(f_103, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.28/1.92  tff(f_141, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 5.28/1.92  tff(f_84, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 5.28/1.92  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.28/1.92  tff(f_172, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 5.28/1.92  tff(f_119, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 5.28/1.92  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 5.28/1.92  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.28/1.92  tff(f_186, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 5.28/1.92  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 5.28/1.92  tff(f_75, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 5.28/1.92  tff(f_168, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 5.28/1.92  tff(c_72, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_219])).
% 5.28/1.92  tff(c_28, plain, (![A_24]: (l1_struct_0(A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.28/1.92  tff(c_76, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_219])).
% 5.28/1.92  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_219])).
% 5.28/1.92  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_219])).
% 5.28/1.92  tff(c_10, plain, (![C_7, A_5, B_6]: (v1_relat_1(C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.28/1.92  tff(c_97, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_10])).
% 5.28/1.92  tff(c_125, plain, (![C_91, A_92, B_93]: (v4_relat_1(C_91, A_92) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.28/1.92  tff(c_129, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_56, c_125])).
% 5.28/1.92  tff(c_146, plain, (![B_98, A_99]: (k1_relat_1(B_98)=A_99 | ~v1_partfun1(B_98, A_99) | ~v4_relat_1(B_98, A_99) | ~v1_relat_1(B_98))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.28/1.92  tff(c_149, plain, (u1_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_2')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_129, c_146])).
% 5.28/1.92  tff(c_152, plain, (u1_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_149])).
% 5.28/1.92  tff(c_153, plain, (~v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_152])).
% 5.28/1.92  tff(c_58, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_219])).
% 5.28/1.92  tff(c_350, plain, (![C_116, A_117, B_118]: (v1_partfun1(C_116, A_117) | ~v1_funct_2(C_116, A_117, B_118) | ~v1_funct_1(C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))) | v1_xboole_0(B_118))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.28/1.92  tff(c_353, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_56, c_350])).
% 5.28/1.92  tff(c_356, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_353])).
% 5.28/1.92  tff(c_357, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_153, c_356])).
% 5.28/1.92  tff(c_32, plain, (![A_28]: (~v1_xboole_0(u1_struct_0(A_28)) | ~l1_struct_0(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.28/1.92  tff(c_360, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_357, c_32])).
% 5.28/1.92  tff(c_363, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_76, c_360])).
% 5.28/1.92  tff(c_366, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_363])).
% 5.28/1.92  tff(c_370, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_366])).
% 5.28/1.92  tff(c_371, plain, (u1_struct_0('#skF_2')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_152])).
% 5.28/1.92  tff(c_377, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_371, c_58])).
% 5.28/1.92  tff(c_376, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_371, c_56])).
% 5.28/1.92  tff(c_821, plain, (![C_152, D_153, A_150, F_151, B_154]: (r1_funct_2(A_150, B_154, C_152, D_153, F_151, F_151) | ~m1_subset_1(F_151, k1_zfmisc_1(k2_zfmisc_1(C_152, D_153))) | ~v1_funct_2(F_151, C_152, D_153) | ~m1_subset_1(F_151, k1_zfmisc_1(k2_zfmisc_1(A_150, B_154))) | ~v1_funct_2(F_151, A_150, B_154) | ~v1_funct_1(F_151) | v1_xboole_0(D_153) | v1_xboole_0(B_154))), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.28/1.92  tff(c_823, plain, (![A_150, B_154]: (r1_funct_2(A_150, B_154, k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_150, B_154))) | ~v1_funct_2('#skF_4', A_150, B_154) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_154))), inference(resolution, [status(thm)], [c_376, c_821])).
% 5.28/1.92  tff(c_826, plain, (![A_150, B_154]: (r1_funct_2(A_150, B_154, k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_150, B_154))) | ~v1_funct_2('#skF_4', A_150, B_154) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_154))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_377, c_823])).
% 5.28/1.92  tff(c_3124, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_826])).
% 5.28/1.92  tff(c_3127, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_3124, c_32])).
% 5.28/1.92  tff(c_3130, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_76, c_3127])).
% 5.28/1.92  tff(c_3133, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_3130])).
% 5.28/1.92  tff(c_3137, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_3133])).
% 5.28/1.92  tff(c_3139, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_826])).
% 5.28/1.92  tff(c_3233, plain, (![A_275, B_276]: (r1_funct_2(A_275, B_276, k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_275, B_276))) | ~v1_funct_2('#skF_4', A_275, B_276) | v1_xboole_0(B_276))), inference(splitRight, [status(thm)], [c_826])).
% 5.28/1.92  tff(c_62, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_219])).
% 5.28/1.92  tff(c_68, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_219])).
% 5.28/1.92  tff(c_66, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_219])).
% 5.28/1.92  tff(c_114, plain, (![B_89, A_90]: (v2_pre_topc(B_89) | ~m1_pre_topc(B_89, A_90) | ~l1_pre_topc(A_90) | ~v2_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.28/1.92  tff(c_120, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_114])).
% 5.28/1.92  tff(c_124, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_120])).
% 5.28/1.92  tff(c_82, plain, (![B_79, A_80]: (l1_pre_topc(B_79) | ~m1_pre_topc(B_79, A_80) | ~l1_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.28/1.92  tff(c_88, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_82])).
% 5.28/1.92  tff(c_92, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_88])).
% 5.28/1.92  tff(c_46, plain, (![A_56]: (m1_pre_topc(A_56, A_56) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.28/1.92  tff(c_451, plain, (![A_122, B_123]: (m1_pre_topc(A_122, g1_pre_topc(u1_struct_0(B_123), u1_pre_topc(B_123))) | ~m1_pre_topc(A_122, B_123) | ~l1_pre_topc(B_123) | ~l1_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.28/1.92  tff(c_466, plain, (![A_122]: (m1_pre_topc(A_122, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))) | ~m1_pre_topc(A_122, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_122))), inference(superposition, [status(thm), theory('equality')], [c_371, c_451])).
% 5.28/1.92  tff(c_518, plain, (![A_128]: (m1_pre_topc(A_128, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))) | ~m1_pre_topc(A_128, '#skF_2') | ~l1_pre_topc(A_128))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_466])).
% 5.28/1.92  tff(c_54, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_219])).
% 5.28/1.92  tff(c_375, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_371, c_54])).
% 5.28/1.92  tff(c_34, plain, (![B_31, A_29]: (m1_pre_topc(B_31, A_29) | ~m1_pre_topc(B_31, g1_pre_topc(u1_struct_0(A_29), u1_pre_topc(A_29))) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.28/1.92  tff(c_439, plain, (![B_31]: (m1_pre_topc(B_31, '#skF_3') | ~m1_pre_topc(B_31, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_375, c_34])).
% 5.28/1.92  tff(c_443, plain, (![B_31]: (m1_pre_topc(B_31, '#skF_3') | ~m1_pre_topc(B_31, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_439])).
% 5.28/1.92  tff(c_535, plain, (![A_129]: (m1_pre_topc(A_129, '#skF_3') | ~m1_pre_topc(A_129, '#skF_2') | ~l1_pre_topc(A_129))), inference(resolution, [status(thm)], [c_518, c_443])).
% 5.28/1.92  tff(c_542, plain, (m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_46, c_535])).
% 5.28/1.92  tff(c_549, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_542])).
% 5.28/1.92  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.28/1.92  tff(c_671, plain, (![B_140, C_141, A_142]: (m1_pre_topc(B_140, C_141) | ~r1_tarski(u1_struct_0(B_140), u1_struct_0(C_141)) | ~m1_pre_topc(C_141, A_142) | ~m1_pre_topc(B_140, A_142) | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142))), inference(cnfTransformation, [status(thm)], [f_186])).
% 5.28/1.92  tff(c_742, plain, (![B_147, A_148]: (m1_pre_topc(B_147, B_147) | ~m1_pre_topc(B_147, A_148) | ~l1_pre_topc(A_148) | ~v2_pre_topc(A_148))), inference(resolution, [status(thm)], [c_6, c_671])).
% 5.28/1.92  tff(c_748, plain, (m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_549, c_742])).
% 5.28/1.92  tff(c_767, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_92, c_748])).
% 5.28/1.92  tff(c_48, plain, (![B_61, C_63, A_57]: (r1_tarski(u1_struct_0(B_61), u1_struct_0(C_63)) | ~m1_pre_topc(B_61, C_63) | ~m1_pre_topc(C_63, A_57) | ~m1_pre_topc(B_61, A_57) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_186])).
% 5.28/1.92  tff(c_781, plain, (![B_61]: (r1_tarski(u1_struct_0(B_61), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_61, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_767, c_48])).
% 5.28/1.92  tff(c_806, plain, (![B_149]: (r1_tarski(u1_struct_0(B_149), k1_relat_1('#skF_4')) | ~m1_pre_topc(B_149, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_371, c_781])).
% 5.28/1.92  tff(c_545, plain, (m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_62, c_535])).
% 5.28/1.92  tff(c_552, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_545])).
% 5.28/1.92  tff(c_680, plain, (![B_143, C_144, A_145]: (r1_tarski(u1_struct_0(B_143), u1_struct_0(C_144)) | ~m1_pre_topc(B_143, C_144) | ~m1_pre_topc(C_144, A_145) | ~m1_pre_topc(B_143, A_145) | ~l1_pre_topc(A_145) | ~v2_pre_topc(A_145))), inference(cnfTransformation, [status(thm)], [f_186])).
% 5.28/1.92  tff(c_684, plain, (![B_143]: (r1_tarski(u1_struct_0(B_143), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_143, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_552, c_680])).
% 5.28/1.92  tff(c_716, plain, (![B_146]: (r1_tarski(u1_struct_0(B_146), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_146, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_92, c_684])).
% 5.28/1.92  tff(c_723, plain, (r1_tarski(k1_relat_1('#skF_4'), u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_371, c_716])).
% 5.28/1.92  tff(c_727, plain, (r1_tarski(k1_relat_1('#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_549, c_723])).
% 5.28/1.92  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.28/1.92  tff(c_736, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_4') | ~r1_tarski(u1_struct_0('#skF_3'), k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_727, c_2])).
% 5.28/1.92  tff(c_741, plain, (~r1_tarski(u1_struct_0('#skF_3'), k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_736])).
% 5.28/1.92  tff(c_809, plain, (~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_806, c_741])).
% 5.28/1.92  tff(c_818, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_809])).
% 5.28/1.92  tff(c_819, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_736])).
% 5.28/1.92  tff(c_8, plain, (![B_4, A_3]: (k7_relat_1(B_4, A_3)=B_4 | ~r1_tarski(k1_relat_1(B_4), A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.28/1.92  tff(c_730, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_727, c_8])).
% 5.28/1.92  tff(c_735, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_97, c_730])).
% 5.28/1.92  tff(c_827, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_819, c_735])).
% 5.28/1.92  tff(c_74, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_219])).
% 5.28/1.92  tff(c_589, plain, (![A_130, B_131, C_132, D_133]: (k2_partfun1(A_130, B_131, C_132, D_133)=k7_relat_1(C_132, D_133) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))) | ~v1_funct_1(C_132))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.28/1.92  tff(c_591, plain, (![D_133]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', D_133)=k7_relat_1('#skF_4', D_133) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_376, c_589])).
% 5.28/1.92  tff(c_594, plain, (![D_133]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', D_133)=k7_relat_1('#skF_4', D_133))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_591])).
% 5.28/1.92  tff(c_70, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_219])).
% 5.28/1.92  tff(c_1078, plain, (![A_172, B_173, C_174, D_175]: (k2_partfun1(u1_struct_0(A_172), u1_struct_0(B_173), C_174, u1_struct_0(D_175))=k2_tmap_1(A_172, B_173, C_174, D_175) | ~m1_pre_topc(D_175, A_172) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_172), u1_struct_0(B_173)))) | ~v1_funct_2(C_174, u1_struct_0(A_172), u1_struct_0(B_173)) | ~v1_funct_1(C_174) | ~l1_pre_topc(B_173) | ~v2_pre_topc(B_173) | v2_struct_0(B_173) | ~l1_pre_topc(A_172) | ~v2_pre_topc(A_172) | v2_struct_0(A_172))), inference(cnfTransformation, [status(thm)], [f_168])).
% 5.28/1.92  tff(c_1084, plain, (![B_173, C_174, D_175]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_173), C_174, u1_struct_0(D_175))=k2_tmap_1('#skF_2', B_173, C_174, D_175) | ~m1_pre_topc(D_175, '#skF_2') | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_173)))) | ~v1_funct_2(C_174, u1_struct_0('#skF_2'), u1_struct_0(B_173)) | ~v1_funct_1(C_174) | ~l1_pre_topc(B_173) | ~v2_pre_topc(B_173) | v2_struct_0(B_173) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_371, c_1078])).
% 5.28/1.92  tff(c_1094, plain, (![B_173, C_174, D_175]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0(B_173), C_174, u1_struct_0(D_175))=k2_tmap_1('#skF_2', B_173, C_174, D_175) | ~m1_pre_topc(D_175, '#skF_2') | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_173)))) | ~v1_funct_2(C_174, k1_relat_1('#skF_4'), u1_struct_0(B_173)) | ~v1_funct_1(C_174) | ~l1_pre_topc(B_173) | ~v2_pre_topc(B_173) | v2_struct_0(B_173) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_371, c_371, c_1084])).
% 5.28/1.92  tff(c_1160, plain, (![B_179, C_180, D_181]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0(B_179), C_180, u1_struct_0(D_181))=k2_tmap_1('#skF_2', B_179, C_180, D_181) | ~m1_pre_topc(D_181, '#skF_2') | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_179)))) | ~v1_funct_2(C_180, k1_relat_1('#skF_4'), u1_struct_0(B_179)) | ~v1_funct_1(C_180) | ~l1_pre_topc(B_179) | ~v2_pre_topc(B_179) | v2_struct_0(B_179))), inference(negUnitSimplification, [status(thm)], [c_70, c_1094])).
% 5.28/1.92  tff(c_1164, plain, (![D_181]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_181))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_181) | ~m1_pre_topc(D_181, '#skF_2') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_376, c_1160])).
% 5.28/1.92  tff(c_1172, plain, (![D_181]: (k7_relat_1('#skF_4', u1_struct_0(D_181))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_181) | ~m1_pre_topc(D_181, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_60, c_377, c_594, c_1164])).
% 5.28/1.92  tff(c_1177, plain, (![D_182]: (k7_relat_1('#skF_4', u1_struct_0(D_182))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_182) | ~m1_pre_topc(D_182, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_76, c_1172])).
% 5.28/1.92  tff(c_1192, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_819, c_1177])).
% 5.28/1.92  tff(c_1199, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_827, c_1192])).
% 5.28/1.92  tff(c_52, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_219])).
% 5.28/1.92  tff(c_373, plain, (~r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_371, c_52])).
% 5.28/1.92  tff(c_830, plain, (~r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_819, c_373])).
% 5.28/1.92  tff(c_1206, plain, (~r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1199, c_830])).
% 5.28/1.92  tff(c_3236, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_3233, c_1206])).
% 5.28/1.92  tff(c_3241, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_377, c_376, c_3236])).
% 5.28/1.92  tff(c_3243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3139, c_3241])).
% 5.28/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.28/1.92  
% 5.28/1.92  Inference rules
% 5.28/1.92  ----------------------
% 5.28/1.92  #Ref     : 0
% 5.28/1.92  #Sup     : 638
% 5.28/1.92  #Fact    : 0
% 5.28/1.92  #Define  : 0
% 5.28/1.92  #Split   : 7
% 5.28/1.92  #Chain   : 0
% 5.28/1.92  #Close   : 0
% 5.28/1.92  
% 5.28/1.92  Ordering : KBO
% 5.28/1.92  
% 5.28/1.92  Simplification rules
% 5.28/1.92  ----------------------
% 5.28/1.92  #Subsume      : 198
% 5.28/1.92  #Demod        : 1277
% 5.28/1.92  #Tautology    : 291
% 5.28/1.92  #SimpNegUnit  : 22
% 5.28/1.92  #BackRed      : 16
% 5.28/1.92  
% 5.28/1.92  #Partial instantiations: 0
% 5.28/1.92  #Strategies tried      : 1
% 5.28/1.92  
% 5.28/1.92  Timing (in seconds)
% 5.28/1.92  ----------------------
% 5.28/1.93  Preprocessing        : 0.36
% 5.28/1.93  Parsing              : 0.19
% 5.28/1.93  CNF conversion       : 0.03
% 5.28/1.93  Main loop            : 0.79
% 5.28/1.93  Inferencing          : 0.25
% 5.28/1.93  Reduction            : 0.29
% 5.28/1.93  Demodulation         : 0.22
% 5.28/1.93  BG Simplification    : 0.03
% 5.28/1.93  Subsumption          : 0.17
% 5.28/1.93  Abstraction          : 0.03
% 5.28/1.93  MUC search           : 0.00
% 5.28/1.93  Cooper               : 0.00
% 5.28/1.93  Total                : 1.20
% 5.28/1.93  Index Insertion      : 0.00
% 5.28/1.93  Index Deletion       : 0.00
% 5.28/1.93  Index Matching       : 0.00
% 5.28/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
