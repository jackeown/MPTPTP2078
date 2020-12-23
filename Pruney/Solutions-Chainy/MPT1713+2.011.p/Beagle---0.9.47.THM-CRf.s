%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:30 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 345 expanded)
%              Number of leaves         :   39 ( 133 expanded)
%              Depth                    :   13
%              Number of atoms          :  182 (1005 expanded)
%              Number of equality atoms :   13 (  48 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_138,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ( m1_pre_topc(B,C)
                 => ( ~ r1_tsep_1(B,C)
                    & ~ r1_tsep_1(C,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(B,A)
          <=> ( r1_tarski(k2_struct_0(B),k2_struct_0(A))
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
                 => ( r2_hidden(C,u1_pre_topc(B))
                  <=> ? [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                        & r2_hidden(D,u1_pre_topc(A))
                        & C = k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_110,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(c_66,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_62,plain,(
    m1_pre_topc('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_89,plain,(
    ! [B_73,A_74] :
      ( l1_pre_topc(B_73)
      | ~ m1_pre_topc(B_73,A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_92,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_89])).

tff(c_101,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_92])).

tff(c_42,plain,(
    ! [A_53] :
      ( l1_struct_0(A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_79,plain,(
    ! [A_71] :
      ( u1_struct_0(A_71) = k2_struct_0(A_71)
      | ~ l1_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_83,plain,(
    ! [A_53] :
      ( u1_struct_0(A_53) = k2_struct_0(A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(resolution,[status(thm)],[c_42,c_79])).

tff(c_109,plain,(
    u1_struct_0('#skF_7') = k2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_101,c_83])).

tff(c_128,plain,(
    ! [A_75] :
      ( ~ v1_xboole_0(u1_struct_0(A_75))
      | ~ l1_struct_0(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_131,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_7'))
    | ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_128])).

tff(c_138,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_7'))
    | ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_131])).

tff(c_141,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_144,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_42,c_141])).

tff(c_148,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_144])).

tff(c_149,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_58,plain,(
    m1_pre_topc('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_95,plain,
    ( l1_pre_topc('#skF_8')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_89])).

tff(c_104,plain,(
    l1_pre_topc('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_95])).

tff(c_56,plain,(
    m1_pre_topc('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_113,plain,(
    u1_struct_0('#skF_8') = k2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_104,c_83])).

tff(c_134,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_8'))
    | ~ l1_struct_0('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_128])).

tff(c_139,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_8'))
    | ~ l1_struct_0('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_134])).

tff(c_173,plain,(
    ~ l1_struct_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_176,plain,(
    ~ l1_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_173])).

tff(c_180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_176])).

tff(c_182,plain,(
    l1_struct_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_54,plain,
    ( r1_tsep_1('#skF_8','#skF_7')
    | r1_tsep_1('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_72,plain,(
    r1_tsep_1('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_150,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_267,plain,(
    ! [A_92,B_93] :
      ( r1_xboole_0(u1_struct_0(A_92),u1_struct_0(B_93))
      | ~ r1_tsep_1(A_92,B_93)
      | ~ l1_struct_0(B_93)
      | ~ l1_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_273,plain,(
    ! [B_93] :
      ( r1_xboole_0(k2_struct_0('#skF_7'),u1_struct_0(B_93))
      | ~ r1_tsep_1('#skF_7',B_93)
      | ~ l1_struct_0(B_93)
      | ~ l1_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_267])).

tff(c_444,plain,(
    ! [B_104] :
      ( r1_xboole_0(k2_struct_0('#skF_7'),u1_struct_0(B_104))
      | ~ r1_tsep_1('#skF_7',B_104)
      | ~ l1_struct_0(B_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_273])).

tff(c_453,plain,
    ( r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_8'))
    | ~ r1_tsep_1('#skF_7','#skF_8')
    | ~ l1_struct_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_444])).

tff(c_462,plain,(
    r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_72,c_453])).

tff(c_322,plain,(
    ! [B_95,A_96] :
      ( r1_tarski(k2_struct_0(B_95),k2_struct_0(A_96))
      | ~ m1_pre_topc(B_95,A_96)
      | ~ l1_pre_topc(B_95)
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_565,plain,(
    ! [B_115,A_116] :
      ( k3_xboole_0(k2_struct_0(B_115),k2_struct_0(A_116)) = k2_struct_0(B_115)
      | ~ m1_pre_topc(B_115,A_116)
      | ~ l1_pre_topc(B_115)
      | ~ l1_pre_topc(A_116) ) ),
    inference(resolution,[status(thm)],[c_322,c_10])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_183,plain,(
    ! [A_78,B_79,C_80] :
      ( ~ r1_xboole_0(A_78,B_79)
      | ~ r2_hidden(C_80,k3_xboole_0(A_78,B_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_188,plain,(
    ! [A_78,B_79] :
      ( ~ r1_xboole_0(A_78,B_79)
      | v1_xboole_0(k3_xboole_0(A_78,B_79)) ) ),
    inference(resolution,[status(thm)],[c_4,c_183])).

tff(c_629,plain,(
    ! [B_119,A_120] :
      ( ~ r1_xboole_0(k2_struct_0(B_119),k2_struct_0(A_120))
      | v1_xboole_0(k2_struct_0(B_119))
      | ~ m1_pre_topc(B_119,A_120)
      | ~ l1_pre_topc(B_119)
      | ~ l1_pre_topc(A_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_565,c_188])).

tff(c_638,plain,
    ( v1_xboole_0(k2_struct_0('#skF_7'))
    | ~ m1_pre_topc('#skF_7','#skF_8')
    | ~ l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_462,c_629])).

tff(c_646,plain,(
    v1_xboole_0(k2_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_101,c_56,c_638])).

tff(c_648,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_646])).

tff(c_650,plain,(
    ~ r1_tsep_1('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_672,plain,(
    ! [B_128,A_129] :
      ( l1_pre_topc(B_128)
      | ~ m1_pre_topc(B_128,A_129)
      | ~ l1_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_678,plain,
    ( l1_pre_topc('#skF_8')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_672])).

tff(c_687,plain,(
    l1_pre_topc('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_678])).

tff(c_657,plain,(
    ! [A_124] :
      ( u1_struct_0(A_124) = k2_struct_0(A_124)
      | ~ l1_struct_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_661,plain,(
    ! [A_53] :
      ( u1_struct_0(A_53) = k2_struct_0(A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(resolution,[status(thm)],[c_42,c_657])).

tff(c_697,plain,(
    u1_struct_0('#skF_8') = k2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_687,c_661])).

tff(c_706,plain,(
    ! [A_130] :
      ( ~ v1_xboole_0(u1_struct_0(A_130))
      | ~ l1_struct_0(A_130)
      | v2_struct_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_709,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_8'))
    | ~ l1_struct_0('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_697,c_706])).

tff(c_716,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_8'))
    | ~ l1_struct_0('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_709])).

tff(c_719,plain,(
    ~ l1_struct_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_716])).

tff(c_728,plain,(
    ~ l1_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_719])).

tff(c_732,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_687,c_728])).

tff(c_734,plain,(
    l1_struct_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_716])).

tff(c_675,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_672])).

tff(c_684,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_675])).

tff(c_692,plain,(
    u1_struct_0('#skF_7') = k2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_684,c_661])).

tff(c_712,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_7'))
    | ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_692,c_706])).

tff(c_717,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_7'))
    | ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_712])).

tff(c_740,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_717])).

tff(c_743,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_42,c_740])).

tff(c_747,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_684,c_743])).

tff(c_749,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_717])).

tff(c_649,plain,(
    r1_tsep_1('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_777,plain,(
    ! [B_139,A_140] :
      ( r1_tsep_1(B_139,A_140)
      | ~ r1_tsep_1(A_140,B_139)
      | ~ l1_struct_0(B_139)
      | ~ l1_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_779,plain,
    ( r1_tsep_1('#skF_7','#skF_8')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_649,c_777])).

tff(c_782,plain,(
    r1_tsep_1('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_734,c_749,c_779])).

tff(c_784,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_650,c_782])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:55:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.47  
% 3.13/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.47  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_5 > #skF_4
% 3.13/1.47  
% 3.13/1.47  %Foreground sorts:
% 3.13/1.47  
% 3.13/1.47  
% 3.13/1.47  %Background operators:
% 3.13/1.47  
% 3.13/1.47  
% 3.13/1.47  %Foreground operators:
% 3.13/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.13/1.47  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.13/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.13/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.13/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.13/1.47  tff('#skF_7', type, '#skF_7': $i).
% 3.13/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.13/1.47  tff('#skF_6', type, '#skF_6': $i).
% 3.13/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.13/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.13/1.47  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.13/1.47  tff('#skF_8', type, '#skF_8': $i).
% 3.13/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.47  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.13/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.13/1.47  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.13/1.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.13/1.47  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 3.13/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.13/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.13/1.47  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.13/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.13/1.47  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.13/1.47  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.13/1.47  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.13/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.13/1.47  
% 3.13/1.49  tff(f_138, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (~r1_tsep_1(B, C) & ~r1_tsep_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_tmap_1)).
% 3.13/1.49  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.13/1.49  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.13/1.49  tff(f_53, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.13/1.49  tff(f_93, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.13/1.49  tff(f_102, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 3.13/1.49  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(B, A) <=> (r1_tarski(k2_struct_0(B), k2_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (r2_hidden(C, u1_pre_topc(B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(D, u1_pre_topc(A))) & (C = k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_pre_topc)).
% 3.13/1.49  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.13/1.49  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.13/1.49  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.13/1.49  tff(f_110, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 3.13/1.49  tff(c_66, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.13/1.49  tff(c_62, plain, (m1_pre_topc('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.13/1.49  tff(c_89, plain, (![B_73, A_74]: (l1_pre_topc(B_73) | ~m1_pre_topc(B_73, A_74) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.13/1.49  tff(c_92, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_62, c_89])).
% 3.13/1.49  tff(c_101, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_92])).
% 3.13/1.49  tff(c_42, plain, (![A_53]: (l1_struct_0(A_53) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.13/1.49  tff(c_64, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.13/1.49  tff(c_79, plain, (![A_71]: (u1_struct_0(A_71)=k2_struct_0(A_71) | ~l1_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.13/1.49  tff(c_83, plain, (![A_53]: (u1_struct_0(A_53)=k2_struct_0(A_53) | ~l1_pre_topc(A_53))), inference(resolution, [status(thm)], [c_42, c_79])).
% 3.13/1.49  tff(c_109, plain, (u1_struct_0('#skF_7')=k2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_101, c_83])).
% 3.13/1.49  tff(c_128, plain, (![A_75]: (~v1_xboole_0(u1_struct_0(A_75)) | ~l1_struct_0(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.13/1.49  tff(c_131, plain, (~v1_xboole_0(k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_109, c_128])).
% 3.13/1.49  tff(c_138, plain, (~v1_xboole_0(k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_64, c_131])).
% 3.13/1.49  tff(c_141, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_138])).
% 3.13/1.49  tff(c_144, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_42, c_141])).
% 3.13/1.49  tff(c_148, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_144])).
% 3.13/1.49  tff(c_149, plain, (~v1_xboole_0(k2_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_138])).
% 3.13/1.49  tff(c_58, plain, (m1_pre_topc('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.13/1.49  tff(c_95, plain, (l1_pre_topc('#skF_8') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_58, c_89])).
% 3.13/1.49  tff(c_104, plain, (l1_pre_topc('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_95])).
% 3.13/1.49  tff(c_56, plain, (m1_pre_topc('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.13/1.49  tff(c_60, plain, (~v2_struct_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.13/1.49  tff(c_113, plain, (u1_struct_0('#skF_8')=k2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_104, c_83])).
% 3.13/1.49  tff(c_134, plain, (~v1_xboole_0(k2_struct_0('#skF_8')) | ~l1_struct_0('#skF_8') | v2_struct_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_113, c_128])).
% 3.13/1.49  tff(c_139, plain, (~v1_xboole_0(k2_struct_0('#skF_8')) | ~l1_struct_0('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_60, c_134])).
% 3.13/1.49  tff(c_173, plain, (~l1_struct_0('#skF_8')), inference(splitLeft, [status(thm)], [c_139])).
% 3.13/1.49  tff(c_176, plain, (~l1_pre_topc('#skF_8')), inference(resolution, [status(thm)], [c_42, c_173])).
% 3.13/1.49  tff(c_180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_176])).
% 3.13/1.49  tff(c_182, plain, (l1_struct_0('#skF_8')), inference(splitRight, [status(thm)], [c_139])).
% 3.13/1.49  tff(c_54, plain, (r1_tsep_1('#skF_8', '#skF_7') | r1_tsep_1('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.13/1.49  tff(c_72, plain, (r1_tsep_1('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_54])).
% 3.13/1.49  tff(c_150, plain, (l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_138])).
% 3.13/1.49  tff(c_267, plain, (![A_92, B_93]: (r1_xboole_0(u1_struct_0(A_92), u1_struct_0(B_93)) | ~r1_tsep_1(A_92, B_93) | ~l1_struct_0(B_93) | ~l1_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.13/1.49  tff(c_273, plain, (![B_93]: (r1_xboole_0(k2_struct_0('#skF_7'), u1_struct_0(B_93)) | ~r1_tsep_1('#skF_7', B_93) | ~l1_struct_0(B_93) | ~l1_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_267])).
% 3.13/1.49  tff(c_444, plain, (![B_104]: (r1_xboole_0(k2_struct_0('#skF_7'), u1_struct_0(B_104)) | ~r1_tsep_1('#skF_7', B_104) | ~l1_struct_0(B_104))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_273])).
% 3.13/1.49  tff(c_453, plain, (r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_8')) | ~r1_tsep_1('#skF_7', '#skF_8') | ~l1_struct_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_113, c_444])).
% 3.13/1.49  tff(c_462, plain, (r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_72, c_453])).
% 3.13/1.49  tff(c_322, plain, (![B_95, A_96]: (r1_tarski(k2_struct_0(B_95), k2_struct_0(A_96)) | ~m1_pre_topc(B_95, A_96) | ~l1_pre_topc(B_95) | ~l1_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.13/1.49  tff(c_10, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.13/1.49  tff(c_565, plain, (![B_115, A_116]: (k3_xboole_0(k2_struct_0(B_115), k2_struct_0(A_116))=k2_struct_0(B_115) | ~m1_pre_topc(B_115, A_116) | ~l1_pre_topc(B_115) | ~l1_pre_topc(A_116))), inference(resolution, [status(thm)], [c_322, c_10])).
% 3.13/1.49  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.13/1.49  tff(c_183, plain, (![A_78, B_79, C_80]: (~r1_xboole_0(A_78, B_79) | ~r2_hidden(C_80, k3_xboole_0(A_78, B_79)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.13/1.49  tff(c_188, plain, (![A_78, B_79]: (~r1_xboole_0(A_78, B_79) | v1_xboole_0(k3_xboole_0(A_78, B_79)))), inference(resolution, [status(thm)], [c_4, c_183])).
% 3.13/1.49  tff(c_629, plain, (![B_119, A_120]: (~r1_xboole_0(k2_struct_0(B_119), k2_struct_0(A_120)) | v1_xboole_0(k2_struct_0(B_119)) | ~m1_pre_topc(B_119, A_120) | ~l1_pre_topc(B_119) | ~l1_pre_topc(A_120))), inference(superposition, [status(thm), theory('equality')], [c_565, c_188])).
% 3.13/1.49  tff(c_638, plain, (v1_xboole_0(k2_struct_0('#skF_7')) | ~m1_pre_topc('#skF_7', '#skF_8') | ~l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_8')), inference(resolution, [status(thm)], [c_462, c_629])).
% 3.13/1.49  tff(c_646, plain, (v1_xboole_0(k2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_101, c_56, c_638])).
% 3.13/1.49  tff(c_648, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_646])).
% 3.13/1.49  tff(c_650, plain, (~r1_tsep_1('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_54])).
% 3.13/1.49  tff(c_672, plain, (![B_128, A_129]: (l1_pre_topc(B_128) | ~m1_pre_topc(B_128, A_129) | ~l1_pre_topc(A_129))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.13/1.49  tff(c_678, plain, (l1_pre_topc('#skF_8') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_58, c_672])).
% 3.13/1.49  tff(c_687, plain, (l1_pre_topc('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_678])).
% 3.13/1.49  tff(c_657, plain, (![A_124]: (u1_struct_0(A_124)=k2_struct_0(A_124) | ~l1_struct_0(A_124))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.13/1.49  tff(c_661, plain, (![A_53]: (u1_struct_0(A_53)=k2_struct_0(A_53) | ~l1_pre_topc(A_53))), inference(resolution, [status(thm)], [c_42, c_657])).
% 3.13/1.49  tff(c_697, plain, (u1_struct_0('#skF_8')=k2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_687, c_661])).
% 3.13/1.49  tff(c_706, plain, (![A_130]: (~v1_xboole_0(u1_struct_0(A_130)) | ~l1_struct_0(A_130) | v2_struct_0(A_130))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.13/1.49  tff(c_709, plain, (~v1_xboole_0(k2_struct_0('#skF_8')) | ~l1_struct_0('#skF_8') | v2_struct_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_697, c_706])).
% 3.13/1.49  tff(c_716, plain, (~v1_xboole_0(k2_struct_0('#skF_8')) | ~l1_struct_0('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_60, c_709])).
% 3.13/1.49  tff(c_719, plain, (~l1_struct_0('#skF_8')), inference(splitLeft, [status(thm)], [c_716])).
% 3.13/1.49  tff(c_728, plain, (~l1_pre_topc('#skF_8')), inference(resolution, [status(thm)], [c_42, c_719])).
% 3.13/1.49  tff(c_732, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_687, c_728])).
% 3.13/1.49  tff(c_734, plain, (l1_struct_0('#skF_8')), inference(splitRight, [status(thm)], [c_716])).
% 3.13/1.49  tff(c_675, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_62, c_672])).
% 3.13/1.49  tff(c_684, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_675])).
% 3.13/1.49  tff(c_692, plain, (u1_struct_0('#skF_7')=k2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_684, c_661])).
% 3.13/1.49  tff(c_712, plain, (~v1_xboole_0(k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_692, c_706])).
% 3.13/1.49  tff(c_717, plain, (~v1_xboole_0(k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_64, c_712])).
% 3.13/1.49  tff(c_740, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_717])).
% 3.13/1.49  tff(c_743, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_42, c_740])).
% 3.13/1.49  tff(c_747, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_684, c_743])).
% 3.13/1.49  tff(c_749, plain, (l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_717])).
% 3.13/1.49  tff(c_649, plain, (r1_tsep_1('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_54])).
% 3.13/1.49  tff(c_777, plain, (![B_139, A_140]: (r1_tsep_1(B_139, A_140) | ~r1_tsep_1(A_140, B_139) | ~l1_struct_0(B_139) | ~l1_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.13/1.49  tff(c_779, plain, (r1_tsep_1('#skF_7', '#skF_8') | ~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_649, c_777])).
% 3.13/1.49  tff(c_782, plain, (r1_tsep_1('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_734, c_749, c_779])).
% 3.13/1.49  tff(c_784, plain, $false, inference(negUnitSimplification, [status(thm)], [c_650, c_782])).
% 3.13/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.49  
% 3.13/1.49  Inference rules
% 3.13/1.49  ----------------------
% 3.13/1.49  #Ref     : 0
% 3.13/1.49  #Sup     : 133
% 3.13/1.49  #Fact    : 0
% 3.13/1.49  #Define  : 0
% 3.13/1.49  #Split   : 15
% 3.13/1.49  #Chain   : 0
% 3.13/1.49  #Close   : 0
% 3.13/1.49  
% 3.13/1.49  Ordering : KBO
% 3.13/1.49  
% 3.13/1.49  Simplification rules
% 3.13/1.49  ----------------------
% 3.13/1.49  #Subsume      : 21
% 3.13/1.49  #Demod        : 106
% 3.13/1.49  #Tautology    : 42
% 3.13/1.49  #SimpNegUnit  : 29
% 3.13/1.49  #BackRed      : 0
% 3.13/1.49  
% 3.13/1.49  #Partial instantiations: 0
% 3.13/1.49  #Strategies tried      : 1
% 3.13/1.49  
% 3.13/1.49  Timing (in seconds)
% 3.13/1.49  ----------------------
% 3.13/1.50  Preprocessing        : 0.34
% 3.13/1.50  Parsing              : 0.17
% 3.13/1.50  CNF conversion       : 0.03
% 3.13/1.50  Main loop            : 0.39
% 3.13/1.50  Inferencing          : 0.14
% 3.13/1.50  Reduction            : 0.12
% 3.13/1.50  Demodulation         : 0.08
% 3.13/1.50  BG Simplification    : 0.02
% 3.13/1.50  Subsumption          : 0.08
% 3.13/1.50  Abstraction          : 0.02
% 3.13/1.50  MUC search           : 0.00
% 3.13/1.50  Cooper               : 0.00
% 3.13/1.50  Total                : 0.78
% 3.13/1.50  Index Insertion      : 0.00
% 3.13/1.50  Index Deletion       : 0.00
% 3.13/1.50  Index Matching       : 0.00
% 3.13/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
