%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:29 EST 2020

% Result     : Theorem 7.38s
% Output     : CNFRefutation 7.38s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 573 expanded)
%              Number of leaves         :   46 ( 208 expanded)
%              Depth                    :   16
%              Number of atoms          :  230 (1563 expanded)
%              Number of equality atoms :   38 ( 137 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_145,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_100,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_81,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

tff(f_117,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(c_12,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_98,plain,(
    ! [B_81,A_82] :
      ( ~ r1_tarski(B_81,A_82)
      | ~ r2_hidden(A_82,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_180,plain,(
    ! [A_92] :
      ( ~ r1_tarski(A_92,'#skF_1'(A_92))
      | v1_xboole_0(A_92) ) ),
    inference(resolution,[status(thm)],[c_6,c_98])).

tff(c_185,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_180])).

tff(c_223,plain,(
    ! [A_97,B_98] :
      ( k3_xboole_0(A_97,B_98) = A_97
      | ~ r1_tarski(A_97,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_228,plain,(
    ! [A_99] : k3_xboole_0(k1_xboole_0,A_99) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_223])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_233,plain,(
    ! [A_99] : k3_xboole_0(A_99,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_2])).

tff(c_16,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_140,plain,(
    ! [A_87,B_88] :
      ( k4_xboole_0(A_87,B_88) = A_87
      | ~ r1_xboole_0(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_144,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(resolution,[status(thm)],[c_16,c_140])).

tff(c_328,plain,(
    ! [A_103,B_104] : k4_xboole_0(A_103,k4_xboole_0(A_103,B_104)) = k3_xboole_0(A_103,B_104) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_354,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_328])).

tff(c_360,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_354])).

tff(c_215,plain,(
    ! [A_95,B_96] :
      ( r1_xboole_0(A_95,B_96)
      | k4_xboole_0(A_95,B_96) != A_95 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( r1_xboole_0(B_8,A_7)
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_222,plain,(
    ! [B_96,A_95] :
      ( r1_xboole_0(B_96,A_95)
      | k4_xboole_0(A_95,B_96) != A_95 ) ),
    inference(resolution,[status(thm)],[c_215,c_8])).

tff(c_78,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_74,plain,(
    m1_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_249,plain,(
    ! [B_100,A_101] :
      ( l1_pre_topc(B_100)
      | ~ m1_pre_topc(B_100,A_101)
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_252,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_249])).

tff(c_261,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_252])).

tff(c_54,plain,(
    ! [A_60] :
      ( l1_struct_0(A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_93,plain,(
    ! [A_80] :
      ( u1_struct_0(A_80) = k2_struct_0(A_80)
      | ~ l1_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_97,plain,(
    ! [A_60] :
      ( u1_struct_0(A_60) = k2_struct_0(A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(resolution,[status(thm)],[c_54,c_93])).

tff(c_269,plain,(
    u1_struct_0('#skF_6') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_261,c_97])).

tff(c_58,plain,(
    ! [A_64] :
      ( ~ v1_xboole_0(u1_struct_0(A_64))
      | ~ l1_struct_0(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_279,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_6'))
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_58])).

tff(c_282,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_6'))
    | ~ l1_struct_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_279])).

tff(c_419,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_282])).

tff(c_423,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_419])).

tff(c_427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_423])).

tff(c_429,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_282])).

tff(c_463,plain,(
    ! [A_109,B_110] :
      ( r1_tsep_1(A_109,B_110)
      | ~ r1_xboole_0(u1_struct_0(A_109),u1_struct_0(B_110))
      | ~ l1_struct_0(B_110)
      | ~ l1_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_472,plain,(
    ! [B_110] :
      ( r1_tsep_1('#skF_6',B_110)
      | ~ r1_xboole_0(k2_struct_0('#skF_6'),u1_struct_0(B_110))
      | ~ l1_struct_0(B_110)
      | ~ l1_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_463])).

tff(c_4831,plain,(
    ! [B_276] :
      ( r1_tsep_1('#skF_6',B_276)
      | ~ r1_xboole_0(k2_struct_0('#skF_6'),u1_struct_0(B_276))
      | ~ l1_struct_0(B_276) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_472])).

tff(c_4840,plain,
    ( r1_tsep_1('#skF_6','#skF_6')
    | ~ r1_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_6'))
    | ~ l1_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_4831])).

tff(c_4851,plain,
    ( r1_tsep_1('#skF_6','#skF_6')
    | ~ r1_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_4840])).

tff(c_4855,plain,(
    ~ r1_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_4851])).

tff(c_4874,plain,(
    k4_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_6')) != k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_222,c_4855])).

tff(c_4879,plain,(
    k2_struct_0('#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_4874])).

tff(c_70,plain,(
    m1_pre_topc('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_255,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_249])).

tff(c_264,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_255])).

tff(c_68,plain,(
    m1_pre_topc('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_621,plain,(
    ! [B_119,A_120] :
      ( r1_tarski(k2_struct_0(B_119),k2_struct_0(A_120))
      | ~ m1_pre_topc(B_119,A_120)
      | ~ l1_pre_topc(B_119)
      | ~ l1_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_7556,plain,(
    ! [B_383,A_384] :
      ( k3_xboole_0(k2_struct_0(B_383),k2_struct_0(A_384)) = k2_struct_0(B_383)
      | ~ m1_pre_topc(B_383,A_384)
      | ~ l1_pre_topc(B_383)
      | ~ l1_pre_topc(A_384) ) ),
    inference(resolution,[status(thm)],[c_621,c_10])).

tff(c_66,plain,
    ( r1_tsep_1('#skF_7','#skF_6')
    | r1_tsep_1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_84,plain,(
    r1_tsep_1('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_273,plain,(
    u1_struct_0('#skF_7') = k2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_264,c_97])).

tff(c_287,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_7'))
    | ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_58])).

tff(c_290,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_7'))
    | ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_287])).

tff(c_435,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_290])).

tff(c_438,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_435])).

tff(c_442,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_438])).

tff(c_444,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_290])).

tff(c_671,plain,(
    ! [A_122,B_123] :
      ( r1_xboole_0(u1_struct_0(A_122),u1_struct_0(B_123))
      | ~ r1_tsep_1(A_122,B_123)
      | ~ l1_struct_0(B_123)
      | ~ l1_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_685,plain,(
    ! [A_122] :
      ( r1_xboole_0(u1_struct_0(A_122),k2_struct_0('#skF_7'))
      | ~ r1_tsep_1(A_122,'#skF_7')
      | ~ l1_struct_0('#skF_7')
      | ~ l1_struct_0(A_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_671])).

tff(c_4737,plain,(
    ! [A_272] :
      ( r1_xboole_0(u1_struct_0(A_272),k2_struct_0('#skF_7'))
      | ~ r1_tsep_1(A_272,'#skF_7')
      | ~ l1_struct_0(A_272) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_685])).

tff(c_4748,plain,
    ( r1_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_7'))
    | ~ r1_tsep_1('#skF_6','#skF_7')
    | ~ l1_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_4737])).

tff(c_4757,plain,(
    r1_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_84,c_4748])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,B_16) = A_15
      | ~ r1_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4766,plain,(
    k4_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_7')) = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4757,c_18])).

tff(c_14,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4798,plain,(
    k4_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_6')) = k3_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4766,c_14])).

tff(c_4802,plain,(
    k3_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_7')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_4798])).

tff(c_7574,plain,
    ( k2_struct_0('#skF_6') = k1_xboole_0
    | ~ m1_pre_topc('#skF_6','#skF_7')
    | ~ l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_7556,c_4802])).

tff(c_7617,plain,(
    k2_struct_0('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_261,c_68,c_7574])).

tff(c_7619,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4879,c_7617])).

tff(c_7621,plain,(
    r1_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_4851])).

tff(c_7629,plain,(
    k4_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_6')) = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_7621,c_18])).

tff(c_7633,plain,(
    k2_struct_0('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_7629])).

tff(c_428,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_282])).

tff(c_7648,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7633,c_428])).

tff(c_7665,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_7648])).

tff(c_7667,plain,(
    ~ r1_tsep_1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_7748,plain,(
    ! [B_401,A_402] :
      ( l1_pre_topc(B_401)
      | ~ m1_pre_topc(B_401,A_402)
      | ~ l1_pre_topc(A_402) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_7754,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_7748])).

tff(c_7763,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_7754])).

tff(c_7675,plain,(
    ! [A_391] :
      ( u1_struct_0(A_391) = k2_struct_0(A_391)
      | ~ l1_struct_0(A_391) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_7679,plain,(
    ! [A_60] :
      ( u1_struct_0(A_60) = k2_struct_0(A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(resolution,[status(thm)],[c_54,c_7675])).

tff(c_7772,plain,(
    u1_struct_0('#skF_7') = k2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_7763,c_7679])).

tff(c_7801,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_7'))
    | ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_7772,c_58])).

tff(c_7804,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_7'))
    | ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_7801])).

tff(c_7857,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_7804])).

tff(c_7860,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_7857])).

tff(c_7864,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7763,c_7860])).

tff(c_7866,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_7804])).

tff(c_7751,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_7748])).

tff(c_7760,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_7751])).

tff(c_7768,plain,(
    u1_struct_0('#skF_6') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_7760,c_7679])).

tff(c_7793,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_6'))
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_7768,c_58])).

tff(c_7796,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_6'))
    | ~ l1_struct_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_7793])).

tff(c_7841,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_7796])).

tff(c_7845,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_7841])).

tff(c_7849,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7760,c_7845])).

tff(c_7851,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_7796])).

tff(c_7666,plain,(
    r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_8055,plain,(
    ! [B_421,A_422] :
      ( r1_tsep_1(B_421,A_422)
      | ~ r1_tsep_1(A_422,B_421)
      | ~ l1_struct_0(B_421)
      | ~ l1_struct_0(A_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_8057,plain,
    ( r1_tsep_1('#skF_6','#skF_7')
    | ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_7666,c_8055])).

tff(c_8060,plain,(
    r1_tsep_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7866,c_7851,c_8057])).

tff(c_8062,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7667,c_8060])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:19:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.38/2.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.38/2.56  
% 7.38/2.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.38/2.57  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 7.38/2.57  
% 7.38/2.57  %Foreground sorts:
% 7.38/2.57  
% 7.38/2.57  
% 7.38/2.57  %Background operators:
% 7.38/2.57  
% 7.38/2.57  
% 7.38/2.57  %Foreground operators:
% 7.38/2.57  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.38/2.57  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 7.38/2.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.38/2.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.38/2.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.38/2.57  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.38/2.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.38/2.57  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.38/2.57  tff('#skF_7', type, '#skF_7': $i).
% 7.38/2.57  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.38/2.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.38/2.57  tff('#skF_5', type, '#skF_5': $i).
% 7.38/2.57  tff('#skF_6', type, '#skF_6': $i).
% 7.38/2.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.38/2.57  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.38/2.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.38/2.57  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.38/2.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.38/2.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.38/2.57  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.38/2.57  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.38/2.57  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 7.38/2.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.38/2.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.38/2.57  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.38/2.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.38/2.57  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.38/2.57  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.38/2.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.38/2.57  
% 7.38/2.59  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.38/2.59  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.38/2.59  tff(f_56, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 7.38/2.59  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.38/2.59  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.38/2.59  tff(f_47, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 7.38/2.59  tff(f_51, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 7.38/2.59  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.38/2.59  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 7.38/2.59  tff(f_145, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (~r1_tsep_1(B, C) & ~r1_tsep_1(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_tmap_1)).
% 7.38/2.59  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 7.38/2.59  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.38/2.59  tff(f_60, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 7.38/2.59  tff(f_100, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 7.38/2.59  tff(f_109, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 7.38/2.59  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(B, A) <=> (r1_tarski(k2_struct_0(B), k2_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (r2_hidden(C, u1_pre_topc(B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(D, u1_pre_topc(A))) & (C = k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_pre_topc)).
% 7.38/2.59  tff(f_117, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 7.38/2.59  tff(c_12, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.38/2.59  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.38/2.59  tff(c_98, plain, (![B_81, A_82]: (~r1_tarski(B_81, A_82) | ~r2_hidden(A_82, B_81))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.38/2.59  tff(c_180, plain, (![A_92]: (~r1_tarski(A_92, '#skF_1'(A_92)) | v1_xboole_0(A_92))), inference(resolution, [status(thm)], [c_6, c_98])).
% 7.38/2.59  tff(c_185, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_180])).
% 7.38/2.59  tff(c_223, plain, (![A_97, B_98]: (k3_xboole_0(A_97, B_98)=A_97 | ~r1_tarski(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.38/2.59  tff(c_228, plain, (![A_99]: (k3_xboole_0(k1_xboole_0, A_99)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_223])).
% 7.38/2.59  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.38/2.59  tff(c_233, plain, (![A_99]: (k3_xboole_0(A_99, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_228, c_2])).
% 7.38/2.59  tff(c_16, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.38/2.59  tff(c_140, plain, (![A_87, B_88]: (k4_xboole_0(A_87, B_88)=A_87 | ~r1_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.38/2.59  tff(c_144, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(resolution, [status(thm)], [c_16, c_140])).
% 7.38/2.59  tff(c_328, plain, (![A_103, B_104]: (k4_xboole_0(A_103, k4_xboole_0(A_103, B_104))=k3_xboole_0(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.38/2.59  tff(c_354, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_144, c_328])).
% 7.38/2.59  tff(c_360, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_233, c_354])).
% 7.38/2.59  tff(c_215, plain, (![A_95, B_96]: (r1_xboole_0(A_95, B_96) | k4_xboole_0(A_95, B_96)!=A_95)), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.38/2.59  tff(c_8, plain, (![B_8, A_7]: (r1_xboole_0(B_8, A_7) | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.38/2.59  tff(c_222, plain, (![B_96, A_95]: (r1_xboole_0(B_96, A_95) | k4_xboole_0(A_95, B_96)!=A_95)), inference(resolution, [status(thm)], [c_215, c_8])).
% 7.38/2.59  tff(c_78, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_145])).
% 7.38/2.59  tff(c_74, plain, (m1_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_145])).
% 7.38/2.59  tff(c_249, plain, (![B_100, A_101]: (l1_pre_topc(B_100) | ~m1_pre_topc(B_100, A_101) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.38/2.59  tff(c_252, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_74, c_249])).
% 7.38/2.59  tff(c_261, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_252])).
% 7.38/2.59  tff(c_54, plain, (![A_60]: (l1_struct_0(A_60) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.38/2.59  tff(c_76, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_145])).
% 7.38/2.59  tff(c_93, plain, (![A_80]: (u1_struct_0(A_80)=k2_struct_0(A_80) | ~l1_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.38/2.59  tff(c_97, plain, (![A_60]: (u1_struct_0(A_60)=k2_struct_0(A_60) | ~l1_pre_topc(A_60))), inference(resolution, [status(thm)], [c_54, c_93])).
% 7.38/2.59  tff(c_269, plain, (u1_struct_0('#skF_6')=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_261, c_97])).
% 7.38/2.59  tff(c_58, plain, (![A_64]: (~v1_xboole_0(u1_struct_0(A_64)) | ~l1_struct_0(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.38/2.59  tff(c_279, plain, (~v1_xboole_0(k2_struct_0('#skF_6')) | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_269, c_58])).
% 7.38/2.59  tff(c_282, plain, (~v1_xboole_0(k2_struct_0('#skF_6')) | ~l1_struct_0('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_76, c_279])).
% 7.38/2.59  tff(c_419, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_282])).
% 7.38/2.59  tff(c_423, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_54, c_419])).
% 7.38/2.59  tff(c_427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_261, c_423])).
% 7.38/2.59  tff(c_429, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_282])).
% 7.38/2.59  tff(c_463, plain, (![A_109, B_110]: (r1_tsep_1(A_109, B_110) | ~r1_xboole_0(u1_struct_0(A_109), u1_struct_0(B_110)) | ~l1_struct_0(B_110) | ~l1_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.38/2.59  tff(c_472, plain, (![B_110]: (r1_tsep_1('#skF_6', B_110) | ~r1_xboole_0(k2_struct_0('#skF_6'), u1_struct_0(B_110)) | ~l1_struct_0(B_110) | ~l1_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_269, c_463])).
% 7.38/2.59  tff(c_4831, plain, (![B_276]: (r1_tsep_1('#skF_6', B_276) | ~r1_xboole_0(k2_struct_0('#skF_6'), u1_struct_0(B_276)) | ~l1_struct_0(B_276))), inference(demodulation, [status(thm), theory('equality')], [c_429, c_472])).
% 7.38/2.59  tff(c_4840, plain, (r1_tsep_1('#skF_6', '#skF_6') | ~r1_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_6')) | ~l1_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_269, c_4831])).
% 7.38/2.59  tff(c_4851, plain, (r1_tsep_1('#skF_6', '#skF_6') | ~r1_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_429, c_4840])).
% 7.38/2.59  tff(c_4855, plain, (~r1_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_4851])).
% 7.38/2.59  tff(c_4874, plain, (k4_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_6'))!=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_222, c_4855])).
% 7.38/2.59  tff(c_4879, plain, (k2_struct_0('#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_360, c_4874])).
% 7.38/2.59  tff(c_70, plain, (m1_pre_topc('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_145])).
% 7.38/2.59  tff(c_255, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_70, c_249])).
% 7.38/2.59  tff(c_264, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_255])).
% 7.38/2.59  tff(c_68, plain, (m1_pre_topc('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_145])).
% 7.38/2.59  tff(c_621, plain, (![B_119, A_120]: (r1_tarski(k2_struct_0(B_119), k2_struct_0(A_120)) | ~m1_pre_topc(B_119, A_120) | ~l1_pre_topc(B_119) | ~l1_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.38/2.59  tff(c_10, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.38/2.59  tff(c_7556, plain, (![B_383, A_384]: (k3_xboole_0(k2_struct_0(B_383), k2_struct_0(A_384))=k2_struct_0(B_383) | ~m1_pre_topc(B_383, A_384) | ~l1_pre_topc(B_383) | ~l1_pre_topc(A_384))), inference(resolution, [status(thm)], [c_621, c_10])).
% 7.38/2.59  tff(c_66, plain, (r1_tsep_1('#skF_7', '#skF_6') | r1_tsep_1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_145])).
% 7.38/2.59  tff(c_84, plain, (r1_tsep_1('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_66])).
% 7.38/2.59  tff(c_72, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_145])).
% 7.38/2.59  tff(c_273, plain, (u1_struct_0('#skF_7')=k2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_264, c_97])).
% 7.38/2.59  tff(c_287, plain, (~v1_xboole_0(k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_273, c_58])).
% 7.38/2.59  tff(c_290, plain, (~v1_xboole_0(k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_72, c_287])).
% 7.38/2.59  tff(c_435, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_290])).
% 7.38/2.59  tff(c_438, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_54, c_435])).
% 7.38/2.59  tff(c_442, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_264, c_438])).
% 7.38/2.59  tff(c_444, plain, (l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_290])).
% 7.38/2.59  tff(c_671, plain, (![A_122, B_123]: (r1_xboole_0(u1_struct_0(A_122), u1_struct_0(B_123)) | ~r1_tsep_1(A_122, B_123) | ~l1_struct_0(B_123) | ~l1_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.38/2.59  tff(c_685, plain, (![A_122]: (r1_xboole_0(u1_struct_0(A_122), k2_struct_0('#skF_7')) | ~r1_tsep_1(A_122, '#skF_7') | ~l1_struct_0('#skF_7') | ~l1_struct_0(A_122))), inference(superposition, [status(thm), theory('equality')], [c_273, c_671])).
% 7.38/2.59  tff(c_4737, plain, (![A_272]: (r1_xboole_0(u1_struct_0(A_272), k2_struct_0('#skF_7')) | ~r1_tsep_1(A_272, '#skF_7') | ~l1_struct_0(A_272))), inference(demodulation, [status(thm), theory('equality')], [c_444, c_685])).
% 7.38/2.59  tff(c_4748, plain, (r1_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_7')) | ~r1_tsep_1('#skF_6', '#skF_7') | ~l1_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_269, c_4737])).
% 7.38/2.59  tff(c_4757, plain, (r1_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_429, c_84, c_4748])).
% 7.38/2.59  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, B_16)=A_15 | ~r1_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.38/2.59  tff(c_4766, plain, (k4_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_7'))=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_4757, c_18])).
% 7.38/2.59  tff(c_14, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.38/2.59  tff(c_4798, plain, (k4_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_6'))=k3_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_4766, c_14])).
% 7.38/2.59  tff(c_4802, plain, (k3_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_7'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_360, c_4798])).
% 7.38/2.59  tff(c_7574, plain, (k2_struct_0('#skF_6')=k1_xboole_0 | ~m1_pre_topc('#skF_6', '#skF_7') | ~l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_7556, c_4802])).
% 7.38/2.59  tff(c_7617, plain, (k2_struct_0('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_264, c_261, c_68, c_7574])).
% 7.38/2.59  tff(c_7619, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4879, c_7617])).
% 7.38/2.59  tff(c_7621, plain, (r1_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_4851])).
% 7.38/2.59  tff(c_7629, plain, (k4_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_6'))=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_7621, c_18])).
% 7.38/2.59  tff(c_7633, plain, (k2_struct_0('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_360, c_7629])).
% 7.38/2.59  tff(c_428, plain, (~v1_xboole_0(k2_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_282])).
% 7.38/2.59  tff(c_7648, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7633, c_428])).
% 7.38/2.59  tff(c_7665, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_185, c_7648])).
% 7.38/2.59  tff(c_7667, plain, (~r1_tsep_1('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_66])).
% 7.38/2.59  tff(c_7748, plain, (![B_401, A_402]: (l1_pre_topc(B_401) | ~m1_pre_topc(B_401, A_402) | ~l1_pre_topc(A_402))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.38/2.59  tff(c_7754, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_70, c_7748])).
% 7.38/2.59  tff(c_7763, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_7754])).
% 7.38/2.59  tff(c_7675, plain, (![A_391]: (u1_struct_0(A_391)=k2_struct_0(A_391) | ~l1_struct_0(A_391))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.38/2.59  tff(c_7679, plain, (![A_60]: (u1_struct_0(A_60)=k2_struct_0(A_60) | ~l1_pre_topc(A_60))), inference(resolution, [status(thm)], [c_54, c_7675])).
% 7.38/2.59  tff(c_7772, plain, (u1_struct_0('#skF_7')=k2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_7763, c_7679])).
% 7.38/2.59  tff(c_7801, plain, (~v1_xboole_0(k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_7772, c_58])).
% 7.38/2.59  tff(c_7804, plain, (~v1_xboole_0(k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_72, c_7801])).
% 7.38/2.59  tff(c_7857, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_7804])).
% 7.38/2.59  tff(c_7860, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_54, c_7857])).
% 7.38/2.59  tff(c_7864, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7763, c_7860])).
% 7.38/2.59  tff(c_7866, plain, (l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_7804])).
% 7.38/2.59  tff(c_7751, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_74, c_7748])).
% 7.38/2.59  tff(c_7760, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_7751])).
% 7.38/2.59  tff(c_7768, plain, (u1_struct_0('#skF_6')=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_7760, c_7679])).
% 7.38/2.59  tff(c_7793, plain, (~v1_xboole_0(k2_struct_0('#skF_6')) | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_7768, c_58])).
% 7.38/2.59  tff(c_7796, plain, (~v1_xboole_0(k2_struct_0('#skF_6')) | ~l1_struct_0('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_76, c_7793])).
% 7.38/2.59  tff(c_7841, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_7796])).
% 7.38/2.59  tff(c_7845, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_54, c_7841])).
% 7.38/2.59  tff(c_7849, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7760, c_7845])).
% 7.38/2.59  tff(c_7851, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_7796])).
% 7.38/2.59  tff(c_7666, plain, (r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_66])).
% 7.38/2.59  tff(c_8055, plain, (![B_421, A_422]: (r1_tsep_1(B_421, A_422) | ~r1_tsep_1(A_422, B_421) | ~l1_struct_0(B_421) | ~l1_struct_0(A_422))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.38/2.59  tff(c_8057, plain, (r1_tsep_1('#skF_6', '#skF_7') | ~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_7666, c_8055])).
% 7.38/2.59  tff(c_8060, plain, (r1_tsep_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_7866, c_7851, c_8057])).
% 7.38/2.59  tff(c_8062, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7667, c_8060])).
% 7.38/2.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.38/2.59  
% 7.38/2.59  Inference rules
% 7.38/2.59  ----------------------
% 7.38/2.59  #Ref     : 0
% 7.38/2.59  #Sup     : 1766
% 7.38/2.59  #Fact    : 0
% 7.38/2.59  #Define  : 0
% 7.38/2.59  #Split   : 21
% 7.38/2.59  #Chain   : 0
% 7.38/2.59  #Close   : 0
% 7.38/2.59  
% 7.38/2.59  Ordering : KBO
% 7.38/2.59  
% 7.38/2.59  Simplification rules
% 7.38/2.59  ----------------------
% 7.38/2.59  #Subsume      : 389
% 7.38/2.59  #Demod        : 2013
% 7.38/2.59  #Tautology    : 669
% 7.38/2.59  #SimpNegUnit  : 249
% 7.38/2.59  #BackRed      : 27
% 7.38/2.59  
% 7.38/2.59  #Partial instantiations: 0
% 7.38/2.59  #Strategies tried      : 1
% 7.38/2.59  
% 7.38/2.59  Timing (in seconds)
% 7.38/2.59  ----------------------
% 7.38/2.59  Preprocessing        : 0.36
% 7.38/2.59  Parsing              : 0.19
% 7.38/2.59  CNF conversion       : 0.03
% 7.38/2.59  Main loop            : 1.43
% 7.38/2.59  Inferencing          : 0.47
% 7.38/2.59  Reduction            : 0.55
% 7.38/2.59  Demodulation         : 0.40
% 7.38/2.59  BG Simplification    : 0.05
% 7.38/2.59  Subsumption          : 0.27
% 7.38/2.59  Abstraction          : 0.08
% 7.66/2.59  MUC search           : 0.00
% 7.66/2.59  Cooper               : 0.00
% 7.66/2.59  Total                : 1.84
% 7.66/2.59  Index Insertion      : 0.00
% 7.66/2.59  Index Deletion       : 0.00
% 7.66/2.59  Index Matching       : 0.00
% 7.66/2.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
