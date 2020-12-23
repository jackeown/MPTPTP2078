%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:46 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 168 expanded)
%              Number of leaves         :   34 (  69 expanded)
%              Depth                    :   11
%              Number of atoms          :  177 ( 435 expanded)
%              Number of equality atoms :   41 (  81 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k8_subset_1 > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k8_subset_1,type,(
    k8_subset_1: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r1_tarski(C,B)
                      & v3_pre_topc(C,A) )
                   => C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_55,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k8_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k8_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_43,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

tff(c_42,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_63,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_695,plain,(
    ! [B_94,A_95] :
      ( v2_tops_1(B_94,A_95)
      | k1_tops_1(A_95,B_94) != k1_xboole_0
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_715,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_695])).

tff(c_729,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_715])).

tff(c_730,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_729])).

tff(c_628,plain,(
    ! [A_92,B_93] :
      ( r1_tarski(k1_tops_1(A_92,B_93),B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_642,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_628])).

tff(c_656,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_642])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_663,plain,(
    k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_656,c_10])).

tff(c_14,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_118,plain,(
    ! [A_51,B_52] : k1_setfam_1(k2_tarski(A_51,B_52)) = k3_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_151,plain,(
    ! [A_57,B_58] : k1_setfam_1(k2_tarski(A_57,B_58)) = k3_xboole_0(B_58,A_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_118])).

tff(c_20,plain,(
    ! [A_17,B_18] : k1_setfam_1(k2_tarski(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_157,plain,(
    ! [B_58,A_57] : k3_xboole_0(B_58,A_57) = k3_xboole_0(A_57,B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_20])).

tff(c_457,plain,(
    ! [A_83,B_84,C_85] :
      ( k8_subset_1(A_83,B_84,C_85) = k3_xboole_0(B_84,C_85)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_467,plain,(
    ! [C_86] : k8_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_86) = k3_xboole_0('#skF_2',C_86) ),
    inference(resolution,[status(thm)],[c_36,c_457])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] :
      ( m1_subset_1(k8_subset_1(A_11,B_12,C_13),k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_473,plain,(
    ! [C_86] :
      ( m1_subset_1(k3_xboole_0('#skF_2',C_86),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_467,c_16])).

tff(c_481,plain,(
    ! [C_87] : m1_subset_1(k3_xboole_0('#skF_2',C_87),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_473])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ m1_subset_1(A_19,k1_zfmisc_1(B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_528,plain,(
    ! [C_88] : r1_tarski(k3_xboole_0('#skF_2',C_88),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_481,c_22])).

tff(c_540,plain,(
    ! [B_58] : r1_tarski(k3_xboole_0(B_58,'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_528])).

tff(c_735,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_663,c_540])).

tff(c_24,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_60,plain,(
    ! [C_43] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_43
      | ~ v3_pre_topc(C_43,'#skF_1')
      | ~ r1_tarski(C_43,'#skF_2')
      | ~ m1_subset_1(C_43,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_334,plain,(
    ! [C_70] :
      ( k1_xboole_0 = C_70
      | ~ v3_pre_topc(C_70,'#skF_1')
      | ~ r1_tarski(C_70,'#skF_2')
      | ~ m1_subset_1(C_70,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_60])).

tff(c_342,plain,(
    ! [A_19] :
      ( k1_xboole_0 = A_19
      | ~ v3_pre_topc(A_19,'#skF_1')
      | ~ r1_tarski(A_19,'#skF_2')
      | ~ r1_tarski(A_19,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_24,c_334])).

tff(c_797,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_735,c_342])).

tff(c_805,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_656,c_797])).

tff(c_806,plain,(
    ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_730,c_805])).

tff(c_40,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_852,plain,(
    ! [A_97,B_98] :
      ( v3_pre_topc(k1_tops_1(A_97,B_98),A_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97)
      | ~ v2_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_868,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_852])).

tff(c_885,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_868])).

tff(c_887,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_806,c_885])).

tff(c_888,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1079,plain,(
    ! [A_117,C_118,B_119] :
      ( r1_tarski(k3_xboole_0(A_117,C_118),B_119)
      | ~ r1_tarski(A_117,B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1110,plain,(
    ! [A_120,C_121] :
      ( k3_xboole_0(A_120,C_121) = k1_xboole_0
      | ~ r1_tarski(A_120,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1079,c_12])).

tff(c_1119,plain,(
    ! [C_122] : k3_xboole_0(k1_xboole_0,C_122) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_1110])).

tff(c_988,plain,(
    ! [A_109,B_110] : k1_setfam_1(k2_tarski(A_109,B_110)) = k3_xboole_0(A_109,B_110) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1003,plain,(
    ! [B_111,A_112] : k1_setfam_1(k2_tarski(B_111,A_112)) = k3_xboole_0(A_112,B_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_988])).

tff(c_1009,plain,(
    ! [B_111,A_112] : k3_xboole_0(B_111,A_112) = k3_xboole_0(A_112,B_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_1003,c_20])).

tff(c_1154,plain,(
    ! [C_123] : k3_xboole_0(C_123,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1119,c_1009])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k3_xboole_0(A_3,C_5),B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1203,plain,(
    ! [B_124,C_125] :
      ( r1_tarski(k1_xboole_0,B_124)
      | ~ r1_tarski(C_125,B_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1154,c_8])).

tff(c_1218,plain,(
    ! [B_2] : r1_tarski(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_1203])).

tff(c_889,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_44,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_891,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_889,c_44])).

tff(c_46,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_933,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_889,c_46])).

tff(c_48,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_971,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_889,c_48])).

tff(c_1912,plain,(
    ! [A_159,B_160] :
      ( k1_tops_1(A_159,B_160) = k1_xboole_0
      | ~ v2_tops_1(B_160,A_159)
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ l1_pre_topc(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1941,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_1912])).

tff(c_1965,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_889,c_1941])).

tff(c_2025,plain,(
    ! [B_164,A_165,C_166] :
      ( r1_tarski(B_164,k1_tops_1(A_165,C_166))
      | ~ r1_tarski(B_164,C_166)
      | ~ v3_pre_topc(B_164,A_165)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ m1_subset_1(B_164,k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ l1_pre_topc(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2045,plain,(
    ! [B_164] :
      ( r1_tarski(B_164,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_164,'#skF_2')
      | ~ v3_pre_topc(B_164,'#skF_1')
      | ~ m1_subset_1(B_164,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_2025])).

tff(c_2105,plain,(
    ! [B_167] :
      ( r1_tarski(B_167,k1_xboole_0)
      | ~ r1_tarski(B_167,'#skF_2')
      | ~ v3_pre_topc(B_167,'#skF_1')
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1965,c_2045])).

tff(c_2127,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_971,c_2105])).

tff(c_2145,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_891,c_933,c_2127])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2155,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_2145,c_2])).

tff(c_2166,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1218,c_2155])).

tff(c_2168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_888,c_2166])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:08:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.51/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/1.61  
% 3.51/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.77/1.61  %$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k8_subset_1 > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.77/1.61  
% 3.77/1.61  %Foreground sorts:
% 3.77/1.61  
% 3.77/1.61  
% 3.77/1.61  %Background operators:
% 3.77/1.61  
% 3.77/1.61  
% 3.77/1.61  %Foreground operators:
% 3.77/1.61  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.77/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.77/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.77/1.61  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.77/1.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.77/1.61  tff(k8_subset_1, type, k8_subset_1: ($i * $i * $i) > $i).
% 3.77/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.77/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.77/1.61  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.77/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.77/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.77/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.77/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.77/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.77/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.77/1.61  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.77/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.77/1.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.77/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.77/1.61  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.77/1.61  
% 3.77/1.63  tff(f_116, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 3.77/1.63  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 3.77/1.63  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 3.77/1.63  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.77/1.63  tff(f_45, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.77/1.63  tff(f_55, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.77/1.63  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_subset_1)).
% 3.77/1.63  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k8_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_subset_1)).
% 3.77/1.63  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.77/1.63  tff(f_67, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.77/1.63  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.77/1.63  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 3.77/1.63  tff(f_43, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.77/1.63  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 3.77/1.63  tff(c_42, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.77/1.63  tff(c_63, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_42])).
% 3.77/1.63  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.77/1.63  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.77/1.63  tff(c_695, plain, (![B_94, A_95]: (v2_tops_1(B_94, A_95) | k1_tops_1(A_95, B_94)!=k1_xboole_0 | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.77/1.63  tff(c_715, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_695])).
% 3.77/1.63  tff(c_729, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_715])).
% 3.77/1.63  tff(c_730, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_63, c_729])).
% 3.77/1.63  tff(c_628, plain, (![A_92, B_93]: (r1_tarski(k1_tops_1(A_92, B_93), B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.77/1.63  tff(c_642, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_628])).
% 3.77/1.63  tff(c_656, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_642])).
% 3.77/1.63  tff(c_10, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.77/1.63  tff(c_663, plain, (k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_656, c_10])).
% 3.77/1.63  tff(c_14, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.77/1.63  tff(c_118, plain, (![A_51, B_52]: (k1_setfam_1(k2_tarski(A_51, B_52))=k3_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.77/1.63  tff(c_151, plain, (![A_57, B_58]: (k1_setfam_1(k2_tarski(A_57, B_58))=k3_xboole_0(B_58, A_57))), inference(superposition, [status(thm), theory('equality')], [c_14, c_118])).
% 3.77/1.63  tff(c_20, plain, (![A_17, B_18]: (k1_setfam_1(k2_tarski(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.77/1.63  tff(c_157, plain, (![B_58, A_57]: (k3_xboole_0(B_58, A_57)=k3_xboole_0(A_57, B_58))), inference(superposition, [status(thm), theory('equality')], [c_151, c_20])).
% 3.77/1.63  tff(c_457, plain, (![A_83, B_84, C_85]: (k8_subset_1(A_83, B_84, C_85)=k3_xboole_0(B_84, C_85) | ~m1_subset_1(B_84, k1_zfmisc_1(A_83)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.77/1.63  tff(c_467, plain, (![C_86]: (k8_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_86)=k3_xboole_0('#skF_2', C_86))), inference(resolution, [status(thm)], [c_36, c_457])).
% 3.77/1.63  tff(c_16, plain, (![A_11, B_12, C_13]: (m1_subset_1(k8_subset_1(A_11, B_12, C_13), k1_zfmisc_1(A_11)) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.77/1.63  tff(c_473, plain, (![C_86]: (m1_subset_1(k3_xboole_0('#skF_2', C_86), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_467, c_16])).
% 3.77/1.63  tff(c_481, plain, (![C_87]: (m1_subset_1(k3_xboole_0('#skF_2', C_87), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_473])).
% 3.77/1.63  tff(c_22, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~m1_subset_1(A_19, k1_zfmisc_1(B_20)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.77/1.63  tff(c_528, plain, (![C_88]: (r1_tarski(k3_xboole_0('#skF_2', C_88), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_481, c_22])).
% 3.77/1.63  tff(c_540, plain, (![B_58]: (r1_tarski(k3_xboole_0(B_58, '#skF_2'), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_157, c_528])).
% 3.77/1.63  tff(c_735, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_663, c_540])).
% 3.77/1.63  tff(c_24, plain, (![A_19, B_20]: (m1_subset_1(A_19, k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.77/1.63  tff(c_60, plain, (![C_43]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_43 | ~v3_pre_topc(C_43, '#skF_1') | ~r1_tarski(C_43, '#skF_2') | ~m1_subset_1(C_43, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.77/1.63  tff(c_334, plain, (![C_70]: (k1_xboole_0=C_70 | ~v3_pre_topc(C_70, '#skF_1') | ~r1_tarski(C_70, '#skF_2') | ~m1_subset_1(C_70, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_63, c_60])).
% 3.77/1.63  tff(c_342, plain, (![A_19]: (k1_xboole_0=A_19 | ~v3_pre_topc(A_19, '#skF_1') | ~r1_tarski(A_19, '#skF_2') | ~r1_tarski(A_19, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_24, c_334])).
% 3.77/1.63  tff(c_797, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_735, c_342])).
% 3.77/1.63  tff(c_805, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_656, c_797])).
% 3.77/1.63  tff(c_806, plain, (~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_730, c_805])).
% 3.77/1.63  tff(c_40, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.77/1.63  tff(c_852, plain, (![A_97, B_98]: (v3_pre_topc(k1_tops_1(A_97, B_98), A_97) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97) | ~v2_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.77/1.63  tff(c_868, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_852])).
% 3.77/1.63  tff(c_885, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_868])).
% 3.77/1.63  tff(c_887, plain, $false, inference(negUnitSimplification, [status(thm)], [c_806, c_885])).
% 3.77/1.63  tff(c_888, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_42])).
% 3.77/1.63  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.77/1.63  tff(c_1079, plain, (![A_117, C_118, B_119]: (r1_tarski(k3_xboole_0(A_117, C_118), B_119) | ~r1_tarski(A_117, B_119))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.77/1.63  tff(c_12, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.77/1.63  tff(c_1110, plain, (![A_120, C_121]: (k3_xboole_0(A_120, C_121)=k1_xboole_0 | ~r1_tarski(A_120, k1_xboole_0))), inference(resolution, [status(thm)], [c_1079, c_12])).
% 3.77/1.63  tff(c_1119, plain, (![C_122]: (k3_xboole_0(k1_xboole_0, C_122)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_1110])).
% 3.77/1.63  tff(c_988, plain, (![A_109, B_110]: (k1_setfam_1(k2_tarski(A_109, B_110))=k3_xboole_0(A_109, B_110))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.77/1.63  tff(c_1003, plain, (![B_111, A_112]: (k1_setfam_1(k2_tarski(B_111, A_112))=k3_xboole_0(A_112, B_111))), inference(superposition, [status(thm), theory('equality')], [c_14, c_988])).
% 3.77/1.63  tff(c_1009, plain, (![B_111, A_112]: (k3_xboole_0(B_111, A_112)=k3_xboole_0(A_112, B_111))), inference(superposition, [status(thm), theory('equality')], [c_1003, c_20])).
% 3.77/1.63  tff(c_1154, plain, (![C_123]: (k3_xboole_0(C_123, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1119, c_1009])).
% 3.77/1.63  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(k3_xboole_0(A_3, C_5), B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.77/1.63  tff(c_1203, plain, (![B_124, C_125]: (r1_tarski(k1_xboole_0, B_124) | ~r1_tarski(C_125, B_124))), inference(superposition, [status(thm), theory('equality')], [c_1154, c_8])).
% 3.77/1.63  tff(c_1218, plain, (![B_2]: (r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_1203])).
% 3.77/1.63  tff(c_889, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_42])).
% 3.77/1.63  tff(c_44, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.77/1.63  tff(c_891, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_889, c_44])).
% 3.77/1.63  tff(c_46, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.77/1.63  tff(c_933, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_889, c_46])).
% 3.77/1.63  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.77/1.63  tff(c_971, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_889, c_48])).
% 3.77/1.63  tff(c_1912, plain, (![A_159, B_160]: (k1_tops_1(A_159, B_160)=k1_xboole_0 | ~v2_tops_1(B_160, A_159) | ~m1_subset_1(B_160, k1_zfmisc_1(u1_struct_0(A_159))) | ~l1_pre_topc(A_159))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.77/1.63  tff(c_1941, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_1912])).
% 3.77/1.63  tff(c_1965, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_889, c_1941])).
% 3.77/1.63  tff(c_2025, plain, (![B_164, A_165, C_166]: (r1_tarski(B_164, k1_tops_1(A_165, C_166)) | ~r1_tarski(B_164, C_166) | ~v3_pre_topc(B_164, A_165) | ~m1_subset_1(C_166, k1_zfmisc_1(u1_struct_0(A_165))) | ~m1_subset_1(B_164, k1_zfmisc_1(u1_struct_0(A_165))) | ~l1_pre_topc(A_165))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.77/1.63  tff(c_2045, plain, (![B_164]: (r1_tarski(B_164, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_164, '#skF_2') | ~v3_pre_topc(B_164, '#skF_1') | ~m1_subset_1(B_164, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_2025])).
% 3.77/1.63  tff(c_2105, plain, (![B_167]: (r1_tarski(B_167, k1_xboole_0) | ~r1_tarski(B_167, '#skF_2') | ~v3_pre_topc(B_167, '#skF_1') | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1965, c_2045])).
% 3.77/1.63  tff(c_2127, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_971, c_2105])).
% 3.77/1.63  tff(c_2145, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_891, c_933, c_2127])).
% 3.77/1.63  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.77/1.63  tff(c_2155, plain, (k1_xboole_0='#skF_3' | ~r1_tarski(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_2145, c_2])).
% 3.77/1.63  tff(c_2166, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1218, c_2155])).
% 3.77/1.63  tff(c_2168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_888, c_2166])).
% 3.77/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.77/1.63  
% 3.77/1.63  Inference rules
% 3.77/1.63  ----------------------
% 3.77/1.63  #Ref     : 0
% 3.77/1.63  #Sup     : 488
% 3.77/1.63  #Fact    : 0
% 3.77/1.63  #Define  : 0
% 3.77/1.63  #Split   : 8
% 3.77/1.63  #Chain   : 0
% 3.77/1.63  #Close   : 0
% 3.77/1.63  
% 3.77/1.63  Ordering : KBO
% 3.77/1.63  
% 3.77/1.63  Simplification rules
% 3.77/1.63  ----------------------
% 3.77/1.63  #Subsume      : 22
% 3.77/1.63  #Demod        : 266
% 3.77/1.63  #Tautology    : 270
% 3.77/1.63  #SimpNegUnit  : 7
% 3.77/1.63  #BackRed      : 6
% 3.77/1.63  
% 3.77/1.63  #Partial instantiations: 0
% 3.77/1.63  #Strategies tried      : 1
% 3.77/1.63  
% 3.77/1.63  Timing (in seconds)
% 3.77/1.63  ----------------------
% 3.77/1.63  Preprocessing        : 0.30
% 3.77/1.63  Parsing              : 0.15
% 3.77/1.63  CNF conversion       : 0.02
% 3.77/1.63  Main loop            : 0.52
% 3.77/1.63  Inferencing          : 0.17
% 3.77/1.63  Reduction            : 0.20
% 3.77/1.63  Demodulation         : 0.15
% 3.77/1.63  BG Simplification    : 0.02
% 3.77/1.63  Subsumption          : 0.09
% 3.77/1.63  Abstraction          : 0.02
% 3.77/1.63  MUC search           : 0.00
% 3.77/1.63  Cooper               : 0.00
% 3.77/1.63  Total                : 0.86
% 3.77/1.63  Index Insertion      : 0.00
% 3.77/1.63  Index Deletion       : 0.00
% 3.77/1.63  Index Matching       : 0.00
% 3.77/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
