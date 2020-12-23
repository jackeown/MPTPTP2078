%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:20 EST 2020

% Result     : Theorem 3.83s
% Output     : CNFRefutation 4.02s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 146 expanded)
%              Number of leaves         :   39 (  66 expanded)
%              Depth                    :    8
%              Number of atoms          :  134 ( 282 expanded)
%              Number of equality atoms :   55 (  89 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_47,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_39,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_53,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1581,plain,(
    ! [A_169,B_170,C_171] :
      ( k7_subset_1(A_169,B_170,C_171) = k4_xboole_0(B_170,C_171)
      | ~ m1_subset_1(B_170,k1_zfmisc_1(A_169)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1590,plain,(
    ! [C_171] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_171) = k4_xboole_0('#skF_2',C_171) ),
    inference(resolution,[status(thm)],[c_38,c_1581])).

tff(c_50,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_134,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_44,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_232,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_847,plain,(
    ! [B_100,A_101] :
      ( v4_pre_topc(B_100,A_101)
      | k2_pre_topc(A_101,B_100) != B_100
      | ~ v2_pre_topc(A_101)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_861,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_847])).

tff(c_867,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_861])).

tff(c_868,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_232,c_867])).

tff(c_920,plain,(
    ! [A_108,B_109] :
      ( k4_subset_1(u1_struct_0(A_108),B_109,k2_tops_1(A_108,B_109)) = k2_pre_topc(A_108,B_109)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_930,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_920])).

tff(c_936,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_930])).

tff(c_366,plain,(
    ! [A_71,B_72,C_73] :
      ( k7_subset_1(A_71,B_72,C_73) = k4_xboole_0(B_72,C_73)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_391,plain,(
    ! [C_74] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_74) = k4_xboole_0('#skF_2',C_74) ),
    inference(resolution,[status(thm)],[c_38,c_366])).

tff(c_403,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_391])).

tff(c_16,plain,(
    ! [A_16,B_17] : k6_subset_1(A_16,B_17) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    ! [A_11,B_12] : m1_subset_1(k6_subset_1(A_11,B_12),k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_51,plain,(
    ! [A_11,B_12] : m1_subset_1(k4_xboole_0(A_11,B_12),k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_12])).

tff(c_135,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(A_51,B_52)
      | ~ m1_subset_1(A_51,k1_zfmisc_1(B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_142,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(resolution,[status(thm)],[c_51,c_135])).

tff(c_145,plain,(
    ! [A_55,B_56] :
      ( k3_xboole_0(A_55,B_56) = A_55
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_414,plain,(
    ! [A_75,B_76] : k3_xboole_0(k4_xboole_0(A_75,B_76),A_75) = k4_xboole_0(A_75,B_76) ),
    inference(resolution,[status(thm)],[c_142,c_145])).

tff(c_8,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_104,plain,(
    ! [A_47,B_48] : k1_setfam_1(k2_tarski(A_47,B_48)) = k3_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_170,plain,(
    ! [B_59,A_60] : k1_setfam_1(k2_tarski(B_59,A_60)) = k3_xboole_0(A_60,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_104])).

tff(c_20,plain,(
    ! [A_21,B_22] : k1_setfam_1(k2_tarski(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_193,plain,(
    ! [B_61,A_62] : k3_xboole_0(B_61,A_62) = k3_xboole_0(A_62,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_20])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_211,plain,(
    ! [B_61,A_62] : k2_xboole_0(B_61,k3_xboole_0(A_62,B_61)) = B_61 ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_4])).

tff(c_423,plain,(
    ! [A_75,B_76] : k2_xboole_0(A_75,k4_xboole_0(A_75,B_76)) = A_75 ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_211])).

tff(c_469,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_423])).

tff(c_544,plain,(
    ! [A_83,B_84] :
      ( m1_subset_1(k2_tops_1(A_83,B_84),k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_22,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ m1_subset_1(A_23,k1_zfmisc_1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_554,plain,(
    ! [A_83,B_84] :
      ( r1_tarski(k2_tops_1(A_83,B_84),u1_struct_0(A_83))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(resolution,[status(thm)],[c_544,c_22])).

tff(c_24,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(A_23,k1_zfmisc_1(B_24))
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_787,plain,(
    ! [A_96,B_97,C_98] :
      ( k4_subset_1(A_96,B_97,C_98) = k2_xboole_0(B_97,C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(A_96))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1066,plain,(
    ! [B_124,B_125,A_126] :
      ( k4_subset_1(B_124,B_125,A_126) = k2_xboole_0(B_125,A_126)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(B_124))
      | ~ r1_tarski(A_126,B_124) ) ),
    inference(resolution,[status(thm)],[c_24,c_787])).

tff(c_1085,plain,(
    ! [A_127] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_127) = k2_xboole_0('#skF_2',A_127)
      | ~ r1_tarski(A_127,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_38,c_1066])).

tff(c_1089,plain,(
    ! [B_84] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_84)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_84))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_554,c_1085])).

tff(c_1241,plain,(
    ! [B_142] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_142)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_142))
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1089])).

tff(c_1256,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_1241])).

tff(c_1263,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_936,c_469,c_1256])).

tff(c_1265,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_868,c_1263])).

tff(c_1266,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1402,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_1266])).

tff(c_1403,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1415,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1403,c_44])).

tff(c_1640,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1590,c_1415])).

tff(c_1664,plain,(
    ! [A_175,B_176] :
      ( k2_pre_topc(A_175,B_176) = B_176
      | ~ v4_pre_topc(B_176,A_175)
      | ~ m1_subset_1(B_176,k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ l1_pre_topc(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1675,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1664])).

tff(c_1680,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1403,c_1675])).

tff(c_2221,plain,(
    ! [A_228,B_229] :
      ( k7_subset_1(u1_struct_0(A_228),k2_pre_topc(A_228,B_229),k1_tops_1(A_228,B_229)) = k2_tops_1(A_228,B_229)
      | ~ m1_subset_1(B_229,k1_zfmisc_1(u1_struct_0(A_228)))
      | ~ l1_pre_topc(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2230,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1680,c_2221])).

tff(c_2234,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1590,c_2230])).

tff(c_2236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1640,c_2234])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:54:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.83/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/1.66  
% 3.83/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/1.66  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 3.83/1.66  
% 3.83/1.66  %Foreground sorts:
% 3.83/1.66  
% 3.83/1.66  
% 3.83/1.66  %Background operators:
% 3.83/1.66  
% 3.83/1.66  
% 3.83/1.66  %Foreground operators:
% 3.83/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.83/1.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.83/1.66  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.83/1.66  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.83/1.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.83/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.83/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.83/1.66  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.83/1.66  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.83/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.83/1.66  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.83/1.66  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.83/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.83/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.83/1.66  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.83/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.83/1.66  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.83/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.83/1.66  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.83/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.83/1.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.83/1.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.83/1.66  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.83/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.83/1.66  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.83/1.66  
% 4.02/1.67  tff(f_112, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 4.02/1.67  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.02/1.67  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.02/1.67  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 4.02/1.67  tff(f_47, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 4.02/1.67  tff(f_39, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 4.02/1.67  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.02/1.67  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.02/1.67  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.02/1.67  tff(f_53, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.02/1.67  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 4.02/1.67  tff(f_78, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 4.02/1.67  tff(f_45, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.02/1.67  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 4.02/1.67  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.02/1.67  tff(c_1581, plain, (![A_169, B_170, C_171]: (k7_subset_1(A_169, B_170, C_171)=k4_xboole_0(B_170, C_171) | ~m1_subset_1(B_170, k1_zfmisc_1(A_169)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.02/1.67  tff(c_1590, plain, (![C_171]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_171)=k4_xboole_0('#skF_2', C_171))), inference(resolution, [status(thm)], [c_38, c_1581])).
% 4.02/1.67  tff(c_50, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.02/1.67  tff(c_134, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_50])).
% 4.02/1.67  tff(c_44, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.02/1.67  tff(c_232, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 4.02/1.67  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.02/1.67  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.02/1.67  tff(c_847, plain, (![B_100, A_101]: (v4_pre_topc(B_100, A_101) | k2_pre_topc(A_101, B_100)!=B_100 | ~v2_pre_topc(A_101) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.02/1.67  tff(c_861, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_847])).
% 4.02/1.67  tff(c_867, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_861])).
% 4.02/1.67  tff(c_868, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_232, c_867])).
% 4.02/1.67  tff(c_920, plain, (![A_108, B_109]: (k4_subset_1(u1_struct_0(A_108), B_109, k2_tops_1(A_108, B_109))=k2_pre_topc(A_108, B_109) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.02/1.67  tff(c_930, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_920])).
% 4.02/1.67  tff(c_936, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_930])).
% 4.02/1.67  tff(c_366, plain, (![A_71, B_72, C_73]: (k7_subset_1(A_71, B_72, C_73)=k4_xboole_0(B_72, C_73) | ~m1_subset_1(B_72, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.02/1.67  tff(c_391, plain, (![C_74]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_74)=k4_xboole_0('#skF_2', C_74))), inference(resolution, [status(thm)], [c_38, c_366])).
% 4.02/1.67  tff(c_403, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_134, c_391])).
% 4.02/1.67  tff(c_16, plain, (![A_16, B_17]: (k6_subset_1(A_16, B_17)=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.02/1.67  tff(c_12, plain, (![A_11, B_12]: (m1_subset_1(k6_subset_1(A_11, B_12), k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.02/1.67  tff(c_51, plain, (![A_11, B_12]: (m1_subset_1(k4_xboole_0(A_11, B_12), k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_12])).
% 4.02/1.67  tff(c_135, plain, (![A_51, B_52]: (r1_tarski(A_51, B_52) | ~m1_subset_1(A_51, k1_zfmisc_1(B_52)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.02/1.67  tff(c_142, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(resolution, [status(thm)], [c_51, c_135])).
% 4.02/1.67  tff(c_145, plain, (![A_55, B_56]: (k3_xboole_0(A_55, B_56)=A_55 | ~r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.02/1.67  tff(c_414, plain, (![A_75, B_76]: (k3_xboole_0(k4_xboole_0(A_75, B_76), A_75)=k4_xboole_0(A_75, B_76))), inference(resolution, [status(thm)], [c_142, c_145])).
% 4.02/1.67  tff(c_8, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.02/1.67  tff(c_104, plain, (![A_47, B_48]: (k1_setfam_1(k2_tarski(A_47, B_48))=k3_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.02/1.67  tff(c_170, plain, (![B_59, A_60]: (k1_setfam_1(k2_tarski(B_59, A_60))=k3_xboole_0(A_60, B_59))), inference(superposition, [status(thm), theory('equality')], [c_8, c_104])).
% 4.02/1.67  tff(c_20, plain, (![A_21, B_22]: (k1_setfam_1(k2_tarski(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.02/1.67  tff(c_193, plain, (![B_61, A_62]: (k3_xboole_0(B_61, A_62)=k3_xboole_0(A_62, B_61))), inference(superposition, [status(thm), theory('equality')], [c_170, c_20])).
% 4.02/1.67  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k3_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.02/1.67  tff(c_211, plain, (![B_61, A_62]: (k2_xboole_0(B_61, k3_xboole_0(A_62, B_61))=B_61)), inference(superposition, [status(thm), theory('equality')], [c_193, c_4])).
% 4.02/1.67  tff(c_423, plain, (![A_75, B_76]: (k2_xboole_0(A_75, k4_xboole_0(A_75, B_76))=A_75)), inference(superposition, [status(thm), theory('equality')], [c_414, c_211])).
% 4.02/1.67  tff(c_469, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_403, c_423])).
% 4.02/1.67  tff(c_544, plain, (![A_83, B_84]: (m1_subset_1(k2_tops_1(A_83, B_84), k1_zfmisc_1(u1_struct_0(A_83))) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.02/1.67  tff(c_22, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | ~m1_subset_1(A_23, k1_zfmisc_1(B_24)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.02/1.67  tff(c_554, plain, (![A_83, B_84]: (r1_tarski(k2_tops_1(A_83, B_84), u1_struct_0(A_83)) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83))), inference(resolution, [status(thm)], [c_544, c_22])).
% 4.02/1.67  tff(c_24, plain, (![A_23, B_24]: (m1_subset_1(A_23, k1_zfmisc_1(B_24)) | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.02/1.67  tff(c_787, plain, (![A_96, B_97, C_98]: (k4_subset_1(A_96, B_97, C_98)=k2_xboole_0(B_97, C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(A_96)) | ~m1_subset_1(B_97, k1_zfmisc_1(A_96)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.02/1.67  tff(c_1066, plain, (![B_124, B_125, A_126]: (k4_subset_1(B_124, B_125, A_126)=k2_xboole_0(B_125, A_126) | ~m1_subset_1(B_125, k1_zfmisc_1(B_124)) | ~r1_tarski(A_126, B_124))), inference(resolution, [status(thm)], [c_24, c_787])).
% 4.02/1.67  tff(c_1085, plain, (![A_127]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_127)=k2_xboole_0('#skF_2', A_127) | ~r1_tarski(A_127, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_38, c_1066])).
% 4.02/1.67  tff(c_1089, plain, (![B_84]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_84))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_84)) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_554, c_1085])).
% 4.02/1.67  tff(c_1241, plain, (![B_142]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_142))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_142)) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1089])).
% 4.02/1.67  tff(c_1256, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_1241])).
% 4.02/1.67  tff(c_1263, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_936, c_469, c_1256])).
% 4.02/1.67  tff(c_1265, plain, $false, inference(negUnitSimplification, [status(thm)], [c_868, c_1263])).
% 4.02/1.67  tff(c_1266, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 4.02/1.67  tff(c_1402, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_1266])).
% 4.02/1.67  tff(c_1403, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 4.02/1.67  tff(c_1415, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1403, c_44])).
% 4.02/1.67  tff(c_1640, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1590, c_1415])).
% 4.02/1.67  tff(c_1664, plain, (![A_175, B_176]: (k2_pre_topc(A_175, B_176)=B_176 | ~v4_pre_topc(B_176, A_175) | ~m1_subset_1(B_176, k1_zfmisc_1(u1_struct_0(A_175))) | ~l1_pre_topc(A_175))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.02/1.67  tff(c_1675, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1664])).
% 4.02/1.67  tff(c_1680, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1403, c_1675])).
% 4.02/1.67  tff(c_2221, plain, (![A_228, B_229]: (k7_subset_1(u1_struct_0(A_228), k2_pre_topc(A_228, B_229), k1_tops_1(A_228, B_229))=k2_tops_1(A_228, B_229) | ~m1_subset_1(B_229, k1_zfmisc_1(u1_struct_0(A_228))) | ~l1_pre_topc(A_228))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.02/1.67  tff(c_2230, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1680, c_2221])).
% 4.02/1.67  tff(c_2234, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1590, c_2230])).
% 4.02/1.67  tff(c_2236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1640, c_2234])).
% 4.02/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.02/1.67  
% 4.02/1.67  Inference rules
% 4.02/1.67  ----------------------
% 4.02/1.67  #Ref     : 0
% 4.02/1.67  #Sup     : 552
% 4.02/1.67  #Fact    : 0
% 4.02/1.67  #Define  : 0
% 4.02/1.67  #Split   : 2
% 4.02/1.67  #Chain   : 0
% 4.02/1.67  #Close   : 0
% 4.02/1.67  
% 4.02/1.67  Ordering : KBO
% 4.02/1.67  
% 4.02/1.67  Simplification rules
% 4.02/1.67  ----------------------
% 4.02/1.67  #Subsume      : 13
% 4.02/1.67  #Demod        : 240
% 4.02/1.67  #Tautology    : 364
% 4.02/1.67  #SimpNegUnit  : 4
% 4.02/1.67  #BackRed      : 1
% 4.02/1.67  
% 4.02/1.67  #Partial instantiations: 0
% 4.02/1.67  #Strategies tried      : 1
% 4.02/1.67  
% 4.02/1.67  Timing (in seconds)
% 4.02/1.67  ----------------------
% 4.02/1.68  Preprocessing        : 0.33
% 4.02/1.68  Parsing              : 0.18
% 4.02/1.68  CNF conversion       : 0.02
% 4.02/1.68  Main loop            : 0.60
% 4.02/1.68  Inferencing          : 0.22
% 4.02/1.68  Reduction            : 0.22
% 4.02/1.68  Demodulation         : 0.17
% 4.02/1.68  BG Simplification    : 0.03
% 4.02/1.68  Subsumption          : 0.09
% 4.02/1.68  Abstraction          : 0.03
% 4.02/1.68  MUC search           : 0.00
% 4.02/1.68  Cooper               : 0.00
% 4.02/1.68  Total                : 0.96
% 4.02/1.68  Index Insertion      : 0.00
% 4.02/1.68  Index Deletion       : 0.00
% 4.02/1.68  Index Matching       : 0.00
% 4.02/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
