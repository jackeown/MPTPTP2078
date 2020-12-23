%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:12 EST 2020

% Result     : Theorem 11.49s
% Output     : CNFRefutation 11.49s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 361 expanded)
%              Number of leaves         :   50 ( 141 expanded)
%              Depth                    :   11
%              Number of atoms          :  180 ( 717 expanded)
%              Number of equality atoms :   77 ( 212 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_169,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_141,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_59,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_61,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_73,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_95,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_150,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_157,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(c_72,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_22069,plain,(
    ! [A_540,B_541,C_542] :
      ( k7_subset_1(A_540,B_541,C_542) = k4_xboole_0(B_541,C_542)
      | ~ m1_subset_1(B_541,k1_zfmisc_1(A_540)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_22091,plain,(
    ! [C_542] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_542) = k4_xboole_0('#skF_2',C_542) ),
    inference(resolution,[status(thm)],[c_72,c_22069])).

tff(c_78,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_222,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_74,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_76,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_5244,plain,(
    ! [B_260,A_261] :
      ( v4_pre_topc(B_260,A_261)
      | k2_pre_topc(A_261,B_260) != B_260
      | ~ v2_pre_topc(A_261)
      | ~ m1_subset_1(B_260,k1_zfmisc_1(u1_struct_0(A_261)))
      | ~ l1_pre_topc(A_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_5276,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_5244])).

tff(c_5291,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_76,c_5276])).

tff(c_5292,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_222,c_5291])).

tff(c_6077,plain,(
    ! [A_279,B_280] :
      ( k4_subset_1(u1_struct_0(A_279),B_280,k2_tops_1(A_279,B_280)) = k2_pre_topc(A_279,B_280)
      | ~ m1_subset_1(B_280,k1_zfmisc_1(u1_struct_0(A_279)))
      | ~ l1_pre_topc(A_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_6100,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_6077])).

tff(c_6115,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_6100])).

tff(c_28,plain,(
    ! [B_23,A_22] : k2_tarski(B_23,A_22) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_223,plain,(
    ! [A_91,B_92] : k3_tarski(k2_tarski(A_91,B_92)) = k2_xboole_0(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1531,plain,(
    ! [A_151,B_152] : k3_tarski(k2_tarski(A_151,B_152)) = k2_xboole_0(B_152,A_151) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_223])).

tff(c_30,plain,(
    ! [A_24,B_25] : k3_tarski(k2_tarski(A_24,B_25)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1537,plain,(
    ! [B_152,A_151] : k2_xboole_0(B_152,A_151) = k2_xboole_0(A_151,B_152) ),
    inference(superposition,[status(thm),theory(equality)],[c_1531,c_30])).

tff(c_3017,plain,(
    ! [A_192,B_193,C_194] :
      ( k7_subset_1(A_192,B_193,C_194) = k4_xboole_0(B_193,C_194)
      | ~ m1_subset_1(B_193,k1_zfmisc_1(A_192)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3066,plain,(
    ! [C_199] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_199) = k4_xboole_0('#skF_2',C_199) ),
    inference(resolution,[status(thm)],[c_72,c_3017])).

tff(c_84,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_131,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_3072,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3066,c_131])).

tff(c_44,plain,(
    ! [A_38,B_39] : k6_subset_1(A_38,B_39) = k4_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_38,plain,(
    ! [A_31,B_32] : m1_subset_1(k6_subset_1(A_31,B_32),k1_zfmisc_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_85,plain,(
    ! [A_31,B_32] : m1_subset_1(k4_xboole_0(A_31,B_32),k1_zfmisc_1(A_31)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38])).

tff(c_238,plain,(
    ! [A_93,B_94] :
      ( r1_tarski(A_93,B_94)
      | ~ m1_subset_1(A_93,k1_zfmisc_1(B_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_258,plain,(
    ! [A_31,B_32] : r1_tarski(k4_xboole_0(A_31,B_32),A_31) ),
    inference(resolution,[status(thm)],[c_85,c_238])).

tff(c_289,plain,(
    ! [A_100,B_101] :
      ( k2_xboole_0(A_100,B_101) = B_101
      | ~ r1_tarski(A_100,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_305,plain,(
    ! [A_31,B_32] : k2_xboole_0(k4_xboole_0(A_31,B_32),A_31) = A_31 ),
    inference(resolution,[status(thm)],[c_258,c_289])).

tff(c_3108,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_3072,c_305])).

tff(c_3166,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1537,c_3108])).

tff(c_259,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_72,c_238])).

tff(c_306,plain,(
    k2_xboole_0('#skF_2',u1_struct_0('#skF_1')) = u1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_259,c_289])).

tff(c_20,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k2_xboole_0(A_14,B_15)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_546,plain,(
    k4_xboole_0('#skF_2',u1_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_20])).

tff(c_853,plain,(
    ! [A_124,B_125] : k2_xboole_0(k3_xboole_0(A_124,B_125),k4_xboole_0(A_124,B_125)) = A_124 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_880,plain,(
    k2_xboole_0(k3_xboole_0('#skF_2',u1_struct_0('#skF_1')),k1_xboole_0) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_546,c_853])).

tff(c_12,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_971,plain,(
    k3_xboole_0('#skF_2',u1_struct_0('#skF_1')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_880,c_12])).

tff(c_261,plain,(
    ! [A_96,B_97] : k1_setfam_1(k2_tarski(A_96,B_97)) = k3_xboole_0(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_698,plain,(
    ! [A_116,B_117] : k1_setfam_1(k2_tarski(A_116,B_117)) = k3_xboole_0(B_117,A_116) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_261])).

tff(c_50,plain,(
    ! [A_45,B_46] : k1_setfam_1(k2_tarski(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_704,plain,(
    ! [B_117,A_116] : k3_xboole_0(B_117,A_116) = k3_xboole_0(A_116,B_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_698,c_50])).

tff(c_24,plain,(
    ! [A_18,B_19] : r1_tarski(A_18,k2_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_862,plain,(
    ! [A_124,B_125] : r1_tarski(k3_xboole_0(A_124,B_125),A_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_853,c_24])).

tff(c_1409,plain,(
    ! [A_143,C_144,B_145] :
      ( r1_tarski(A_143,C_144)
      | ~ r1_tarski(B_145,C_144)
      | ~ r1_tarski(A_143,B_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3976,plain,(
    ! [A_223,A_224,B_225] :
      ( r1_tarski(A_223,A_224)
      | ~ r1_tarski(A_223,k3_xboole_0(A_224,B_225)) ) ),
    inference(resolution,[status(thm)],[c_862,c_1409])).

tff(c_4197,plain,(
    ! [A_230,B_231,B_232] : r1_tarski(k4_xboole_0(k3_xboole_0(A_230,B_231),B_232),A_230) ),
    inference(resolution,[status(thm)],[c_258,c_3976])).

tff(c_4652,plain,(
    ! [B_245,A_246,B_247] : r1_tarski(k4_xboole_0(k3_xboole_0(B_245,A_246),B_247),A_246) ),
    inference(superposition,[status(thm),theory(equality)],[c_704,c_4197])).

tff(c_4747,plain,(
    ! [B_248] : r1_tarski(k4_xboole_0('#skF_2',B_248),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_971,c_4652])).

tff(c_4756,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3072,c_4747])).

tff(c_54,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(A_47,k1_zfmisc_1(B_48))
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_4535,plain,(
    ! [A_240,B_241,C_242] :
      ( k4_subset_1(A_240,B_241,C_242) = k2_xboole_0(B_241,C_242)
      | ~ m1_subset_1(C_242,k1_zfmisc_1(A_240))
      | ~ m1_subset_1(B_241,k1_zfmisc_1(A_240)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_18913,plain,(
    ! [B_417,B_418,A_419] :
      ( k4_subset_1(B_417,B_418,A_419) = k2_xboole_0(B_418,A_419)
      | ~ m1_subset_1(B_418,k1_zfmisc_1(B_417))
      | ~ r1_tarski(A_419,B_417) ) ),
    inference(resolution,[status(thm)],[c_54,c_4535])).

tff(c_19395,plain,(
    ! [A_425] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_425) = k2_xboole_0('#skF_2',A_425)
      | ~ r1_tarski(A_425,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_72,c_18913])).

tff(c_19427,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_4756,c_19395])).

tff(c_19517,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6115,c_3166,c_19427])).

tff(c_19519,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5292,c_19517])).

tff(c_19520,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_19882,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19520,c_131])).

tff(c_19883,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_19975,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19883,c_78])).

tff(c_22214,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22091,c_19975])).

tff(c_24063,plain,(
    ! [A_608,B_609] :
      ( r1_tarski(k2_tops_1(A_608,B_609),B_609)
      | ~ v4_pre_topc(B_609,A_608)
      | ~ m1_subset_1(B_609,k1_zfmisc_1(u1_struct_0(A_608)))
      | ~ l1_pre_topc(A_608) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_24084,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_24063])).

tff(c_24096,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_19883,c_24084])).

tff(c_25319,plain,(
    ! [A_639,B_640] :
      ( k7_subset_1(u1_struct_0(A_639),B_640,k2_tops_1(A_639,B_640)) = k1_tops_1(A_639,B_640)
      | ~ m1_subset_1(B_640,k1_zfmisc_1(u1_struct_0(A_639)))
      | ~ l1_pre_topc(A_639) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_25342,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_25319])).

tff(c_25359,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_22091,c_25342])).

tff(c_21389,plain,(
    ! [A_520,B_521] :
      ( k4_xboole_0(A_520,B_521) = k3_subset_1(A_520,B_521)
      | ~ m1_subset_1(B_521,k1_zfmisc_1(A_520)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_26758,plain,(
    ! [B_672,A_673] :
      ( k4_xboole_0(B_672,A_673) = k3_subset_1(B_672,A_673)
      | ~ r1_tarski(A_673,B_672) ) ),
    inference(resolution,[status(thm)],[c_54,c_21389])).

tff(c_26854,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24096,c_26758])).

tff(c_26959,plain,(
    k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25359,c_26854])).

tff(c_21562,plain,(
    ! [A_528,B_529] :
      ( k3_subset_1(A_528,k3_subset_1(A_528,B_529)) = B_529
      | ~ m1_subset_1(B_529,k1_zfmisc_1(A_528)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_21573,plain,(
    ! [B_48,A_47] :
      ( k3_subset_1(B_48,k3_subset_1(B_48,A_47)) = A_47
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(resolution,[status(thm)],[c_54,c_21562])).

tff(c_27921,plain,
    ( k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_26959,c_21573])).

tff(c_27931,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24096,c_27921])).

tff(c_27082,plain,(
    ! [A_675,B_676] : k4_xboole_0(A_675,k4_xboole_0(A_675,B_676)) = k3_subset_1(A_675,k4_xboole_0(A_675,B_676)) ),
    inference(resolution,[status(thm)],[c_85,c_21389])).

tff(c_27596,plain,(
    ! [A_681,B_682] : m1_subset_1(k3_subset_1(A_681,k4_xboole_0(A_681,B_682)),k1_zfmisc_1(A_681)) ),
    inference(superposition,[status(thm),theory(equality)],[c_27082,c_85])).

tff(c_27643,plain,(
    m1_subset_1(k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_25359,c_27596])).

tff(c_28137,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27931,c_27643])).

tff(c_21789,plain,(
    ! [A_534,B_535] :
      ( m1_subset_1(k3_subset_1(A_534,B_535),k1_zfmisc_1(A_534))
      | ~ m1_subset_1(B_535,k1_zfmisc_1(A_534)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_34,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(A_27,B_28) = k3_subset_1(A_27,B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_37557,plain,(
    ! [A_784,B_785] :
      ( k4_xboole_0(A_784,k3_subset_1(A_784,B_785)) = k3_subset_1(A_784,k3_subset_1(A_784,B_785))
      | ~ m1_subset_1(B_785,k1_zfmisc_1(A_784)) ) ),
    inference(resolution,[status(thm)],[c_21789,c_34])).

tff(c_37559,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'))) = k3_subset_1('#skF_2',k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_28137,c_37557])).

tff(c_37583,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27931,c_26959,c_26959,c_37559])).

tff(c_37585,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22214,c_37583])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:00:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.49/5.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.49/5.08  
% 11.49/5.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.49/5.08  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 11.49/5.08  
% 11.49/5.08  %Foreground sorts:
% 11.49/5.08  
% 11.49/5.08  
% 11.49/5.08  %Background operators:
% 11.49/5.08  
% 11.49/5.08  
% 11.49/5.08  %Foreground operators:
% 11.49/5.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.49/5.08  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.49/5.08  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 11.49/5.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.49/5.08  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.49/5.08  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.49/5.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.49/5.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.49/5.08  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 11.49/5.08  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 11.49/5.08  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 11.49/5.08  tff('#skF_2', type, '#skF_2': $i).
% 11.49/5.08  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 11.49/5.08  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 11.49/5.08  tff('#skF_1', type, '#skF_1': $i).
% 11.49/5.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.49/5.08  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 11.49/5.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.49/5.08  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.49/5.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.49/5.08  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.49/5.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.49/5.08  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.49/5.08  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.49/5.08  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 11.49/5.08  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 11.49/5.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.49/5.08  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 11.49/5.08  
% 11.49/5.10  tff(f_169, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 11.49/5.10  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 11.49/5.10  tff(f_114, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 11.49/5.10  tff(f_141, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 11.49/5.10  tff(f_59, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 11.49/5.10  tff(f_61, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 11.49/5.10  tff(f_85, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 11.49/5.10  tff(f_73, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 11.49/5.10  tff(f_99, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 11.49/5.10  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 11.49/5.10  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 11.49/5.10  tff(f_53, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 11.49/5.10  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 11.49/5.10  tff(f_95, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 11.49/5.10  tff(f_55, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 11.49/5.10  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 11.49/5.10  tff(f_83, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 11.49/5.10  tff(f_150, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 11.49/5.10  tff(f_157, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 11.49/5.10  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 11.49/5.10  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 11.49/5.10  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 11.49/5.10  tff(c_72, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_169])).
% 11.49/5.10  tff(c_22069, plain, (![A_540, B_541, C_542]: (k7_subset_1(A_540, B_541, C_542)=k4_xboole_0(B_541, C_542) | ~m1_subset_1(B_541, k1_zfmisc_1(A_540)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.49/5.10  tff(c_22091, plain, (![C_542]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_542)=k4_xboole_0('#skF_2', C_542))), inference(resolution, [status(thm)], [c_72, c_22069])).
% 11.49/5.10  tff(c_78, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_169])).
% 11.49/5.10  tff(c_222, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_78])).
% 11.49/5.10  tff(c_74, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_169])).
% 11.49/5.10  tff(c_76, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_169])).
% 11.49/5.10  tff(c_5244, plain, (![B_260, A_261]: (v4_pre_topc(B_260, A_261) | k2_pre_topc(A_261, B_260)!=B_260 | ~v2_pre_topc(A_261) | ~m1_subset_1(B_260, k1_zfmisc_1(u1_struct_0(A_261))) | ~l1_pre_topc(A_261))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.49/5.10  tff(c_5276, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_72, c_5244])).
% 11.49/5.10  tff(c_5291, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_76, c_5276])).
% 11.49/5.10  tff(c_5292, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_222, c_5291])).
% 11.49/5.10  tff(c_6077, plain, (![A_279, B_280]: (k4_subset_1(u1_struct_0(A_279), B_280, k2_tops_1(A_279, B_280))=k2_pre_topc(A_279, B_280) | ~m1_subset_1(B_280, k1_zfmisc_1(u1_struct_0(A_279))) | ~l1_pre_topc(A_279))), inference(cnfTransformation, [status(thm)], [f_141])).
% 11.49/5.10  tff(c_6100, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_72, c_6077])).
% 11.49/5.10  tff(c_6115, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_6100])).
% 11.49/5.10  tff(c_28, plain, (![B_23, A_22]: (k2_tarski(B_23, A_22)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.49/5.10  tff(c_223, plain, (![A_91, B_92]: (k3_tarski(k2_tarski(A_91, B_92))=k2_xboole_0(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.49/5.10  tff(c_1531, plain, (![A_151, B_152]: (k3_tarski(k2_tarski(A_151, B_152))=k2_xboole_0(B_152, A_151))), inference(superposition, [status(thm), theory('equality')], [c_28, c_223])).
% 11.49/5.10  tff(c_30, plain, (![A_24, B_25]: (k3_tarski(k2_tarski(A_24, B_25))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.49/5.10  tff(c_1537, plain, (![B_152, A_151]: (k2_xboole_0(B_152, A_151)=k2_xboole_0(A_151, B_152))), inference(superposition, [status(thm), theory('equality')], [c_1531, c_30])).
% 11.49/5.10  tff(c_3017, plain, (![A_192, B_193, C_194]: (k7_subset_1(A_192, B_193, C_194)=k4_xboole_0(B_193, C_194) | ~m1_subset_1(B_193, k1_zfmisc_1(A_192)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.49/5.10  tff(c_3066, plain, (![C_199]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_199)=k4_xboole_0('#skF_2', C_199))), inference(resolution, [status(thm)], [c_72, c_3017])).
% 11.49/5.10  tff(c_84, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 11.49/5.10  tff(c_131, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_84])).
% 11.49/5.10  tff(c_3072, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3066, c_131])).
% 11.49/5.10  tff(c_44, plain, (![A_38, B_39]: (k6_subset_1(A_38, B_39)=k4_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.49/5.10  tff(c_38, plain, (![A_31, B_32]: (m1_subset_1(k6_subset_1(A_31, B_32), k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.49/5.10  tff(c_85, plain, (![A_31, B_32]: (m1_subset_1(k4_xboole_0(A_31, B_32), k1_zfmisc_1(A_31)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38])).
% 11.49/5.10  tff(c_238, plain, (![A_93, B_94]: (r1_tarski(A_93, B_94) | ~m1_subset_1(A_93, k1_zfmisc_1(B_94)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 11.49/5.10  tff(c_258, plain, (![A_31, B_32]: (r1_tarski(k4_xboole_0(A_31, B_32), A_31))), inference(resolution, [status(thm)], [c_85, c_238])).
% 11.49/5.10  tff(c_289, plain, (![A_100, B_101]: (k2_xboole_0(A_100, B_101)=B_101 | ~r1_tarski(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.49/5.10  tff(c_305, plain, (![A_31, B_32]: (k2_xboole_0(k4_xboole_0(A_31, B_32), A_31)=A_31)), inference(resolution, [status(thm)], [c_258, c_289])).
% 11.49/5.10  tff(c_3108, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_3072, c_305])).
% 11.49/5.10  tff(c_3166, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1537, c_3108])).
% 11.49/5.10  tff(c_259, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_72, c_238])).
% 11.49/5.10  tff(c_306, plain, (k2_xboole_0('#skF_2', u1_struct_0('#skF_1'))=u1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_259, c_289])).
% 11.49/5.10  tff(c_20, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k2_xboole_0(A_14, B_15))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.49/5.10  tff(c_546, plain, (k4_xboole_0('#skF_2', u1_struct_0('#skF_1'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_306, c_20])).
% 11.49/5.10  tff(c_853, plain, (![A_124, B_125]: (k2_xboole_0(k3_xboole_0(A_124, B_125), k4_xboole_0(A_124, B_125))=A_124)), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.49/5.10  tff(c_880, plain, (k2_xboole_0(k3_xboole_0('#skF_2', u1_struct_0('#skF_1')), k1_xboole_0)='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_546, c_853])).
% 11.49/5.10  tff(c_12, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.49/5.10  tff(c_971, plain, (k3_xboole_0('#skF_2', u1_struct_0('#skF_1'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_880, c_12])).
% 11.49/5.10  tff(c_261, plain, (![A_96, B_97]: (k1_setfam_1(k2_tarski(A_96, B_97))=k3_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_95])).
% 11.49/5.10  tff(c_698, plain, (![A_116, B_117]: (k1_setfam_1(k2_tarski(A_116, B_117))=k3_xboole_0(B_117, A_116))), inference(superposition, [status(thm), theory('equality')], [c_28, c_261])).
% 11.49/5.10  tff(c_50, plain, (![A_45, B_46]: (k1_setfam_1(k2_tarski(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_95])).
% 11.49/5.10  tff(c_704, plain, (![B_117, A_116]: (k3_xboole_0(B_117, A_116)=k3_xboole_0(A_116, B_117))), inference(superposition, [status(thm), theory('equality')], [c_698, c_50])).
% 11.49/5.10  tff(c_24, plain, (![A_18, B_19]: (r1_tarski(A_18, k2_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.49/5.10  tff(c_862, plain, (![A_124, B_125]: (r1_tarski(k3_xboole_0(A_124, B_125), A_124))), inference(superposition, [status(thm), theory('equality')], [c_853, c_24])).
% 11.49/5.10  tff(c_1409, plain, (![A_143, C_144, B_145]: (r1_tarski(A_143, C_144) | ~r1_tarski(B_145, C_144) | ~r1_tarski(A_143, B_145))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.49/5.10  tff(c_3976, plain, (![A_223, A_224, B_225]: (r1_tarski(A_223, A_224) | ~r1_tarski(A_223, k3_xboole_0(A_224, B_225)))), inference(resolution, [status(thm)], [c_862, c_1409])).
% 11.49/5.10  tff(c_4197, plain, (![A_230, B_231, B_232]: (r1_tarski(k4_xboole_0(k3_xboole_0(A_230, B_231), B_232), A_230))), inference(resolution, [status(thm)], [c_258, c_3976])).
% 11.49/5.10  tff(c_4652, plain, (![B_245, A_246, B_247]: (r1_tarski(k4_xboole_0(k3_xboole_0(B_245, A_246), B_247), A_246))), inference(superposition, [status(thm), theory('equality')], [c_704, c_4197])).
% 11.49/5.10  tff(c_4747, plain, (![B_248]: (r1_tarski(k4_xboole_0('#skF_2', B_248), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_971, c_4652])).
% 11.49/5.10  tff(c_4756, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3072, c_4747])).
% 11.49/5.10  tff(c_54, plain, (![A_47, B_48]: (m1_subset_1(A_47, k1_zfmisc_1(B_48)) | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_99])).
% 11.49/5.10  tff(c_4535, plain, (![A_240, B_241, C_242]: (k4_subset_1(A_240, B_241, C_242)=k2_xboole_0(B_241, C_242) | ~m1_subset_1(C_242, k1_zfmisc_1(A_240)) | ~m1_subset_1(B_241, k1_zfmisc_1(A_240)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.49/5.10  tff(c_18913, plain, (![B_417, B_418, A_419]: (k4_subset_1(B_417, B_418, A_419)=k2_xboole_0(B_418, A_419) | ~m1_subset_1(B_418, k1_zfmisc_1(B_417)) | ~r1_tarski(A_419, B_417))), inference(resolution, [status(thm)], [c_54, c_4535])).
% 11.49/5.10  tff(c_19395, plain, (![A_425]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_425)=k2_xboole_0('#skF_2', A_425) | ~r1_tarski(A_425, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_72, c_18913])).
% 11.49/5.10  tff(c_19427, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_4756, c_19395])).
% 11.49/5.10  tff(c_19517, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6115, c_3166, c_19427])).
% 11.49/5.10  tff(c_19519, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5292, c_19517])).
% 11.49/5.10  tff(c_19520, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_78])).
% 11.49/5.10  tff(c_19882, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19520, c_131])).
% 11.49/5.10  tff(c_19883, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_84])).
% 11.49/5.10  tff(c_19975, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_19883, c_78])).
% 11.49/5.10  tff(c_22214, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22091, c_19975])).
% 11.49/5.10  tff(c_24063, plain, (![A_608, B_609]: (r1_tarski(k2_tops_1(A_608, B_609), B_609) | ~v4_pre_topc(B_609, A_608) | ~m1_subset_1(B_609, k1_zfmisc_1(u1_struct_0(A_608))) | ~l1_pre_topc(A_608))), inference(cnfTransformation, [status(thm)], [f_150])).
% 11.49/5.10  tff(c_24084, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_72, c_24063])).
% 11.49/5.10  tff(c_24096, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_19883, c_24084])).
% 11.49/5.10  tff(c_25319, plain, (![A_639, B_640]: (k7_subset_1(u1_struct_0(A_639), B_640, k2_tops_1(A_639, B_640))=k1_tops_1(A_639, B_640) | ~m1_subset_1(B_640, k1_zfmisc_1(u1_struct_0(A_639))) | ~l1_pre_topc(A_639))), inference(cnfTransformation, [status(thm)], [f_157])).
% 11.49/5.10  tff(c_25342, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_72, c_25319])).
% 11.49/5.10  tff(c_25359, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_22091, c_25342])).
% 11.49/5.10  tff(c_21389, plain, (![A_520, B_521]: (k4_xboole_0(A_520, B_521)=k3_subset_1(A_520, B_521) | ~m1_subset_1(B_521, k1_zfmisc_1(A_520)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.49/5.10  tff(c_26758, plain, (![B_672, A_673]: (k4_xboole_0(B_672, A_673)=k3_subset_1(B_672, A_673) | ~r1_tarski(A_673, B_672))), inference(resolution, [status(thm)], [c_54, c_21389])).
% 11.49/5.10  tff(c_26854, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_24096, c_26758])).
% 11.49/5.10  tff(c_26959, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_25359, c_26854])).
% 11.49/5.10  tff(c_21562, plain, (![A_528, B_529]: (k3_subset_1(A_528, k3_subset_1(A_528, B_529))=B_529 | ~m1_subset_1(B_529, k1_zfmisc_1(A_528)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.49/5.10  tff(c_21573, plain, (![B_48, A_47]: (k3_subset_1(B_48, k3_subset_1(B_48, A_47))=A_47 | ~r1_tarski(A_47, B_48))), inference(resolution, [status(thm)], [c_54, c_21562])).
% 11.49/5.10  tff(c_27921, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_26959, c_21573])).
% 11.49/5.10  tff(c_27931, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24096, c_27921])).
% 11.49/5.10  tff(c_27082, plain, (![A_675, B_676]: (k4_xboole_0(A_675, k4_xboole_0(A_675, B_676))=k3_subset_1(A_675, k4_xboole_0(A_675, B_676)))), inference(resolution, [status(thm)], [c_85, c_21389])).
% 11.49/5.10  tff(c_27596, plain, (![A_681, B_682]: (m1_subset_1(k3_subset_1(A_681, k4_xboole_0(A_681, B_682)), k1_zfmisc_1(A_681)))), inference(superposition, [status(thm), theory('equality')], [c_27082, c_85])).
% 11.49/5.10  tff(c_27643, plain, (m1_subset_1(k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_25359, c_27596])).
% 11.49/5.10  tff(c_28137, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_27931, c_27643])).
% 11.49/5.10  tff(c_21789, plain, (![A_534, B_535]: (m1_subset_1(k3_subset_1(A_534, B_535), k1_zfmisc_1(A_534)) | ~m1_subset_1(B_535, k1_zfmisc_1(A_534)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.49/5.10  tff(c_34, plain, (![A_27, B_28]: (k4_xboole_0(A_27, B_28)=k3_subset_1(A_27, B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.49/5.10  tff(c_37557, plain, (![A_784, B_785]: (k4_xboole_0(A_784, k3_subset_1(A_784, B_785))=k3_subset_1(A_784, k3_subset_1(A_784, B_785)) | ~m1_subset_1(B_785, k1_zfmisc_1(A_784)))), inference(resolution, [status(thm)], [c_21789, c_34])).
% 11.49/5.10  tff(c_37559, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2')))=k3_subset_1('#skF_2', k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_28137, c_37557])).
% 11.49/5.10  tff(c_37583, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_27931, c_26959, c_26959, c_37559])).
% 11.49/5.10  tff(c_37585, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22214, c_37583])).
% 11.49/5.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.49/5.10  
% 11.49/5.10  Inference rules
% 11.49/5.10  ----------------------
% 11.49/5.10  #Ref     : 0
% 11.49/5.10  #Sup     : 9221
% 11.49/5.10  #Fact    : 0
% 11.49/5.10  #Define  : 0
% 11.49/5.10  #Split   : 7
% 11.49/5.10  #Chain   : 0
% 11.49/5.10  #Close   : 0
% 11.49/5.10  
% 11.49/5.10  Ordering : KBO
% 11.49/5.10  
% 11.49/5.10  Simplification rules
% 11.49/5.10  ----------------------
% 11.49/5.10  #Subsume      : 328
% 11.49/5.10  #Demod        : 8697
% 11.49/5.10  #Tautology    : 6367
% 11.49/5.10  #SimpNegUnit  : 5
% 11.49/5.10  #BackRed      : 9
% 11.49/5.10  
% 11.49/5.10  #Partial instantiations: 0
% 11.49/5.10  #Strategies tried      : 1
% 11.49/5.10  
% 11.49/5.10  Timing (in seconds)
% 11.49/5.10  ----------------------
% 11.49/5.11  Preprocessing        : 0.38
% 11.49/5.11  Parsing              : 0.21
% 11.49/5.11  CNF conversion       : 0.03
% 11.49/5.11  Main loop            : 3.89
% 11.49/5.11  Inferencing          : 0.77
% 11.49/5.11  Reduction            : 2.09
% 11.49/5.11  Demodulation         : 1.78
% 11.49/5.11  BG Simplification    : 0.08
% 11.49/5.11  Subsumption          : 0.74
% 11.49/5.11  Abstraction          : 0.14
% 11.49/5.11  MUC search           : 0.00
% 11.49/5.11  Cooper               : 0.00
% 11.49/5.11  Total                : 4.32
% 11.49/5.11  Index Insertion      : 0.00
% 11.49/5.11  Index Deletion       : 0.00
% 11.49/5.11  Index Matching       : 0.00
% 11.49/5.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
