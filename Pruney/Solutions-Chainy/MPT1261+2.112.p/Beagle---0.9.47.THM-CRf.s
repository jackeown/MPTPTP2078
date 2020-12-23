%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:27 EST 2020

% Result     : Theorem 4.36s
% Output     : CNFRefutation 4.46s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 475 expanded)
%              Number of leaves         :   39 ( 172 expanded)
%              Depth                    :   16
%              Number of atoms          :  194 (1004 expanded)
%              Number of equality atoms :   75 ( 269 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_125,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_78,axiom,(
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

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_113,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1844,plain,(
    ! [A_167,B_168] :
      ( r1_tarski(k1_tops_1(A_167,B_168),B_168)
      | ~ m1_subset_1(B_168,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ l1_pre_topc(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1852,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1844])).

tff(c_1857,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1852])).

tff(c_24,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(A_22,k1_zfmisc_1(B_23))
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1642,plain,(
    ! [A_144,B_145] :
      ( k4_xboole_0(A_144,B_145) = k3_subset_1(A_144,B_145)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(A_144)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1649,plain,(
    ! [B_23,A_22] :
      ( k4_xboole_0(B_23,A_22) = k3_subset_1(B_23,A_22)
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(resolution,[status(thm)],[c_24,c_1642])).

tff(c_1864,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1857,c_1649])).

tff(c_1770,plain,(
    ! [A_160,B_161,C_162] :
      ( k7_subset_1(A_160,B_161,C_162) = k4_xboole_0(B_161,C_162)
      | ~ m1_subset_1(B_161,k1_zfmisc_1(A_160)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1779,plain,(
    ! [C_162] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_162) = k4_xboole_0('#skF_2',C_162) ),
    inference(resolution,[status(thm)],[c_40,c_1770])).

tff(c_46,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_115,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_963,plain,(
    ! [B_106,A_107] :
      ( v4_pre_topc(B_106,A_107)
      | k2_pre_topc(A_107,B_106) != B_106
      | ~ v2_pre_topc(A_107)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_977,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_963])).

tff(c_983,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_977])).

tff(c_984,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_983])).

tff(c_344,plain,(
    ! [A_75,B_76] :
      ( r1_tarski(k1_tops_1(A_75,B_76),B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_352,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_344])).

tff(c_357,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_352])).

tff(c_272,plain,(
    ! [A_68,B_69,C_70] :
      ( k7_subset_1(A_68,B_69,C_70) = k4_xboole_0(B_69,C_70)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_282,plain,(
    ! [C_71] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_71) = k4_xboole_0('#skF_2',C_71) ),
    inference(resolution,[status(thm)],[c_40,c_272])).

tff(c_52,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_183,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_52])).

tff(c_288,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_183])).

tff(c_125,plain,(
    ! [A_52,B_53] :
      ( k4_xboole_0(A_52,B_53) = k3_subset_1(A_52,B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_132,plain,(
    ! [B_23,A_22] :
      ( k4_xboole_0(B_23,A_22) = k3_subset_1(B_23,A_22)
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(resolution,[status(thm)],[c_24,c_125])).

tff(c_362,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_357,c_132])).

tff(c_365,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_362])).

tff(c_147,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(k3_subset_1(A_56,B_57),k1_zfmisc_1(A_56))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ m1_subset_1(A_22,k1_zfmisc_1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_155,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(k3_subset_1(A_56,B_57),A_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(resolution,[status(thm)],[c_147,c_22])).

tff(c_375,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_365,c_155])).

tff(c_425,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_375])).

tff(c_428,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_425])).

tff(c_432,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_428])).

tff(c_433,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_375])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_300,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_6])).

tff(c_303,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_300])).

tff(c_834,plain,(
    ! [A_100,B_101,C_102] :
      ( k4_subset_1(A_100,B_101,C_102) = k2_xboole_0(B_101,C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(A_100))
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_992,plain,(
    ! [B_108,B_109,A_110] :
      ( k4_subset_1(B_108,B_109,A_110) = k2_xboole_0(B_109,A_110)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(B_108))
      | ~ r1_tarski(A_110,B_108) ) ),
    inference(resolution,[status(thm)],[c_24,c_834])).

tff(c_1039,plain,(
    ! [B_112,A_113,A_114] :
      ( k4_subset_1(B_112,A_113,A_114) = k2_xboole_0(A_113,A_114)
      | ~ r1_tarski(A_114,B_112)
      | ~ r1_tarski(A_113,B_112) ) ),
    inference(resolution,[status(thm)],[c_24,c_992])).

tff(c_1082,plain,(
    ! [A_117] :
      ( k4_subset_1('#skF_2',A_117,k1_tops_1('#skF_1','#skF_2')) = k2_xboole_0(A_117,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_117,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_357,c_1039])).

tff(c_161,plain,(
    ! [A_60,B_61] :
      ( k3_subset_1(A_60,k3_subset_1(A_60,B_61)) = B_61
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_169,plain,(
    ! [B_23,A_22] :
      ( k3_subset_1(B_23,k3_subset_1(B_23,A_22)) = A_22
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(resolution,[status(thm)],[c_24,c_161])).

tff(c_372,plain,
    ( k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_365,c_169])).

tff(c_384,plain,(
    k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_372])).

tff(c_434,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_375])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(k3_subset_1(A_10,B_11),k1_zfmisc_1(A_10))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_378,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_365,c_12])).

tff(c_548,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_378])).

tff(c_8,plain,(
    ! [A_7] : k2_subset_1(A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( k4_subset_1(A_20,B_21,k3_subset_1(A_20,B_21)) = k2_subset_1(A_20)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_53,plain,(
    ! [A_20,B_21] :
      ( k4_subset_1(A_20,B_21,k3_subset_1(A_20,B_21)) = A_20
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_20])).

tff(c_552,plain,(
    k4_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'),k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'))) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_548,c_53])).

tff(c_564,plain,(
    k4_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_552])).

tff(c_1088,plain,
    ( k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1082,c_564])).

tff(c_1097,plain,(
    k2_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_303,c_2,c_1088])).

tff(c_439,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_433,c_132])).

tff(c_442,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_439])).

tff(c_482,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_6])).

tff(c_485,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_482])).

tff(c_589,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_485,c_2])).

tff(c_601,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_589])).

tff(c_1103,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1097,c_601])).

tff(c_1061,plain,(
    ! [A_115,B_116] :
      ( k4_subset_1(u1_struct_0(A_115),B_116,k2_tops_1(A_115,B_116)) = k2_pre_topc(A_115,B_116)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1071,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1061])).

tff(c_1077,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1071])).

tff(c_522,plain,(
    ! [A_83,B_84] :
      ( m1_subset_1(k2_tops_1(A_83,B_84),k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_545,plain,(
    ! [A_83,B_84] :
      ( r1_tarski(k2_tops_1(A_83,B_84),u1_struct_0(A_83))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(resolution,[status(thm)],[c_522,c_22])).

tff(c_1011,plain,(
    ! [A_111] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_111) = k2_xboole_0('#skF_2',A_111)
      | ~ r1_tarski(A_111,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_40,c_992])).

tff(c_1015,plain,(
    ! [B_84] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_84)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_84))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_545,c_1011])).

tff(c_1606,plain,(
    ! [B_141] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_141)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_141))
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1015])).

tff(c_1621,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_1606])).

tff(c_1628,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1103,c_1077,c_1621])).

tff(c_1630,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_984,c_1628])).

tff(c_1631,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1780,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1779,c_1631])).

tff(c_1865,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1864,c_1780])).

tff(c_1632,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1913,plain,(
    ! [A_172,B_173] :
      ( k2_pre_topc(A_172,B_173) = B_173
      | ~ v4_pre_topc(B_173,A_172)
      | ~ m1_subset_1(B_173,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ l1_pre_topc(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1924,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1913])).

tff(c_1929,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1632,c_1924])).

tff(c_2562,plain,(
    ! [A_218,B_219] :
      ( k7_subset_1(u1_struct_0(A_218),k2_pre_topc(A_218,B_219),k1_tops_1(A_218,B_219)) = k2_tops_1(A_218,B_219)
      | ~ m1_subset_1(B_219,k1_zfmisc_1(u1_struct_0(A_218)))
      | ~ l1_pre_topc(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2571,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1929,c_2562])).

tff(c_2575,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1864,c_1779,c_2571])).

tff(c_2577,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1865,c_2575])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 12:05:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.36/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.46/1.78  
% 4.46/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.46/1.78  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 4.46/1.78  
% 4.46/1.78  %Foreground sorts:
% 4.46/1.78  
% 4.46/1.78  
% 4.46/1.78  %Background operators:
% 4.46/1.78  
% 4.46/1.78  
% 4.46/1.78  %Foreground operators:
% 4.46/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.46/1.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.46/1.78  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.46/1.78  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.46/1.78  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.46/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.46/1.78  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.46/1.78  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.46/1.78  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.46/1.78  tff('#skF_2', type, '#skF_2': $i).
% 4.46/1.78  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.46/1.78  tff('#skF_1', type, '#skF_1': $i).
% 4.46/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.46/1.78  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.46/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.46/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.46/1.78  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.46/1.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.46/1.78  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.46/1.78  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.46/1.78  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.46/1.78  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.46/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.46/1.78  
% 4.46/1.80  tff(f_125, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 4.46/1.80  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 4.46/1.80  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.46/1.80  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 4.46/1.80  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.46/1.80  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.46/1.80  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.46/1.80  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.46/1.80  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.46/1.80  tff(f_51, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.46/1.80  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.46/1.80  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.46/1.80  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 4.46/1.80  tff(f_113, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 4.46/1.80  tff(f_84, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 4.46/1.80  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 4.46/1.80  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.46/1.80  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.46/1.80  tff(c_1844, plain, (![A_167, B_168]: (r1_tarski(k1_tops_1(A_167, B_168), B_168) | ~m1_subset_1(B_168, k1_zfmisc_1(u1_struct_0(A_167))) | ~l1_pre_topc(A_167))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.46/1.80  tff(c_1852, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1844])).
% 4.46/1.80  tff(c_1857, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1852])).
% 4.46/1.80  tff(c_24, plain, (![A_22, B_23]: (m1_subset_1(A_22, k1_zfmisc_1(B_23)) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.46/1.80  tff(c_1642, plain, (![A_144, B_145]: (k4_xboole_0(A_144, B_145)=k3_subset_1(A_144, B_145) | ~m1_subset_1(B_145, k1_zfmisc_1(A_144)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.46/1.80  tff(c_1649, plain, (![B_23, A_22]: (k4_xboole_0(B_23, A_22)=k3_subset_1(B_23, A_22) | ~r1_tarski(A_22, B_23))), inference(resolution, [status(thm)], [c_24, c_1642])).
% 4.46/1.80  tff(c_1864, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_1857, c_1649])).
% 4.46/1.80  tff(c_1770, plain, (![A_160, B_161, C_162]: (k7_subset_1(A_160, B_161, C_162)=k4_xboole_0(B_161, C_162) | ~m1_subset_1(B_161, k1_zfmisc_1(A_160)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.46/1.80  tff(c_1779, plain, (![C_162]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_162)=k4_xboole_0('#skF_2', C_162))), inference(resolution, [status(thm)], [c_40, c_1770])).
% 4.46/1.80  tff(c_46, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.46/1.80  tff(c_115, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 4.46/1.80  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.46/1.80  tff(c_963, plain, (![B_106, A_107]: (v4_pre_topc(B_106, A_107) | k2_pre_topc(A_107, B_106)!=B_106 | ~v2_pre_topc(A_107) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.46/1.80  tff(c_977, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_963])).
% 4.46/1.80  tff(c_983, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_977])).
% 4.46/1.80  tff(c_984, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_115, c_983])).
% 4.46/1.80  tff(c_344, plain, (![A_75, B_76]: (r1_tarski(k1_tops_1(A_75, B_76), B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.46/1.80  tff(c_352, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_344])).
% 4.46/1.80  tff(c_357, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_352])).
% 4.46/1.80  tff(c_272, plain, (![A_68, B_69, C_70]: (k7_subset_1(A_68, B_69, C_70)=k4_xboole_0(B_69, C_70) | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.46/1.80  tff(c_282, plain, (![C_71]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_71)=k4_xboole_0('#skF_2', C_71))), inference(resolution, [status(thm)], [c_40, c_272])).
% 4.46/1.80  tff(c_52, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.46/1.80  tff(c_183, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_115, c_52])).
% 4.46/1.80  tff(c_288, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_282, c_183])).
% 4.46/1.80  tff(c_125, plain, (![A_52, B_53]: (k4_xboole_0(A_52, B_53)=k3_subset_1(A_52, B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.46/1.80  tff(c_132, plain, (![B_23, A_22]: (k4_xboole_0(B_23, A_22)=k3_subset_1(B_23, A_22) | ~r1_tarski(A_22, B_23))), inference(resolution, [status(thm)], [c_24, c_125])).
% 4.46/1.80  tff(c_362, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_357, c_132])).
% 4.46/1.80  tff(c_365, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_288, c_362])).
% 4.46/1.80  tff(c_147, plain, (![A_56, B_57]: (m1_subset_1(k3_subset_1(A_56, B_57), k1_zfmisc_1(A_56)) | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.46/1.80  tff(c_22, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~m1_subset_1(A_22, k1_zfmisc_1(B_23)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.46/1.80  tff(c_155, plain, (![A_56, B_57]: (r1_tarski(k3_subset_1(A_56, B_57), A_56) | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(resolution, [status(thm)], [c_147, c_22])).
% 4.46/1.80  tff(c_375, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_365, c_155])).
% 4.46/1.80  tff(c_425, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_375])).
% 4.46/1.80  tff(c_428, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_24, c_425])).
% 4.46/1.80  tff(c_432, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_357, c_428])).
% 4.46/1.80  tff(c_433, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_375])).
% 4.46/1.80  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.46/1.80  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.46/1.80  tff(c_300, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_288, c_6])).
% 4.46/1.80  tff(c_303, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_300])).
% 4.46/1.80  tff(c_834, plain, (![A_100, B_101, C_102]: (k4_subset_1(A_100, B_101, C_102)=k2_xboole_0(B_101, C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(A_100)) | ~m1_subset_1(B_101, k1_zfmisc_1(A_100)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.46/1.80  tff(c_992, plain, (![B_108, B_109, A_110]: (k4_subset_1(B_108, B_109, A_110)=k2_xboole_0(B_109, A_110) | ~m1_subset_1(B_109, k1_zfmisc_1(B_108)) | ~r1_tarski(A_110, B_108))), inference(resolution, [status(thm)], [c_24, c_834])).
% 4.46/1.80  tff(c_1039, plain, (![B_112, A_113, A_114]: (k4_subset_1(B_112, A_113, A_114)=k2_xboole_0(A_113, A_114) | ~r1_tarski(A_114, B_112) | ~r1_tarski(A_113, B_112))), inference(resolution, [status(thm)], [c_24, c_992])).
% 4.46/1.80  tff(c_1082, plain, (![A_117]: (k4_subset_1('#skF_2', A_117, k1_tops_1('#skF_1', '#skF_2'))=k2_xboole_0(A_117, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(A_117, '#skF_2'))), inference(resolution, [status(thm)], [c_357, c_1039])).
% 4.46/1.80  tff(c_161, plain, (![A_60, B_61]: (k3_subset_1(A_60, k3_subset_1(A_60, B_61))=B_61 | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.46/1.80  tff(c_169, plain, (![B_23, A_22]: (k3_subset_1(B_23, k3_subset_1(B_23, A_22))=A_22 | ~r1_tarski(A_22, B_23))), inference(resolution, [status(thm)], [c_24, c_161])).
% 4.46/1.80  tff(c_372, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_365, c_169])).
% 4.46/1.80  tff(c_384, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_357, c_372])).
% 4.46/1.80  tff(c_434, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(splitRight, [status(thm)], [c_375])).
% 4.46/1.80  tff(c_12, plain, (![A_10, B_11]: (m1_subset_1(k3_subset_1(A_10, B_11), k1_zfmisc_1(A_10)) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.46/1.80  tff(c_378, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_365, c_12])).
% 4.46/1.80  tff(c_548, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_434, c_378])).
% 4.46/1.80  tff(c_8, plain, (![A_7]: (k2_subset_1(A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.46/1.80  tff(c_20, plain, (![A_20, B_21]: (k4_subset_1(A_20, B_21, k3_subset_1(A_20, B_21))=k2_subset_1(A_20) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.46/1.80  tff(c_53, plain, (![A_20, B_21]: (k4_subset_1(A_20, B_21, k3_subset_1(A_20, B_21))=A_20 | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_20])).
% 4.46/1.80  tff(c_552, plain, (k4_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'), k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2')))='#skF_2'), inference(resolution, [status(thm)], [c_548, c_53])).
% 4.46/1.80  tff(c_564, plain, (k4_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_384, c_552])).
% 4.46/1.80  tff(c_1088, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1082, c_564])).
% 4.46/1.80  tff(c_1097, plain, (k2_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_433, c_303, c_2, c_1088])).
% 4.46/1.80  tff(c_439, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_433, c_132])).
% 4.46/1.80  tff(c_442, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_384, c_439])).
% 4.46/1.80  tff(c_482, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_442, c_6])).
% 4.46/1.80  tff(c_485, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_482])).
% 4.46/1.80  tff(c_589, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_485, c_2])).
% 4.46/1.80  tff(c_601, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_303, c_589])).
% 4.46/1.80  tff(c_1103, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1097, c_601])).
% 4.46/1.80  tff(c_1061, plain, (![A_115, B_116]: (k4_subset_1(u1_struct_0(A_115), B_116, k2_tops_1(A_115, B_116))=k2_pre_topc(A_115, B_116) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.46/1.80  tff(c_1071, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1061])).
% 4.46/1.80  tff(c_1077, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1071])).
% 4.46/1.80  tff(c_522, plain, (![A_83, B_84]: (m1_subset_1(k2_tops_1(A_83, B_84), k1_zfmisc_1(u1_struct_0(A_83))) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.46/1.80  tff(c_545, plain, (![A_83, B_84]: (r1_tarski(k2_tops_1(A_83, B_84), u1_struct_0(A_83)) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83))), inference(resolution, [status(thm)], [c_522, c_22])).
% 4.46/1.80  tff(c_1011, plain, (![A_111]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_111)=k2_xboole_0('#skF_2', A_111) | ~r1_tarski(A_111, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_40, c_992])).
% 4.46/1.80  tff(c_1015, plain, (![B_84]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_84))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_84)) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_545, c_1011])).
% 4.46/1.80  tff(c_1606, plain, (![B_141]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_141))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_141)) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1015])).
% 4.46/1.80  tff(c_1621, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_1606])).
% 4.46/1.80  tff(c_1628, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1103, c_1077, c_1621])).
% 4.46/1.80  tff(c_1630, plain, $false, inference(negUnitSimplification, [status(thm)], [c_984, c_1628])).
% 4.46/1.80  tff(c_1631, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 4.46/1.80  tff(c_1780, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1779, c_1631])).
% 4.46/1.80  tff(c_1865, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1864, c_1780])).
% 4.46/1.80  tff(c_1632, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 4.46/1.80  tff(c_1913, plain, (![A_172, B_173]: (k2_pre_topc(A_172, B_173)=B_173 | ~v4_pre_topc(B_173, A_172) | ~m1_subset_1(B_173, k1_zfmisc_1(u1_struct_0(A_172))) | ~l1_pre_topc(A_172))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.46/1.80  tff(c_1924, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1913])).
% 4.46/1.80  tff(c_1929, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1632, c_1924])).
% 4.46/1.80  tff(c_2562, plain, (![A_218, B_219]: (k7_subset_1(u1_struct_0(A_218), k2_pre_topc(A_218, B_219), k1_tops_1(A_218, B_219))=k2_tops_1(A_218, B_219) | ~m1_subset_1(B_219, k1_zfmisc_1(u1_struct_0(A_218))) | ~l1_pre_topc(A_218))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.46/1.80  tff(c_2571, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1929, c_2562])).
% 4.46/1.80  tff(c_2575, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1864, c_1779, c_2571])).
% 4.46/1.80  tff(c_2577, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1865, c_2575])).
% 4.46/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.46/1.80  
% 4.46/1.80  Inference rules
% 4.46/1.80  ----------------------
% 4.46/1.80  #Ref     : 0
% 4.46/1.80  #Sup     : 616
% 4.46/1.80  #Fact    : 0
% 4.46/1.80  #Define  : 0
% 4.46/1.80  #Split   : 4
% 4.46/1.80  #Chain   : 0
% 4.46/1.80  #Close   : 0
% 4.46/1.80  
% 4.46/1.80  Ordering : KBO
% 4.46/1.80  
% 4.46/1.80  Simplification rules
% 4.46/1.80  ----------------------
% 4.46/1.80  #Subsume      : 29
% 4.46/1.80  #Demod        : 418
% 4.46/1.80  #Tautology    : 351
% 4.46/1.80  #SimpNegUnit  : 6
% 4.46/1.80  #BackRed      : 13
% 4.46/1.80  
% 4.46/1.80  #Partial instantiations: 0
% 4.46/1.80  #Strategies tried      : 1
% 4.46/1.80  
% 4.46/1.80  Timing (in seconds)
% 4.46/1.80  ----------------------
% 4.46/1.80  Preprocessing        : 0.33
% 4.46/1.80  Parsing              : 0.18
% 4.46/1.80  CNF conversion       : 0.02
% 4.46/1.80  Main loop            : 0.68
% 4.46/1.80  Inferencing          : 0.24
% 4.46/1.80  Reduction            : 0.24
% 4.46/1.80  Demodulation         : 0.19
% 4.46/1.80  BG Simplification    : 0.03
% 4.46/1.80  Subsumption          : 0.11
% 4.46/1.80  Abstraction          : 0.04
% 4.46/1.80  MUC search           : 0.00
% 4.46/1.80  Cooper               : 0.00
% 4.46/1.80  Total                : 1.06
% 4.46/1.80  Index Insertion      : 0.00
% 4.46/1.80  Index Deletion       : 0.00
% 4.46/1.80  Index Matching       : 0.00
% 4.46/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
