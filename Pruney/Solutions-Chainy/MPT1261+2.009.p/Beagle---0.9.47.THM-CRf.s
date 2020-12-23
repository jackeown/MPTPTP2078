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
% DateTime   : Thu Dec  3 10:21:12 EST 2020

% Result     : Theorem 12.50s
% Output     : CNFRefutation 12.50s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 377 expanded)
%              Number of leaves         :   48 ( 146 expanded)
%              Depth                    :   16
%              Number of atoms          :  197 ( 631 expanded)
%              Number of equality atoms :   99 ( 249 expanded)
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

tff(f_137,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_125,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_55,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_96,axiom,(
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

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_49,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_118,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(c_60,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_58,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_24229,plain,(
    ! [A_545,B_546,C_547] :
      ( k7_subset_1(A_545,B_546,C_547) = k4_xboole_0(B_546,C_547)
      | ~ m1_subset_1(B_546,k1_zfmisc_1(A_545)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_24248,plain,(
    ! [C_547] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_547) = k4_xboole_0('#skF_2',C_547) ),
    inference(resolution,[status(thm)],[c_58,c_24229])).

tff(c_25374,plain,(
    ! [A_585,B_586] :
      ( k7_subset_1(u1_struct_0(A_585),B_586,k2_tops_1(A_585,B_586)) = k1_tops_1(A_585,B_586)
      | ~ m1_subset_1(B_586,k1_zfmisc_1(u1_struct_0(A_585)))
      | ~ l1_pre_topc(A_585) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_25398,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_25374])).

tff(c_25412,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_24248,c_25398])).

tff(c_16,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_34,plain,(
    ! [A_27,B_28] : k6_subset_1(A_27,B_28) = k4_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_28,plain,(
    ! [A_20,B_21] : m1_subset_1(k6_subset_1(A_20,B_21),k1_zfmisc_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_71,plain,(
    ! [A_20,B_21] : m1_subset_1(k4_xboole_0(A_20,B_21),k1_zfmisc_1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28])).

tff(c_23978,plain,(
    ! [A_536,B_537] :
      ( k4_xboole_0(A_536,B_537) = k3_subset_1(A_536,B_537)
      | ~ m1_subset_1(B_537,k1_zfmisc_1(A_536)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_23993,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_subset_1(A_20,k4_xboole_0(A_20,B_21)) ),
    inference(resolution,[status(thm)],[c_71,c_23978])).

tff(c_24002,plain,(
    ! [A_20,B_21] : k3_subset_1(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_23993])).

tff(c_25426,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_25412,c_24002])).

tff(c_25429,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_25412,c_16])).

tff(c_25921,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25426,c_25429])).

tff(c_64,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_128,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_62,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_2051,plain,(
    ! [B_156,A_157] :
      ( v4_pre_topc(B_156,A_157)
      | k2_pre_topc(A_157,B_156) != B_156
      | ~ v2_pre_topc(A_157)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ l1_pre_topc(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2081,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_2051])).

tff(c_2091,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_62,c_2081])).

tff(c_2092,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_2091])).

tff(c_1269,plain,(
    ! [A_125,B_126,C_127] :
      ( k7_subset_1(A_125,B_126,C_127) = k4_xboole_0(B_126,C_127)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(A_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1292,plain,(
    ! [C_128] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_128) = k4_xboole_0('#skF_2',C_128) ),
    inference(resolution,[status(thm)],[c_58,c_1269])).

tff(c_70,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_231,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_70])).

tff(c_1298,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1292,c_231])).

tff(c_1288,plain,(
    ! [C_127] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_127) = k4_xboole_0('#skF_2',C_127) ),
    inference(resolution,[status(thm)],[c_58,c_1269])).

tff(c_2234,plain,(
    ! [A_158,B_159] :
      ( k7_subset_1(u1_struct_0(A_158),B_159,k2_tops_1(A_158,B_159)) = k1_tops_1(A_158,B_159)
      | ~ m1_subset_1(B_159,k1_zfmisc_1(u1_struct_0(A_158)))
      | ~ l1_pre_topc(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_2258,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_2234])).

tff(c_2272,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1288,c_2258])).

tff(c_2288,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2272,c_16])).

tff(c_2300,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1298,c_2288])).

tff(c_437,plain,(
    ! [A_91,B_92] : k4_xboole_0(A_91,k4_xboole_0(A_91,B_92)) = k3_xboole_0(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_456,plain,(
    ! [A_91,B_92] : r1_tarski(k3_xboole_0(A_91,B_92),A_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_14])).

tff(c_44,plain,(
    ! [A_36,B_37] :
      ( m1_subset_1(A_36,k1_zfmisc_1(B_37))
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1742,plain,(
    ! [A_146,B_147,C_148] :
      ( k4_subset_1(A_146,B_147,C_148) = k2_xboole_0(B_147,C_148)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(A_146))
      | ~ m1_subset_1(B_147,k1_zfmisc_1(A_146)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8504,plain,(
    ! [A_262,B_263,B_264] :
      ( k4_subset_1(A_262,B_263,k4_xboole_0(A_262,B_264)) = k2_xboole_0(B_263,k4_xboole_0(A_262,B_264))
      | ~ m1_subset_1(B_263,k1_zfmisc_1(A_262)) ) ),
    inference(resolution,[status(thm)],[c_71,c_1742])).

tff(c_21840,plain,(
    ! [B_467,A_468,B_469] :
      ( k4_subset_1(B_467,A_468,k4_xboole_0(B_467,B_469)) = k2_xboole_0(A_468,k4_xboole_0(B_467,B_469))
      | ~ r1_tarski(A_468,B_467) ) ),
    inference(resolution,[status(thm)],[c_44,c_8504])).

tff(c_1139,plain,(
    ! [A_122,B_123] :
      ( k4_xboole_0(A_122,B_123) = k3_subset_1(A_122,B_123)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(A_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1154,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_subset_1(A_20,k4_xboole_0(A_20,B_21)) ),
    inference(resolution,[status(thm)],[c_71,c_1139])).

tff(c_1163,plain,(
    ! [A_20,B_21] : k3_subset_1(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1154])).

tff(c_994,plain,(
    ! [A_115,B_116] :
      ( k3_subset_1(A_115,k3_subset_1(A_115,B_116)) = B_116
      | ~ m1_subset_1(B_116,k1_zfmisc_1(A_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2580,plain,(
    ! [B_168,A_169] :
      ( k3_subset_1(B_168,k3_subset_1(B_168,A_169)) = A_169
      | ~ r1_tarski(A_169,B_168) ) ),
    inference(resolution,[status(thm)],[c_44,c_994])).

tff(c_2611,plain,(
    ! [A_20,B_21] :
      ( k3_subset_1(A_20,k3_xboole_0(A_20,B_21)) = k4_xboole_0(A_20,B_21)
      | ~ r1_tarski(k4_xboole_0(A_20,B_21),A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1163,c_2580])).

tff(c_2644,plain,(
    ! [A_20,B_21] : k3_subset_1(A_20,k3_xboole_0(A_20,B_21)) = k4_xboole_0(A_20,B_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2611])).

tff(c_3158,plain,(
    ! [B_181,A_182] :
      ( k4_xboole_0(B_181,A_182) = k3_subset_1(B_181,A_182)
      | ~ r1_tarski(A_182,B_181) ) ),
    inference(resolution,[status(thm)],[c_44,c_1139])).

tff(c_3173,plain,(
    ! [A_91,B_92] : k4_xboole_0(A_91,k3_xboole_0(A_91,B_92)) = k3_subset_1(A_91,k3_xboole_0(A_91,B_92)) ),
    inference(resolution,[status(thm)],[c_456,c_3158])).

tff(c_3198,plain,(
    ! [A_91,B_92] : k4_xboole_0(A_91,k3_xboole_0(A_91,B_92)) = k4_xboole_0(A_91,B_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2644,c_3173])).

tff(c_440,plain,(
    ! [A_91,B_92] : k4_xboole_0(A_91,k3_xboole_0(A_91,B_92)) = k3_xboole_0(A_91,k4_xboole_0(A_91,B_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_16])).

tff(c_3795,plain,(
    ! [A_91,B_92] : k3_xboole_0(A_91,k4_xboole_0(A_91,B_92)) = k4_xboole_0(A_91,B_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3198,c_440])).

tff(c_24,plain,(
    ! [A_17] : k2_subset_1(A_17) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_38,plain,(
    ! [A_32,B_33] :
      ( k4_subset_1(A_32,B_33,k3_subset_1(A_32,B_33)) = k2_subset_1(A_32)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1401,plain,(
    ! [A_134,B_135] :
      ( k4_subset_1(A_134,B_135,k3_subset_1(A_134,B_135)) = A_134
      | ~ m1_subset_1(B_135,k1_zfmisc_1(A_134)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_38])).

tff(c_1418,plain,(
    ! [A_20,B_21] : k4_subset_1(A_20,k4_xboole_0(A_20,B_21),k3_subset_1(A_20,k4_xboole_0(A_20,B_21))) = A_20 ),
    inference(resolution,[status(thm)],[c_71,c_1401])).

tff(c_5307,plain,(
    ! [A_224,B_225] : k4_subset_1(A_224,k4_xboole_0(A_224,B_225),k3_xboole_0(A_224,B_225)) = A_224 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1163,c_1418])).

tff(c_5391,plain,(
    ! [A_9,B_10] : k4_subset_1(A_9,k3_xboole_0(A_9,B_10),k3_xboole_0(A_9,k4_xboole_0(A_9,B_10))) = A_9 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_5307])).

tff(c_5434,plain,(
    ! [A_9,B_10] : k4_subset_1(A_9,k3_xboole_0(A_9,B_10),k4_xboole_0(A_9,B_10)) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3795,c_5391])).

tff(c_21867,plain,(
    ! [B_467,B_469] :
      ( k2_xboole_0(k3_xboole_0(B_467,B_469),k4_xboole_0(B_467,B_469)) = B_467
      | ~ r1_tarski(k3_xboole_0(B_467,B_469),B_467) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21840,c_5434])).

tff(c_21992,plain,(
    ! [B_467,B_469] : k2_xboole_0(k3_xboole_0(B_467,B_469),k4_xboole_0(B_467,B_469)) = B_467 ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_21867])).

tff(c_20,plain,(
    ! [B_14,A_13] : k2_tarski(B_14,A_13) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_271,plain,(
    ! [A_77,B_78] : k3_tarski(k2_tarski(A_77,B_78)) = k2_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_414,plain,(
    ! [A_89,B_90] : k3_tarski(k2_tarski(A_89,B_90)) = k2_xboole_0(B_90,A_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_271])).

tff(c_22,plain,(
    ! [A_15,B_16] : k3_tarski(k2_tarski(A_15,B_16)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_420,plain,(
    ! [B_90,A_89] : k2_xboole_0(B_90,A_89) = k2_xboole_0(A_89,B_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_22])).

tff(c_22032,plain,(
    ! [B_470,B_471] : k2_xboole_0(k3_xboole_0(B_470,B_471),k4_xboole_0(B_470,B_471)) = B_470 ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_21867])).

tff(c_18,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22059,plain,(
    ! [B_470,B_471] : k2_xboole_0(k3_xboole_0(B_470,B_471),k4_xboole_0(B_470,B_471)) = k2_xboole_0(k3_xboole_0(B_470,B_471),B_470) ),
    inference(superposition,[status(thm),theory(equality)],[c_22032,c_18])).

tff(c_22288,plain,(
    ! [B_472,B_473] : k2_xboole_0(B_472,k3_xboole_0(B_472,B_473)) = B_472 ),
    inference(demodulation,[status(thm),theory(equality)],[c_21992,c_420,c_22059])).

tff(c_22389,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2300,c_22288])).

tff(c_2438,plain,(
    ! [A_162,B_163] :
      ( k4_subset_1(u1_struct_0(A_162),B_163,k2_tops_1(A_162,B_163)) = k2_pre_topc(A_162,B_163)
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ l1_pre_topc(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2462,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_2438])).

tff(c_2475,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2462])).

tff(c_50,plain,(
    ! [A_41,B_42] :
      ( m1_subset_1(k2_tops_1(A_41,B_42),k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_14087,plain,(
    ! [A_366,B_367,B_368] :
      ( k4_subset_1(u1_struct_0(A_366),B_367,k2_tops_1(A_366,B_368)) = k2_xboole_0(B_367,k2_tops_1(A_366,B_368))
      | ~ m1_subset_1(B_367,k1_zfmisc_1(u1_struct_0(A_366)))
      | ~ m1_subset_1(B_368,k1_zfmisc_1(u1_struct_0(A_366)))
      | ~ l1_pre_topc(A_366) ) ),
    inference(resolution,[status(thm)],[c_50,c_1742])).

tff(c_14113,plain,(
    ! [B_368] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_368)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_368))
      | ~ m1_subset_1(B_368,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_58,c_14087])).

tff(c_14134,plain,(
    ! [B_369] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_369)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_369))
      | ~ m1_subset_1(B_369,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_14113])).

tff(c_14171,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_14134])).

tff(c_14184,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2475,c_14171])).

tff(c_22933,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22389,c_14184])).

tff(c_22935,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2092,c_22933])).

tff(c_22936,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_24315,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24248,c_22936])).

tff(c_25922,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25921,c_24315])).

tff(c_22937,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_24847,plain,(
    ! [A_570,B_571] :
      ( r1_tarski(k2_tops_1(A_570,B_571),B_571)
      | ~ v4_pre_topc(B_571,A_570)
      | ~ m1_subset_1(B_571,k1_zfmisc_1(u1_struct_0(A_570)))
      | ~ l1_pre_topc(A_570) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_24869,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_24847])).

tff(c_24879,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_22937,c_24869])).

tff(c_25871,plain,(
    ! [B_598,A_599] :
      ( k4_xboole_0(B_598,A_599) = k3_subset_1(B_598,A_599)
      | ~ r1_tarski(A_599,B_598) ) ),
    inference(resolution,[status(thm)],[c_44,c_23978])).

tff(c_25877,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24879,c_25871])).

tff(c_25904,plain,(
    k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25412,c_25877])).

tff(c_24105,plain,(
    ! [A_539,B_540] :
      ( k3_subset_1(A_539,k3_subset_1(A_539,B_540)) = B_540
      | ~ m1_subset_1(B_540,k1_zfmisc_1(A_539)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24120,plain,(
    ! [B_37,A_36] :
      ( k3_subset_1(B_37,k3_subset_1(B_37,A_36)) = A_36
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(resolution,[status(thm)],[c_44,c_24105])).

tff(c_26319,plain,
    ( k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_25904,c_24120])).

tff(c_26323,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24879,c_26319])).

tff(c_26325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25922,c_26323])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:32:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.50/5.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.50/5.34  
% 12.50/5.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.50/5.34  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 12.50/5.34  
% 12.50/5.34  %Foreground sorts:
% 12.50/5.34  
% 12.50/5.34  
% 12.50/5.34  %Background operators:
% 12.50/5.34  
% 12.50/5.34  
% 12.50/5.34  %Foreground operators:
% 12.50/5.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.50/5.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.50/5.34  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 12.50/5.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.50/5.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 12.50/5.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.50/5.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.50/5.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.50/5.34  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 12.50/5.34  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 12.50/5.34  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 12.50/5.34  tff('#skF_2', type, '#skF_2': $i).
% 12.50/5.34  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 12.50/5.34  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 12.50/5.34  tff('#skF_1', type, '#skF_1': $i).
% 12.50/5.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.50/5.34  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 12.50/5.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.50/5.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 12.50/5.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.50/5.34  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 12.50/5.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.50/5.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.50/5.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.50/5.34  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 12.50/5.34  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 12.50/5.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.50/5.34  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 12.50/5.34  
% 12.50/5.36  tff(f_137, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 12.50/5.36  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 12.50/5.36  tff(f_125, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 12.50/5.36  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 12.50/5.36  tff(f_67, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 12.50/5.36  tff(f_55, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 12.50/5.36  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 12.50/5.36  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 12.50/5.36  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 12.50/5.36  tff(f_81, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 12.50/5.36  tff(f_65, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 12.50/5.36  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 12.50/5.36  tff(f_49, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 12.50/5.36  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 12.50/5.36  tff(f_45, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 12.50/5.36  tff(f_47, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 12.50/5.36  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_1)).
% 12.50/5.36  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 12.50/5.36  tff(f_102, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 12.50/5.36  tff(f_118, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 12.50/5.36  tff(c_60, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_137])).
% 12.50/5.36  tff(c_58, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 12.50/5.36  tff(c_24229, plain, (![A_545, B_546, C_547]: (k7_subset_1(A_545, B_546, C_547)=k4_xboole_0(B_546, C_547) | ~m1_subset_1(B_546, k1_zfmisc_1(A_545)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.50/5.36  tff(c_24248, plain, (![C_547]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_547)=k4_xboole_0('#skF_2', C_547))), inference(resolution, [status(thm)], [c_58, c_24229])).
% 12.50/5.36  tff(c_25374, plain, (![A_585, B_586]: (k7_subset_1(u1_struct_0(A_585), B_586, k2_tops_1(A_585, B_586))=k1_tops_1(A_585, B_586) | ~m1_subset_1(B_586, k1_zfmisc_1(u1_struct_0(A_585))) | ~l1_pre_topc(A_585))), inference(cnfTransformation, [status(thm)], [f_125])).
% 12.50/5.36  tff(c_25398, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_25374])).
% 12.50/5.36  tff(c_25412, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_24248, c_25398])).
% 12.50/5.36  tff(c_16, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.50/5.36  tff(c_34, plain, (![A_27, B_28]: (k6_subset_1(A_27, B_28)=k4_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_67])).
% 12.50/5.36  tff(c_28, plain, (![A_20, B_21]: (m1_subset_1(k6_subset_1(A_20, B_21), k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.50/5.36  tff(c_71, plain, (![A_20, B_21]: (m1_subset_1(k4_xboole_0(A_20, B_21), k1_zfmisc_1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28])).
% 12.50/5.36  tff(c_23978, plain, (![A_536, B_537]: (k4_xboole_0(A_536, B_537)=k3_subset_1(A_536, B_537) | ~m1_subset_1(B_537, k1_zfmisc_1(A_536)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.50/5.36  tff(c_23993, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_subset_1(A_20, k4_xboole_0(A_20, B_21)))), inference(resolution, [status(thm)], [c_71, c_23978])).
% 12.50/5.36  tff(c_24002, plain, (![A_20, B_21]: (k3_subset_1(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_23993])).
% 12.50/5.36  tff(c_25426, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_25412, c_24002])).
% 12.50/5.36  tff(c_25429, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_25412, c_16])).
% 12.50/5.36  tff(c_25921, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_25426, c_25429])).
% 12.50/5.36  tff(c_64, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_137])).
% 12.50/5.36  tff(c_128, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_64])).
% 12.50/5.36  tff(c_62, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_137])).
% 12.50/5.36  tff(c_2051, plain, (![B_156, A_157]: (v4_pre_topc(B_156, A_157) | k2_pre_topc(A_157, B_156)!=B_156 | ~v2_pre_topc(A_157) | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0(A_157))) | ~l1_pre_topc(A_157))), inference(cnfTransformation, [status(thm)], [f_96])).
% 12.50/5.36  tff(c_2081, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_2051])).
% 12.50/5.36  tff(c_2091, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_62, c_2081])).
% 12.50/5.36  tff(c_2092, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_128, c_2091])).
% 12.50/5.36  tff(c_1269, plain, (![A_125, B_126, C_127]: (k7_subset_1(A_125, B_126, C_127)=k4_xboole_0(B_126, C_127) | ~m1_subset_1(B_126, k1_zfmisc_1(A_125)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.50/5.36  tff(c_1292, plain, (![C_128]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_128)=k4_xboole_0('#skF_2', C_128))), inference(resolution, [status(thm)], [c_58, c_1269])).
% 12.50/5.36  tff(c_70, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_137])).
% 12.50/5.36  tff(c_231, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_128, c_70])).
% 12.50/5.36  tff(c_1298, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1292, c_231])).
% 12.50/5.36  tff(c_1288, plain, (![C_127]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_127)=k4_xboole_0('#skF_2', C_127))), inference(resolution, [status(thm)], [c_58, c_1269])).
% 12.50/5.36  tff(c_2234, plain, (![A_158, B_159]: (k7_subset_1(u1_struct_0(A_158), B_159, k2_tops_1(A_158, B_159))=k1_tops_1(A_158, B_159) | ~m1_subset_1(B_159, k1_zfmisc_1(u1_struct_0(A_158))) | ~l1_pre_topc(A_158))), inference(cnfTransformation, [status(thm)], [f_125])).
% 12.50/5.36  tff(c_2258, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_2234])).
% 12.50/5.36  tff(c_2272, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1288, c_2258])).
% 12.50/5.36  tff(c_2288, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2272, c_16])).
% 12.50/5.36  tff(c_2300, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1298, c_2288])).
% 12.50/5.36  tff(c_437, plain, (![A_91, B_92]: (k4_xboole_0(A_91, k4_xboole_0(A_91, B_92))=k3_xboole_0(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.50/5.36  tff(c_14, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.50/5.36  tff(c_456, plain, (![A_91, B_92]: (r1_tarski(k3_xboole_0(A_91, B_92), A_91))), inference(superposition, [status(thm), theory('equality')], [c_437, c_14])).
% 12.50/5.36  tff(c_44, plain, (![A_36, B_37]: (m1_subset_1(A_36, k1_zfmisc_1(B_37)) | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_81])).
% 12.50/5.36  tff(c_1742, plain, (![A_146, B_147, C_148]: (k4_subset_1(A_146, B_147, C_148)=k2_xboole_0(B_147, C_148) | ~m1_subset_1(C_148, k1_zfmisc_1(A_146)) | ~m1_subset_1(B_147, k1_zfmisc_1(A_146)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.50/5.36  tff(c_8504, plain, (![A_262, B_263, B_264]: (k4_subset_1(A_262, B_263, k4_xboole_0(A_262, B_264))=k2_xboole_0(B_263, k4_xboole_0(A_262, B_264)) | ~m1_subset_1(B_263, k1_zfmisc_1(A_262)))), inference(resolution, [status(thm)], [c_71, c_1742])).
% 12.50/5.36  tff(c_21840, plain, (![B_467, A_468, B_469]: (k4_subset_1(B_467, A_468, k4_xboole_0(B_467, B_469))=k2_xboole_0(A_468, k4_xboole_0(B_467, B_469)) | ~r1_tarski(A_468, B_467))), inference(resolution, [status(thm)], [c_44, c_8504])).
% 12.50/5.36  tff(c_1139, plain, (![A_122, B_123]: (k4_xboole_0(A_122, B_123)=k3_subset_1(A_122, B_123) | ~m1_subset_1(B_123, k1_zfmisc_1(A_122)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.50/5.36  tff(c_1154, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_subset_1(A_20, k4_xboole_0(A_20, B_21)))), inference(resolution, [status(thm)], [c_71, c_1139])).
% 12.50/5.36  tff(c_1163, plain, (![A_20, B_21]: (k3_subset_1(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1154])).
% 12.50/5.36  tff(c_994, plain, (![A_115, B_116]: (k3_subset_1(A_115, k3_subset_1(A_115, B_116))=B_116 | ~m1_subset_1(B_116, k1_zfmisc_1(A_115)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.50/5.36  tff(c_2580, plain, (![B_168, A_169]: (k3_subset_1(B_168, k3_subset_1(B_168, A_169))=A_169 | ~r1_tarski(A_169, B_168))), inference(resolution, [status(thm)], [c_44, c_994])).
% 12.50/5.36  tff(c_2611, plain, (![A_20, B_21]: (k3_subset_1(A_20, k3_xboole_0(A_20, B_21))=k4_xboole_0(A_20, B_21) | ~r1_tarski(k4_xboole_0(A_20, B_21), A_20))), inference(superposition, [status(thm), theory('equality')], [c_1163, c_2580])).
% 12.50/5.36  tff(c_2644, plain, (![A_20, B_21]: (k3_subset_1(A_20, k3_xboole_0(A_20, B_21))=k4_xboole_0(A_20, B_21))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2611])).
% 12.50/5.36  tff(c_3158, plain, (![B_181, A_182]: (k4_xboole_0(B_181, A_182)=k3_subset_1(B_181, A_182) | ~r1_tarski(A_182, B_181))), inference(resolution, [status(thm)], [c_44, c_1139])).
% 12.50/5.36  tff(c_3173, plain, (![A_91, B_92]: (k4_xboole_0(A_91, k3_xboole_0(A_91, B_92))=k3_subset_1(A_91, k3_xboole_0(A_91, B_92)))), inference(resolution, [status(thm)], [c_456, c_3158])).
% 12.50/5.36  tff(c_3198, plain, (![A_91, B_92]: (k4_xboole_0(A_91, k3_xboole_0(A_91, B_92))=k4_xboole_0(A_91, B_92))), inference(demodulation, [status(thm), theory('equality')], [c_2644, c_3173])).
% 12.50/5.36  tff(c_440, plain, (![A_91, B_92]: (k4_xboole_0(A_91, k3_xboole_0(A_91, B_92))=k3_xboole_0(A_91, k4_xboole_0(A_91, B_92)))), inference(superposition, [status(thm), theory('equality')], [c_437, c_16])).
% 12.50/5.36  tff(c_3795, plain, (![A_91, B_92]: (k3_xboole_0(A_91, k4_xboole_0(A_91, B_92))=k4_xboole_0(A_91, B_92))), inference(demodulation, [status(thm), theory('equality')], [c_3198, c_440])).
% 12.50/5.36  tff(c_24, plain, (![A_17]: (k2_subset_1(A_17)=A_17)), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.50/5.36  tff(c_38, plain, (![A_32, B_33]: (k4_subset_1(A_32, B_33, k3_subset_1(A_32, B_33))=k2_subset_1(A_32) | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.50/5.36  tff(c_1401, plain, (![A_134, B_135]: (k4_subset_1(A_134, B_135, k3_subset_1(A_134, B_135))=A_134 | ~m1_subset_1(B_135, k1_zfmisc_1(A_134)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_38])).
% 12.50/5.36  tff(c_1418, plain, (![A_20, B_21]: (k4_subset_1(A_20, k4_xboole_0(A_20, B_21), k3_subset_1(A_20, k4_xboole_0(A_20, B_21)))=A_20)), inference(resolution, [status(thm)], [c_71, c_1401])).
% 12.50/5.36  tff(c_5307, plain, (![A_224, B_225]: (k4_subset_1(A_224, k4_xboole_0(A_224, B_225), k3_xboole_0(A_224, B_225))=A_224)), inference(demodulation, [status(thm), theory('equality')], [c_1163, c_1418])).
% 12.50/5.36  tff(c_5391, plain, (![A_9, B_10]: (k4_subset_1(A_9, k3_xboole_0(A_9, B_10), k3_xboole_0(A_9, k4_xboole_0(A_9, B_10)))=A_9)), inference(superposition, [status(thm), theory('equality')], [c_16, c_5307])).
% 12.50/5.36  tff(c_5434, plain, (![A_9, B_10]: (k4_subset_1(A_9, k3_xboole_0(A_9, B_10), k4_xboole_0(A_9, B_10))=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_3795, c_5391])).
% 12.50/5.36  tff(c_21867, plain, (![B_467, B_469]: (k2_xboole_0(k3_xboole_0(B_467, B_469), k4_xboole_0(B_467, B_469))=B_467 | ~r1_tarski(k3_xboole_0(B_467, B_469), B_467))), inference(superposition, [status(thm), theory('equality')], [c_21840, c_5434])).
% 12.50/5.36  tff(c_21992, plain, (![B_467, B_469]: (k2_xboole_0(k3_xboole_0(B_467, B_469), k4_xboole_0(B_467, B_469))=B_467)), inference(demodulation, [status(thm), theory('equality')], [c_456, c_21867])).
% 12.50/5.36  tff(c_20, plain, (![B_14, A_13]: (k2_tarski(B_14, A_13)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.50/5.36  tff(c_271, plain, (![A_77, B_78]: (k3_tarski(k2_tarski(A_77, B_78))=k2_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.50/5.36  tff(c_414, plain, (![A_89, B_90]: (k3_tarski(k2_tarski(A_89, B_90))=k2_xboole_0(B_90, A_89))), inference(superposition, [status(thm), theory('equality')], [c_20, c_271])).
% 12.50/5.36  tff(c_22, plain, (![A_15, B_16]: (k3_tarski(k2_tarski(A_15, B_16))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.50/5.36  tff(c_420, plain, (![B_90, A_89]: (k2_xboole_0(B_90, A_89)=k2_xboole_0(A_89, B_90))), inference(superposition, [status(thm), theory('equality')], [c_414, c_22])).
% 12.50/5.36  tff(c_22032, plain, (![B_470, B_471]: (k2_xboole_0(k3_xboole_0(B_470, B_471), k4_xboole_0(B_470, B_471))=B_470)), inference(demodulation, [status(thm), theory('equality')], [c_456, c_21867])).
% 12.50/5.36  tff(c_18, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k2_xboole_0(A_11, B_12))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.50/5.36  tff(c_22059, plain, (![B_470, B_471]: (k2_xboole_0(k3_xboole_0(B_470, B_471), k4_xboole_0(B_470, B_471))=k2_xboole_0(k3_xboole_0(B_470, B_471), B_470))), inference(superposition, [status(thm), theory('equality')], [c_22032, c_18])).
% 12.50/5.36  tff(c_22288, plain, (![B_472, B_473]: (k2_xboole_0(B_472, k3_xboole_0(B_472, B_473))=B_472)), inference(demodulation, [status(thm), theory('equality')], [c_21992, c_420, c_22059])).
% 12.50/5.36  tff(c_22389, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2300, c_22288])).
% 12.50/5.36  tff(c_2438, plain, (![A_162, B_163]: (k4_subset_1(u1_struct_0(A_162), B_163, k2_tops_1(A_162, B_163))=k2_pre_topc(A_162, B_163) | ~m1_subset_1(B_163, k1_zfmisc_1(u1_struct_0(A_162))) | ~l1_pre_topc(A_162))), inference(cnfTransformation, [status(thm)], [f_109])).
% 12.50/5.36  tff(c_2462, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_2438])).
% 12.50/5.36  tff(c_2475, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2462])).
% 12.50/5.36  tff(c_50, plain, (![A_41, B_42]: (m1_subset_1(k2_tops_1(A_41, B_42), k1_zfmisc_1(u1_struct_0(A_41))) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.50/5.36  tff(c_14087, plain, (![A_366, B_367, B_368]: (k4_subset_1(u1_struct_0(A_366), B_367, k2_tops_1(A_366, B_368))=k2_xboole_0(B_367, k2_tops_1(A_366, B_368)) | ~m1_subset_1(B_367, k1_zfmisc_1(u1_struct_0(A_366))) | ~m1_subset_1(B_368, k1_zfmisc_1(u1_struct_0(A_366))) | ~l1_pre_topc(A_366))), inference(resolution, [status(thm)], [c_50, c_1742])).
% 12.50/5.36  tff(c_14113, plain, (![B_368]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_368))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_368)) | ~m1_subset_1(B_368, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_58, c_14087])).
% 12.50/5.36  tff(c_14134, plain, (![B_369]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_369))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_369)) | ~m1_subset_1(B_369, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_14113])).
% 12.50/5.36  tff(c_14171, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_14134])).
% 12.50/5.36  tff(c_14184, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2475, c_14171])).
% 12.50/5.36  tff(c_22933, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_22389, c_14184])).
% 12.50/5.36  tff(c_22935, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2092, c_22933])).
% 12.50/5.36  tff(c_22936, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_64])).
% 12.50/5.36  tff(c_24315, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24248, c_22936])).
% 12.50/5.36  tff(c_25922, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_25921, c_24315])).
% 12.50/5.36  tff(c_22937, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_64])).
% 12.50/5.36  tff(c_24847, plain, (![A_570, B_571]: (r1_tarski(k2_tops_1(A_570, B_571), B_571) | ~v4_pre_topc(B_571, A_570) | ~m1_subset_1(B_571, k1_zfmisc_1(u1_struct_0(A_570))) | ~l1_pre_topc(A_570))), inference(cnfTransformation, [status(thm)], [f_118])).
% 12.50/5.36  tff(c_24869, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_24847])).
% 12.50/5.36  tff(c_24879, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_22937, c_24869])).
% 12.50/5.36  tff(c_25871, plain, (![B_598, A_599]: (k4_xboole_0(B_598, A_599)=k3_subset_1(B_598, A_599) | ~r1_tarski(A_599, B_598))), inference(resolution, [status(thm)], [c_44, c_23978])).
% 12.50/5.36  tff(c_25877, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_24879, c_25871])).
% 12.50/5.36  tff(c_25904, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_25412, c_25877])).
% 12.50/5.36  tff(c_24105, plain, (![A_539, B_540]: (k3_subset_1(A_539, k3_subset_1(A_539, B_540))=B_540 | ~m1_subset_1(B_540, k1_zfmisc_1(A_539)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.50/5.36  tff(c_24120, plain, (![B_37, A_36]: (k3_subset_1(B_37, k3_subset_1(B_37, A_36))=A_36 | ~r1_tarski(A_36, B_37))), inference(resolution, [status(thm)], [c_44, c_24105])).
% 12.50/5.36  tff(c_26319, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_25904, c_24120])).
% 12.50/5.36  tff(c_26323, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24879, c_26319])).
% 12.50/5.36  tff(c_26325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25922, c_26323])).
% 12.50/5.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.50/5.36  
% 12.50/5.36  Inference rules
% 12.50/5.36  ----------------------
% 12.50/5.36  #Ref     : 0
% 12.50/5.36  #Sup     : 6308
% 12.50/5.36  #Fact    : 0
% 12.50/5.36  #Define  : 0
% 12.50/5.36  #Split   : 12
% 12.50/5.36  #Chain   : 0
% 12.50/5.36  #Close   : 0
% 12.50/5.36  
% 12.50/5.36  Ordering : KBO
% 12.50/5.36  
% 12.50/5.36  Simplification rules
% 12.50/5.36  ----------------------
% 12.50/5.36  #Subsume      : 598
% 12.50/5.36  #Demod        : 8275
% 12.50/5.36  #Tautology    : 4352
% 12.50/5.36  #SimpNegUnit  : 34
% 12.50/5.36  #BackRed      : 71
% 12.50/5.36  
% 12.50/5.36  #Partial instantiations: 0
% 12.50/5.36  #Strategies tried      : 1
% 12.50/5.36  
% 12.50/5.36  Timing (in seconds)
% 12.50/5.36  ----------------------
% 12.50/5.37  Preprocessing        : 0.43
% 12.50/5.37  Parsing              : 0.20
% 12.50/5.37  CNF conversion       : 0.04
% 12.50/5.37  Main loop            : 4.13
% 12.76/5.37  Inferencing          : 0.89
% 12.76/5.37  Reduction            : 2.26
% 12.76/5.37  Demodulation         : 1.92
% 12.76/5.37  BG Simplification    : 0.09
% 12.76/5.37  Subsumption          : 0.67
% 12.76/5.37  Abstraction          : 0.17
% 12.76/5.37  MUC search           : 0.00
% 12.76/5.37  Cooper               : 0.00
% 12.76/5.37  Total                : 4.61
% 12.76/5.37  Index Insertion      : 0.00
% 12.76/5.37  Index Deletion       : 0.00
% 12.76/5.37  Index Matching       : 0.00
% 12.76/5.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
