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
% DateTime   : Thu Dec  3 10:20:35 EST 2020

% Result     : Theorem 8.90s
% Output     : CNFRefutation 8.90s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 232 expanded)
%              Number of leaves         :   24 (  88 expanded)
%              Depth                    :   16
%              Number of atoms          :  118 ( 450 expanded)
%              Number of equality atoms :   10 (  60 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(k3_subset_1(A,B),C)
           => r1_tarski(k3_subset_1(A,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_subset_1)).

tff(c_20,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_45,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(A_30,B_31) = k3_subset_1(A_30,B_31)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_53,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),'#skF_2') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_45])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_57,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_4])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_61,plain,(
    ! [B_32,A_33] :
      ( k4_xboole_0(B_32,A_33) = k3_subset_1(B_32,A_33)
      | ~ r1_tarski(A_33,B_32) ) ),
    inference(resolution,[status(thm)],[c_12,c_45])).

tff(c_75,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k4_xboole_0(A_34,B_35)) = k3_subset_1(A_34,k4_xboole_0(A_34,B_35)) ),
    inference(resolution,[status(thm)],[c_4,c_61])).

tff(c_99,plain,(
    ! [A_36,B_37] : r1_tarski(k3_subset_1(A_36,k4_xboole_0(A_36,B_37)),A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_4])).

tff(c_108,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_99])).

tff(c_18,plain,(
    ! [A_18,B_20] :
      ( k3_subset_1(u1_struct_0(A_18),k2_pre_topc(A_18,k3_subset_1(u1_struct_0(A_18),B_20))) = k1_tops_1(A_18,B_20)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_201,plain,(
    ! [A_48,B_49] :
      ( m1_subset_1(k2_pre_topc(A_48,B_49),k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k3_subset_1(A_5,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_655,plain,(
    ! [A_71,B_72] :
      ( k4_xboole_0(u1_struct_0(A_71),k2_pre_topc(A_71,B_72)) = k3_subset_1(u1_struct_0(A_71),k2_pre_topc(A_71,B_72))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(resolution,[status(thm)],[c_201,c_6])).

tff(c_770,plain,(
    ! [A_75,A_76] :
      ( k4_xboole_0(u1_struct_0(A_75),k2_pre_topc(A_75,A_76)) = k3_subset_1(u1_struct_0(A_75),k2_pre_topc(A_75,A_76))
      | ~ l1_pre_topc(A_75)
      | ~ r1_tarski(A_76,u1_struct_0(A_75)) ) ),
    inference(resolution,[status(thm)],[c_12,c_655])).

tff(c_824,plain,(
    ! [A_77,A_78] :
      ( r1_tarski(k3_subset_1(u1_struct_0(A_77),k2_pre_topc(A_77,A_78)),u1_struct_0(A_77))
      | ~ l1_pre_topc(A_77)
      | ~ r1_tarski(A_78,u1_struct_0(A_77)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_770,c_4])).

tff(c_1376,plain,(
    ! [A_102,B_103] :
      ( r1_tarski(k1_tops_1(A_102,B_103),u1_struct_0(A_102))
      | ~ l1_pre_topc(A_102)
      | ~ r1_tarski(k3_subset_1(u1_struct_0(A_102),B_103),u1_struct_0(A_102))
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_824])).

tff(c_1457,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_108,c_1376])).

tff(c_1518,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1457])).

tff(c_2235,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1518])).

tff(c_2238,plain,(
    ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_12,c_2235])).

tff(c_2242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_2238])).

tff(c_2244,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1518])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k2_pre_topc(A_13,B_14),k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [B_17,A_15] :
      ( r1_tarski(B_17,k2_pre_topc(A_15,B_17))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2273,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2244,c_16])).

tff(c_2288,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2273])).

tff(c_8,plain,(
    ! [A_7,C_10,B_8] :
      ( r1_tarski(k3_subset_1(A_7,C_10),B_8)
      | ~ r1_tarski(k3_subset_1(A_7,B_8),C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2303,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),'#skF_2')
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2288,c_8])).

tff(c_2309,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),'#skF_2')
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2303])).

tff(c_7046,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2309])).

tff(c_7170,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_7046])).

tff(c_7177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2244,c_7170])).

tff(c_7179,plain,(
    m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_2309])).

tff(c_121,plain,(
    ! [B_40,A_41] :
      ( r1_tarski(B_40,k2_pre_topc(A_41,B_40))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_127,plain,(
    ! [A_11,A_41] :
      ( r1_tarski(A_11,k2_pre_topc(A_41,A_11))
      | ~ l1_pre_topc(A_41)
      | ~ r1_tarski(A_11,u1_struct_0(A_41)) ) ),
    inference(resolution,[status(thm)],[c_12,c_121])).

tff(c_326,plain,(
    ! [A_56,C_57,B_58] :
      ( r1_tarski(k3_subset_1(A_56,C_57),B_58)
      | ~ r1_tarski(k3_subset_1(A_56,B_58),C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(A_56))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1633,plain,(
    ! [A_104,A_105,B_106] :
      ( r1_tarski(k3_subset_1(A_104,k2_pre_topc(A_105,k3_subset_1(A_104,B_106))),B_106)
      | ~ m1_subset_1(k2_pre_topc(A_105,k3_subset_1(A_104,B_106)),k1_zfmisc_1(A_104))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_104))
      | ~ l1_pre_topc(A_105)
      | ~ r1_tarski(k3_subset_1(A_104,B_106),u1_struct_0(A_105)) ) ),
    inference(resolution,[status(thm)],[c_127,c_326])).

tff(c_1651,plain,(
    ! [A_18,B_20] :
      ( r1_tarski(k1_tops_1(A_18,B_20),B_20)
      | ~ m1_subset_1(k2_pre_topc(A_18,k3_subset_1(u1_struct_0(A_18),B_20)),k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18)
      | ~ r1_tarski(k3_subset_1(u1_struct_0(A_18),B_20),u1_struct_0(A_18))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1633])).

tff(c_7183,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_7179,c_1651])).

tff(c_7204,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_57,c_7183])).

tff(c_7206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_7204])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:11:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.90/2.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.90/2.93  
% 8.90/2.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.90/2.93  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 8.90/2.93  
% 8.90/2.93  %Foreground sorts:
% 8.90/2.93  
% 8.90/2.93  
% 8.90/2.93  %Background operators:
% 8.90/2.93  
% 8.90/2.93  
% 8.90/2.93  %Foreground operators:
% 8.90/2.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.90/2.93  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.90/2.93  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.90/2.93  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.90/2.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.90/2.93  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 8.90/2.93  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 8.90/2.93  tff('#skF_2', type, '#skF_2': $i).
% 8.90/2.93  tff('#skF_1', type, '#skF_1': $i).
% 8.90/2.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.90/2.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.90/2.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.90/2.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.90/2.93  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.90/2.93  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.90/2.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.90/2.93  
% 8.90/2.95  tff(f_74, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 8.90/2.95  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 8.90/2.95  tff(f_29, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.90/2.95  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.90/2.95  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 8.90/2.95  tff(f_52, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 8.90/2.95  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 8.90/2.95  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), C) => r1_tarski(k3_subset_1(A, C), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_subset_1)).
% 8.90/2.95  tff(c_20, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.90/2.95  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.90/2.95  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.90/2.95  tff(c_45, plain, (![A_30, B_31]: (k4_xboole_0(A_30, B_31)=k3_subset_1(A_30, B_31) | ~m1_subset_1(B_31, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.90/2.95  tff(c_53, plain, (k4_xboole_0(u1_struct_0('#skF_1'), '#skF_2')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_22, c_45])).
% 8.90/2.95  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.90/2.95  tff(c_57, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_53, c_4])).
% 8.90/2.95  tff(c_12, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.90/2.95  tff(c_61, plain, (![B_32, A_33]: (k4_xboole_0(B_32, A_33)=k3_subset_1(B_32, A_33) | ~r1_tarski(A_33, B_32))), inference(resolution, [status(thm)], [c_12, c_45])).
% 8.90/2.95  tff(c_75, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k4_xboole_0(A_34, B_35))=k3_subset_1(A_34, k4_xboole_0(A_34, B_35)))), inference(resolution, [status(thm)], [c_4, c_61])).
% 8.90/2.95  tff(c_99, plain, (![A_36, B_37]: (r1_tarski(k3_subset_1(A_36, k4_xboole_0(A_36, B_37)), A_36))), inference(superposition, [status(thm), theory('equality')], [c_75, c_4])).
% 8.90/2.95  tff(c_108, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_53, c_99])).
% 8.90/2.95  tff(c_18, plain, (![A_18, B_20]: (k3_subset_1(u1_struct_0(A_18), k2_pre_topc(A_18, k3_subset_1(u1_struct_0(A_18), B_20)))=k1_tops_1(A_18, B_20) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.90/2.95  tff(c_201, plain, (![A_48, B_49]: (m1_subset_1(k2_pre_topc(A_48, B_49), k1_zfmisc_1(u1_struct_0(A_48))) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.90/2.95  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k3_subset_1(A_5, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.90/2.95  tff(c_655, plain, (![A_71, B_72]: (k4_xboole_0(u1_struct_0(A_71), k2_pre_topc(A_71, B_72))=k3_subset_1(u1_struct_0(A_71), k2_pre_topc(A_71, B_72)) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(resolution, [status(thm)], [c_201, c_6])).
% 8.90/2.95  tff(c_770, plain, (![A_75, A_76]: (k4_xboole_0(u1_struct_0(A_75), k2_pre_topc(A_75, A_76))=k3_subset_1(u1_struct_0(A_75), k2_pre_topc(A_75, A_76)) | ~l1_pre_topc(A_75) | ~r1_tarski(A_76, u1_struct_0(A_75)))), inference(resolution, [status(thm)], [c_12, c_655])).
% 8.90/2.95  tff(c_824, plain, (![A_77, A_78]: (r1_tarski(k3_subset_1(u1_struct_0(A_77), k2_pre_topc(A_77, A_78)), u1_struct_0(A_77)) | ~l1_pre_topc(A_77) | ~r1_tarski(A_78, u1_struct_0(A_77)))), inference(superposition, [status(thm), theory('equality')], [c_770, c_4])).
% 8.90/2.95  tff(c_1376, plain, (![A_102, B_103]: (r1_tarski(k1_tops_1(A_102, B_103), u1_struct_0(A_102)) | ~l1_pre_topc(A_102) | ~r1_tarski(k3_subset_1(u1_struct_0(A_102), B_103), u1_struct_0(A_102)) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(superposition, [status(thm), theory('equality')], [c_18, c_824])).
% 8.90/2.95  tff(c_1457, plain, (r1_tarski(k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), u1_struct_0('#skF_1')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_108, c_1376])).
% 8.90/2.95  tff(c_1518, plain, (r1_tarski(k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), u1_struct_0('#skF_1')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1457])).
% 8.90/2.95  tff(c_2235, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1518])).
% 8.90/2.95  tff(c_2238, plain, (~r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_2235])).
% 8.90/2.95  tff(c_2242, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57, c_2238])).
% 8.90/2.95  tff(c_2244, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1518])).
% 8.90/2.95  tff(c_14, plain, (![A_13, B_14]: (m1_subset_1(k2_pre_topc(A_13, B_14), k1_zfmisc_1(u1_struct_0(A_13))) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.90/2.95  tff(c_16, plain, (![B_17, A_15]: (r1_tarski(B_17, k2_pre_topc(A_15, B_17)) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.90/2.95  tff(c_2273, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2244, c_16])).
% 8.90/2.95  tff(c_2288, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2273])).
% 8.90/2.95  tff(c_8, plain, (![A_7, C_10, B_8]: (r1_tarski(k3_subset_1(A_7, C_10), B_8) | ~r1_tarski(k3_subset_1(A_7, B_8), C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.90/2.95  tff(c_2303, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), '#skF_2') | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_2288, c_8])).
% 8.90/2.95  tff(c_2309, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), '#skF_2') | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2303])).
% 8.90/2.95  tff(c_7046, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_2309])).
% 8.90/2.95  tff(c_7170, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_7046])).
% 8.90/2.95  tff(c_7177, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_2244, c_7170])).
% 8.90/2.95  tff(c_7179, plain, (m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_2309])).
% 8.90/2.95  tff(c_121, plain, (![B_40, A_41]: (r1_tarski(B_40, k2_pre_topc(A_41, B_40)) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.90/2.95  tff(c_127, plain, (![A_11, A_41]: (r1_tarski(A_11, k2_pre_topc(A_41, A_11)) | ~l1_pre_topc(A_41) | ~r1_tarski(A_11, u1_struct_0(A_41)))), inference(resolution, [status(thm)], [c_12, c_121])).
% 8.90/2.95  tff(c_326, plain, (![A_56, C_57, B_58]: (r1_tarski(k3_subset_1(A_56, C_57), B_58) | ~r1_tarski(k3_subset_1(A_56, B_58), C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(A_56)) | ~m1_subset_1(B_58, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.90/2.95  tff(c_1633, plain, (![A_104, A_105, B_106]: (r1_tarski(k3_subset_1(A_104, k2_pre_topc(A_105, k3_subset_1(A_104, B_106))), B_106) | ~m1_subset_1(k2_pre_topc(A_105, k3_subset_1(A_104, B_106)), k1_zfmisc_1(A_104)) | ~m1_subset_1(B_106, k1_zfmisc_1(A_104)) | ~l1_pre_topc(A_105) | ~r1_tarski(k3_subset_1(A_104, B_106), u1_struct_0(A_105)))), inference(resolution, [status(thm)], [c_127, c_326])).
% 8.90/2.95  tff(c_1651, plain, (![A_18, B_20]: (r1_tarski(k1_tops_1(A_18, B_20), B_20) | ~m1_subset_1(k2_pre_topc(A_18, k3_subset_1(u1_struct_0(A_18), B_20)), k1_zfmisc_1(u1_struct_0(A_18))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18) | ~r1_tarski(k3_subset_1(u1_struct_0(A_18), B_20), u1_struct_0(A_18)) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1633])).
% 8.90/2.95  tff(c_7183, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_7179, c_1651])).
% 8.90/2.95  tff(c_7204, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_57, c_7183])).
% 8.90/2.95  tff(c_7206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_7204])).
% 8.90/2.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.90/2.95  
% 8.90/2.95  Inference rules
% 8.90/2.95  ----------------------
% 8.90/2.95  #Ref     : 0
% 8.90/2.95  #Sup     : 1779
% 8.90/2.95  #Fact    : 0
% 8.90/2.95  #Define  : 0
% 8.90/2.95  #Split   : 10
% 8.90/2.95  #Chain   : 0
% 8.90/2.95  #Close   : 0
% 8.90/2.95  
% 8.90/2.95  Ordering : KBO
% 8.90/2.95  
% 8.90/2.95  Simplification rules
% 8.90/2.95  ----------------------
% 8.90/2.95  #Subsume      : 146
% 8.90/2.95  #Demod        : 1567
% 8.90/2.95  #Tautology    : 287
% 8.90/2.95  #SimpNegUnit  : 1
% 8.90/2.95  #BackRed      : 7
% 8.90/2.95  
% 8.90/2.95  #Partial instantiations: 0
% 8.90/2.95  #Strategies tried      : 1
% 8.90/2.95  
% 8.90/2.95  Timing (in seconds)
% 8.90/2.95  ----------------------
% 8.90/2.95  Preprocessing        : 0.29
% 8.90/2.95  Parsing              : 0.16
% 8.90/2.95  CNF conversion       : 0.02
% 8.90/2.95  Main loop            : 1.89
% 8.90/2.95  Inferencing          : 0.46
% 8.90/2.95  Reduction            : 0.87
% 8.90/2.95  Demodulation         : 0.70
% 8.90/2.95  BG Simplification    : 0.06
% 8.90/2.95  Subsumption          : 0.38
% 8.90/2.95  Abstraction          : 0.10
% 8.90/2.95  MUC search           : 0.00
% 8.90/2.95  Cooper               : 0.00
% 8.90/2.95  Total                : 2.22
% 8.90/2.95  Index Insertion      : 0.00
% 8.90/2.95  Index Deletion       : 0.00
% 8.90/2.95  Index Matching       : 0.00
% 8.90/2.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
