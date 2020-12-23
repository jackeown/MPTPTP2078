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
% DateTime   : Thu Dec  3 10:20:55 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 184 expanded)
%              Number of leaves         :   31 (  80 expanded)
%              Depth                    :   11
%              Number of atoms          :   97 ( 413 expanded)
%              Number of equality atoms :   12 (  57 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_80,axiom,(
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

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_30,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_66,plain,(
    ! [A_41,B_42] :
      ( k4_xboole_0(A_41,B_42) = k3_subset_1(A_41,B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_74,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),'#skF_2') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_66])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_78,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_4])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_22,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(k2_pre_topc(A_22,B_23),k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_32,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_186,plain,(
    ! [A_61,B_62] :
      ( k2_pre_topc(A_61,B_62) = B_62
      | ~ v4_pre_topc(B_62,A_61)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_197,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_186])).

tff(c_202,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_197])).

tff(c_949,plain,(
    ! [A_118,B_119] :
      ( k9_subset_1(u1_struct_0(A_118),k2_pre_topc(A_118,B_119),k2_pre_topc(A_118,k3_subset_1(u1_struct_0(A_118),B_119))) = k2_tops_1(A_118,B_119)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_982,plain,
    ( k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_949])).

tff(c_986,plain,(
    k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_982])).

tff(c_120,plain,(
    ! [A_47,B_48,C_49] :
      ( m1_subset_1(k9_subset_1(A_47,B_48,C_49),k1_zfmisc_1(A_47))
      | ~ m1_subset_1(C_49,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ m1_subset_1(A_20,k1_zfmisc_1(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_128,plain,(
    ! [A_47,B_48,C_49] :
      ( r1_tarski(k9_subset_1(A_47,B_48,C_49),A_47)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(A_47)) ) ),
    inference(resolution,[status(thm)],[c_120,c_18])).

tff(c_1008,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_986,c_128])).

tff(c_1036,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1008])).

tff(c_1056,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_1036])).

tff(c_1062,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1056])).

tff(c_1066,plain,(
    ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_20,c_1062])).

tff(c_1070,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1066])).

tff(c_1072,plain,(
    m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1008])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] :
      ( m1_subset_1(k9_subset_1(A_7,B_8,C_9),k1_zfmisc_1(A_7))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1011,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_986,c_8])).

tff(c_1247,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1072,c_1011])).

tff(c_739,plain,(
    ! [A_104,B_105,C_106] :
      ( r1_tarski(k3_subset_1(A_104,B_105),k3_subset_1(A_104,k9_subset_1(A_104,B_105,C_106)))
      | ~ m1_subset_1(C_106,k1_zfmisc_1(A_104))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(A_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    ! [B_11,C_13,A_10] :
      ( r1_tarski(B_11,C_13)
      | ~ r1_tarski(k3_subset_1(A_10,C_13),k3_subset_1(A_10,B_11))
      | ~ m1_subset_1(C_13,k1_zfmisc_1(A_10))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1333,plain,(
    ! [A_126,B_127,C_128] :
      ( r1_tarski(k9_subset_1(A_126,B_127,C_128),B_127)
      | ~ m1_subset_1(k9_subset_1(A_126,B_127,C_128),k1_zfmisc_1(A_126))
      | ~ m1_subset_1(C_128,k1_zfmisc_1(A_126))
      | ~ m1_subset_1(B_127,k1_zfmisc_1(A_126)) ) ),
    inference(resolution,[status(thm)],[c_739,c_10])).

tff(c_1335,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),'#skF_2')
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_986,c_1333])).

tff(c_1344,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1072,c_1247,c_986,c_1335])).

tff(c_1346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1344])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:39:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.42/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.56  
% 3.42/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.56  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 3.42/1.56  
% 3.42/1.56  %Foreground sorts:
% 3.42/1.56  
% 3.42/1.56  
% 3.42/1.56  %Background operators:
% 3.42/1.56  
% 3.42/1.56  
% 3.42/1.56  %Foreground operators:
% 3.42/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.42/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.42/1.56  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.42/1.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.42/1.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.42/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.42/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.42/1.56  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.42/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.42/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.42/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.42/1.56  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.42/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.42/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.42/1.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.42/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.42/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.42/1.56  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.42/1.56  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.42/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.42/1.56  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.42/1.56  
% 3.56/1.58  tff(f_97, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 3.56/1.58  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.56/1.58  tff(f_29, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.56/1.58  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.56/1.58  tff(f_65, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 3.56/1.58  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.56/1.58  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_1)).
% 3.56/1.58  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 3.56/1.58  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_subset_1)).
% 3.56/1.58  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 3.56/1.58  tff(c_30, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.56/1.58  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.56/1.58  tff(c_66, plain, (![A_41, B_42]: (k4_xboole_0(A_41, B_42)=k3_subset_1(A_41, B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.56/1.58  tff(c_74, plain, (k4_xboole_0(u1_struct_0('#skF_1'), '#skF_2')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_34, c_66])).
% 3.56/1.58  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.56/1.58  tff(c_78, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_4])).
% 3.56/1.58  tff(c_20, plain, (![A_20, B_21]: (m1_subset_1(A_20, k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.56/1.58  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.56/1.58  tff(c_22, plain, (![A_22, B_23]: (m1_subset_1(k2_pre_topc(A_22, B_23), k1_zfmisc_1(u1_struct_0(A_22))) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.56/1.58  tff(c_32, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.56/1.58  tff(c_186, plain, (![A_61, B_62]: (k2_pre_topc(A_61, B_62)=B_62 | ~v4_pre_topc(B_62, A_61) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.56/1.58  tff(c_197, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_186])).
% 3.56/1.58  tff(c_202, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_197])).
% 3.56/1.58  tff(c_949, plain, (![A_118, B_119]: (k9_subset_1(u1_struct_0(A_118), k2_pre_topc(A_118, B_119), k2_pre_topc(A_118, k3_subset_1(u1_struct_0(A_118), B_119)))=k2_tops_1(A_118, B_119) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.56/1.58  tff(c_982, plain, (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_202, c_949])).
% 3.56/1.58  tff(c_986, plain, (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_982])).
% 3.56/1.58  tff(c_120, plain, (![A_47, B_48, C_49]: (m1_subset_1(k9_subset_1(A_47, B_48, C_49), k1_zfmisc_1(A_47)) | ~m1_subset_1(C_49, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.56/1.58  tff(c_18, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~m1_subset_1(A_20, k1_zfmisc_1(B_21)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.56/1.58  tff(c_128, plain, (![A_47, B_48, C_49]: (r1_tarski(k9_subset_1(A_47, B_48, C_49), A_47) | ~m1_subset_1(C_49, k1_zfmisc_1(A_47)))), inference(resolution, [status(thm)], [c_120, c_18])).
% 3.56/1.58  tff(c_1008, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_986, c_128])).
% 3.56/1.58  tff(c_1036, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1008])).
% 3.56/1.58  tff(c_1056, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_1036])).
% 3.56/1.58  tff(c_1062, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1056])).
% 3.56/1.58  tff(c_1066, plain, (~r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_1062])).
% 3.56/1.58  tff(c_1070, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_1066])).
% 3.56/1.58  tff(c_1072, plain, (m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1008])).
% 3.56/1.58  tff(c_8, plain, (![A_7, B_8, C_9]: (m1_subset_1(k9_subset_1(A_7, B_8, C_9), k1_zfmisc_1(A_7)) | ~m1_subset_1(C_9, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.56/1.58  tff(c_1011, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_986, c_8])).
% 3.56/1.58  tff(c_1247, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1072, c_1011])).
% 3.56/1.58  tff(c_739, plain, (![A_104, B_105, C_106]: (r1_tarski(k3_subset_1(A_104, B_105), k3_subset_1(A_104, k9_subset_1(A_104, B_105, C_106))) | ~m1_subset_1(C_106, k1_zfmisc_1(A_104)) | ~m1_subset_1(B_105, k1_zfmisc_1(A_104)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.56/1.58  tff(c_10, plain, (![B_11, C_13, A_10]: (r1_tarski(B_11, C_13) | ~r1_tarski(k3_subset_1(A_10, C_13), k3_subset_1(A_10, B_11)) | ~m1_subset_1(C_13, k1_zfmisc_1(A_10)) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.56/1.58  tff(c_1333, plain, (![A_126, B_127, C_128]: (r1_tarski(k9_subset_1(A_126, B_127, C_128), B_127) | ~m1_subset_1(k9_subset_1(A_126, B_127, C_128), k1_zfmisc_1(A_126)) | ~m1_subset_1(C_128, k1_zfmisc_1(A_126)) | ~m1_subset_1(B_127, k1_zfmisc_1(A_126)))), inference(resolution, [status(thm)], [c_739, c_10])).
% 3.56/1.58  tff(c_1335, plain, (r1_tarski(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), '#skF_2') | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_986, c_1333])).
% 3.56/1.58  tff(c_1344, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1072, c_1247, c_986, c_1335])).
% 3.56/1.58  tff(c_1346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_1344])).
% 3.56/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.58  
% 3.56/1.58  Inference rules
% 3.56/1.58  ----------------------
% 3.56/1.58  #Ref     : 0
% 3.56/1.58  #Sup     : 306
% 3.56/1.58  #Fact    : 0
% 3.56/1.58  #Define  : 0
% 3.56/1.58  #Split   : 4
% 3.56/1.58  #Chain   : 0
% 3.56/1.58  #Close   : 0
% 3.56/1.58  
% 3.56/1.58  Ordering : KBO
% 3.56/1.58  
% 3.56/1.58  Simplification rules
% 3.56/1.58  ----------------------
% 3.56/1.58  #Subsume      : 13
% 3.56/1.58  #Demod        : 153
% 3.56/1.58  #Tautology    : 65
% 3.56/1.58  #SimpNegUnit  : 3
% 3.56/1.58  #BackRed      : 0
% 3.56/1.58  
% 3.56/1.58  #Partial instantiations: 0
% 3.56/1.58  #Strategies tried      : 1
% 3.56/1.58  
% 3.56/1.58  Timing (in seconds)
% 3.56/1.58  ----------------------
% 3.56/1.58  Preprocessing        : 0.32
% 3.56/1.58  Parsing              : 0.17
% 3.56/1.58  CNF conversion       : 0.02
% 3.56/1.58  Main loop            : 0.48
% 3.56/1.58  Inferencing          : 0.17
% 3.56/1.58  Reduction            : 0.17
% 3.56/1.58  Demodulation         : 0.12
% 3.56/1.58  BG Simplification    : 0.03
% 3.56/1.58  Subsumption          : 0.08
% 3.56/1.58  Abstraction          : 0.04
% 3.56/1.58  MUC search           : 0.00
% 3.56/1.58  Cooper               : 0.00
% 3.56/1.58  Total                : 0.83
% 3.56/1.58  Index Insertion      : 0.00
% 3.56/1.58  Index Deletion       : 0.00
% 3.56/1.58  Index Matching       : 0.00
% 3.56/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
