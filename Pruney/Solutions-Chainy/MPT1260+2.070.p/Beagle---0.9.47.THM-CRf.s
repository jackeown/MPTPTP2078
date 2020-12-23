%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:09 EST 2020

% Result     : Theorem 10.84s
% Output     : CNFRefutation 10.84s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 328 expanded)
%              Number of leaves         :   35 ( 124 expanded)
%              Depth                    :   15
%              Number of atoms          :  177 ( 736 expanded)
%              Number of equality atoms :   56 ( 182 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_131,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_119,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_112,axiom,(
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

tff(c_54,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_77,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_48,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_155,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1337,plain,(
    ! [B_128,A_129] :
      ( r1_tarski(B_128,k2_pre_topc(A_129,B_128))
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1345,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1337])).

tff(c_1350,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1345])).

tff(c_1727,plain,(
    ! [A_141,B_142] :
      ( m1_subset_1(k2_pre_topc(A_141,B_142),k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    ! [A_19,B_20,C_21] :
      ( k7_subset_1(A_19,B_20,C_21) = k4_xboole_0(B_20,C_21)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_11096,plain,(
    ! [A_329,B_330,C_331] :
      ( k7_subset_1(u1_struct_0(A_329),k2_pre_topc(A_329,B_330),C_331) = k4_xboole_0(k2_pre_topc(A_329,B_330),C_331)
      | ~ m1_subset_1(B_330,k1_zfmisc_1(u1_struct_0(A_329)))
      | ~ l1_pre_topc(A_329) ) ),
    inference(resolution,[status(thm)],[c_1727,c_22])).

tff(c_11106,plain,(
    ! [C_331] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_331) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_331)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_11096])).

tff(c_11261,plain,(
    ! [C_334] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_334) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_334) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_11106])).

tff(c_11278,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_11261,c_77])).

tff(c_26,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(A_22,k1_zfmisc_1(B_23))
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_109,plain,(
    ! [A_62,B_63] :
      ( k4_xboole_0(A_62,B_63) = k3_subset_1(A_62,B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_116,plain,(
    ! [B_23,A_22] :
      ( k4_xboole_0(B_23,A_22) = k3_subset_1(B_23,A_22)
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(resolution,[status(thm)],[c_26,c_109])).

tff(c_1361,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1350,c_116])).

tff(c_11307,plain,(
    k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11278,c_1361])).

tff(c_543,plain,(
    ! [A_98,B_99] :
      ( k3_subset_1(A_98,k3_subset_1(A_98,B_99)) = B_99
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_551,plain,(
    ! [B_23,A_22] :
      ( k3_subset_1(B_23,k3_subset_1(B_23,A_22)) = A_22
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(resolution,[status(thm)],[c_26,c_543])).

tff(c_11457,plain,
    ( k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11307,c_551])).

tff(c_11468,plain,(
    k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1350,c_11457])).

tff(c_34,plain,(
    ! [A_31,B_33] :
      ( k7_subset_1(u1_struct_0(A_31),k2_pre_topc(A_31,B_33),k1_tops_1(A_31,B_33)) = k2_tops_1(A_31,B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_11293,plain,
    ( k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_11261])).

tff(c_11306,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_11293])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_162,plain,(
    ! [B_70,A_71] :
      ( k4_xboole_0(B_70,A_71) = k3_subset_1(B_70,A_71)
      | ~ r1_tarski(A_71,B_70) ) ),
    inference(resolution,[status(thm)],[c_26,c_109])).

tff(c_186,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_subset_1(A_8,k4_xboole_0(A_8,B_9)) ),
    inference(resolution,[status(thm)],[c_12,c_162])).

tff(c_11764,plain,(
    k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2'))) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11306,c_186])).

tff(c_11802,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11468,c_11306,c_11764])).

tff(c_818,plain,(
    ! [A_108,B_109,C_110] :
      ( k7_subset_1(A_108,B_109,C_110) = k4_xboole_0(B_109,C_110)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(A_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_827,plain,(
    ! [C_110] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_110) = k4_xboole_0('#skF_2',C_110) ),
    inference(resolution,[status(thm)],[c_42,c_818])).

tff(c_2163,plain,(
    ! [A_155,B_156] :
      ( k7_subset_1(u1_struct_0(A_155),B_156,k2_tops_1(A_155,B_156)) = k1_tops_1(A_155,B_156)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ l1_pre_topc(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2173,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_2163])).

tff(c_2179,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_827,c_2173])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_826,plain,(
    ! [B_23,A_22,C_110] :
      ( k7_subset_1(B_23,A_22,C_110) = k4_xboole_0(A_22,C_110)
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(resolution,[status(thm)],[c_26,c_818])).

tff(c_1360,plain,(
    ! [C_110] : k7_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2',C_110) = k4_xboole_0('#skF_2',C_110) ),
    inference(resolution,[status(thm)],[c_1350,c_826])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] : k4_xboole_0(k4_xboole_0(A_10,B_11),C_12) = k4_xboole_0(A_10,k2_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1098,plain,(
    ! [B_119,A_120,C_121] :
      ( k7_subset_1(B_119,A_120,C_121) = k4_xboole_0(A_120,C_121)
      | ~ r1_tarski(A_120,B_119) ) ),
    inference(resolution,[status(thm)],[c_26,c_818])).

tff(c_1136,plain,(
    ! [A_8,B_9,C_121] : k7_subset_1(A_8,k4_xboole_0(A_8,B_9),C_121) = k4_xboole_0(k4_xboole_0(A_8,B_9),C_121) ),
    inference(resolution,[status(thm)],[c_12,c_1098])).

tff(c_1166,plain,(
    ! [A_8,B_9,C_121] : k7_subset_1(A_8,k4_xboole_0(A_8,B_9),C_121) = k4_xboole_0(A_8,k2_xboole_0(B_9,C_121)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1136])).

tff(c_11842,plain,(
    ! [C_121] : k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),C_121)) = k7_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2',C_121) ),
    inference(superposition,[status(thm),theory(equality)],[c_11802,c_1166])).

tff(c_15881,plain,(
    ! [C_401] : k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),C_401)) = k4_xboole_0('#skF_2',C_401) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1360,c_11842])).

tff(c_15997,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_15881])).

tff(c_16021,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11802,c_2179,c_15997])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1470,plain,(
    ! [A_132,B_133] :
      ( v3_pre_topc(k1_tops_1(A_132,B_133),A_132)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1478,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1470])).

tff(c_1483,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1478])).

tff(c_16071,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16021,c_1483])).

tff(c_16113,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_16071])).

tff(c_16114,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_16458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_16114])).

tff(c_16459,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_16524,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16459,c_48])).

tff(c_17085,plain,(
    ! [A_489,B_490] :
      ( r1_tarski(k1_tops_1(A_489,B_490),B_490)
      | ~ m1_subset_1(B_490,k1_zfmisc_1(u1_struct_0(A_489)))
      | ~ l1_pre_topc(A_489) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_17093,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_17085])).

tff(c_17098,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_17093])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_17108,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_17098,c_4])).

tff(c_17211,plain,(
    ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_17108])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18474,plain,(
    ! [B_534,A_535,C_536] :
      ( r1_tarski(B_534,k1_tops_1(A_535,C_536))
      | ~ r1_tarski(B_534,C_536)
      | ~ v3_pre_topc(B_534,A_535)
      | ~ m1_subset_1(C_536,k1_zfmisc_1(u1_struct_0(A_535)))
      | ~ m1_subset_1(B_534,k1_zfmisc_1(u1_struct_0(A_535)))
      | ~ l1_pre_topc(A_535) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_18484,plain,(
    ! [B_534] :
      ( r1_tarski(B_534,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_534,'#skF_2')
      | ~ v3_pre_topc(B_534,'#skF_1')
      | ~ m1_subset_1(B_534,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_18474])).

tff(c_18647,plain,(
    ! [B_540] :
      ( r1_tarski(B_540,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_540,'#skF_2')
      | ~ v3_pre_topc(B_540,'#skF_1')
      | ~ m1_subset_1(B_540,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_18484])).

tff(c_18662,plain,
    ( r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_18647])).

tff(c_18670,plain,(
    r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16459,c_8,c_18662])).

tff(c_18672,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17211,c_18670])).

tff(c_18673,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_17108])).

tff(c_19584,plain,(
    ! [A_573,B_574] :
      ( k7_subset_1(u1_struct_0(A_573),k2_pre_topc(A_573,B_574),k1_tops_1(A_573,B_574)) = k2_tops_1(A_573,B_574)
      | ~ m1_subset_1(B_574,k1_zfmisc_1(u1_struct_0(A_573)))
      | ~ l1_pre_topc(A_573) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_19593,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_18673,c_19584])).

tff(c_19597,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_19593])).

tff(c_19599,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16524,c_19597])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:40:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.84/4.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.84/4.39  
% 10.84/4.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.84/4.39  %$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 10.84/4.39  
% 10.84/4.39  %Foreground sorts:
% 10.84/4.39  
% 10.84/4.39  
% 10.84/4.39  %Background operators:
% 10.84/4.39  
% 10.84/4.39  
% 10.84/4.39  %Foreground operators:
% 10.84/4.39  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 10.84/4.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.84/4.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.84/4.39  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 10.84/4.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.84/4.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.84/4.39  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.84/4.39  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 10.84/4.39  tff('#skF_2', type, '#skF_2': $i).
% 10.84/4.39  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 10.84/4.39  tff('#skF_1', type, '#skF_1': $i).
% 10.84/4.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.84/4.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.84/4.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.84/4.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.84/4.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.84/4.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.84/4.39  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 10.84/4.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.84/4.39  
% 10.84/4.41  tff(f_131, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 10.84/4.41  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 10.84/4.41  tff(f_69, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 10.84/4.41  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 10.84/4.41  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.84/4.41  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 10.84/4.41  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 10.84/4.41  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 10.84/4.41  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 10.84/4.41  tff(f_119, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 10.84/4.41  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 10.84/4.41  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 10.84/4.41  tff(f_84, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 10.84/4.41  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 10.84/4.41  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.84/4.41  tff(f_112, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 10.84/4.41  tff(c_54, plain, (v3_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 10.84/4.41  tff(c_77, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_54])).
% 10.84/4.41  tff(c_48, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 10.84/4.41  tff(c_155, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_48])).
% 10.84/4.41  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 10.84/4.41  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 10.84/4.41  tff(c_1337, plain, (![B_128, A_129]: (r1_tarski(B_128, k2_pre_topc(A_129, B_128)) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.84/4.41  tff(c_1345, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1337])).
% 10.84/4.41  tff(c_1350, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1345])).
% 10.84/4.41  tff(c_1727, plain, (![A_141, B_142]: (m1_subset_1(k2_pre_topc(A_141, B_142), k1_zfmisc_1(u1_struct_0(A_141))) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.84/4.41  tff(c_22, plain, (![A_19, B_20, C_21]: (k7_subset_1(A_19, B_20, C_21)=k4_xboole_0(B_20, C_21) | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.84/4.41  tff(c_11096, plain, (![A_329, B_330, C_331]: (k7_subset_1(u1_struct_0(A_329), k2_pre_topc(A_329, B_330), C_331)=k4_xboole_0(k2_pre_topc(A_329, B_330), C_331) | ~m1_subset_1(B_330, k1_zfmisc_1(u1_struct_0(A_329))) | ~l1_pre_topc(A_329))), inference(resolution, [status(thm)], [c_1727, c_22])).
% 10.84/4.41  tff(c_11106, plain, (![C_331]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_331)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_331) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_11096])).
% 10.84/4.41  tff(c_11261, plain, (![C_334]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_334)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_334))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_11106])).
% 10.84/4.41  tff(c_11278, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_11261, c_77])).
% 10.84/4.41  tff(c_26, plain, (![A_22, B_23]: (m1_subset_1(A_22, k1_zfmisc_1(B_23)) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.84/4.41  tff(c_109, plain, (![A_62, B_63]: (k4_xboole_0(A_62, B_63)=k3_subset_1(A_62, B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.84/4.41  tff(c_116, plain, (![B_23, A_22]: (k4_xboole_0(B_23, A_22)=k3_subset_1(B_23, A_22) | ~r1_tarski(A_22, B_23))), inference(resolution, [status(thm)], [c_26, c_109])).
% 10.84/4.41  tff(c_1361, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_1350, c_116])).
% 10.84/4.41  tff(c_11307, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_11278, c_1361])).
% 10.84/4.41  tff(c_543, plain, (![A_98, B_99]: (k3_subset_1(A_98, k3_subset_1(A_98, B_99))=B_99 | ~m1_subset_1(B_99, k1_zfmisc_1(A_98)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.84/4.41  tff(c_551, plain, (![B_23, A_22]: (k3_subset_1(B_23, k3_subset_1(B_23, A_22))=A_22 | ~r1_tarski(A_22, B_23))), inference(resolution, [status(thm)], [c_26, c_543])).
% 10.84/4.41  tff(c_11457, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_11307, c_551])).
% 10.84/4.41  tff(c_11468, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1350, c_11457])).
% 10.84/4.41  tff(c_34, plain, (![A_31, B_33]: (k7_subset_1(u1_struct_0(A_31), k2_pre_topc(A_31, B_33), k1_tops_1(A_31, B_33))=k2_tops_1(A_31, B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.84/4.41  tff(c_11293, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_34, c_11261])).
% 10.84/4.41  tff(c_11306, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_11293])).
% 10.84/4.41  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.84/4.41  tff(c_162, plain, (![B_70, A_71]: (k4_xboole_0(B_70, A_71)=k3_subset_1(B_70, A_71) | ~r1_tarski(A_71, B_70))), inference(resolution, [status(thm)], [c_26, c_109])).
% 10.84/4.41  tff(c_186, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_subset_1(A_8, k4_xboole_0(A_8, B_9)))), inference(resolution, [status(thm)], [c_12, c_162])).
% 10.84/4.41  tff(c_11764, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2')))=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_11306, c_186])).
% 10.84/4.41  tff(c_11802, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_11468, c_11306, c_11764])).
% 10.84/4.41  tff(c_818, plain, (![A_108, B_109, C_110]: (k7_subset_1(A_108, B_109, C_110)=k4_xboole_0(B_109, C_110) | ~m1_subset_1(B_109, k1_zfmisc_1(A_108)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.84/4.41  tff(c_827, plain, (![C_110]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_110)=k4_xboole_0('#skF_2', C_110))), inference(resolution, [status(thm)], [c_42, c_818])).
% 10.84/4.41  tff(c_2163, plain, (![A_155, B_156]: (k7_subset_1(u1_struct_0(A_155), B_156, k2_tops_1(A_155, B_156))=k1_tops_1(A_155, B_156) | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0(A_155))) | ~l1_pre_topc(A_155))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.84/4.41  tff(c_2173, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_2163])).
% 10.84/4.41  tff(c_2179, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_827, c_2173])).
% 10.84/4.41  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.84/4.41  tff(c_826, plain, (![B_23, A_22, C_110]: (k7_subset_1(B_23, A_22, C_110)=k4_xboole_0(A_22, C_110) | ~r1_tarski(A_22, B_23))), inference(resolution, [status(thm)], [c_26, c_818])).
% 10.84/4.41  tff(c_1360, plain, (![C_110]: (k7_subset_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2', C_110)=k4_xboole_0('#skF_2', C_110))), inference(resolution, [status(thm)], [c_1350, c_826])).
% 10.84/4.41  tff(c_14, plain, (![A_10, B_11, C_12]: (k4_xboole_0(k4_xboole_0(A_10, B_11), C_12)=k4_xboole_0(A_10, k2_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.84/4.41  tff(c_1098, plain, (![B_119, A_120, C_121]: (k7_subset_1(B_119, A_120, C_121)=k4_xboole_0(A_120, C_121) | ~r1_tarski(A_120, B_119))), inference(resolution, [status(thm)], [c_26, c_818])).
% 10.84/4.41  tff(c_1136, plain, (![A_8, B_9, C_121]: (k7_subset_1(A_8, k4_xboole_0(A_8, B_9), C_121)=k4_xboole_0(k4_xboole_0(A_8, B_9), C_121))), inference(resolution, [status(thm)], [c_12, c_1098])).
% 10.84/4.41  tff(c_1166, plain, (![A_8, B_9, C_121]: (k7_subset_1(A_8, k4_xboole_0(A_8, B_9), C_121)=k4_xboole_0(A_8, k2_xboole_0(B_9, C_121)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1136])).
% 10.84/4.41  tff(c_11842, plain, (![C_121]: (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), C_121))=k7_subset_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2', C_121))), inference(superposition, [status(thm), theory('equality')], [c_11802, c_1166])).
% 10.84/4.41  tff(c_15881, plain, (![C_401]: (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), C_401))=k4_xboole_0('#skF_2', C_401))), inference(demodulation, [status(thm), theory('equality')], [c_1360, c_11842])).
% 10.84/4.41  tff(c_15997, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_15881])).
% 10.84/4.41  tff(c_16021, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_11802, c_2179, c_15997])).
% 10.84/4.41  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 10.84/4.41  tff(c_1470, plain, (![A_132, B_133]: (v3_pre_topc(k1_tops_1(A_132, B_133), A_132) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.84/4.41  tff(c_1478, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1470])).
% 10.84/4.41  tff(c_1483, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1478])).
% 10.84/4.41  tff(c_16071, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16021, c_1483])).
% 10.84/4.41  tff(c_16113, plain, $false, inference(negUnitSimplification, [status(thm)], [c_155, c_16071])).
% 10.84/4.41  tff(c_16114, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 10.84/4.41  tff(c_16458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_16114])).
% 10.84/4.41  tff(c_16459, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_54])).
% 10.84/4.41  tff(c_16524, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16459, c_48])).
% 10.84/4.41  tff(c_17085, plain, (![A_489, B_490]: (r1_tarski(k1_tops_1(A_489, B_490), B_490) | ~m1_subset_1(B_490, k1_zfmisc_1(u1_struct_0(A_489))) | ~l1_pre_topc(A_489))), inference(cnfTransformation, [status(thm)], [f_98])).
% 10.84/4.41  tff(c_17093, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_17085])).
% 10.84/4.41  tff(c_17098, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_17093])).
% 10.84/4.41  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.84/4.41  tff(c_17108, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_17098, c_4])).
% 10.84/4.41  tff(c_17211, plain, (~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_17108])).
% 10.84/4.41  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.84/4.41  tff(c_18474, plain, (![B_534, A_535, C_536]: (r1_tarski(B_534, k1_tops_1(A_535, C_536)) | ~r1_tarski(B_534, C_536) | ~v3_pre_topc(B_534, A_535) | ~m1_subset_1(C_536, k1_zfmisc_1(u1_struct_0(A_535))) | ~m1_subset_1(B_534, k1_zfmisc_1(u1_struct_0(A_535))) | ~l1_pre_topc(A_535))), inference(cnfTransformation, [status(thm)], [f_112])).
% 10.84/4.41  tff(c_18484, plain, (![B_534]: (r1_tarski(B_534, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_534, '#skF_2') | ~v3_pre_topc(B_534, '#skF_1') | ~m1_subset_1(B_534, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_18474])).
% 10.84/4.41  tff(c_18647, plain, (![B_540]: (r1_tarski(B_540, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_540, '#skF_2') | ~v3_pre_topc(B_540, '#skF_1') | ~m1_subset_1(B_540, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_18484])).
% 10.84/4.41  tff(c_18662, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_18647])).
% 10.84/4.41  tff(c_18670, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16459, c_8, c_18662])).
% 10.84/4.41  tff(c_18672, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17211, c_18670])).
% 10.84/4.41  tff(c_18673, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_17108])).
% 10.84/4.41  tff(c_19584, plain, (![A_573, B_574]: (k7_subset_1(u1_struct_0(A_573), k2_pre_topc(A_573, B_574), k1_tops_1(A_573, B_574))=k2_tops_1(A_573, B_574) | ~m1_subset_1(B_574, k1_zfmisc_1(u1_struct_0(A_573))) | ~l1_pre_topc(A_573))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.84/4.41  tff(c_19593, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_18673, c_19584])).
% 10.84/4.41  tff(c_19597, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_19593])).
% 10.84/4.41  tff(c_19599, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16524, c_19597])).
% 10.84/4.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.84/4.41  
% 10.84/4.41  Inference rules
% 10.84/4.41  ----------------------
% 10.84/4.41  #Ref     : 0
% 10.84/4.41  #Sup     : 4601
% 10.84/4.41  #Fact    : 0
% 10.84/4.41  #Define  : 0
% 10.84/4.41  #Split   : 13
% 10.84/4.41  #Chain   : 0
% 10.84/4.41  #Close   : 0
% 10.84/4.41  
% 10.84/4.41  Ordering : KBO
% 10.84/4.41  
% 10.84/4.41  Simplification rules
% 10.84/4.41  ----------------------
% 10.84/4.41  #Subsume      : 607
% 10.84/4.41  #Demod        : 2465
% 10.84/4.41  #Tautology    : 1067
% 10.84/4.41  #SimpNegUnit  : 4
% 10.84/4.41  #BackRed      : 75
% 10.84/4.41  
% 10.84/4.41  #Partial instantiations: 0
% 10.84/4.41  #Strategies tried      : 1
% 10.84/4.41  
% 10.84/4.41  Timing (in seconds)
% 10.84/4.41  ----------------------
% 10.84/4.42  Preprocessing        : 0.33
% 10.84/4.42  Parsing              : 0.18
% 10.84/4.42  CNF conversion       : 0.02
% 10.84/4.42  Main loop            : 3.32
% 10.84/4.42  Inferencing          : 0.69
% 10.84/4.42  Reduction            : 1.48
% 10.84/4.42  Demodulation         : 1.22
% 10.84/4.42  BG Simplification    : 0.09
% 10.84/4.42  Subsumption          : 0.83
% 10.84/4.42  Abstraction          : 0.13
% 10.84/4.42  MUC search           : 0.00
% 10.84/4.42  Cooper               : 0.00
% 10.84/4.42  Total                : 3.69
% 10.84/4.42  Index Insertion      : 0.00
% 10.84/4.42  Index Deletion       : 0.00
% 10.84/4.42  Index Matching       : 0.00
% 10.84/4.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
