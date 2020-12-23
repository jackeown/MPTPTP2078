%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:08 EST 2020

% Result     : Theorem 8.59s
% Output     : CNFRefutation 8.73s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 526 expanded)
%              Number of leaves         :   41 ( 191 expanded)
%              Depth                    :   22
%              Number of atoms          :  256 (1185 expanded)
%              Number of equality atoms :   44 ( 299 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v3_pre_topc > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_154,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v3_pre_topc(B,A)
                & v3_tops_1(B,A) )
             => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_tops_1)).

tff(f_59,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_41,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(k3_subset_1(A,B),B)
      <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_131,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_140,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_tops_1)).

tff(f_122,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_91,axiom,(
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

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_113,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_tops_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_102,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_24,plain,(
    ! [A_17] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k3_subset_1(A_11,B_12),k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_80,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_91,plain,(
    ! [A_17] : r1_tarski(k1_xboole_0,A_17) ),
    inference(resolution,[status(thm)],[c_24,c_80])).

tff(c_433,plain,(
    ! [A_100,B_101] :
      ( k3_subset_1(A_100,k3_subset_1(A_100,B_101)) = B_101
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_447,plain,(
    ! [A_17] : k3_subset_1(A_17,k3_subset_1(A_17,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_433])).

tff(c_12,plain,(
    ! [A_9] : k2_subset_1(A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( k2_subset_1(A_15) = B_16
      | ~ r1_tarski(k3_subset_1(A_15,B_16),B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_659,plain,(
    ! [B_119,A_120] :
      ( B_119 = A_120
      | ~ r1_tarski(k3_subset_1(A_120,B_119),B_119)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(A_120)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_22])).

tff(c_671,plain,(
    ! [A_17] :
      ( k3_subset_1(A_17,k1_xboole_0) = A_17
      | ~ r1_tarski(k1_xboole_0,k3_subset_1(A_17,k1_xboole_0))
      | ~ m1_subset_1(k3_subset_1(A_17,k1_xboole_0),k1_zfmisc_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_447,c_659])).

tff(c_16535,plain,(
    ! [A_585] :
      ( k3_subset_1(A_585,k1_xboole_0) = A_585
      | ~ m1_subset_1(k3_subset_1(A_585,k1_xboole_0),k1_zfmisc_1(A_585)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_671])).

tff(c_16545,plain,(
    ! [A_11] :
      ( k3_subset_1(A_11,k1_xboole_0) = A_11
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ) ),
    inference(resolution,[status(thm)],[c_16,c_16535])).

tff(c_16556,plain,(
    ! [A_11] : k3_subset_1(A_11,k1_xboole_0) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_16545])).

tff(c_16743,plain,(
    ! [A_587] : k3_subset_1(A_587,A_587) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16556,c_447])).

tff(c_60,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_446,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_58,c_433])).

tff(c_665,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),'#skF_3') = u1_struct_0('#skF_2')
    | ~ r1_tarski('#skF_3',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_446,c_659])).

tff(c_890,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_665])).

tff(c_905,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_16,c_890])).

tff(c_912,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_905])).

tff(c_914,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_665])).

tff(c_56,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1823,plain,(
    ! [B_167,A_168] :
      ( v4_pre_topc(B_167,A_168)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_168),B_167),A_168)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ l1_pre_topc(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1833,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_446,c_1823])).

tff(c_1844,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_914,c_56,c_1833])).

tff(c_54,plain,(
    v3_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_50,plain,(
    ! [A_41,B_43] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_41),B_43),A_41)
      | ~ v3_tops_1(B_43,A_41)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1431,plain,(
    ! [A_145,B_146] :
      ( k2_pre_topc(A_145,B_146) = k2_struct_0(A_145)
      | ~ v1_tops_1(B_146,A_145)
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1434,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k2_struct_0('#skF_2')
    | ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_914,c_1431])).

tff(c_1460,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k2_struct_0('#skF_2')
    | ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1434])).

tff(c_4466,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1460])).

tff(c_4469,plain,
    ( ~ v3_tops_1('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_4466])).

tff(c_4473,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_4469])).

tff(c_4474,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1460])).

tff(c_26,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_981,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_914,c_26])).

tff(c_28,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1077,plain,(
    ! [A_133,B_134] :
      ( k2_pre_topc(A_133,B_134) = B_134
      | ~ v4_pre_topc(B_134,A_133)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4494,plain,(
    ! [A_278,A_279] :
      ( k2_pre_topc(A_278,A_279) = A_279
      | ~ v4_pre_topc(A_279,A_278)
      | ~ l1_pre_topc(A_278)
      | ~ r1_tarski(A_279,u1_struct_0(A_278)) ) ),
    inference(resolution,[status(thm)],[c_28,c_1077])).

tff(c_4526,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_981,c_4494])).

tff(c_4569,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1844,c_4474,c_4526])).

tff(c_913,plain,
    ( ~ r1_tarski('#skF_3',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'))
    | k3_subset_1(u1_struct_0('#skF_2'),'#skF_3') = u1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_665])).

tff(c_1116,plain,(
    ~ r1_tarski('#skF_3',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_913])).

tff(c_4589,plain,(
    ~ r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4569,c_1116])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_62,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_10,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(B_7,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_991,plain,(
    ! [A_6] :
      ( r1_tarski(A_6,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_6,k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_981,c_10])).

tff(c_5060,plain,(
    ! [A_286] :
      ( r1_tarski(A_286,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_286,k2_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4569,c_991])).

tff(c_1199,plain,(
    ! [B_136,A_137] :
      ( v3_tops_1(B_136,A_137)
      | ~ v1_xboole_0(B_136)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1231,plain,(
    ! [A_18,A_137] :
      ( v3_tops_1(A_18,A_137)
      | ~ v1_xboole_0(A_18)
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137)
      | ~ r1_tarski(A_18,u1_struct_0(A_137)) ) ),
    inference(resolution,[status(thm)],[c_28,c_1199])).

tff(c_5066,plain,(
    ! [A_286] :
      ( v3_tops_1(A_286,'#skF_2')
      | ~ v1_xboole_0(A_286)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ r1_tarski(A_286,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_5060,c_1231])).

tff(c_5397,plain,(
    ! [A_295] :
      ( v3_tops_1(A_295,'#skF_2')
      | ~ v1_xboole_0(A_295)
      | ~ r1_tarski(A_295,k2_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_5066])).

tff(c_5437,plain,
    ( v3_tops_1(k1_xboole_0,'#skF_2')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_91,c_5397])).

tff(c_5450,plain,(
    v3_tops_1(k1_xboole_0,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_5437])).

tff(c_2689,plain,(
    ! [A_193] :
      ( k3_subset_1(A_193,k1_xboole_0) = A_193
      | ~ m1_subset_1(k3_subset_1(A_193,k1_xboole_0),k1_zfmisc_1(A_193)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_671])).

tff(c_2699,plain,(
    ! [A_11] :
      ( k3_subset_1(A_11,k1_xboole_0) = A_11
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ) ),
    inference(resolution,[status(thm)],[c_16,c_2689])).

tff(c_2710,plain,(
    ! [A_11] : k3_subset_1(A_11,k1_xboole_0) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2699])).

tff(c_2716,plain,(
    ! [A_17] : k3_subset_1(A_17,A_17) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2710,c_447])).

tff(c_14,plain,(
    ! [A_10] : m1_subset_1(k2_subset_1(A_10),k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_65,plain,(
    ! [A_10] : m1_subset_1(A_10,k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_108,plain,(
    ! [C_59,B_60,A_61] :
      ( ~ v1_xboole_0(C_59)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(C_59))
      | ~ r2_hidden(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_130,plain,(
    ! [A_63,A_64] :
      ( ~ v1_xboole_0(A_63)
      | ~ r2_hidden(A_64,A_63) ) ),
    inference(resolution,[status(thm)],[c_65,c_108])).

tff(c_134,plain,(
    ! [A_1,B_2] :
      ( ~ v1_xboole_0(A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_130])).

tff(c_921,plain,(
    ! [B_126,A_127] :
      ( v3_pre_topc(B_126,A_127)
      | ~ v1_xboole_0(B_126)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127)
      | ~ v2_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_947,plain,(
    ! [A_18,A_127] :
      ( v3_pre_topc(A_18,A_127)
      | ~ v1_xboole_0(A_18)
      | ~ l1_pre_topc(A_127)
      | ~ v2_pre_topc(A_127)
      | ~ r1_tarski(A_18,u1_struct_0(A_127)) ) ),
    inference(resolution,[status(thm)],[c_28,c_921])).

tff(c_5063,plain,(
    ! [A_286] :
      ( v3_pre_topc(A_286,'#skF_2')
      | ~ v1_xboole_0(A_286)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ r1_tarski(A_286,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_5060,c_947])).

tff(c_5463,plain,(
    ! [A_297] :
      ( v3_pre_topc(A_297,'#skF_2')
      | ~ v1_xboole_0(A_297)
      | ~ r1_tarski(A_297,k2_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_5063])).

tff(c_5611,plain,(
    ! [A_300] :
      ( v3_pre_topc(A_300,'#skF_2')
      | ~ v1_xboole_0(A_300) ) ),
    inference(resolution,[status(thm)],[c_134,c_5463])).

tff(c_46,plain,(
    ! [B_40,A_38] :
      ( v4_pre_topc(B_40,A_38)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_38),B_40),A_38)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_5622,plain,(
    ! [B_40] :
      ( v4_pre_topc(B_40,'#skF_2')
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'),B_40)) ) ),
    inference(resolution,[status(thm)],[c_5611,c_46])).

tff(c_14585,plain,(
    ! [B_525] :
      ( v4_pre_topc(B_525,'#skF_2')
      | ~ m1_subset_1(B_525,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'),B_525)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_5622])).

tff(c_14619,plain,
    ( v4_pre_topc(u1_struct_0('#skF_2'),'#skF_2')
    | ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_65,c_14585])).

tff(c_14635,plain,(
    v4_pre_topc(u1_struct_0('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2716,c_14619])).

tff(c_1114,plain,(
    ! [A_133] :
      ( k2_pre_topc(A_133,u1_struct_0(A_133)) = u1_struct_0(A_133)
      | ~ v4_pre_topc(u1_struct_0(A_133),A_133)
      | ~ l1_pre_topc(A_133) ) ),
    inference(resolution,[status(thm)],[c_65,c_1077])).

tff(c_14680,plain,
    ( k2_pre_topc('#skF_2',u1_struct_0('#skF_2')) = u1_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14635,c_1114])).

tff(c_14695,plain,(
    k2_pre_topc('#skF_2',u1_struct_0('#skF_2')) = u1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_14680])).

tff(c_2717,plain,(
    ! [A_194] : k3_subset_1(A_194,k1_xboole_0) = A_194 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2699])).

tff(c_2760,plain,(
    ! [A_41] :
      ( v1_tops_1(u1_struct_0(A_41),A_41)
      | ~ v3_tops_1(k1_xboole_0,A_41)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2717,c_50])).

tff(c_2843,plain,(
    ! [A_41] :
      ( v1_tops_1(u1_struct_0(A_41),A_41)
      | ~ v3_tops_1(k1_xboole_0,A_41)
      | ~ l1_pre_topc(A_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2760])).

tff(c_3692,plain,(
    ! [A_250] :
      ( k2_pre_topc(A_250,u1_struct_0(A_250)) = k2_struct_0(A_250)
      | ~ v1_tops_1(u1_struct_0(A_250),A_250)
      | ~ l1_pre_topc(A_250) ) ),
    inference(resolution,[status(thm)],[c_65,c_1431])).

tff(c_3696,plain,(
    ! [A_41] :
      ( k2_pre_topc(A_41,u1_struct_0(A_41)) = k2_struct_0(A_41)
      | ~ v3_tops_1(k1_xboole_0,A_41)
      | ~ l1_pre_topc(A_41) ) ),
    inference(resolution,[status(thm)],[c_2843,c_3692])).

tff(c_14705,plain,
    ( u1_struct_0('#skF_2') = k2_struct_0('#skF_2')
    | ~ v3_tops_1(k1_xboole_0,'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14695,c_3696])).

tff(c_14718,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_5450,c_14705])).

tff(c_90,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_80])).

tff(c_14766,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14718,c_90])).

tff(c_14773,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4589,c_14766])).

tff(c_14774,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),'#skF_3') = u1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_913])).

tff(c_14778,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14774,c_446])).

tff(c_16790,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_16743,c_14778])).

tff(c_16836,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_16790])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:02:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.59/3.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.73/3.38  
% 8.73/3.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.73/3.38  %$ v4_pre_topc > v3_tops_1 > v3_pre_topc > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 8.73/3.38  
% 8.73/3.38  %Foreground sorts:
% 8.73/3.38  
% 8.73/3.38  
% 8.73/3.38  %Background operators:
% 8.73/3.38  
% 8.73/3.38  
% 8.73/3.38  %Foreground operators:
% 8.73/3.38  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 8.73/3.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.73/3.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.73/3.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.73/3.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.73/3.38  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 8.73/3.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.73/3.38  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 8.73/3.38  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 8.73/3.38  tff('#skF_2', type, '#skF_2': $i).
% 8.73/3.38  tff('#skF_3', type, '#skF_3': $i).
% 8.73/3.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.73/3.38  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 8.73/3.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.73/3.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.73/3.38  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.73/3.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.73/3.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.73/3.38  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 8.73/3.38  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 8.73/3.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.73/3.38  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.73/3.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.73/3.38  
% 8.73/3.40  tff(f_154, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tops_1(B, A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_tops_1)).
% 8.73/3.40  tff(f_59, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 8.73/3.40  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 8.73/3.40  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.73/3.40  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 8.73/3.40  tff(f_41, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 8.73/3.40  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 8.73/3.40  tff(f_131, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 8.73/3.40  tff(f_140, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_tops_1)).
% 8.73/3.40  tff(f_122, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 8.73/3.40  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 8.73/3.40  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.73/3.40  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 8.73/3.40  tff(f_113, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v3_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_tops_1)).
% 8.73/3.40  tff(f_43, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 8.73/3.40  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.73/3.40  tff(f_76, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 8.73/3.40  tff(f_102, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tops_1)).
% 8.73/3.40  tff(c_52, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_154])).
% 8.73/3.40  tff(c_24, plain, (![A_17]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.73/3.40  tff(c_16, plain, (![A_11, B_12]: (m1_subset_1(k3_subset_1(A_11, B_12), k1_zfmisc_1(A_11)) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.73/3.40  tff(c_80, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.73/3.40  tff(c_91, plain, (![A_17]: (r1_tarski(k1_xboole_0, A_17))), inference(resolution, [status(thm)], [c_24, c_80])).
% 8.73/3.40  tff(c_433, plain, (![A_100, B_101]: (k3_subset_1(A_100, k3_subset_1(A_100, B_101))=B_101 | ~m1_subset_1(B_101, k1_zfmisc_1(A_100)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.73/3.40  tff(c_447, plain, (![A_17]: (k3_subset_1(A_17, k3_subset_1(A_17, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_433])).
% 8.73/3.40  tff(c_12, plain, (![A_9]: (k2_subset_1(A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.73/3.40  tff(c_22, plain, (![A_15, B_16]: (k2_subset_1(A_15)=B_16 | ~r1_tarski(k3_subset_1(A_15, B_16), B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.73/3.40  tff(c_659, plain, (![B_119, A_120]: (B_119=A_120 | ~r1_tarski(k3_subset_1(A_120, B_119), B_119) | ~m1_subset_1(B_119, k1_zfmisc_1(A_120)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_22])).
% 8.73/3.40  tff(c_671, plain, (![A_17]: (k3_subset_1(A_17, k1_xboole_0)=A_17 | ~r1_tarski(k1_xboole_0, k3_subset_1(A_17, k1_xboole_0)) | ~m1_subset_1(k3_subset_1(A_17, k1_xboole_0), k1_zfmisc_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_447, c_659])).
% 8.73/3.40  tff(c_16535, plain, (![A_585]: (k3_subset_1(A_585, k1_xboole_0)=A_585 | ~m1_subset_1(k3_subset_1(A_585, k1_xboole_0), k1_zfmisc_1(A_585)))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_671])).
% 8.73/3.40  tff(c_16545, plain, (![A_11]: (k3_subset_1(A_11, k1_xboole_0)=A_11 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(resolution, [status(thm)], [c_16, c_16535])).
% 8.73/3.40  tff(c_16556, plain, (![A_11]: (k3_subset_1(A_11, k1_xboole_0)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_16545])).
% 8.73/3.40  tff(c_16743, plain, (![A_587]: (k3_subset_1(A_587, A_587)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16556, c_447])).
% 8.73/3.40  tff(c_60, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 8.73/3.40  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 8.73/3.40  tff(c_446, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_58, c_433])).
% 8.73/3.40  tff(c_665, plain, (k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')=u1_struct_0('#skF_2') | ~r1_tarski('#skF_3', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_446, c_659])).
% 8.73/3.40  tff(c_890, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_665])).
% 8.73/3.40  tff(c_905, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_16, c_890])).
% 8.73/3.40  tff(c_912, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_905])).
% 8.73/3.40  tff(c_914, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_665])).
% 8.73/3.40  tff(c_56, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 8.73/3.40  tff(c_1823, plain, (![B_167, A_168]: (v4_pre_topc(B_167, A_168) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_168), B_167), A_168) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0(A_168))) | ~l1_pre_topc(A_168))), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.73/3.40  tff(c_1833, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_446, c_1823])).
% 8.73/3.40  tff(c_1844, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_914, c_56, c_1833])).
% 8.73/3.40  tff(c_54, plain, (v3_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 8.73/3.40  tff(c_50, plain, (![A_41, B_43]: (v1_tops_1(k3_subset_1(u1_struct_0(A_41), B_43), A_41) | ~v3_tops_1(B_43, A_41) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_140])).
% 8.73/3.40  tff(c_1431, plain, (![A_145, B_146]: (k2_pre_topc(A_145, B_146)=k2_struct_0(A_145) | ~v1_tops_1(B_146, A_145) | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(A_145))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.73/3.40  tff(c_1434, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k2_struct_0('#skF_2') | ~v1_tops_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_914, c_1431])).
% 8.73/3.40  tff(c_1460, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k2_struct_0('#skF_2') | ~v1_tops_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1434])).
% 8.73/3.40  tff(c_4466, plain, (~v1_tops_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_1460])).
% 8.73/3.40  tff(c_4469, plain, (~v3_tops_1('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_4466])).
% 8.73/3.40  tff(c_4473, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_4469])).
% 8.73/3.40  tff(c_4474, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_1460])).
% 8.73/3.40  tff(c_26, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | ~m1_subset_1(A_18, k1_zfmisc_1(B_19)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.73/3.40  tff(c_981, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_914, c_26])).
% 8.73/3.40  tff(c_28, plain, (![A_18, B_19]: (m1_subset_1(A_18, k1_zfmisc_1(B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.73/3.40  tff(c_1077, plain, (![A_133, B_134]: (k2_pre_topc(A_133, B_134)=B_134 | ~v4_pre_topc(B_134, A_133) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.73/3.40  tff(c_4494, plain, (![A_278, A_279]: (k2_pre_topc(A_278, A_279)=A_279 | ~v4_pre_topc(A_279, A_278) | ~l1_pre_topc(A_278) | ~r1_tarski(A_279, u1_struct_0(A_278)))), inference(resolution, [status(thm)], [c_28, c_1077])).
% 8.73/3.40  tff(c_4526, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_3') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_981, c_4494])).
% 8.73/3.40  tff(c_4569, plain, (k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1844, c_4474, c_4526])).
% 8.73/3.40  tff(c_913, plain, (~r1_tarski('#skF_3', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')) | k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')=u1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_665])).
% 8.73/3.40  tff(c_1116, plain, (~r1_tarski('#skF_3', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_913])).
% 8.73/3.40  tff(c_4589, plain, (~r1_tarski('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4569, c_1116])).
% 8.73/3.40  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.73/3.40  tff(c_62, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 8.73/3.40  tff(c_10, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(B_7, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.73/3.40  tff(c_991, plain, (![A_6]: (r1_tarski(A_6, u1_struct_0('#skF_2')) | ~r1_tarski(A_6, k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')))), inference(resolution, [status(thm)], [c_981, c_10])).
% 8.73/3.40  tff(c_5060, plain, (![A_286]: (r1_tarski(A_286, u1_struct_0('#skF_2')) | ~r1_tarski(A_286, k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4569, c_991])).
% 8.73/3.40  tff(c_1199, plain, (![B_136, A_137]: (v3_tops_1(B_136, A_137) | ~v1_xboole_0(B_136) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_137))) | ~l1_pre_topc(A_137) | ~v2_pre_topc(A_137))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.73/3.40  tff(c_1231, plain, (![A_18, A_137]: (v3_tops_1(A_18, A_137) | ~v1_xboole_0(A_18) | ~l1_pre_topc(A_137) | ~v2_pre_topc(A_137) | ~r1_tarski(A_18, u1_struct_0(A_137)))), inference(resolution, [status(thm)], [c_28, c_1199])).
% 8.73/3.40  tff(c_5066, plain, (![A_286]: (v3_tops_1(A_286, '#skF_2') | ~v1_xboole_0(A_286) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r1_tarski(A_286, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_5060, c_1231])).
% 8.73/3.40  tff(c_5397, plain, (![A_295]: (v3_tops_1(A_295, '#skF_2') | ~v1_xboole_0(A_295) | ~r1_tarski(A_295, k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_5066])).
% 8.73/3.40  tff(c_5437, plain, (v3_tops_1(k1_xboole_0, '#skF_2') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_91, c_5397])).
% 8.73/3.40  tff(c_5450, plain, (v3_tops_1(k1_xboole_0, '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_5437])).
% 8.73/3.40  tff(c_2689, plain, (![A_193]: (k3_subset_1(A_193, k1_xboole_0)=A_193 | ~m1_subset_1(k3_subset_1(A_193, k1_xboole_0), k1_zfmisc_1(A_193)))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_671])).
% 8.73/3.40  tff(c_2699, plain, (![A_11]: (k3_subset_1(A_11, k1_xboole_0)=A_11 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(resolution, [status(thm)], [c_16, c_2689])).
% 8.73/3.40  tff(c_2710, plain, (![A_11]: (k3_subset_1(A_11, k1_xboole_0)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2699])).
% 8.73/3.40  tff(c_2716, plain, (![A_17]: (k3_subset_1(A_17, A_17)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2710, c_447])).
% 8.73/3.40  tff(c_14, plain, (![A_10]: (m1_subset_1(k2_subset_1(A_10), k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.73/3.40  tff(c_65, plain, (![A_10]: (m1_subset_1(A_10, k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14])).
% 8.73/3.40  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.73/3.40  tff(c_108, plain, (![C_59, B_60, A_61]: (~v1_xboole_0(C_59) | ~m1_subset_1(B_60, k1_zfmisc_1(C_59)) | ~r2_hidden(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.73/3.40  tff(c_130, plain, (![A_63, A_64]: (~v1_xboole_0(A_63) | ~r2_hidden(A_64, A_63))), inference(resolution, [status(thm)], [c_65, c_108])).
% 8.73/3.40  tff(c_134, plain, (![A_1, B_2]: (~v1_xboole_0(A_1) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_130])).
% 8.73/3.40  tff(c_921, plain, (![B_126, A_127]: (v3_pre_topc(B_126, A_127) | ~v1_xboole_0(B_126) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127) | ~v2_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.73/3.40  tff(c_947, plain, (![A_18, A_127]: (v3_pre_topc(A_18, A_127) | ~v1_xboole_0(A_18) | ~l1_pre_topc(A_127) | ~v2_pre_topc(A_127) | ~r1_tarski(A_18, u1_struct_0(A_127)))), inference(resolution, [status(thm)], [c_28, c_921])).
% 8.73/3.40  tff(c_5063, plain, (![A_286]: (v3_pre_topc(A_286, '#skF_2') | ~v1_xboole_0(A_286) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r1_tarski(A_286, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_5060, c_947])).
% 8.73/3.40  tff(c_5463, plain, (![A_297]: (v3_pre_topc(A_297, '#skF_2') | ~v1_xboole_0(A_297) | ~r1_tarski(A_297, k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_5063])).
% 8.73/3.40  tff(c_5611, plain, (![A_300]: (v3_pre_topc(A_300, '#skF_2') | ~v1_xboole_0(A_300))), inference(resolution, [status(thm)], [c_134, c_5463])).
% 8.73/3.40  tff(c_46, plain, (![B_40, A_38]: (v4_pre_topc(B_40, A_38) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_38), B_40), A_38) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.73/3.40  tff(c_5622, plain, (![B_40]: (v4_pre_topc(B_40, '#skF_2') | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'), B_40)))), inference(resolution, [status(thm)], [c_5611, c_46])).
% 8.73/3.40  tff(c_14585, plain, (![B_525]: (v4_pre_topc(B_525, '#skF_2') | ~m1_subset_1(B_525, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'), B_525)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_5622])).
% 8.73/3.40  tff(c_14619, plain, (v4_pre_topc(u1_struct_0('#skF_2'), '#skF_2') | ~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_65, c_14585])).
% 8.73/3.40  tff(c_14635, plain, (v4_pre_topc(u1_struct_0('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2716, c_14619])).
% 8.73/3.40  tff(c_1114, plain, (![A_133]: (k2_pre_topc(A_133, u1_struct_0(A_133))=u1_struct_0(A_133) | ~v4_pre_topc(u1_struct_0(A_133), A_133) | ~l1_pre_topc(A_133))), inference(resolution, [status(thm)], [c_65, c_1077])).
% 8.73/3.40  tff(c_14680, plain, (k2_pre_topc('#skF_2', u1_struct_0('#skF_2'))=u1_struct_0('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14635, c_1114])).
% 8.73/3.40  tff(c_14695, plain, (k2_pre_topc('#skF_2', u1_struct_0('#skF_2'))=u1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_14680])).
% 8.73/3.40  tff(c_2717, plain, (![A_194]: (k3_subset_1(A_194, k1_xboole_0)=A_194)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2699])).
% 8.73/3.40  tff(c_2760, plain, (![A_41]: (v1_tops_1(u1_struct_0(A_41), A_41) | ~v3_tops_1(k1_xboole_0, A_41) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41))), inference(superposition, [status(thm), theory('equality')], [c_2717, c_50])).
% 8.73/3.40  tff(c_2843, plain, (![A_41]: (v1_tops_1(u1_struct_0(A_41), A_41) | ~v3_tops_1(k1_xboole_0, A_41) | ~l1_pre_topc(A_41))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2760])).
% 8.73/3.40  tff(c_3692, plain, (![A_250]: (k2_pre_topc(A_250, u1_struct_0(A_250))=k2_struct_0(A_250) | ~v1_tops_1(u1_struct_0(A_250), A_250) | ~l1_pre_topc(A_250))), inference(resolution, [status(thm)], [c_65, c_1431])).
% 8.73/3.40  tff(c_3696, plain, (![A_41]: (k2_pre_topc(A_41, u1_struct_0(A_41))=k2_struct_0(A_41) | ~v3_tops_1(k1_xboole_0, A_41) | ~l1_pre_topc(A_41))), inference(resolution, [status(thm)], [c_2843, c_3692])).
% 8.73/3.40  tff(c_14705, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2') | ~v3_tops_1(k1_xboole_0, '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_14695, c_3696])).
% 8.73/3.40  tff(c_14718, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_5450, c_14705])).
% 8.73/3.40  tff(c_90, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_58, c_80])).
% 8.73/3.40  tff(c_14766, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14718, c_90])).
% 8.73/3.40  tff(c_14773, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4589, c_14766])).
% 8.73/3.40  tff(c_14774, plain, (k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')=u1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_913])).
% 8.73/3.40  tff(c_14778, plain, (k3_subset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14774, c_446])).
% 8.73/3.40  tff(c_16790, plain, (k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_16743, c_14778])).
% 8.73/3.40  tff(c_16836, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_16790])).
% 8.73/3.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.73/3.40  
% 8.73/3.40  Inference rules
% 8.73/3.40  ----------------------
% 8.73/3.40  #Ref     : 0
% 8.73/3.40  #Sup     : 3684
% 8.73/3.40  #Fact    : 0
% 8.73/3.40  #Define  : 0
% 8.73/3.40  #Split   : 21
% 8.73/3.40  #Chain   : 0
% 8.73/3.40  #Close   : 0
% 8.73/3.40  
% 8.73/3.40  Ordering : KBO
% 8.73/3.40  
% 8.73/3.40  Simplification rules
% 8.73/3.40  ----------------------
% 8.73/3.40  #Subsume      : 1619
% 8.73/3.40  #Demod        : 2532
% 8.73/3.40  #Tautology    : 1051
% 8.73/3.40  #SimpNegUnit  : 57
% 8.73/3.40  #BackRed      : 99
% 8.73/3.40  
% 8.73/3.40  #Partial instantiations: 0
% 8.73/3.40  #Strategies tried      : 1
% 8.73/3.40  
% 8.73/3.40  Timing (in seconds)
% 8.73/3.40  ----------------------
% 8.73/3.40  Preprocessing        : 0.35
% 8.73/3.40  Parsing              : 0.19
% 8.73/3.40  CNF conversion       : 0.02
% 8.73/3.40  Main loop            : 2.27
% 8.73/3.40  Inferencing          : 0.62
% 8.73/3.40  Reduction            : 0.72
% 8.73/3.40  Demodulation         : 0.49
% 8.73/3.40  BG Simplification    : 0.06
% 8.73/3.40  Subsumption          : 0.73
% 8.73/3.40  Abstraction          : 0.09
% 8.73/3.40  MUC search           : 0.00
% 8.73/3.40  Cooper               : 0.00
% 8.73/3.40  Total                : 2.66
% 8.73/3.40  Index Insertion      : 0.00
% 8.73/3.40  Index Deletion       : 0.00
% 8.73/3.40  Index Matching       : 0.00
% 8.73/3.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
