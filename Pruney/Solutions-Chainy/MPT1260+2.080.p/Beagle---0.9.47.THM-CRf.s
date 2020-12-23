%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:10 EST 2020

% Result     : Theorem 10.94s
% Output     : CNFRefutation 11.12s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 599 expanded)
%              Number of leaves         :   35 ( 214 expanded)
%              Depth                    :   15
%              Number of atoms          :  237 (1293 expanded)
%              Number of equality atoms :   78 ( 322 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(f_109,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( v3_pre_topc(D,B)
                     => k1_tops_1(B,D) = D )
                    & ( k1_tops_1(A,C) = C
                     => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_116,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_42,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_66,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_40,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k3_subset_1(A_6,B_7),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_167,plain,(
    ! [A_69,B_70] :
      ( k4_xboole_0(A_69,B_70) = k3_subset_1(A_69,B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_179,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),'#skF_2') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_167])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_269,plain,(
    ! [A_78,B_79,C_80] :
      ( k7_subset_1(A_78,B_79,C_80) = k4_xboole_0(B_79,C_80)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_316,plain,(
    ! [B_86,A_87,C_88] :
      ( k7_subset_1(B_86,A_87,C_88) = k4_xboole_0(A_87,C_88)
      | ~ r1_tarski(A_87,B_86) ) ),
    inference(resolution,[status(thm)],[c_20,c_269])).

tff(c_507,plain,(
    ! [A_101,B_102,C_103] : k7_subset_1(A_101,k4_xboole_0(A_101,B_102),C_103) = k4_xboole_0(k4_xboole_0(A_101,B_102),C_103) ),
    inference(resolution,[status(thm)],[c_2,c_316])).

tff(c_528,plain,(
    ! [C_103] : k7_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),C_103) = k4_xboole_0(k4_xboole_0(u1_struct_0('#skF_1'),'#skF_2'),C_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_507])).

tff(c_538,plain,(
    ! [C_103] : k7_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),C_103) = k4_xboole_0(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),C_103) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_528])).

tff(c_1130,plain,(
    ! [A_135,B_136,C_137] :
      ( k9_subset_1(A_135,B_136,k3_subset_1(A_135,C_137)) = k7_subset_1(A_135,B_136,C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(A_135))
      | ~ m1_subset_1(B_136,k1_zfmisc_1(A_135)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1178,plain,(
    ! [B_138] :
      ( k9_subset_1(u1_struct_0('#skF_1'),B_138,k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k7_subset_1(u1_struct_0('#skF_1'),B_138,'#skF_2')
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_36,c_1130])).

tff(c_6,plain,(
    ! [A_5] : m1_subset_1(k2_subset_1(A_5),k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_67,plain,(
    ! [A_59,B_60,C_61] :
      ( k9_subset_1(A_59,B_60,B_60) = B_60
      | ~ m1_subset_1(C_61,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_75,plain,(
    ! [A_5,B_60] : k9_subset_1(A_5,B_60,B_60) = B_60 ),
    inference(resolution,[status(thm)],[c_6,c_67])).

tff(c_1185,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_2') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1178,c_75])).

tff(c_1194,plain,
    ( k4_xboole_0(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_2') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_1185])).

tff(c_1453,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1194])).

tff(c_1456,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8,c_1453])).

tff(c_1463,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1456])).

tff(c_1465,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1194])).

tff(c_30,plain,(
    ! [C_44,A_32,D_46,B_40] :
      ( v3_pre_topc(C_44,A_32)
      | k1_tops_1(A_32,C_44) != C_44
      | ~ m1_subset_1(D_46,k1_zfmisc_1(u1_struct_0(B_40)))
      | ~ m1_subset_1(C_44,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(B_40)
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1546,plain,(
    ! [D_148,B_149] :
      ( ~ m1_subset_1(D_148,k1_zfmisc_1(u1_struct_0(B_149)))
      | ~ l1_pre_topc(B_149) ) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_1549,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1465,c_1546])).

tff(c_1567,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1549])).

tff(c_1760,plain,(
    ! [C_160,A_161] :
      ( v3_pre_topc(C_160,A_161)
      | k1_tops_1(A_161,C_160) != C_160
      | ~ m1_subset_1(C_160,k1_zfmisc_1(u1_struct_0(A_161)))
      | ~ l1_pre_topc(A_161)
      | ~ v2_pre_topc(A_161) ) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_1781,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_1760])).

tff(c_1791,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1781])).

tff(c_1792,plain,(
    k1_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1791])).

tff(c_681,plain,(
    ! [A_116,B_117] :
      ( m1_subset_1(k2_pre_topc(A_116,B_117),k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( k3_subset_1(A_11,k3_subset_1(A_11,B_12)) = B_12
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3528,plain,(
    ! [A_212,B_213] :
      ( k3_subset_1(u1_struct_0(A_212),k3_subset_1(u1_struct_0(A_212),k2_pre_topc(A_212,B_213))) = k2_pre_topc(A_212,B_213)
      | ~ m1_subset_1(B_213,k1_zfmisc_1(u1_struct_0(A_212)))
      | ~ l1_pre_topc(A_212) ) ),
    inference(resolution,[status(thm)],[c_681,c_12])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k3_subset_1(A_3,B_4)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3216,plain,(
    ! [A_209,B_210] :
      ( k4_xboole_0(u1_struct_0(A_209),k2_pre_topc(A_209,B_210)) = k3_subset_1(u1_struct_0(A_209),k2_pre_topc(A_209,B_210))
      | ~ m1_subset_1(B_210,k1_zfmisc_1(u1_struct_0(A_209)))
      | ~ l1_pre_topc(A_209) ) ),
    inference(resolution,[status(thm)],[c_681,c_4])).

tff(c_3231,plain,
    ( k4_xboole_0(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_3216])).

tff(c_3241,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_3231])).

tff(c_223,plain,(
    ! [B_75,A_76] :
      ( k4_xboole_0(B_75,A_76) = k3_subset_1(B_75,A_76)
      | ~ r1_tarski(A_76,B_75) ) ),
    inference(resolution,[status(thm)],[c_20,c_167])).

tff(c_337,plain,(
    ! [A_89,B_90] : k4_xboole_0(A_89,k4_xboole_0(A_89,B_90)) = k3_subset_1(A_89,k4_xboole_0(A_89,B_90)) ),
    inference(resolution,[status(thm)],[c_2,c_223])).

tff(c_346,plain,(
    ! [A_89,B_90] : r1_tarski(k3_subset_1(A_89,k4_xboole_0(A_89,B_90)),A_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_2])).

tff(c_3266,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'))),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3241,c_346])).

tff(c_3537,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3528,c_3266])).

tff(c_3621,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_3537])).

tff(c_279,plain,(
    ! [B_21,A_20,C_80] :
      ( k7_subset_1(B_21,A_20,C_80) = k4_xboole_0(A_20,C_80)
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(resolution,[status(thm)],[c_20,c_269])).

tff(c_3910,plain,(
    ! [C_214] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_214) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_214) ),
    inference(resolution,[status(thm)],[c_3621,c_279])).

tff(c_48,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_162,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_48])).

tff(c_3924,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3910,c_162])).

tff(c_3980,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3924,c_2])).

tff(c_281,plain,(
    ! [C_80] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_80) = k4_xboole_0('#skF_2',C_80) ),
    inference(resolution,[status(thm)],[c_36,c_269])).

tff(c_994,plain,(
    ! [A_132,B_133] :
      ( k7_subset_1(u1_struct_0(A_132),B_133,k2_tops_1(A_132,B_133)) = k1_tops_1(A_132,B_133)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1007,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_994])).

tff(c_1015,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_281,c_1007])).

tff(c_373,plain,(
    ! [B_91,A_92] :
      ( r1_tarski(B_91,k2_pre_topc(A_92,B_91))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_384,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_373])).

tff(c_390,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_384])).

tff(c_396,plain,(
    ! [C_80] : k7_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2',C_80) = k4_xboole_0('#skF_2',C_80) ),
    inference(resolution,[status(thm)],[c_390,c_279])).

tff(c_177,plain,(
    ! [B_21,A_20] :
      ( k4_xboole_0(B_21,A_20) = k3_subset_1(B_21,A_20)
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(resolution,[status(thm)],[c_20,c_167])).

tff(c_397,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_390,c_177])).

tff(c_3949,plain,(
    k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3924,c_397])).

tff(c_89,plain,(
    ! [A_64,B_65] :
      ( k3_subset_1(A_64,k3_subset_1(A_64,B_65)) = B_65
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_96,plain,(
    ! [B_21,A_20] :
      ( k3_subset_1(B_21,k3_subset_1(B_21,A_20)) = A_20
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(resolution,[status(thm)],[c_20,c_89])).

tff(c_4032,plain,
    ( k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3949,c_96])).

tff(c_4052,plain,(
    k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_4032])).

tff(c_4029,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(k2_pre_topc('#skF_1','#skF_2')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3949,c_8])).

tff(c_4923,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_4029])).

tff(c_5002,plain,(
    ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_20,c_4923])).

tff(c_5006,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_5002])).

tff(c_5007,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_4029])).

tff(c_2407,plain,(
    ! [B_187,B_188,A_189] :
      ( k9_subset_1(B_187,B_188,k3_subset_1(B_187,A_189)) = k7_subset_1(B_187,B_188,A_189)
      | ~ m1_subset_1(B_188,k1_zfmisc_1(B_187))
      | ~ r1_tarski(A_189,B_187) ) ),
    inference(resolution,[status(thm)],[c_20,c_1130])).

tff(c_14474,plain,(
    ! [A_328,B_329,A_330] :
      ( k9_subset_1(A_328,k3_subset_1(A_328,B_329),k3_subset_1(A_328,A_330)) = k7_subset_1(A_328,k3_subset_1(A_328,B_329),A_330)
      | ~ r1_tarski(A_330,A_328)
      | ~ m1_subset_1(B_329,k1_zfmisc_1(A_328)) ) ),
    inference(resolution,[status(thm)],[c_8,c_2407])).

tff(c_14709,plain,(
    ! [A_331,A_332] :
      ( k7_subset_1(A_331,k3_subset_1(A_331,A_332),A_332) = k3_subset_1(A_331,A_332)
      | ~ r1_tarski(A_332,A_331)
      | ~ m1_subset_1(A_332,k1_zfmisc_1(A_331)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14474,c_75])).

tff(c_14711,plain,
    ( k7_subset_1(k2_pre_topc('#skF_1','#skF_2'),k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2')) = k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_5007,c_14709])).

tff(c_14732,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3980,c_1015,c_396,c_4052,c_4052,c_14711])).

tff(c_14734,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1792,c_14732])).

tff(c_14735,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_14736,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_14779,plain,(
    ! [A_341,B_342] :
      ( k4_xboole_0(A_341,B_342) = k3_subset_1(A_341,B_342)
      | ~ m1_subset_1(B_342,k1_zfmisc_1(A_341)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14791,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),'#skF_2') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_14779])).

tff(c_14799,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14791,c_2])).

tff(c_14991,plain,(
    ! [A_356,B_357,C_358] :
      ( k7_subset_1(A_356,B_357,C_358) = k4_xboole_0(B_357,C_358)
      | ~ m1_subset_1(B_357,k1_zfmisc_1(A_356)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_15076,plain,(
    ! [B_366,A_367,C_368] :
      ( k7_subset_1(B_366,A_367,C_368) = k4_xboole_0(A_367,C_368)
      | ~ r1_tarski(A_367,B_366) ) ),
    inference(resolution,[status(thm)],[c_20,c_14991])).

tff(c_15097,plain,(
    ! [C_368] : k7_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),C_368) = k4_xboole_0(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),C_368) ),
    inference(resolution,[status(thm)],[c_14799,c_15076])).

tff(c_14737,plain,(
    ! [A_333,B_334,C_335] :
      ( k9_subset_1(A_333,B_334,B_334) = B_334
      | ~ m1_subset_1(C_335,k1_zfmisc_1(A_333)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14745,plain,(
    ! [A_5,B_334] : k9_subset_1(A_5,B_334,B_334) = B_334 ),
    inference(resolution,[status(thm)],[c_6,c_14737])).

tff(c_15512,plain,(
    ! [A_397,B_398,C_399] :
      ( k9_subset_1(A_397,B_398,k3_subset_1(A_397,C_399)) = k7_subset_1(A_397,B_398,C_399)
      | ~ m1_subset_1(C_399,k1_zfmisc_1(A_397))
      | ~ m1_subset_1(B_398,k1_zfmisc_1(A_397)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_15552,plain,(
    ! [B_400] :
      ( k9_subset_1(u1_struct_0('#skF_1'),B_400,k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k7_subset_1(u1_struct_0('#skF_1'),B_400,'#skF_2')
      | ~ m1_subset_1(B_400,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_36,c_15512])).

tff(c_15566,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_2') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_14745,c_15552])).

tff(c_15570,plain,
    ( k4_xboole_0(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_2') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15097,c_15566])).

tff(c_15966,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_15570])).

tff(c_15969,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8,c_15966])).

tff(c_15976,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_15969])).

tff(c_15978,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_15570])).

tff(c_32,plain,(
    ! [B_40,D_46,C_44,A_32] :
      ( k1_tops_1(B_40,D_46) = D_46
      | ~ v3_pre_topc(D_46,B_40)
      | ~ m1_subset_1(D_46,k1_zfmisc_1(u1_struct_0(B_40)))
      | ~ m1_subset_1(C_44,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(B_40)
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_16059,plain,(
    ! [C_417,A_418] :
      ( ~ m1_subset_1(C_417,k1_zfmisc_1(u1_struct_0(A_418)))
      | ~ l1_pre_topc(A_418)
      | ~ v2_pre_topc(A_418) ) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_16062,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_15978,c_16059])).

tff(c_16083,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_16062])).

tff(c_16092,plain,(
    ! [B_419,D_420] :
      ( k1_tops_1(B_419,D_420) = D_420
      | ~ v3_pre_topc(D_420,B_419)
      | ~ m1_subset_1(D_420,k1_zfmisc_1(u1_struct_0(B_419)))
      | ~ l1_pre_topc(B_419) ) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_16113,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_16092])).

tff(c_16123,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_14736,c_16113])).

tff(c_28,plain,(
    ! [A_29,B_31] :
      ( k7_subset_1(u1_struct_0(A_29),k2_pre_topc(A_29,B_31),k1_tops_1(A_29,B_31)) = k2_tops_1(A_29,B_31)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_16137,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16123,c_28])).

tff(c_16144,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_16137])).

tff(c_16146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14735,c_16144])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:41:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.94/4.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.94/4.14  
% 10.94/4.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.94/4.14  %$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 10.94/4.14  
% 10.94/4.14  %Foreground sorts:
% 10.94/4.14  
% 10.94/4.14  
% 10.94/4.14  %Background operators:
% 10.94/4.14  
% 10.94/4.14  
% 10.94/4.14  %Foreground operators:
% 10.94/4.14  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 10.94/4.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.94/4.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.94/4.14  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 10.94/4.14  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.94/4.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.94/4.14  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.94/4.14  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 10.94/4.14  tff('#skF_2', type, '#skF_2': $i).
% 10.94/4.14  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 10.94/4.14  tff('#skF_1', type, '#skF_1': $i).
% 10.94/4.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.94/4.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.94/4.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.94/4.14  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.94/4.14  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.94/4.14  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 10.94/4.14  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 10.94/4.14  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 10.94/4.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.94/4.14  
% 11.12/4.16  tff(f_128, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 11.12/4.16  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 11.12/4.16  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 11.12/4.16  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 11.12/4.16  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.12/4.16  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 11.12/4.16  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_subset_1)).
% 11.12/4.16  tff(f_33, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 11.12/4.16  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 11.12/4.16  tff(f_109, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 11.12/4.16  tff(f_66, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 11.12/4.16  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 11.12/4.16  tff(f_116, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 11.12/4.16  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 11.12/4.16  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 11.12/4.16  tff(c_42, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 11.12/4.16  tff(c_66, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_42])).
% 11.12/4.16  tff(c_40, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 11.12/4.16  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 11.12/4.16  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 11.12/4.16  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(k3_subset_1(A_6, B_7), k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.12/4.16  tff(c_167, plain, (![A_69, B_70]: (k4_xboole_0(A_69, B_70)=k3_subset_1(A_69, B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.12/4.16  tff(c_179, plain, (k4_xboole_0(u1_struct_0('#skF_1'), '#skF_2')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_36, c_167])).
% 11.12/4.16  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.12/4.16  tff(c_20, plain, (![A_20, B_21]: (m1_subset_1(A_20, k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.12/4.16  tff(c_269, plain, (![A_78, B_79, C_80]: (k7_subset_1(A_78, B_79, C_80)=k4_xboole_0(B_79, C_80) | ~m1_subset_1(B_79, k1_zfmisc_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.12/4.16  tff(c_316, plain, (![B_86, A_87, C_88]: (k7_subset_1(B_86, A_87, C_88)=k4_xboole_0(A_87, C_88) | ~r1_tarski(A_87, B_86))), inference(resolution, [status(thm)], [c_20, c_269])).
% 11.12/4.16  tff(c_507, plain, (![A_101, B_102, C_103]: (k7_subset_1(A_101, k4_xboole_0(A_101, B_102), C_103)=k4_xboole_0(k4_xboole_0(A_101, B_102), C_103))), inference(resolution, [status(thm)], [c_2, c_316])).
% 11.12/4.16  tff(c_528, plain, (![C_103]: (k7_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), C_103)=k4_xboole_0(k4_xboole_0(u1_struct_0('#skF_1'), '#skF_2'), C_103))), inference(superposition, [status(thm), theory('equality')], [c_179, c_507])).
% 11.12/4.16  tff(c_538, plain, (![C_103]: (k7_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), C_103)=k4_xboole_0(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), C_103))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_528])).
% 11.12/4.16  tff(c_1130, plain, (![A_135, B_136, C_137]: (k9_subset_1(A_135, B_136, k3_subset_1(A_135, C_137))=k7_subset_1(A_135, B_136, C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(A_135)) | ~m1_subset_1(B_136, k1_zfmisc_1(A_135)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.12/4.16  tff(c_1178, plain, (![B_138]: (k9_subset_1(u1_struct_0('#skF_1'), B_138, k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k7_subset_1(u1_struct_0('#skF_1'), B_138, '#skF_2') | ~m1_subset_1(B_138, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_36, c_1130])).
% 11.12/4.16  tff(c_6, plain, (![A_5]: (m1_subset_1(k2_subset_1(A_5), k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.12/4.16  tff(c_67, plain, (![A_59, B_60, C_61]: (k9_subset_1(A_59, B_60, B_60)=B_60 | ~m1_subset_1(C_61, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.12/4.16  tff(c_75, plain, (![A_5, B_60]: (k9_subset_1(A_5, B_60, B_60)=B_60)), inference(resolution, [status(thm)], [c_6, c_67])).
% 11.12/4.16  tff(c_1185, plain, (k7_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_2')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1178, c_75])).
% 11.12/4.16  tff(c_1194, plain, (k4_xboole_0(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_2')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_538, c_1185])).
% 11.12/4.16  tff(c_1453, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1194])).
% 11.12/4.16  tff(c_1456, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_8, c_1453])).
% 11.12/4.16  tff(c_1463, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_1456])).
% 11.12/4.16  tff(c_1465, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1194])).
% 11.12/4.16  tff(c_30, plain, (![C_44, A_32, D_46, B_40]: (v3_pre_topc(C_44, A_32) | k1_tops_1(A_32, C_44)!=C_44 | ~m1_subset_1(D_46, k1_zfmisc_1(u1_struct_0(B_40))) | ~m1_subset_1(C_44, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(B_40) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.12/4.16  tff(c_1546, plain, (![D_148, B_149]: (~m1_subset_1(D_148, k1_zfmisc_1(u1_struct_0(B_149))) | ~l1_pre_topc(B_149))), inference(splitLeft, [status(thm)], [c_30])).
% 11.12/4.16  tff(c_1549, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1465, c_1546])).
% 11.12/4.16  tff(c_1567, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_1549])).
% 11.12/4.16  tff(c_1760, plain, (![C_160, A_161]: (v3_pre_topc(C_160, A_161) | k1_tops_1(A_161, C_160)!=C_160 | ~m1_subset_1(C_160, k1_zfmisc_1(u1_struct_0(A_161))) | ~l1_pre_topc(A_161) | ~v2_pre_topc(A_161))), inference(splitRight, [status(thm)], [c_30])).
% 11.12/4.16  tff(c_1781, plain, (v3_pre_topc('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_1760])).
% 11.12/4.16  tff(c_1791, plain, (v3_pre_topc('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1781])).
% 11.12/4.16  tff(c_1792, plain, (k1_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_66, c_1791])).
% 11.12/4.16  tff(c_681, plain, (![A_116, B_117]: (m1_subset_1(k2_pre_topc(A_116, B_117), k1_zfmisc_1(u1_struct_0(A_116))) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_66])).
% 11.12/4.16  tff(c_12, plain, (![A_11, B_12]: (k3_subset_1(A_11, k3_subset_1(A_11, B_12))=B_12 | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.12/4.16  tff(c_3528, plain, (![A_212, B_213]: (k3_subset_1(u1_struct_0(A_212), k3_subset_1(u1_struct_0(A_212), k2_pre_topc(A_212, B_213)))=k2_pre_topc(A_212, B_213) | ~m1_subset_1(B_213, k1_zfmisc_1(u1_struct_0(A_212))) | ~l1_pre_topc(A_212))), inference(resolution, [status(thm)], [c_681, c_12])).
% 11.12/4.16  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k3_subset_1(A_3, B_4) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.12/4.16  tff(c_3216, plain, (![A_209, B_210]: (k4_xboole_0(u1_struct_0(A_209), k2_pre_topc(A_209, B_210))=k3_subset_1(u1_struct_0(A_209), k2_pre_topc(A_209, B_210)) | ~m1_subset_1(B_210, k1_zfmisc_1(u1_struct_0(A_209))) | ~l1_pre_topc(A_209))), inference(resolution, [status(thm)], [c_681, c_4])).
% 11.12/4.16  tff(c_3231, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_3216])).
% 11.12/4.16  tff(c_3241, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_3231])).
% 11.12/4.16  tff(c_223, plain, (![B_75, A_76]: (k4_xboole_0(B_75, A_76)=k3_subset_1(B_75, A_76) | ~r1_tarski(A_76, B_75))), inference(resolution, [status(thm)], [c_20, c_167])).
% 11.12/4.16  tff(c_337, plain, (![A_89, B_90]: (k4_xboole_0(A_89, k4_xboole_0(A_89, B_90))=k3_subset_1(A_89, k4_xboole_0(A_89, B_90)))), inference(resolution, [status(thm)], [c_2, c_223])).
% 11.12/4.16  tff(c_346, plain, (![A_89, B_90]: (r1_tarski(k3_subset_1(A_89, k4_xboole_0(A_89, B_90)), A_89))), inference(superposition, [status(thm), theory('equality')], [c_337, c_2])).
% 11.12/4.16  tff(c_3266, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3241, c_346])).
% 11.12/4.16  tff(c_3537, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3528, c_3266])).
% 11.12/4.16  tff(c_3621, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_3537])).
% 11.12/4.16  tff(c_279, plain, (![B_21, A_20, C_80]: (k7_subset_1(B_21, A_20, C_80)=k4_xboole_0(A_20, C_80) | ~r1_tarski(A_20, B_21))), inference(resolution, [status(thm)], [c_20, c_269])).
% 11.12/4.16  tff(c_3910, plain, (![C_214]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_214)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_214))), inference(resolution, [status(thm)], [c_3621, c_279])).
% 11.12/4.16  tff(c_48, plain, (v3_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 11.12/4.16  tff(c_162, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_66, c_48])).
% 11.12/4.16  tff(c_3924, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3910, c_162])).
% 11.12/4.16  tff(c_3980, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3924, c_2])).
% 11.12/4.16  tff(c_281, plain, (![C_80]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_80)=k4_xboole_0('#skF_2', C_80))), inference(resolution, [status(thm)], [c_36, c_269])).
% 11.12/4.16  tff(c_994, plain, (![A_132, B_133]: (k7_subset_1(u1_struct_0(A_132), B_133, k2_tops_1(A_132, B_133))=k1_tops_1(A_132, B_133) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132))), inference(cnfTransformation, [status(thm)], [f_116])).
% 11.12/4.16  tff(c_1007, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_994])).
% 11.12/4.16  tff(c_1015, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_281, c_1007])).
% 11.12/4.16  tff(c_373, plain, (![B_91, A_92]: (r1_tarski(B_91, k2_pre_topc(A_92, B_91)) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.12/4.16  tff(c_384, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_373])).
% 11.12/4.16  tff(c_390, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_384])).
% 11.12/4.16  tff(c_396, plain, (![C_80]: (k7_subset_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2', C_80)=k4_xboole_0('#skF_2', C_80))), inference(resolution, [status(thm)], [c_390, c_279])).
% 11.12/4.16  tff(c_177, plain, (![B_21, A_20]: (k4_xboole_0(B_21, A_20)=k3_subset_1(B_21, A_20) | ~r1_tarski(A_20, B_21))), inference(resolution, [status(thm)], [c_20, c_167])).
% 11.12/4.16  tff(c_397, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_390, c_177])).
% 11.12/4.16  tff(c_3949, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3924, c_397])).
% 11.12/4.16  tff(c_89, plain, (![A_64, B_65]: (k3_subset_1(A_64, k3_subset_1(A_64, B_65))=B_65 | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.12/4.16  tff(c_96, plain, (![B_21, A_20]: (k3_subset_1(B_21, k3_subset_1(B_21, A_20))=A_20 | ~r1_tarski(A_20, B_21))), inference(resolution, [status(thm)], [c_20, c_89])).
% 11.12/4.16  tff(c_4032, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3949, c_96])).
% 11.12/4.16  tff(c_4052, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_390, c_4032])).
% 11.12/4.16  tff(c_4029, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(k2_pre_topc('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_pre_topc('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_3949, c_8])).
% 11.12/4.16  tff(c_4923, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_pre_topc('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_4029])).
% 11.12/4.16  tff(c_5002, plain, (~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_4923])).
% 11.12/4.16  tff(c_5006, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_390, c_5002])).
% 11.12/4.16  tff(c_5007, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(k2_pre_topc('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_4029])).
% 11.12/4.16  tff(c_2407, plain, (![B_187, B_188, A_189]: (k9_subset_1(B_187, B_188, k3_subset_1(B_187, A_189))=k7_subset_1(B_187, B_188, A_189) | ~m1_subset_1(B_188, k1_zfmisc_1(B_187)) | ~r1_tarski(A_189, B_187))), inference(resolution, [status(thm)], [c_20, c_1130])).
% 11.12/4.16  tff(c_14474, plain, (![A_328, B_329, A_330]: (k9_subset_1(A_328, k3_subset_1(A_328, B_329), k3_subset_1(A_328, A_330))=k7_subset_1(A_328, k3_subset_1(A_328, B_329), A_330) | ~r1_tarski(A_330, A_328) | ~m1_subset_1(B_329, k1_zfmisc_1(A_328)))), inference(resolution, [status(thm)], [c_8, c_2407])).
% 11.12/4.16  tff(c_14709, plain, (![A_331, A_332]: (k7_subset_1(A_331, k3_subset_1(A_331, A_332), A_332)=k3_subset_1(A_331, A_332) | ~r1_tarski(A_332, A_331) | ~m1_subset_1(A_332, k1_zfmisc_1(A_331)))), inference(superposition, [status(thm), theory('equality')], [c_14474, c_75])).
% 11.12/4.16  tff(c_14711, plain, (k7_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_5007, c_14709])).
% 11.12/4.16  tff(c_14732, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3980, c_1015, c_396, c_4052, c_4052, c_14711])).
% 11.12/4.16  tff(c_14734, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1792, c_14732])).
% 11.12/4.16  tff(c_14735, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 11.12/4.16  tff(c_14736, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_42])).
% 11.12/4.16  tff(c_14779, plain, (![A_341, B_342]: (k4_xboole_0(A_341, B_342)=k3_subset_1(A_341, B_342) | ~m1_subset_1(B_342, k1_zfmisc_1(A_341)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.12/4.16  tff(c_14791, plain, (k4_xboole_0(u1_struct_0('#skF_1'), '#skF_2')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_36, c_14779])).
% 11.12/4.16  tff(c_14799, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_14791, c_2])).
% 11.12/4.16  tff(c_14991, plain, (![A_356, B_357, C_358]: (k7_subset_1(A_356, B_357, C_358)=k4_xboole_0(B_357, C_358) | ~m1_subset_1(B_357, k1_zfmisc_1(A_356)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.12/4.16  tff(c_15076, plain, (![B_366, A_367, C_368]: (k7_subset_1(B_366, A_367, C_368)=k4_xboole_0(A_367, C_368) | ~r1_tarski(A_367, B_366))), inference(resolution, [status(thm)], [c_20, c_14991])).
% 11.12/4.16  tff(c_15097, plain, (![C_368]: (k7_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), C_368)=k4_xboole_0(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), C_368))), inference(resolution, [status(thm)], [c_14799, c_15076])).
% 11.12/4.16  tff(c_14737, plain, (![A_333, B_334, C_335]: (k9_subset_1(A_333, B_334, B_334)=B_334 | ~m1_subset_1(C_335, k1_zfmisc_1(A_333)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.12/4.16  tff(c_14745, plain, (![A_5, B_334]: (k9_subset_1(A_5, B_334, B_334)=B_334)), inference(resolution, [status(thm)], [c_6, c_14737])).
% 11.12/4.16  tff(c_15512, plain, (![A_397, B_398, C_399]: (k9_subset_1(A_397, B_398, k3_subset_1(A_397, C_399))=k7_subset_1(A_397, B_398, C_399) | ~m1_subset_1(C_399, k1_zfmisc_1(A_397)) | ~m1_subset_1(B_398, k1_zfmisc_1(A_397)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.12/4.16  tff(c_15552, plain, (![B_400]: (k9_subset_1(u1_struct_0('#skF_1'), B_400, k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k7_subset_1(u1_struct_0('#skF_1'), B_400, '#skF_2') | ~m1_subset_1(B_400, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_36, c_15512])).
% 11.12/4.16  tff(c_15566, plain, (k7_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_2')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_14745, c_15552])).
% 11.12/4.16  tff(c_15570, plain, (k4_xboole_0(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_2')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_15097, c_15566])).
% 11.12/4.16  tff(c_15966, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_15570])).
% 11.12/4.16  tff(c_15969, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_8, c_15966])).
% 11.12/4.16  tff(c_15976, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_15969])).
% 11.12/4.16  tff(c_15978, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_15570])).
% 11.12/4.16  tff(c_32, plain, (![B_40, D_46, C_44, A_32]: (k1_tops_1(B_40, D_46)=D_46 | ~v3_pre_topc(D_46, B_40) | ~m1_subset_1(D_46, k1_zfmisc_1(u1_struct_0(B_40))) | ~m1_subset_1(C_44, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(B_40) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.12/4.16  tff(c_16059, plain, (![C_417, A_418]: (~m1_subset_1(C_417, k1_zfmisc_1(u1_struct_0(A_418))) | ~l1_pre_topc(A_418) | ~v2_pre_topc(A_418))), inference(splitLeft, [status(thm)], [c_32])).
% 11.12/4.16  tff(c_16062, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_15978, c_16059])).
% 11.12/4.16  tff(c_16083, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_16062])).
% 11.12/4.16  tff(c_16092, plain, (![B_419, D_420]: (k1_tops_1(B_419, D_420)=D_420 | ~v3_pre_topc(D_420, B_419) | ~m1_subset_1(D_420, k1_zfmisc_1(u1_struct_0(B_419))) | ~l1_pre_topc(B_419))), inference(splitRight, [status(thm)], [c_32])).
% 11.12/4.16  tff(c_16113, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_16092])).
% 11.12/4.16  tff(c_16123, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_14736, c_16113])).
% 11.12/4.16  tff(c_28, plain, (![A_29, B_31]: (k7_subset_1(u1_struct_0(A_29), k2_pre_topc(A_29, B_31), k1_tops_1(A_29, B_31))=k2_tops_1(A_29, B_31) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.12/4.16  tff(c_16137, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16123, c_28])).
% 11.12/4.16  tff(c_16144, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_16137])).
% 11.12/4.16  tff(c_16146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14735, c_16144])).
% 11.12/4.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.12/4.16  
% 11.12/4.16  Inference rules
% 11.12/4.16  ----------------------
% 11.12/4.16  #Ref     : 0
% 11.12/4.16  #Sup     : 3787
% 11.12/4.16  #Fact    : 0
% 11.12/4.16  #Define  : 0
% 11.12/4.16  #Split   : 10
% 11.12/4.16  #Chain   : 0
% 11.12/4.16  #Close   : 0
% 11.12/4.16  
% 11.12/4.16  Ordering : KBO
% 11.12/4.16  
% 11.12/4.16  Simplification rules
% 11.12/4.16  ----------------------
% 11.12/4.16  #Subsume      : 158
% 11.12/4.16  #Demod        : 4219
% 11.12/4.16  #Tautology    : 1690
% 11.12/4.16  #SimpNegUnit  : 18
% 11.12/4.16  #BackRed      : 29
% 11.12/4.16  
% 11.12/4.16  #Partial instantiations: 0
% 11.12/4.16  #Strategies tried      : 1
% 11.12/4.16  
% 11.12/4.16  Timing (in seconds)
% 11.12/4.16  ----------------------
% 11.12/4.17  Preprocessing        : 0.34
% 11.12/4.17  Parsing              : 0.18
% 11.12/4.17  CNF conversion       : 0.02
% 11.12/4.17  Main loop            : 3.04
% 11.12/4.17  Inferencing          : 0.75
% 11.12/4.17  Reduction            : 1.46
% 11.12/4.17  Demodulation         : 1.21
% 11.12/4.17  BG Simplification    : 0.09
% 11.12/4.17  Subsumption          : 0.55
% 11.12/4.17  Abstraction          : 0.15
% 11.12/4.17  MUC search           : 0.00
% 11.12/4.17  Cooper               : 0.00
% 11.12/4.17  Total                : 3.44
% 11.12/4.17  Index Insertion      : 0.00
% 11.12/4.17  Index Deletion       : 0.00
% 11.12/4.17  Index Matching       : 0.00
% 11.12/4.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
