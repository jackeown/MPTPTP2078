%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:58 EST 2020

% Result     : Theorem 15.28s
% Output     : CNFRefutation 15.42s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 234 expanded)
%              Number of leaves         :   36 (  93 expanded)
%              Depth                    :   12
%              Number of atoms          :  214 ( 535 expanded)
%              Number of equality atoms :   56 (  95 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tops_1 > v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tops_1(B,A)
             => v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_tops_1)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
          <=> v2_tops_1(k2_pre_topc(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_461,plain,(
    ! [B_87,A_88] :
      ( v2_tops_1(B_87,A_88)
      | k1_tops_1(A_88,B_87) != k1_xboole_0
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_468,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_461])).

tff(c_472,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_468])).

tff(c_473,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_472])).

tff(c_624,plain,(
    ! [A_100,B_101] :
      ( m1_subset_1(k2_pre_topc(A_100,B_101),k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_638,plain,(
    ! [A_100,B_101] :
      ( r1_tarski(k2_pre_topc(A_100,B_101),u1_struct_0(A_100))
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(resolution,[status(thm)],[c_624,c_14])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2160,plain,(
    ! [A_205,B_206,C_207] :
      ( r1_tarski(k1_tops_1(A_205,B_206),k1_tops_1(A_205,C_207))
      | ~ r1_tarski(B_206,C_207)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(u1_struct_0(A_205)))
      | ~ m1_subset_1(B_206,k1_zfmisc_1(u1_struct_0(A_205)))
      | ~ l1_pre_topc(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10279,plain,(
    ! [A_335,B_336,C_337] :
      ( k4_xboole_0(k1_tops_1(A_335,B_336),k1_tops_1(A_335,C_337)) = k1_xboole_0
      | ~ r1_tarski(B_336,C_337)
      | ~ m1_subset_1(C_337,k1_zfmisc_1(u1_struct_0(A_335)))
      | ~ m1_subset_1(B_336,k1_zfmisc_1(u1_struct_0(A_335)))
      | ~ l1_pre_topc(A_335) ) ),
    inference(resolution,[status(thm)],[c_2160,c_6])).

tff(c_10288,plain,(
    ! [B_336] :
      ( k4_xboole_0(k1_tops_1('#skF_1',B_336),k1_tops_1('#skF_1','#skF_2')) = k1_xboole_0
      | ~ r1_tarski(B_336,'#skF_2')
      | ~ m1_subset_1(B_336,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_10279])).

tff(c_10732,plain,(
    ! [B_345] :
      ( k4_xboole_0(k1_tops_1('#skF_1',B_345),k1_tops_1('#skF_1','#skF_2')) = k1_xboole_0
      | ~ r1_tarski(B_345,'#skF_2')
      | ~ m1_subset_1(B_345,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_10288])).

tff(c_11076,plain,(
    ! [A_351] :
      ( k4_xboole_0(k1_tops_1('#skF_1',A_351),k1_tops_1('#skF_1','#skF_2')) = k1_xboole_0
      | ~ r1_tarski(A_351,'#skF_2')
      | ~ r1_tarski(A_351,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_16,c_10732])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k4_xboole_0(B_6,A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_11091,plain,(
    ! [A_351] :
      ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_xboole_0)
      | ~ r1_tarski(A_351,'#skF_2')
      | ~ r1_tarski(A_351,u1_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11076,c_8])).

tff(c_11100,plain,(
    ! [A_351] :
      ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_xboole_0)
      | ~ r1_tarski(A_351,'#skF_2')
      | ~ r1_tarski(A_351,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_473,c_11091])).

tff(c_11102,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_11100])).

tff(c_11106,plain,(
    k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_11102])).

tff(c_349,plain,(
    ! [B_83,A_84] :
      ( r1_tarski(B_83,k2_pre_topc(A_84,B_83))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_354,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_349])).

tff(c_358,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_354])).

tff(c_42,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1092,plain,(
    ! [A_137,B_138] :
      ( v2_tops_1(k2_pre_topc(A_137,B_138),A_137)
      | ~ v3_tops_1(B_138,A_137)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ l1_pre_topc(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1101,plain,
    ( v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_1092])).

tff(c_1107,plain,(
    v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_1101])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k2_pre_topc(A_15,B_16),k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_833,plain,(
    ! [A_128,B_129] :
      ( k1_tops_1(A_128,B_129) = k1_xboole_0
      | ~ v2_tops_1(B_129,A_128)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_4304,plain,(
    ! [A_247,B_248] :
      ( k1_tops_1(A_247,k2_pre_topc(A_247,B_248)) = k1_xboole_0
      | ~ v2_tops_1(k2_pre_topc(A_247,B_248),A_247)
      | ~ m1_subset_1(B_248,k1_zfmisc_1(u1_struct_0(A_247)))
      | ~ l1_pre_topc(A_247) ) ),
    inference(resolution,[status(thm)],[c_18,c_833])).

tff(c_4308,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_xboole_0
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1107,c_4304])).

tff(c_4312,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_4308])).

tff(c_20357,plain,(
    ! [A_444,B_445,A_446] :
      ( k4_xboole_0(k1_tops_1(A_444,B_445),k1_tops_1(A_444,A_446)) = k1_xboole_0
      | ~ r1_tarski(B_445,A_446)
      | ~ m1_subset_1(B_445,k1_zfmisc_1(u1_struct_0(A_444)))
      | ~ l1_pre_topc(A_444)
      | ~ r1_tarski(A_446,u1_struct_0(A_444)) ) ),
    inference(resolution,[status(thm)],[c_16,c_10279])).

tff(c_20366,plain,(
    ! [A_446] :
      ( k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',A_446)) = k1_xboole_0
      | ~ r1_tarski('#skF_2',A_446)
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_446,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_44,c_20357])).

tff(c_20375,plain,(
    ! [A_447] :
      ( k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',A_447)) = k1_xboole_0
      | ~ r1_tarski('#skF_2',A_447)
      | ~ r1_tarski(A_447,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_20366])).

tff(c_20404,plain,
    ( k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4312,c_20375])).

tff(c_20412,plain,
    ( k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_20404])).

tff(c_20413,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_11106,c_20412])).

tff(c_20416,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_638,c_20413])).

tff(c_20423,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_20416])).

tff(c_20425,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_11100])).

tff(c_20432,plain,(
    k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20425,c_6])).

tff(c_746,plain,(
    ! [A_116,B_117] :
      ( m1_subset_1(k2_tops_1(A_116,B_117),k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1228,plain,(
    ! [A_151,B_152] :
      ( r1_tarski(k2_tops_1(A_151,B_152),u1_struct_0(A_151))
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151) ) ),
    inference(resolution,[status(thm)],[c_746,c_14])).

tff(c_5179,plain,(
    ! [A_262,B_263] :
      ( k4_xboole_0(k2_tops_1(A_262,B_263),u1_struct_0(A_262)) = k1_xboole_0
      | ~ m1_subset_1(B_263,k1_zfmisc_1(u1_struct_0(A_262)))
      | ~ l1_pre_topc(A_262) ) ),
    inference(resolution,[status(thm)],[c_1228,c_6])).

tff(c_5188,plain,
    ( k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) = k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_5179])).

tff(c_5194,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_5188])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] :
      ( k7_subset_1(A_10,B_11,C_12) = k4_xboole_0(B_11,C_12)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6899,plain,(
    ! [A_296,B_297,C_298] :
      ( k7_subset_1(u1_struct_0(A_296),k2_pre_topc(A_296,B_297),C_298) = k4_xboole_0(k2_pre_topc(A_296,B_297),C_298)
      | ~ m1_subset_1(B_297,k1_zfmisc_1(u1_struct_0(A_296)))
      | ~ l1_pre_topc(A_296) ) ),
    inference(resolution,[status(thm)],[c_624,c_12])).

tff(c_6908,plain,(
    ! [C_298] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_298) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_298)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_6899])).

tff(c_6915,plain,(
    ! [C_299] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_299) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_299) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6908])).

tff(c_32,plain,(
    ! [A_28,B_30] :
      ( k7_subset_1(u1_struct_0(A_28),k2_pre_topc(A_28,B_30),k1_tops_1(A_28,B_30)) = k2_tops_1(A_28,B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6922,plain,
    ( k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6915,c_32])).

tff(c_6939,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_6922])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9] : k4_xboole_0(k4_xboole_0(A_7,B_8),C_9) = k4_xboole_0(A_7,k2_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_25307,plain,(
    ! [C_534] : k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),C_534)) = k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),C_534) ),
    inference(superposition,[status(thm),theory(equality)],[c_6939,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1247,plain,(
    ! [A_153,B_154] :
      ( r1_tarski(k2_pre_topc(A_153,B_154),u1_struct_0(A_153))
      | ~ m1_subset_1(B_154,k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ l1_pre_topc(A_153) ) ),
    inference(resolution,[status(thm)],[c_624,c_14])).

tff(c_5933,plain,(
    ! [A_284,B_285] :
      ( k4_xboole_0(k2_pre_topc(A_284,B_285),u1_struct_0(A_284)) = k1_xboole_0
      | ~ m1_subset_1(B_285,k1_zfmisc_1(u1_struct_0(A_284)))
      | ~ l1_pre_topc(A_284) ) ),
    inference(resolution,[status(thm)],[c_1247,c_6])).

tff(c_5942,plain,
    ( k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1')) = k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_5933])).

tff(c_5948,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_5942])).

tff(c_5972,plain,(
    ! [C_286] : k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k2_xboole_0(u1_struct_0('#skF_1'),C_286)) = k4_xboole_0(k1_xboole_0,C_286) ),
    inference(superposition,[status(thm),theory(equality)],[c_5948,c_10])).

tff(c_6058,plain,(
    ! [B_2] : k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k2_xboole_0(B_2,u1_struct_0('#skF_1'))) = k4_xboole_0(k1_xboole_0,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5972])).

tff(c_25373,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) = k4_xboole_0(k1_xboole_0,k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_25307,c_6058])).

tff(c_25509,plain,(
    k4_xboole_0(k1_xboole_0,k1_tops_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5194,c_25373])).

tff(c_104,plain,(
    ! [A_52,B_53] :
      ( k1_xboole_0 = A_52
      | ~ r1_tarski(A_52,k4_xboole_0(B_53,A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_112,plain,(
    ! [A_3,B_53] :
      ( k1_xboole_0 = A_3
      | k4_xboole_0(A_3,k4_xboole_0(B_53,A_3)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_104])).

tff(c_25587,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_25509,c_112])).

tff(c_25611,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20432,c_25587])).

tff(c_25613,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_473,c_25611])).

tff(c_25614,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_472])).

tff(c_26323,plain,(
    ! [A_592,B_593] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_592),B_593),A_592)
      | ~ v2_tops_1(B_593,A_592)
      | ~ m1_subset_1(B_593,k1_zfmisc_1(u1_struct_0(A_592)))
      | ~ l1_pre_topc(A_592) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_40,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_26326,plain,
    ( ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26323,c_40])).

tff(c_26330,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_25614,c_26326])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:48:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.28/6.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.28/6.79  
% 15.28/6.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.28/6.79  %$ v3_tops_1 > v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 15.28/6.79  
% 15.28/6.79  %Foreground sorts:
% 15.28/6.79  
% 15.28/6.79  
% 15.28/6.79  %Background operators:
% 15.28/6.79  
% 15.28/6.79  
% 15.28/6.79  %Foreground operators:
% 15.28/6.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.28/6.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.28/6.79  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 15.28/6.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.28/6.79  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 15.28/6.79  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 15.28/6.79  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 15.28/6.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.28/6.79  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 15.28/6.79  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 15.28/6.79  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 15.28/6.79  tff('#skF_2', type, '#skF_2': $i).
% 15.28/6.79  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 15.28/6.79  tff('#skF_1', type, '#skF_1': $i).
% 15.28/6.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.28/6.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.28/6.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.28/6.79  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 15.28/6.79  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 15.28/6.79  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 15.28/6.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.28/6.79  
% 15.42/6.81  tff(f_120, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_tops_1)).
% 15.42/6.81  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 15.42/6.81  tff(f_51, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 15.42/6.81  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 15.42/6.81  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 15.42/6.81  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 15.42/6.81  tff(f_35, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 15.42/6.81  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 15.42/6.81  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) <=> v2_tops_1(k2_pre_topc(A, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_1)).
% 15.42/6.81  tff(f_82, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 15.42/6.81  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 15.42/6.81  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 15.42/6.81  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 15.42/6.81  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 15.42/6.81  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_1)).
% 15.42/6.81  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 15.42/6.81  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 15.42/6.81  tff(c_461, plain, (![B_87, A_88]: (v2_tops_1(B_87, A_88) | k1_tops_1(A_88, B_87)!=k1_xboole_0 | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_110])).
% 15.42/6.81  tff(c_468, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_461])).
% 15.42/6.81  tff(c_472, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_468])).
% 15.42/6.81  tff(c_473, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_472])).
% 15.42/6.81  tff(c_624, plain, (![A_100, B_101]: (m1_subset_1(k2_pre_topc(A_100, B_101), k1_zfmisc_1(u1_struct_0(A_100))) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.42/6.81  tff(c_14, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.42/6.81  tff(c_638, plain, (![A_100, B_101]: (r1_tarski(k2_pre_topc(A_100, B_101), u1_struct_0(A_100)) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(resolution, [status(thm)], [c_624, c_14])).
% 15.42/6.81  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.42/6.81  tff(c_16, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.42/6.81  tff(c_2160, plain, (![A_205, B_206, C_207]: (r1_tarski(k1_tops_1(A_205, B_206), k1_tops_1(A_205, C_207)) | ~r1_tarski(B_206, C_207) | ~m1_subset_1(C_207, k1_zfmisc_1(u1_struct_0(A_205))) | ~m1_subset_1(B_206, k1_zfmisc_1(u1_struct_0(A_205))) | ~l1_pre_topc(A_205))), inference(cnfTransformation, [status(thm)], [f_101])).
% 15.42/6.81  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.42/6.81  tff(c_10279, plain, (![A_335, B_336, C_337]: (k4_xboole_0(k1_tops_1(A_335, B_336), k1_tops_1(A_335, C_337))=k1_xboole_0 | ~r1_tarski(B_336, C_337) | ~m1_subset_1(C_337, k1_zfmisc_1(u1_struct_0(A_335))) | ~m1_subset_1(B_336, k1_zfmisc_1(u1_struct_0(A_335))) | ~l1_pre_topc(A_335))), inference(resolution, [status(thm)], [c_2160, c_6])).
% 15.42/6.81  tff(c_10288, plain, (![B_336]: (k4_xboole_0(k1_tops_1('#skF_1', B_336), k1_tops_1('#skF_1', '#skF_2'))=k1_xboole_0 | ~r1_tarski(B_336, '#skF_2') | ~m1_subset_1(B_336, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_10279])).
% 15.42/6.81  tff(c_10732, plain, (![B_345]: (k4_xboole_0(k1_tops_1('#skF_1', B_345), k1_tops_1('#skF_1', '#skF_2'))=k1_xboole_0 | ~r1_tarski(B_345, '#skF_2') | ~m1_subset_1(B_345, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_10288])).
% 15.42/6.81  tff(c_11076, plain, (![A_351]: (k4_xboole_0(k1_tops_1('#skF_1', A_351), k1_tops_1('#skF_1', '#skF_2'))=k1_xboole_0 | ~r1_tarski(A_351, '#skF_2') | ~r1_tarski(A_351, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_16, c_10732])).
% 15.42/6.81  tff(c_8, plain, (![A_5, B_6]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k4_xboole_0(B_6, A_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.42/6.81  tff(c_11091, plain, (![A_351]: (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_xboole_0) | ~r1_tarski(A_351, '#skF_2') | ~r1_tarski(A_351, u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_11076, c_8])).
% 15.42/6.81  tff(c_11100, plain, (![A_351]: (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_xboole_0) | ~r1_tarski(A_351, '#skF_2') | ~r1_tarski(A_351, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_473, c_11091])).
% 15.42/6.81  tff(c_11102, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_11100])).
% 15.42/6.81  tff(c_11106, plain, (k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_11102])).
% 15.42/6.81  tff(c_349, plain, (![B_83, A_84]: (r1_tarski(B_83, k2_pre_topc(A_84, B_83)) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_58])).
% 15.42/6.81  tff(c_354, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_349])).
% 15.42/6.81  tff(c_358, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_354])).
% 15.42/6.81  tff(c_42, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 15.42/6.81  tff(c_1092, plain, (![A_137, B_138]: (v2_tops_1(k2_pre_topc(A_137, B_138), A_137) | ~v3_tops_1(B_138, A_137) | ~m1_subset_1(B_138, k1_zfmisc_1(u1_struct_0(A_137))) | ~l1_pre_topc(A_137))), inference(cnfTransformation, [status(thm)], [f_76])).
% 15.42/6.81  tff(c_1101, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_1092])).
% 15.42/6.81  tff(c_1107, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_1101])).
% 15.42/6.81  tff(c_18, plain, (![A_15, B_16]: (m1_subset_1(k2_pre_topc(A_15, B_16), k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.42/6.81  tff(c_833, plain, (![A_128, B_129]: (k1_tops_1(A_128, B_129)=k1_xboole_0 | ~v2_tops_1(B_129, A_128) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_110])).
% 15.42/6.81  tff(c_4304, plain, (![A_247, B_248]: (k1_tops_1(A_247, k2_pre_topc(A_247, B_248))=k1_xboole_0 | ~v2_tops_1(k2_pre_topc(A_247, B_248), A_247) | ~m1_subset_1(B_248, k1_zfmisc_1(u1_struct_0(A_247))) | ~l1_pre_topc(A_247))), inference(resolution, [status(thm)], [c_18, c_833])).
% 15.42/6.81  tff(c_4308, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_xboole_0 | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1107, c_4304])).
% 15.42/6.81  tff(c_4312, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_4308])).
% 15.42/6.81  tff(c_20357, plain, (![A_444, B_445, A_446]: (k4_xboole_0(k1_tops_1(A_444, B_445), k1_tops_1(A_444, A_446))=k1_xboole_0 | ~r1_tarski(B_445, A_446) | ~m1_subset_1(B_445, k1_zfmisc_1(u1_struct_0(A_444))) | ~l1_pre_topc(A_444) | ~r1_tarski(A_446, u1_struct_0(A_444)))), inference(resolution, [status(thm)], [c_16, c_10279])).
% 15.42/6.81  tff(c_20366, plain, (![A_446]: (k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', A_446))=k1_xboole_0 | ~r1_tarski('#skF_2', A_446) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_446, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_44, c_20357])).
% 15.42/6.81  tff(c_20375, plain, (![A_447]: (k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', A_447))=k1_xboole_0 | ~r1_tarski('#skF_2', A_447) | ~r1_tarski(A_447, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_20366])).
% 15.42/6.81  tff(c_20404, plain, (k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k1_xboole_0)=k1_xboole_0 | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4312, c_20375])).
% 15.42/6.81  tff(c_20412, plain, (k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_358, c_20404])).
% 15.42/6.81  tff(c_20413, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_11106, c_20412])).
% 15.42/6.81  tff(c_20416, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_638, c_20413])).
% 15.42/6.81  tff(c_20423, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_20416])).
% 15.42/6.81  tff(c_20425, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_11100])).
% 15.42/6.81  tff(c_20432, plain, (k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_20425, c_6])).
% 15.42/6.81  tff(c_746, plain, (![A_116, B_117]: (m1_subset_1(k2_tops_1(A_116, B_117), k1_zfmisc_1(u1_struct_0(A_116))) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_82])).
% 15.42/6.81  tff(c_1228, plain, (![A_151, B_152]: (r1_tarski(k2_tops_1(A_151, B_152), u1_struct_0(A_151)) | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0(A_151))) | ~l1_pre_topc(A_151))), inference(resolution, [status(thm)], [c_746, c_14])).
% 15.42/6.81  tff(c_5179, plain, (![A_262, B_263]: (k4_xboole_0(k2_tops_1(A_262, B_263), u1_struct_0(A_262))=k1_xboole_0 | ~m1_subset_1(B_263, k1_zfmisc_1(u1_struct_0(A_262))) | ~l1_pre_topc(A_262))), inference(resolution, [status(thm)], [c_1228, c_6])).
% 15.42/6.81  tff(c_5188, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_5179])).
% 15.42/6.81  tff(c_5194, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_5188])).
% 15.42/6.81  tff(c_12, plain, (![A_10, B_11, C_12]: (k7_subset_1(A_10, B_11, C_12)=k4_xboole_0(B_11, C_12) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.42/6.81  tff(c_6899, plain, (![A_296, B_297, C_298]: (k7_subset_1(u1_struct_0(A_296), k2_pre_topc(A_296, B_297), C_298)=k4_xboole_0(k2_pre_topc(A_296, B_297), C_298) | ~m1_subset_1(B_297, k1_zfmisc_1(u1_struct_0(A_296))) | ~l1_pre_topc(A_296))), inference(resolution, [status(thm)], [c_624, c_12])).
% 15.42/6.81  tff(c_6908, plain, (![C_298]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_298)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_298) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_6899])).
% 15.42/6.81  tff(c_6915, plain, (![C_299]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_299)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_299))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_6908])).
% 15.42/6.81  tff(c_32, plain, (![A_28, B_30]: (k7_subset_1(u1_struct_0(A_28), k2_pre_topc(A_28, B_30), k1_tops_1(A_28, B_30))=k2_tops_1(A_28, B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_89])).
% 15.42/6.81  tff(c_6922, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6915, c_32])).
% 15.42/6.81  tff(c_6939, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_6922])).
% 15.42/6.81  tff(c_10, plain, (![A_7, B_8, C_9]: (k4_xboole_0(k4_xboole_0(A_7, B_8), C_9)=k4_xboole_0(A_7, k2_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.42/6.81  tff(c_25307, plain, (![C_534]: (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), C_534))=k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), C_534))), inference(superposition, [status(thm), theory('equality')], [c_6939, c_10])).
% 15.42/6.81  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 15.42/6.81  tff(c_1247, plain, (![A_153, B_154]: (r1_tarski(k2_pre_topc(A_153, B_154), u1_struct_0(A_153)) | ~m1_subset_1(B_154, k1_zfmisc_1(u1_struct_0(A_153))) | ~l1_pre_topc(A_153))), inference(resolution, [status(thm)], [c_624, c_14])).
% 15.42/6.81  tff(c_5933, plain, (![A_284, B_285]: (k4_xboole_0(k2_pre_topc(A_284, B_285), u1_struct_0(A_284))=k1_xboole_0 | ~m1_subset_1(B_285, k1_zfmisc_1(u1_struct_0(A_284))) | ~l1_pre_topc(A_284))), inference(resolution, [status(thm)], [c_1247, c_6])).
% 15.42/6.81  tff(c_5942, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_5933])).
% 15.42/6.81  tff(c_5948, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_5942])).
% 15.42/6.81  tff(c_5972, plain, (![C_286]: (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k2_xboole_0(u1_struct_0('#skF_1'), C_286))=k4_xboole_0(k1_xboole_0, C_286))), inference(superposition, [status(thm), theory('equality')], [c_5948, c_10])).
% 15.42/6.81  tff(c_6058, plain, (![B_2]: (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k2_xboole_0(B_2, u1_struct_0('#skF_1')))=k4_xboole_0(k1_xboole_0, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_5972])).
% 15.42/6.81  tff(c_25373, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))=k4_xboole_0(k1_xboole_0, k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_25307, c_6058])).
% 15.42/6.81  tff(c_25509, plain, (k4_xboole_0(k1_xboole_0, k1_tops_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5194, c_25373])).
% 15.42/6.81  tff(c_104, plain, (![A_52, B_53]: (k1_xboole_0=A_52 | ~r1_tarski(A_52, k4_xboole_0(B_53, A_52)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.42/6.81  tff(c_112, plain, (![A_3, B_53]: (k1_xboole_0=A_3 | k4_xboole_0(A_3, k4_xboole_0(B_53, A_3))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_104])).
% 15.42/6.81  tff(c_25587, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k1_xboole_0)!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_25509, c_112])).
% 15.42/6.81  tff(c_25611, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20432, c_25587])).
% 15.42/6.81  tff(c_25613, plain, $false, inference(negUnitSimplification, [status(thm)], [c_473, c_25611])).
% 15.42/6.81  tff(c_25614, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_472])).
% 15.42/6.81  tff(c_26323, plain, (![A_592, B_593]: (v1_tops_1(k3_subset_1(u1_struct_0(A_592), B_593), A_592) | ~v2_tops_1(B_593, A_592) | ~m1_subset_1(B_593, k1_zfmisc_1(u1_struct_0(A_592))) | ~l1_pre_topc(A_592))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.42/6.81  tff(c_40, plain, (~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 15.42/6.81  tff(c_26326, plain, (~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26323, c_40])).
% 15.42/6.81  tff(c_26330, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_25614, c_26326])).
% 15.42/6.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.42/6.81  
% 15.42/6.81  Inference rules
% 15.42/6.81  ----------------------
% 15.42/6.81  #Ref     : 0
% 15.42/6.81  #Sup     : 6412
% 15.42/6.81  #Fact    : 0
% 15.42/6.81  #Define  : 0
% 15.42/6.81  #Split   : 13
% 15.42/6.82  #Chain   : 0
% 15.42/6.82  #Close   : 0
% 15.42/6.82  
% 15.42/6.82  Ordering : KBO
% 15.42/6.82  
% 15.42/6.82  Simplification rules
% 15.42/6.82  ----------------------
% 15.42/6.82  #Subsume      : 1984
% 15.42/6.82  #Demod        : 3314
% 15.42/6.82  #Tautology    : 1432
% 15.42/6.82  #SimpNegUnit  : 29
% 15.42/6.82  #BackRed      : 14
% 15.42/6.82  
% 15.42/6.82  #Partial instantiations: 0
% 15.42/6.82  #Strategies tried      : 1
% 15.42/6.82  
% 15.42/6.82  Timing (in seconds)
% 15.42/6.82  ----------------------
% 15.43/6.82  Preprocessing        : 0.34
% 15.43/6.82  Parsing              : 0.18
% 15.43/6.82  CNF conversion       : 0.02
% 15.43/6.82  Main loop            : 5.71
% 15.43/6.82  Inferencing          : 1.08
% 15.43/6.82  Reduction            : 3.43
% 15.43/6.82  Demodulation         : 3.08
% 15.43/6.82  BG Simplification    : 0.12
% 15.43/6.82  Subsumption          : 0.85
% 15.43/6.82  Abstraction          : 0.18
% 15.43/6.82  MUC search           : 0.00
% 15.43/6.82  Cooper               : 0.00
% 15.43/6.82  Total                : 6.09
% 15.43/6.82  Index Insertion      : 0.00
% 15.43/6.82  Index Deletion       : 0.00
% 15.43/6.82  Index Matching       : 0.00
% 15.43/6.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
