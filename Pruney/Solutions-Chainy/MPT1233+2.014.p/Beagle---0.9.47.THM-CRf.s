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
% DateTime   : Thu Dec  3 10:20:31 EST 2020

% Result     : Theorem 4.02s
% Output     : CNFRefutation 4.02s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 222 expanded)
%              Number of leaves         :   51 (  94 expanded)
%              Depth                    :   16
%              Number of atoms          :  196 ( 369 expanded)
%              Number of equality atoms :   57 ( 114 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_191,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_113,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_93,axiom,(
    ! [A] : r1_tarski(k1_tarski(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_67,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_73,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
        & r1_xboole_0(C,A)
        & r1_xboole_0(D,B) )
     => C = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_128,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_145,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_153,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_149,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_177,axiom,(
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

tff(f_117,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_184,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_28,plain,(
    ! [A_21] : r1_xboole_0(A_21,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_78,plain,(
    k1_tops_1('#skF_5',k2_struct_0('#skF_5')) != k2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_50,plain,(
    ! [A_35] : ~ v1_xboole_0(k1_zfmisc_1(A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_38,plain,(
    ! [A_30] : r1_tarski(k1_tarski(A_30),k1_zfmisc_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_145,plain,(
    ! [A_79,B_80,C_81] :
      ( ~ r1_xboole_0(A_79,B_80)
      | ~ r2_hidden(C_81,k3_xboole_0(A_79,B_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_150,plain,(
    ! [A_79,B_80,B_2] :
      ( ~ r1_xboole_0(A_79,B_80)
      | r1_tarski(k3_xboole_0(A_79,B_80),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_145])).

tff(c_20,plain,(
    ! [A_16] : k2_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),A_6)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_458,plain,(
    ! [C_117,B_118,A_119] :
      ( r2_hidden(C_117,B_118)
      | ~ r2_hidden(C_117,A_119)
      | ~ r1_tarski(A_119,B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1210,plain,(
    ! [A_180,B_181,B_182] :
      ( r2_hidden('#skF_2'(A_180,B_181),B_182)
      | ~ r1_tarski(A_180,B_182)
      | r1_xboole_0(A_180,B_181) ) ),
    inference(resolution,[status(thm)],[c_14,c_458])).

tff(c_166,plain,(
    ! [A_86,B_87] : k4_xboole_0(A_86,k4_xboole_0(A_86,B_87)) = k3_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    ! [A_20] : k4_xboole_0(k1_xboole_0,A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_208,plain,(
    ! [B_88] : k3_xboole_0(k1_xboole_0,B_88) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_26])).

tff(c_18,plain,(
    ! [A_11,B_12,C_15] :
      ( ~ r1_xboole_0(A_11,B_12)
      | ~ r2_hidden(C_15,k3_xboole_0(A_11,B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_213,plain,(
    ! [B_88,C_15] :
      ( ~ r1_xboole_0(k1_xboole_0,B_88)
      | ~ r2_hidden(C_15,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_18])).

tff(c_237,plain,(
    ! [C_15] : ~ r2_hidden(C_15,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_213])).

tff(c_1235,plain,(
    ! [A_180,B_181] :
      ( ~ r1_tarski(A_180,k1_xboole_0)
      | r1_xboole_0(A_180,B_181) ) ),
    inference(resolution,[status(thm)],[c_1210,c_237])).

tff(c_1349,plain,(
    ! [C_192,B_193,D_194,A_195] :
      ( C_192 = B_193
      | ~ r1_xboole_0(D_194,B_193)
      | ~ r1_xboole_0(C_192,A_195)
      | k2_xboole_0(C_192,D_194) != k2_xboole_0(A_195,B_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1359,plain,(
    ! [C_192,A_195,A_21] :
      ( k1_xboole_0 = C_192
      | ~ r1_xboole_0(C_192,A_195)
      | k2_xboole_0(C_192,A_21) != k2_xboole_0(A_195,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28,c_1349])).

tff(c_1368,plain,(
    ! [C_196,A_197,A_198] :
      ( k1_xboole_0 = C_196
      | ~ r1_xboole_0(C_196,A_197)
      | k2_xboole_0(C_196,A_198) != A_197 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1359])).

tff(c_1393,plain,(
    ! [A_201,A_202,B_203] :
      ( k1_xboole_0 = A_201
      | k2_xboole_0(A_201,A_202) != B_203
      | ~ r1_tarski(A_201,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1235,c_1368])).

tff(c_1402,plain,(
    ! [B_205] :
      ( k1_xboole_0 = B_205
      | ~ r1_tarski(B_205,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1393])).

tff(c_1420,plain,(
    ! [A_206,B_207] :
      ( k3_xboole_0(A_206,B_207) = k1_xboole_0
      | ~ r1_xboole_0(A_206,B_207) ) ),
    inference(resolution,[status(thm)],[c_150,c_1402])).

tff(c_1441,plain,(
    ! [A_21] : k3_xboole_0(A_21,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_1420])).

tff(c_279,plain,(
    ! [A_99,B_100] :
      ( k4_xboole_0(k2_xboole_0(A_99,B_100),B_100) = A_99
      | ~ r1_xboole_0(A_99,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_291,plain,(
    ! [A_16] :
      ( k4_xboole_0(A_16,k1_xboole_0) = A_16
      | ~ r1_xboole_0(A_16,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_279])).

tff(c_296,plain,(
    ! [A_101] : k4_xboole_0(A_101,k1_xboole_0) = A_101 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_291])).

tff(c_24,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_344,plain,(
    ! [A_103] : k4_xboole_0(A_103,A_103) = k3_xboole_0(A_103,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_24])).

tff(c_34,plain,(
    ! [A_28,B_29] :
      ( r2_hidden(A_28,B_29)
      | k4_xboole_0(k1_tarski(A_28),B_29) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_358,plain,(
    ! [A_28] :
      ( r2_hidden(A_28,k1_tarski(A_28))
      | k3_xboole_0(k1_tarski(A_28),k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_34])).

tff(c_1503,plain,(
    ! [A_209] : r2_hidden(A_209,k1_tarski(A_209)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1441,c_358])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1942,plain,(
    ! [A_239,B_240] :
      ( r2_hidden(A_239,B_240)
      | ~ r1_tarski(k1_tarski(A_239),B_240) ) ),
    inference(resolution,[status(thm)],[c_1503,c_2])).

tff(c_1958,plain,(
    ! [A_241] : r2_hidden(A_241,k1_zfmisc_1(A_241)) ),
    inference(resolution,[status(thm)],[c_38,c_1942])).

tff(c_40,plain,(
    ! [B_32,A_31] :
      ( m1_subset_1(B_32,A_31)
      | ~ r2_hidden(B_32,A_31)
      | v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1966,plain,(
    ! [A_241] :
      ( m1_subset_1(A_241,k1_zfmisc_1(A_241))
      | v1_xboole_0(k1_zfmisc_1(A_241)) ) ),
    inference(resolution,[status(thm)],[c_1958,c_40])).

tff(c_1971,plain,(
    ! [A_241] : m1_subset_1(A_241,k1_zfmisc_1(A_241)) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1966])).

tff(c_295,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_291])).

tff(c_58,plain,(
    ! [A_42] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_42)) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_555,plain,(
    ! [A_129,B_130] :
      ( k4_xboole_0(A_129,B_130) = k3_subset_1(A_129,B_130)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(A_129)) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_568,plain,(
    ! [A_42] : k4_xboole_0(A_42,k1_xboole_0) = k3_subset_1(A_42,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_58,c_555])).

tff(c_573,plain,(
    ! [A_42] : k3_subset_1(A_42,k1_xboole_0) = A_42 ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_568])).

tff(c_82,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_80,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1021,plain,(
    ! [B_170,A_171] :
      ( v4_pre_topc(B_170,A_171)
      | ~ v1_xboole_0(B_170)
      | ~ m1_subset_1(B_170,k1_zfmisc_1(u1_struct_0(A_171)))
      | ~ l1_pre_topc(A_171)
      | ~ v2_pre_topc(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1047,plain,(
    ! [A_171] :
      ( v4_pre_topc(k1_xboole_0,A_171)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_171)
      | ~ v2_pre_topc(A_171) ) ),
    inference(resolution,[status(thm)],[c_58,c_1021])).

tff(c_1074,plain,(
    ! [A_174] :
      ( v4_pre_topc(k1_xboole_0,A_174)
      | ~ l1_pre_topc(A_174)
      | ~ v2_pre_topc(A_174) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1047])).

tff(c_66,plain,(
    ! [A_50] :
      ( l1_struct_0(A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_105,plain,(
    ! [A_67] :
      ( u1_struct_0(A_67) = k2_struct_0(A_67)
      | ~ l1_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_110,plain,(
    ! [A_68] :
      ( u1_struct_0(A_68) = k2_struct_0(A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_66,c_105])).

tff(c_114,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_110])).

tff(c_758,plain,(
    ! [A_145,B_146] :
      ( k2_pre_topc(A_145,B_146) = B_146
      | ~ v4_pre_topc(B_146,A_145)
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_780,plain,(
    ! [B_146] :
      ( k2_pre_topc('#skF_5',B_146) = B_146
      | ~ v4_pre_topc(B_146,'#skF_5')
      | ~ m1_subset_1(B_146,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_758])).

tff(c_891,plain,(
    ! [B_152] :
      ( k2_pre_topc('#skF_5',B_152) = B_152
      | ~ v4_pre_topc(B_152,'#skF_5')
      | ~ m1_subset_1(B_152,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_780])).

tff(c_926,plain,
    ( k2_pre_topc('#skF_5',k1_xboole_0) = k1_xboole_0
    | ~ v4_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_891])).

tff(c_942,plain,(
    ~ v4_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_926])).

tff(c_1077,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_1074,c_942])).

tff(c_1084,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_1077])).

tff(c_1085,plain,(
    k2_pre_topc('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_926])).

tff(c_583,plain,(
    ! [A_132,B_133] :
      ( k3_subset_1(A_132,k3_subset_1(A_132,B_133)) = B_133
      | ~ m1_subset_1(B_133,k1_zfmisc_1(A_132)) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_592,plain,(
    ! [A_42] : k3_subset_1(A_42,k3_subset_1(A_42,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_583])).

tff(c_597,plain,(
    ! [A_42] : k3_subset_1(A_42,A_42) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_592])).

tff(c_2110,plain,(
    ! [A_249,B_250] :
      ( k3_subset_1(u1_struct_0(A_249),k2_pre_topc(A_249,k3_subset_1(u1_struct_0(A_249),B_250))) = k1_tops_1(A_249,B_250)
      | ~ m1_subset_1(B_250,k1_zfmisc_1(u1_struct_0(A_249)))
      | ~ l1_pre_topc(A_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_2139,plain,(
    ! [B_250] :
      ( k3_subset_1(k2_struct_0('#skF_5'),k2_pre_topc('#skF_5',k3_subset_1(u1_struct_0('#skF_5'),B_250))) = k1_tops_1('#skF_5',B_250)
      | ~ m1_subset_1(B_250,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_2110])).

tff(c_2181,plain,(
    ! [B_255] :
      ( k3_subset_1(k2_struct_0('#skF_5'),k2_pre_topc('#skF_5',k3_subset_1(k2_struct_0('#skF_5'),B_255))) = k1_tops_1('#skF_5',B_255)
      | ~ m1_subset_1(B_255,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_114,c_114,c_2139])).

tff(c_2206,plain,
    ( k3_subset_1(k2_struct_0('#skF_5'),k2_pre_topc('#skF_5',k1_xboole_0)) = k1_tops_1('#skF_5',k2_struct_0('#skF_5'))
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_597,c_2181])).

tff(c_2215,plain,(
    k1_tops_1('#skF_5',k2_struct_0('#skF_5')) = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1971,c_573,c_1085,c_2206])).

tff(c_2217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2215])).

tff(c_2219,plain,(
    ! [B_256] : ~ r1_xboole_0(k1_xboole_0,B_256) ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_2224,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_28,c_2219])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:08:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.02/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.02/1.72  
% 4.02/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.02/1.72  %$ v4_pre_topc > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_2 > #skF_1
% 4.02/1.72  
% 4.02/1.72  %Foreground sorts:
% 4.02/1.72  
% 4.02/1.72  
% 4.02/1.72  %Background operators:
% 4.02/1.72  
% 4.02/1.72  
% 4.02/1.72  %Foreground operators:
% 4.02/1.72  tff('#skF_4', type, '#skF_4': $i > $i).
% 4.02/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.02/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.02/1.72  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.02/1.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.02/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.02/1.72  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.02/1.72  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.02/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.02/1.72  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.02/1.72  tff('#skF_5', type, '#skF_5': $i).
% 4.02/1.72  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.02/1.72  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.02/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.02/1.72  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.02/1.72  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.02/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.02/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.02/1.72  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.02/1.72  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.02/1.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.02/1.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.02/1.72  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.02/1.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.02/1.72  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.02/1.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.02/1.72  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.02/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.02/1.72  
% 4.02/1.74  tff(f_75, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.02/1.74  tff(f_191, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tops_1)).
% 4.02/1.74  tff(f_113, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.02/1.74  tff(f_93, axiom, (![A]: r1_tarski(k1_tarski(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 4.02/1.74  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.02/1.74  tff(f_65, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.02/1.74  tff(f_67, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.02/1.74  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.02/1.74  tff(f_71, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.02/1.74  tff(f_73, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 4.02/1.74  tff(f_83, axiom, (![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 4.02/1.74  tff(f_87, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 4.02/1.74  tff(f_91, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 4.02/1.74  tff(f_106, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.02/1.74  tff(f_128, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.02/1.74  tff(f_110, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 4.02/1.74  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.02/1.74  tff(f_145, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 4.02/1.74  tff(f_153, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.02/1.74  tff(f_149, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.02/1.74  tff(f_177, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.02/1.74  tff(f_117, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.02/1.74  tff(f_184, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 4.02/1.74  tff(c_28, plain, (![A_21]: (r1_xboole_0(A_21, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.02/1.74  tff(c_78, plain, (k1_tops_1('#skF_5', k2_struct_0('#skF_5'))!=k2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.02/1.74  tff(c_50, plain, (![A_35]: (~v1_xboole_0(k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.02/1.74  tff(c_38, plain, (![A_30]: (r1_tarski(k1_tarski(A_30), k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.02/1.74  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.02/1.74  tff(c_145, plain, (![A_79, B_80, C_81]: (~r1_xboole_0(A_79, B_80) | ~r2_hidden(C_81, k3_xboole_0(A_79, B_80)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.02/1.74  tff(c_150, plain, (![A_79, B_80, B_2]: (~r1_xboole_0(A_79, B_80) | r1_tarski(k3_xboole_0(A_79, B_80), B_2))), inference(resolution, [status(thm)], [c_6, c_145])).
% 4.02/1.74  tff(c_20, plain, (![A_16]: (k2_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.02/1.74  tff(c_14, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), A_6) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.02/1.74  tff(c_458, plain, (![C_117, B_118, A_119]: (r2_hidden(C_117, B_118) | ~r2_hidden(C_117, A_119) | ~r1_tarski(A_119, B_118))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.02/1.74  tff(c_1210, plain, (![A_180, B_181, B_182]: (r2_hidden('#skF_2'(A_180, B_181), B_182) | ~r1_tarski(A_180, B_182) | r1_xboole_0(A_180, B_181))), inference(resolution, [status(thm)], [c_14, c_458])).
% 4.02/1.74  tff(c_166, plain, (![A_86, B_87]: (k4_xboole_0(A_86, k4_xboole_0(A_86, B_87))=k3_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.02/1.74  tff(c_26, plain, (![A_20]: (k4_xboole_0(k1_xboole_0, A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.02/1.74  tff(c_208, plain, (![B_88]: (k3_xboole_0(k1_xboole_0, B_88)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_166, c_26])).
% 4.02/1.74  tff(c_18, plain, (![A_11, B_12, C_15]: (~r1_xboole_0(A_11, B_12) | ~r2_hidden(C_15, k3_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.02/1.74  tff(c_213, plain, (![B_88, C_15]: (~r1_xboole_0(k1_xboole_0, B_88) | ~r2_hidden(C_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_208, c_18])).
% 4.02/1.74  tff(c_237, plain, (![C_15]: (~r2_hidden(C_15, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_213])).
% 4.02/1.74  tff(c_1235, plain, (![A_180, B_181]: (~r1_tarski(A_180, k1_xboole_0) | r1_xboole_0(A_180, B_181))), inference(resolution, [status(thm)], [c_1210, c_237])).
% 4.02/1.74  tff(c_1349, plain, (![C_192, B_193, D_194, A_195]: (C_192=B_193 | ~r1_xboole_0(D_194, B_193) | ~r1_xboole_0(C_192, A_195) | k2_xboole_0(C_192, D_194)!=k2_xboole_0(A_195, B_193))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.02/1.74  tff(c_1359, plain, (![C_192, A_195, A_21]: (k1_xboole_0=C_192 | ~r1_xboole_0(C_192, A_195) | k2_xboole_0(C_192, A_21)!=k2_xboole_0(A_195, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_1349])).
% 4.02/1.74  tff(c_1368, plain, (![C_196, A_197, A_198]: (k1_xboole_0=C_196 | ~r1_xboole_0(C_196, A_197) | k2_xboole_0(C_196, A_198)!=A_197)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1359])).
% 4.02/1.74  tff(c_1393, plain, (![A_201, A_202, B_203]: (k1_xboole_0=A_201 | k2_xboole_0(A_201, A_202)!=B_203 | ~r1_tarski(A_201, k1_xboole_0))), inference(resolution, [status(thm)], [c_1235, c_1368])).
% 4.02/1.74  tff(c_1402, plain, (![B_205]: (k1_xboole_0=B_205 | ~r1_tarski(B_205, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1393])).
% 4.02/1.74  tff(c_1420, plain, (![A_206, B_207]: (k3_xboole_0(A_206, B_207)=k1_xboole_0 | ~r1_xboole_0(A_206, B_207))), inference(resolution, [status(thm)], [c_150, c_1402])).
% 4.02/1.74  tff(c_1441, plain, (![A_21]: (k3_xboole_0(A_21, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_1420])).
% 4.02/1.74  tff(c_279, plain, (![A_99, B_100]: (k4_xboole_0(k2_xboole_0(A_99, B_100), B_100)=A_99 | ~r1_xboole_0(A_99, B_100))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.02/1.74  tff(c_291, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16 | ~r1_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_279])).
% 4.02/1.74  tff(c_296, plain, (![A_101]: (k4_xboole_0(A_101, k1_xboole_0)=A_101)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_291])).
% 4.02/1.74  tff(c_24, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.02/1.74  tff(c_344, plain, (![A_103]: (k4_xboole_0(A_103, A_103)=k3_xboole_0(A_103, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_296, c_24])).
% 4.02/1.74  tff(c_34, plain, (![A_28, B_29]: (r2_hidden(A_28, B_29) | k4_xboole_0(k1_tarski(A_28), B_29)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.02/1.74  tff(c_358, plain, (![A_28]: (r2_hidden(A_28, k1_tarski(A_28)) | k3_xboole_0(k1_tarski(A_28), k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_344, c_34])).
% 4.02/1.74  tff(c_1503, plain, (![A_209]: (r2_hidden(A_209, k1_tarski(A_209)))), inference(demodulation, [status(thm), theory('equality')], [c_1441, c_358])).
% 4.02/1.74  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.02/1.74  tff(c_1942, plain, (![A_239, B_240]: (r2_hidden(A_239, B_240) | ~r1_tarski(k1_tarski(A_239), B_240))), inference(resolution, [status(thm)], [c_1503, c_2])).
% 4.02/1.74  tff(c_1958, plain, (![A_241]: (r2_hidden(A_241, k1_zfmisc_1(A_241)))), inference(resolution, [status(thm)], [c_38, c_1942])).
% 4.02/1.74  tff(c_40, plain, (![B_32, A_31]: (m1_subset_1(B_32, A_31) | ~r2_hidden(B_32, A_31) | v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.02/1.74  tff(c_1966, plain, (![A_241]: (m1_subset_1(A_241, k1_zfmisc_1(A_241)) | v1_xboole_0(k1_zfmisc_1(A_241)))), inference(resolution, [status(thm)], [c_1958, c_40])).
% 4.02/1.74  tff(c_1971, plain, (![A_241]: (m1_subset_1(A_241, k1_zfmisc_1(A_241)))), inference(negUnitSimplification, [status(thm)], [c_50, c_1966])).
% 4.02/1.74  tff(c_295, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_291])).
% 4.02/1.74  tff(c_58, plain, (![A_42]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.02/1.74  tff(c_555, plain, (![A_129, B_130]: (k4_xboole_0(A_129, B_130)=k3_subset_1(A_129, B_130) | ~m1_subset_1(B_130, k1_zfmisc_1(A_129)))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.02/1.74  tff(c_568, plain, (![A_42]: (k4_xboole_0(A_42, k1_xboole_0)=k3_subset_1(A_42, k1_xboole_0))), inference(resolution, [status(thm)], [c_58, c_555])).
% 4.02/1.74  tff(c_573, plain, (![A_42]: (k3_subset_1(A_42, k1_xboole_0)=A_42)), inference(demodulation, [status(thm), theory('equality')], [c_295, c_568])).
% 4.02/1.74  tff(c_82, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.02/1.74  tff(c_80, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.02/1.74  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.02/1.74  tff(c_1021, plain, (![B_170, A_171]: (v4_pre_topc(B_170, A_171) | ~v1_xboole_0(B_170) | ~m1_subset_1(B_170, k1_zfmisc_1(u1_struct_0(A_171))) | ~l1_pre_topc(A_171) | ~v2_pre_topc(A_171))), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.02/1.74  tff(c_1047, plain, (![A_171]: (v4_pre_topc(k1_xboole_0, A_171) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_171) | ~v2_pre_topc(A_171))), inference(resolution, [status(thm)], [c_58, c_1021])).
% 4.02/1.74  tff(c_1074, plain, (![A_174]: (v4_pre_topc(k1_xboole_0, A_174) | ~l1_pre_topc(A_174) | ~v2_pre_topc(A_174))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1047])).
% 4.02/1.74  tff(c_66, plain, (![A_50]: (l1_struct_0(A_50) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.02/1.74  tff(c_105, plain, (![A_67]: (u1_struct_0(A_67)=k2_struct_0(A_67) | ~l1_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.02/1.74  tff(c_110, plain, (![A_68]: (u1_struct_0(A_68)=k2_struct_0(A_68) | ~l1_pre_topc(A_68))), inference(resolution, [status(thm)], [c_66, c_105])).
% 4.02/1.74  tff(c_114, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_80, c_110])).
% 4.02/1.74  tff(c_758, plain, (![A_145, B_146]: (k2_pre_topc(A_145, B_146)=B_146 | ~v4_pre_topc(B_146, A_145) | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(A_145))), inference(cnfTransformation, [status(thm)], [f_177])).
% 4.02/1.74  tff(c_780, plain, (![B_146]: (k2_pre_topc('#skF_5', B_146)=B_146 | ~v4_pre_topc(B_146, '#skF_5') | ~m1_subset_1(B_146, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_114, c_758])).
% 4.02/1.74  tff(c_891, plain, (![B_152]: (k2_pre_topc('#skF_5', B_152)=B_152 | ~v4_pre_topc(B_152, '#skF_5') | ~m1_subset_1(B_152, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_780])).
% 4.02/1.74  tff(c_926, plain, (k2_pre_topc('#skF_5', k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, '#skF_5')), inference(resolution, [status(thm)], [c_58, c_891])).
% 4.02/1.74  tff(c_942, plain, (~v4_pre_topc(k1_xboole_0, '#skF_5')), inference(splitLeft, [status(thm)], [c_926])).
% 4.02/1.74  tff(c_1077, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_1074, c_942])).
% 4.02/1.74  tff(c_1084, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_1077])).
% 4.02/1.74  tff(c_1085, plain, (k2_pre_topc('#skF_5', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_926])).
% 4.02/1.74  tff(c_583, plain, (![A_132, B_133]: (k3_subset_1(A_132, k3_subset_1(A_132, B_133))=B_133 | ~m1_subset_1(B_133, k1_zfmisc_1(A_132)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.02/1.74  tff(c_592, plain, (![A_42]: (k3_subset_1(A_42, k3_subset_1(A_42, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_58, c_583])).
% 4.02/1.74  tff(c_597, plain, (![A_42]: (k3_subset_1(A_42, A_42)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_573, c_592])).
% 4.02/1.74  tff(c_2110, plain, (![A_249, B_250]: (k3_subset_1(u1_struct_0(A_249), k2_pre_topc(A_249, k3_subset_1(u1_struct_0(A_249), B_250)))=k1_tops_1(A_249, B_250) | ~m1_subset_1(B_250, k1_zfmisc_1(u1_struct_0(A_249))) | ~l1_pre_topc(A_249))), inference(cnfTransformation, [status(thm)], [f_184])).
% 4.02/1.74  tff(c_2139, plain, (![B_250]: (k3_subset_1(k2_struct_0('#skF_5'), k2_pre_topc('#skF_5', k3_subset_1(u1_struct_0('#skF_5'), B_250)))=k1_tops_1('#skF_5', B_250) | ~m1_subset_1(B_250, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_114, c_2110])).
% 4.02/1.74  tff(c_2181, plain, (![B_255]: (k3_subset_1(k2_struct_0('#skF_5'), k2_pre_topc('#skF_5', k3_subset_1(k2_struct_0('#skF_5'), B_255)))=k1_tops_1('#skF_5', B_255) | ~m1_subset_1(B_255, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_114, c_114, c_2139])).
% 4.02/1.74  tff(c_2206, plain, (k3_subset_1(k2_struct_0('#skF_5'), k2_pre_topc('#skF_5', k1_xboole_0))=k1_tops_1('#skF_5', k2_struct_0('#skF_5')) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_597, c_2181])).
% 4.02/1.74  tff(c_2215, plain, (k1_tops_1('#skF_5', k2_struct_0('#skF_5'))=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1971, c_573, c_1085, c_2206])).
% 4.02/1.74  tff(c_2217, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_2215])).
% 4.02/1.74  tff(c_2219, plain, (![B_256]: (~r1_xboole_0(k1_xboole_0, B_256))), inference(splitRight, [status(thm)], [c_213])).
% 4.02/1.74  tff(c_2224, plain, $false, inference(resolution, [status(thm)], [c_28, c_2219])).
% 4.02/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.02/1.74  
% 4.02/1.74  Inference rules
% 4.02/1.74  ----------------------
% 4.02/1.74  #Ref     : 2
% 4.02/1.74  #Sup     : 456
% 4.02/1.74  #Fact    : 0
% 4.02/1.74  #Define  : 0
% 4.02/1.74  #Split   : 6
% 4.02/1.74  #Chain   : 0
% 4.02/1.74  #Close   : 0
% 4.02/1.74  
% 4.02/1.74  Ordering : KBO
% 4.02/1.74  
% 4.02/1.74  Simplification rules
% 4.02/1.74  ----------------------
% 4.02/1.74  #Subsume      : 62
% 4.02/1.74  #Demod        : 157
% 4.02/1.74  #Tautology    : 161
% 4.02/1.74  #SimpNegUnit  : 41
% 4.02/1.74  #BackRed      : 4
% 4.02/1.74  
% 4.02/1.74  #Partial instantiations: 0
% 4.02/1.74  #Strategies tried      : 1
% 4.02/1.74  
% 4.02/1.74  Timing (in seconds)
% 4.02/1.74  ----------------------
% 4.02/1.74  Preprocessing        : 0.36
% 4.02/1.74  Parsing              : 0.20
% 4.02/1.74  CNF conversion       : 0.03
% 4.02/1.74  Main loop            : 0.55
% 4.02/1.74  Inferencing          : 0.20
% 4.02/1.74  Reduction            : 0.17
% 4.02/1.74  Demodulation         : 0.11
% 4.02/1.74  BG Simplification    : 0.03
% 4.02/1.74  Subsumption          : 0.10
% 4.02/1.74  Abstraction          : 0.03
% 4.02/1.74  MUC search           : 0.00
% 4.02/1.74  Cooper               : 0.00
% 4.02/1.74  Total                : 0.95
% 4.02/1.74  Index Insertion      : 0.00
% 4.02/1.74  Index Deletion       : 0.00
% 4.02/1.74  Index Matching       : 0.00
% 4.02/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
