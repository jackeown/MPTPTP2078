%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:08 EST 2020

% Result     : Theorem 11.68s
% Output     : CNFRefutation 11.68s
% Verified   : 
% Statistics : Number of formulae       :  155 (1286 expanded)
%              Number of leaves         :   38 ( 451 expanded)
%              Depth                    :   25
%              Number of atoms          :  252 (2490 expanded)
%              Number of equality atoms :  100 (1084 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_92,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_50,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_52,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_66,plain,
    ( k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') != k2_tops_1('#skF_5','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_171,plain,(
    ~ v3_pre_topc('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_64,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_62,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_60,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_54,plain,(
    ! [C_42,A_30,D_44,B_38] :
      ( v3_pre_topc(C_42,A_30)
      | k1_tops_1(A_30,C_42) != C_42
      | ~ m1_subset_1(D_44,k1_zfmisc_1(u1_struct_0(B_38)))
      | ~ m1_subset_1(C_42,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(B_38)
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_9859,plain,(
    ! [D_340,B_341] :
      ( ~ m1_subset_1(D_340,k1_zfmisc_1(u1_struct_0(B_341)))
      | ~ l1_pre_topc(B_341) ) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_9862,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_9859])).

tff(c_9866,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_9862])).

tff(c_10472,plain,(
    ! [C_351,A_352] :
      ( v3_pre_topc(C_351,A_352)
      | k1_tops_1(A_352,C_351) != C_351
      | ~ m1_subset_1(C_351,k1_zfmisc_1(u1_struct_0(A_352)))
      | ~ l1_pre_topc(A_352)
      | ~ v2_pre_topc(A_352) ) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_10478,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | k1_tops_1('#skF_5','#skF_6') != '#skF_6'
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_10472])).

tff(c_10482,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | k1_tops_1('#skF_5','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_10478])).

tff(c_10483,plain,(
    k1_tops_1('#skF_5','#skF_6') != '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_171,c_10482])).

tff(c_1991,plain,(
    ! [A_156,B_157,C_158] :
      ( r2_hidden('#skF_1'(A_156,B_157,C_158),A_156)
      | r2_hidden('#skF_2'(A_156,B_157,C_158),C_158)
      | k3_xboole_0(A_156,B_157) = C_158 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k3_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2085,plain,(
    ! [A_156,B_157] :
      ( r2_hidden('#skF_2'(A_156,B_157,A_156),A_156)
      | k3_xboole_0(A_156,B_157) = A_156 ) ),
    inference(resolution,[status(thm)],[c_1991,c_16])).

tff(c_18,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),B_4)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k3_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2843,plain,(
    ! [A_184,B_185,C_186] :
      ( r2_hidden('#skF_1'(A_184,B_185,C_186),B_185)
      | ~ r2_hidden('#skF_2'(A_184,B_185,C_186),B_185)
      | ~ r2_hidden('#skF_2'(A_184,B_185,C_186),A_184)
      | k3_xboole_0(A_184,B_185) = C_186 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12362,plain,(
    ! [C_388,B_389] :
      ( ~ r2_hidden('#skF_2'(C_388,B_389,C_388),B_389)
      | r2_hidden('#skF_1'(C_388,B_389,C_388),B_389)
      | k3_xboole_0(C_388,B_389) = C_388 ) ),
    inference(resolution,[status(thm)],[c_18,c_2843])).

tff(c_10,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),B_4)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),A_3)
      | k3_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_13043,plain,(
    ! [B_397] :
      ( ~ r2_hidden('#skF_2'(B_397,B_397,B_397),B_397)
      | k3_xboole_0(B_397,B_397) = B_397 ) ),
    inference(resolution,[status(thm)],[c_12362,c_10])).

tff(c_13108,plain,(
    ! [B_157] : k3_xboole_0(B_157,B_157) = B_157 ),
    inference(resolution,[status(thm)],[c_2085,c_13043])).

tff(c_1377,plain,(
    ! [A_140,B_141,C_142] :
      ( r2_hidden('#skF_3'(A_140,B_141,C_142),A_140)
      | r2_hidden('#skF_4'(A_140,B_141,C_142),C_142)
      | k4_xboole_0(A_140,B_141) = C_142 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_36,plain,(
    ! [A_9,B_10,C_11] :
      ( ~ r2_hidden('#skF_3'(A_9,B_10,C_11),B_10)
      | r2_hidden('#skF_4'(A_9,B_10,C_11),C_11)
      | k4_xboole_0(A_9,B_10) = C_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1488,plain,(
    ! [A_143,C_144] :
      ( r2_hidden('#skF_4'(A_143,A_143,C_144),C_144)
      | k4_xboole_0(A_143,A_143) = C_144 ) ),
    inference(resolution,[status(thm)],[c_1377,c_36])).

tff(c_80,plain,(
    ! [B_50,A_51] : k3_xboole_0(B_50,A_51) = k3_xboole_0(A_51,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_42,plain,(
    ! [A_17] : k3_xboole_0(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_96,plain,(
    ! [A_51] : k3_xboole_0(k1_xboole_0,A_51) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_42])).

tff(c_300,plain,(
    ! [D_65,B_66,A_67] :
      ( r2_hidden(D_65,B_66)
      | ~ r2_hidden(D_65,k3_xboole_0(A_67,B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_303,plain,(
    ! [D_65,A_51] :
      ( r2_hidden(D_65,A_51)
      | ~ r2_hidden(D_65,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_300])).

tff(c_1542,plain,(
    ! [A_143,A_51] :
      ( r2_hidden('#skF_4'(A_143,A_143,k1_xboole_0),A_51)
      | k4_xboole_0(A_143,A_143) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1488,c_303])).

tff(c_1545,plain,(
    ! [A_145,A_146] :
      ( r2_hidden('#skF_4'(A_145,A_145,k1_xboole_0),A_146)
      | k4_xboole_0(A_145,A_145) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1488,c_303])).

tff(c_24,plain,(
    ! [D_14,B_10,A_9] :
      ( ~ r2_hidden(D_14,B_10)
      | ~ r2_hidden(D_14,k4_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1602,plain,(
    ! [A_147,B_148] :
      ( ~ r2_hidden('#skF_4'(A_147,A_147,k1_xboole_0),B_148)
      | k4_xboole_0(A_147,A_147) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1545,c_24])).

tff(c_1630,plain,(
    ! [A_149] : k4_xboole_0(A_149,A_149) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1542,c_1602])).

tff(c_44,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1678,plain,(
    ! [A_149] : k4_xboole_0(A_149,k1_xboole_0) = k3_xboole_0(A_149,A_149) ),
    inference(superposition,[status(thm),theory(equality)],[c_1630,c_44])).

tff(c_13130,plain,(
    ! [A_149] : k4_xboole_0(A_149,k1_xboole_0) = A_149 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13108,c_1678])).

tff(c_1754,plain,(
    ! [A_153] : k4_xboole_0(A_153,k1_xboole_0) = k3_xboole_0(A_153,A_153) ),
    inference(superposition,[status(thm),theory(equality)],[c_1630,c_44])).

tff(c_4,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,k3_xboole_0(A_3,B_4))
      | ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1800,plain,(
    ! [D_8,A_153] :
      ( r2_hidden(D_8,k4_xboole_0(A_153,k1_xboole_0))
      | ~ r2_hidden(D_8,A_153)
      | ~ r2_hidden(D_8,A_153) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1754,c_4])).

tff(c_173,plain,(
    ! [A_55,B_56] : k4_xboole_0(A_55,k4_xboole_0(A_55,B_56)) = k3_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_416,plain,(
    ! [A_90,B_91] : k4_xboole_0(A_90,k3_xboole_0(A_90,B_91)) = k3_xboole_0(A_90,k4_xboole_0(A_90,B_91)) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_44])).

tff(c_438,plain,(
    ! [A_90,B_91] : k4_xboole_0(A_90,k3_xboole_0(A_90,k4_xboole_0(A_90,B_91))) = k3_xboole_0(A_90,k3_xboole_0(A_90,B_91)) ),
    inference(superposition,[status(thm),theory(equality)],[c_416,c_44])).

tff(c_1649,plain,(
    ! [A_149] : k4_xboole_0(A_149,k3_xboole_0(A_149,k1_xboole_0)) = k3_xboole_0(A_149,k3_xboole_0(A_149,A_149)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1630,c_438])).

tff(c_1689,plain,(
    ! [A_149] : k3_xboole_0(A_149,k3_xboole_0(A_149,A_149)) = k4_xboole_0(A_149,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1649])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_463,plain,(
    ! [A_92] : k3_xboole_0(A_92,k4_xboole_0(A_92,k1_xboole_0)) = k4_xboole_0(A_92,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_416])).

tff(c_188,plain,(
    ! [A_57,B_58] : k5_xboole_0(A_57,k3_xboole_0(A_57,B_58)) = k4_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_203,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_188])).

tff(c_472,plain,(
    ! [A_92] : k5_xboole_0(k4_xboole_0(A_92,k1_xboole_0),k4_xboole_0(A_92,k1_xboole_0)) = k4_xboole_0(k4_xboole_0(A_92,k1_xboole_0),A_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_463,c_203])).

tff(c_2237,plain,(
    ! [A_162] : k3_xboole_0(A_162,k3_xboole_0(A_162,A_162)) = k4_xboole_0(A_162,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1649])).

tff(c_9375,plain,(
    ! [A_330] : k5_xboole_0(k3_xboole_0(A_330,A_330),k4_xboole_0(A_330,k1_xboole_0)) = k4_xboole_0(k3_xboole_0(A_330,A_330),A_330) ),
    inference(superposition,[status(thm),theory(equality)],[c_2237,c_203])).

tff(c_9868,plain,(
    ! [A_342] : k5_xboole_0(k4_xboole_0(A_342,k1_xboole_0),k4_xboole_0(A_342,k1_xboole_0)) = k4_xboole_0(k3_xboole_0(A_342,A_342),A_342) ),
    inference(superposition,[status(thm),theory(equality)],[c_1678,c_9375])).

tff(c_316,plain,(
    ! [D_70,B_71,A_72] :
      ( ~ r2_hidden(D_70,B_71)
      | ~ r2_hidden(D_70,k4_xboole_0(A_72,B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_322,plain,(
    ! [D_70,A_18,B_19] :
      ( ~ r2_hidden(D_70,k4_xboole_0(A_18,B_19))
      | ~ r2_hidden(D_70,k3_xboole_0(A_18,B_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_316])).

tff(c_9901,plain,(
    ! [D_70,A_342] :
      ( ~ r2_hidden(D_70,k5_xboole_0(k4_xboole_0(A_342,k1_xboole_0),k4_xboole_0(A_342,k1_xboole_0)))
      | ~ r2_hidden(D_70,k3_xboole_0(k3_xboole_0(A_342,A_342),A_342)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9868,c_322])).

tff(c_10352,plain,(
    ! [D_349,A_350] :
      ( ~ r2_hidden(D_349,k4_xboole_0(k4_xboole_0(A_350,k1_xboole_0),A_350))
      | ~ r2_hidden(D_349,k4_xboole_0(A_350,k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1689,c_2,c_472,c_9901])).

tff(c_10391,plain,(
    ! [D_8] : ~ r2_hidden(D_8,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_1800,c_10352])).

tff(c_10458,plain,(
    ! [D_8] : ~ r2_hidden(D_8,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_1678,c_10391])).

tff(c_222,plain,(
    ! [A_63] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_188])).

tff(c_238,plain,(
    ! [B_19] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_44])).

tff(c_252,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_238])).

tff(c_197,plain,(
    ! [A_51] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_188])).

tff(c_255,plain,(
    ! [A_51] : k4_xboole_0(k1_xboole_0,A_51) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_197])).

tff(c_26,plain,(
    ! [D_14,A_9,B_10] :
      ( r2_hidden(D_14,A_9)
      | ~ r2_hidden(D_14,k4_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_14430,plain,(
    ! [A_425,B_426,A_427,B_428] :
      ( r2_hidden('#skF_2'(A_425,B_426,k4_xboole_0(A_427,B_428)),A_427)
      | r2_hidden('#skF_1'(A_425,B_426,k4_xboole_0(A_427,B_428)),A_425)
      | k4_xboole_0(A_427,B_428) = k3_xboole_0(A_425,B_426) ) ),
    inference(resolution,[status(thm)],[c_1991,c_26])).

tff(c_14625,plain,(
    ! [A_425,B_426,A_51] :
      ( r2_hidden('#skF_2'(A_425,B_426,k4_xboole_0(k1_xboole_0,A_51)),k1_xboole_0)
      | r2_hidden('#skF_1'(A_425,B_426,k1_xboole_0),A_425)
      | k4_xboole_0(k1_xboole_0,A_51) = k3_xboole_0(A_425,B_426) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_14430])).

tff(c_14685,plain,(
    ! [A_425,B_426] :
      ( r2_hidden('#skF_2'(A_425,B_426,k1_xboole_0),k1_xboole_0)
      | r2_hidden('#skF_1'(A_425,B_426,k1_xboole_0),A_425)
      | k3_xboole_0(A_425,B_426) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_255,c_14625])).

tff(c_14689,plain,(
    ! [A_429,B_430] :
      ( r2_hidden('#skF_1'(A_429,B_430,k1_xboole_0),A_429)
      | k3_xboole_0(A_429,B_430) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_10458,c_14685])).

tff(c_609,plain,(
    ! [A_102,B_103] :
      ( m1_subset_1(k2_pre_topc(A_102,B_103),k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_46,plain,(
    ! [A_20,B_21,C_22] :
      ( k7_subset_1(A_20,B_21,C_22) = k4_xboole_0(B_21,C_22)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_13623,plain,(
    ! [A_405,B_406,C_407] :
      ( k7_subset_1(u1_struct_0(A_405),k2_pre_topc(A_405,B_406),C_407) = k4_xboole_0(k2_pre_topc(A_405,B_406),C_407)
      | ~ m1_subset_1(B_406,k1_zfmisc_1(u1_struct_0(A_405)))
      | ~ l1_pre_topc(A_405) ) ),
    inference(resolution,[status(thm)],[c_609,c_46])).

tff(c_13627,plain,(
    ! [C_407] :
      ( k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),C_407) = k4_xboole_0(k2_pre_topc('#skF_5','#skF_6'),C_407)
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_60,c_13623])).

tff(c_13635,plain,(
    ! [C_408] : k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),C_408) = k4_xboole_0(k2_pre_topc('#skF_5','#skF_6'),C_408) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_13627])).

tff(c_72,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_267,plain,(
    k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_171,c_72])).

tff(c_13645,plain,(
    k4_xboole_0(k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_13635,c_267])).

tff(c_13692,plain,(
    ! [D_14] :
      ( ~ r2_hidden(D_14,'#skF_6')
      | ~ r2_hidden(D_14,k2_tops_1('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13645,c_24])).

tff(c_17803,plain,(
    ! [B_492] :
      ( ~ r2_hidden('#skF_1'(k2_tops_1('#skF_5','#skF_6'),B_492,k1_xboole_0),'#skF_6')
      | k3_xboole_0(k2_tops_1('#skF_5','#skF_6'),B_492) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14689,c_13692])).

tff(c_17811,plain,
    ( r2_hidden('#skF_2'(k2_tops_1('#skF_5','#skF_6'),'#skF_6',k1_xboole_0),k1_xboole_0)
    | k3_xboole_0(k2_tops_1('#skF_5','#skF_6'),'#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_17803])).

tff(c_17816,plain,
    ( r2_hidden('#skF_2'(k2_tops_1('#skF_5','#skF_6'),'#skF_6',k1_xboole_0),k1_xboole_0)
    | k3_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_17811])).

tff(c_17817,plain,(
    k3_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_10458,c_17816])).

tff(c_38,plain,(
    ! [A_9,B_10,C_11] :
      ( r2_hidden('#skF_3'(A_9,B_10,C_11),A_9)
      | r2_hidden('#skF_4'(A_9,B_10,C_11),C_11)
      | k4_xboole_0(A_9,B_10) = C_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10485,plain,(
    ! [D_353] : ~ r2_hidden(D_353,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_1678,c_10391])).

tff(c_10968,plain,(
    ! [A_367,B_368] :
      ( r2_hidden('#skF_3'(A_367,B_368,k1_xboole_0),A_367)
      | k4_xboole_0(A_367,B_368) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_10485])).

tff(c_372,plain,(
    ! [A_80,B_81,C_82] :
      ( k7_subset_1(A_80,B_81,C_82) = k4_xboole_0(B_81,C_82)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_375,plain,(
    ! [C_82] : k7_subset_1(u1_struct_0('#skF_5'),'#skF_6',C_82) = k4_xboole_0('#skF_6',C_82) ),
    inference(resolution,[status(thm)],[c_60,c_372])).

tff(c_2383,plain,(
    ! [A_165,B_166] :
      ( k7_subset_1(u1_struct_0(A_165),B_166,k2_tops_1(A_165,B_166)) = k1_tops_1(A_165,B_166)
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ l1_pre_topc(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2387,plain,
    ( k7_subset_1(u1_struct_0('#skF_5'),'#skF_6',k2_tops_1('#skF_5','#skF_6')) = k1_tops_1('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_2383])).

tff(c_2391,plain,(
    k4_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = k1_tops_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_375,c_2387])).

tff(c_2416,plain,(
    ! [D_14] :
      ( r2_hidden(D_14,'#skF_6')
      | ~ r2_hidden(D_14,k1_tops_1('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2391,c_26])).

tff(c_12450,plain,(
    ! [B_390] :
      ( r2_hidden('#skF_3'(k1_tops_1('#skF_5','#skF_6'),B_390,k1_xboole_0),'#skF_6')
      | k4_xboole_0(k1_tops_1('#skF_5','#skF_6'),B_390) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10968,c_2416])).

tff(c_12453,plain,
    ( r2_hidden('#skF_4'(k1_tops_1('#skF_5','#skF_6'),'#skF_6',k1_xboole_0),k1_xboole_0)
    | k4_xboole_0(k1_tops_1('#skF_5','#skF_6'),'#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12450,c_36])).

tff(c_12456,plain,(
    k4_xboole_0(k1_tops_1('#skF_5','#skF_6'),'#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_10458,c_12453])).

tff(c_12493,plain,(
    k4_xboole_0(k1_tops_1('#skF_5','#skF_6'),k1_xboole_0) = k3_xboole_0(k1_tops_1('#skF_5','#skF_6'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_12456,c_44])).

tff(c_12506,plain,(
    k4_xboole_0(k1_tops_1('#skF_5','#skF_6'),k1_xboole_0) = k3_xboole_0('#skF_6',k1_tops_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12493])).

tff(c_14348,plain,(
    k3_xboole_0('#skF_6',k1_tops_1('#skF_5','#skF_6')) = k1_tops_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13130,c_12506])).

tff(c_2419,plain,(
    k4_xboole_0('#skF_6',k1_tops_1('#skF_5','#skF_6')) = k3_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2391,c_44])).

tff(c_2658,plain,(
    k4_xboole_0('#skF_6',k3_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6'))) = k3_xboole_0('#skF_6',k1_tops_1('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2419,c_44])).

tff(c_14350,plain,(
    k4_xboole_0('#skF_6',k3_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6'))) = k1_tops_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14348,c_2658])).

tff(c_17819,plain,(
    k4_xboole_0('#skF_6',k1_xboole_0) = k1_tops_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17817,c_14350])).

tff(c_17822,plain,(
    k1_tops_1('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13130,c_17819])).

tff(c_17824,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10483,c_17822])).

tff(c_17825,plain,(
    k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') != k2_tops_1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_17826,plain,(
    v3_pre_topc('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_56,plain,(
    ! [B_38,D_44,C_42,A_30] :
      ( k1_tops_1(B_38,D_44) = D_44
      | ~ v3_pre_topc(D_44,B_38)
      | ~ m1_subset_1(D_44,k1_zfmisc_1(u1_struct_0(B_38)))
      | ~ m1_subset_1(C_42,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(B_38)
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_25434,plain,(
    ! [C_743,A_744] :
      ( ~ m1_subset_1(C_743,k1_zfmisc_1(u1_struct_0(A_744)))
      | ~ l1_pre_topc(A_744)
      | ~ v2_pre_topc(A_744) ) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_25440,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_25434])).

tff(c_25445,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_25440])).

tff(c_25731,plain,(
    ! [B_749,D_750] :
      ( k1_tops_1(B_749,D_750) = D_750
      | ~ v3_pre_topc(D_750,B_749)
      | ~ m1_subset_1(D_750,k1_zfmisc_1(u1_struct_0(B_749)))
      | ~ l1_pre_topc(B_749) ) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_25737,plain,
    ( k1_tops_1('#skF_5','#skF_6') = '#skF_6'
    | ~ v3_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_25731])).

tff(c_25741,plain,(
    k1_tops_1('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_17826,c_25737])).

tff(c_52,plain,(
    ! [A_27,B_29] :
      ( k7_subset_1(u1_struct_0(A_27),k2_pre_topc(A_27,B_29),k1_tops_1(A_27,B_29)) = k2_tops_1(A_27,B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_25761,plain,
    ( k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_25741,c_52])).

tff(c_25765,plain,(
    k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_25761])).

tff(c_25767,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17825,c_25765])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:10:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.68/4.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.68/4.37  
% 11.68/4.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.68/4.37  %$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 11.68/4.37  
% 11.68/4.37  %Foreground sorts:
% 11.68/4.37  
% 11.68/4.37  
% 11.68/4.37  %Background operators:
% 11.68/4.37  
% 11.68/4.37  
% 11.68/4.37  %Foreground operators:
% 11.68/4.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 11.68/4.37  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 11.68/4.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.68/4.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.68/4.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.68/4.37  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 11.68/4.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.68/4.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.68/4.37  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 11.68/4.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.68/4.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.68/4.37  tff('#skF_5', type, '#skF_5': $i).
% 11.68/4.37  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 11.68/4.37  tff('#skF_6', type, '#skF_6': $i).
% 11.68/4.37  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 11.68/4.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.68/4.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.68/4.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.68/4.37  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 11.68/4.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.68/4.37  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.68/4.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.68/4.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.68/4.37  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 11.68/4.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.68/4.37  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 11.68/4.37  
% 11.68/4.39  tff(f_111, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 11.68/4.39  tff(f_92, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 11.68/4.39  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 11.68/4.39  tff(f_46, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 11.68/4.39  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.68/4.39  tff(f_50, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 11.68/4.39  tff(f_52, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.68/4.39  tff(f_48, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.68/4.39  tff(f_64, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 11.68/4.39  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 11.68/4.39  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 11.68/4.39  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 11.68/4.39  tff(c_66, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')!=k2_tops_1('#skF_5', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 11.68/4.39  tff(c_171, plain, (~v3_pre_topc('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_66])).
% 11.68/4.39  tff(c_64, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 11.68/4.39  tff(c_62, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 11.68/4.39  tff(c_60, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 11.68/4.39  tff(c_54, plain, (![C_42, A_30, D_44, B_38]: (v3_pre_topc(C_42, A_30) | k1_tops_1(A_30, C_42)!=C_42 | ~m1_subset_1(D_44, k1_zfmisc_1(u1_struct_0(B_38))) | ~m1_subset_1(C_42, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(B_38) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.68/4.39  tff(c_9859, plain, (![D_340, B_341]: (~m1_subset_1(D_340, k1_zfmisc_1(u1_struct_0(B_341))) | ~l1_pre_topc(B_341))), inference(splitLeft, [status(thm)], [c_54])).
% 11.68/4.39  tff(c_9862, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_60, c_9859])).
% 11.68/4.39  tff(c_9866, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_9862])).
% 11.68/4.39  tff(c_10472, plain, (![C_351, A_352]: (v3_pre_topc(C_351, A_352) | k1_tops_1(A_352, C_351)!=C_351 | ~m1_subset_1(C_351, k1_zfmisc_1(u1_struct_0(A_352))) | ~l1_pre_topc(A_352) | ~v2_pre_topc(A_352))), inference(splitRight, [status(thm)], [c_54])).
% 11.68/4.39  tff(c_10478, plain, (v3_pre_topc('#skF_6', '#skF_5') | k1_tops_1('#skF_5', '#skF_6')!='#skF_6' | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_60, c_10472])).
% 11.68/4.39  tff(c_10482, plain, (v3_pre_topc('#skF_6', '#skF_5') | k1_tops_1('#skF_5', '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_10478])).
% 11.68/4.39  tff(c_10483, plain, (k1_tops_1('#skF_5', '#skF_6')!='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_171, c_10482])).
% 11.68/4.39  tff(c_1991, plain, (![A_156, B_157, C_158]: (r2_hidden('#skF_1'(A_156, B_157, C_158), A_156) | r2_hidden('#skF_2'(A_156, B_157, C_158), C_158) | k3_xboole_0(A_156, B_157)=C_158)), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.68/4.39  tff(c_16, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k3_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.68/4.39  tff(c_2085, plain, (![A_156, B_157]: (r2_hidden('#skF_2'(A_156, B_157, A_156), A_156) | k3_xboole_0(A_156, B_157)=A_156)), inference(resolution, [status(thm)], [c_1991, c_16])).
% 11.68/4.39  tff(c_18, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), B_4) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k3_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.68/4.39  tff(c_2843, plain, (![A_184, B_185, C_186]: (r2_hidden('#skF_1'(A_184, B_185, C_186), B_185) | ~r2_hidden('#skF_2'(A_184, B_185, C_186), B_185) | ~r2_hidden('#skF_2'(A_184, B_185, C_186), A_184) | k3_xboole_0(A_184, B_185)=C_186)), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.68/4.39  tff(c_12362, plain, (![C_388, B_389]: (~r2_hidden('#skF_2'(C_388, B_389, C_388), B_389) | r2_hidden('#skF_1'(C_388, B_389, C_388), B_389) | k3_xboole_0(C_388, B_389)=C_388)), inference(resolution, [status(thm)], [c_18, c_2843])).
% 11.68/4.39  tff(c_10, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), B_4) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), A_3) | k3_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.68/4.39  tff(c_13043, plain, (![B_397]: (~r2_hidden('#skF_2'(B_397, B_397, B_397), B_397) | k3_xboole_0(B_397, B_397)=B_397)), inference(resolution, [status(thm)], [c_12362, c_10])).
% 11.68/4.39  tff(c_13108, plain, (![B_157]: (k3_xboole_0(B_157, B_157)=B_157)), inference(resolution, [status(thm)], [c_2085, c_13043])).
% 11.68/4.39  tff(c_1377, plain, (![A_140, B_141, C_142]: (r2_hidden('#skF_3'(A_140, B_141, C_142), A_140) | r2_hidden('#skF_4'(A_140, B_141, C_142), C_142) | k4_xboole_0(A_140, B_141)=C_142)), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.68/4.39  tff(c_36, plain, (![A_9, B_10, C_11]: (~r2_hidden('#skF_3'(A_9, B_10, C_11), B_10) | r2_hidden('#skF_4'(A_9, B_10, C_11), C_11) | k4_xboole_0(A_9, B_10)=C_11)), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.68/4.39  tff(c_1488, plain, (![A_143, C_144]: (r2_hidden('#skF_4'(A_143, A_143, C_144), C_144) | k4_xboole_0(A_143, A_143)=C_144)), inference(resolution, [status(thm)], [c_1377, c_36])).
% 11.68/4.39  tff(c_80, plain, (![B_50, A_51]: (k3_xboole_0(B_50, A_51)=k3_xboole_0(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.68/4.39  tff(c_42, plain, (![A_17]: (k3_xboole_0(A_17, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.68/4.39  tff(c_96, plain, (![A_51]: (k3_xboole_0(k1_xboole_0, A_51)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_80, c_42])).
% 11.68/4.39  tff(c_300, plain, (![D_65, B_66, A_67]: (r2_hidden(D_65, B_66) | ~r2_hidden(D_65, k3_xboole_0(A_67, B_66)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.68/4.39  tff(c_303, plain, (![D_65, A_51]: (r2_hidden(D_65, A_51) | ~r2_hidden(D_65, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_96, c_300])).
% 11.68/4.39  tff(c_1542, plain, (![A_143, A_51]: (r2_hidden('#skF_4'(A_143, A_143, k1_xboole_0), A_51) | k4_xboole_0(A_143, A_143)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1488, c_303])).
% 11.68/4.39  tff(c_1545, plain, (![A_145, A_146]: (r2_hidden('#skF_4'(A_145, A_145, k1_xboole_0), A_146) | k4_xboole_0(A_145, A_145)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1488, c_303])).
% 11.68/4.39  tff(c_24, plain, (![D_14, B_10, A_9]: (~r2_hidden(D_14, B_10) | ~r2_hidden(D_14, k4_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.68/4.39  tff(c_1602, plain, (![A_147, B_148]: (~r2_hidden('#skF_4'(A_147, A_147, k1_xboole_0), B_148) | k4_xboole_0(A_147, A_147)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1545, c_24])).
% 11.68/4.39  tff(c_1630, plain, (![A_149]: (k4_xboole_0(A_149, A_149)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1542, c_1602])).
% 11.68/4.39  tff(c_44, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.68/4.39  tff(c_1678, plain, (![A_149]: (k4_xboole_0(A_149, k1_xboole_0)=k3_xboole_0(A_149, A_149))), inference(superposition, [status(thm), theory('equality')], [c_1630, c_44])).
% 11.68/4.39  tff(c_13130, plain, (![A_149]: (k4_xboole_0(A_149, k1_xboole_0)=A_149)), inference(demodulation, [status(thm), theory('equality')], [c_13108, c_1678])).
% 11.68/4.39  tff(c_1754, plain, (![A_153]: (k4_xboole_0(A_153, k1_xboole_0)=k3_xboole_0(A_153, A_153))), inference(superposition, [status(thm), theory('equality')], [c_1630, c_44])).
% 11.68/4.39  tff(c_4, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, k3_xboole_0(A_3, B_4)) | ~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.68/4.39  tff(c_1800, plain, (![D_8, A_153]: (r2_hidden(D_8, k4_xboole_0(A_153, k1_xboole_0)) | ~r2_hidden(D_8, A_153) | ~r2_hidden(D_8, A_153))), inference(superposition, [status(thm), theory('equality')], [c_1754, c_4])).
% 11.68/4.39  tff(c_173, plain, (![A_55, B_56]: (k4_xboole_0(A_55, k4_xboole_0(A_55, B_56))=k3_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.68/4.39  tff(c_416, plain, (![A_90, B_91]: (k4_xboole_0(A_90, k3_xboole_0(A_90, B_91))=k3_xboole_0(A_90, k4_xboole_0(A_90, B_91)))), inference(superposition, [status(thm), theory('equality')], [c_173, c_44])).
% 11.68/4.39  tff(c_438, plain, (![A_90, B_91]: (k4_xboole_0(A_90, k3_xboole_0(A_90, k4_xboole_0(A_90, B_91)))=k3_xboole_0(A_90, k3_xboole_0(A_90, B_91)))), inference(superposition, [status(thm), theory('equality')], [c_416, c_44])).
% 11.68/4.39  tff(c_1649, plain, (![A_149]: (k4_xboole_0(A_149, k3_xboole_0(A_149, k1_xboole_0))=k3_xboole_0(A_149, k3_xboole_0(A_149, A_149)))), inference(superposition, [status(thm), theory('equality')], [c_1630, c_438])).
% 11.68/4.39  tff(c_1689, plain, (![A_149]: (k3_xboole_0(A_149, k3_xboole_0(A_149, A_149))=k4_xboole_0(A_149, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1649])).
% 11.68/4.39  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.68/4.39  tff(c_463, plain, (![A_92]: (k3_xboole_0(A_92, k4_xboole_0(A_92, k1_xboole_0))=k4_xboole_0(A_92, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_42, c_416])).
% 11.68/4.39  tff(c_188, plain, (![A_57, B_58]: (k5_xboole_0(A_57, k3_xboole_0(A_57, B_58))=k4_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.68/4.39  tff(c_203, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_188])).
% 11.68/4.39  tff(c_472, plain, (![A_92]: (k5_xboole_0(k4_xboole_0(A_92, k1_xboole_0), k4_xboole_0(A_92, k1_xboole_0))=k4_xboole_0(k4_xboole_0(A_92, k1_xboole_0), A_92))), inference(superposition, [status(thm), theory('equality')], [c_463, c_203])).
% 11.68/4.39  tff(c_2237, plain, (![A_162]: (k3_xboole_0(A_162, k3_xboole_0(A_162, A_162))=k4_xboole_0(A_162, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1649])).
% 11.68/4.39  tff(c_9375, plain, (![A_330]: (k5_xboole_0(k3_xboole_0(A_330, A_330), k4_xboole_0(A_330, k1_xboole_0))=k4_xboole_0(k3_xboole_0(A_330, A_330), A_330))), inference(superposition, [status(thm), theory('equality')], [c_2237, c_203])).
% 11.68/4.39  tff(c_9868, plain, (![A_342]: (k5_xboole_0(k4_xboole_0(A_342, k1_xboole_0), k4_xboole_0(A_342, k1_xboole_0))=k4_xboole_0(k3_xboole_0(A_342, A_342), A_342))), inference(superposition, [status(thm), theory('equality')], [c_1678, c_9375])).
% 11.68/4.39  tff(c_316, plain, (![D_70, B_71, A_72]: (~r2_hidden(D_70, B_71) | ~r2_hidden(D_70, k4_xboole_0(A_72, B_71)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.68/4.39  tff(c_322, plain, (![D_70, A_18, B_19]: (~r2_hidden(D_70, k4_xboole_0(A_18, B_19)) | ~r2_hidden(D_70, k3_xboole_0(A_18, B_19)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_316])).
% 11.68/4.39  tff(c_9901, plain, (![D_70, A_342]: (~r2_hidden(D_70, k5_xboole_0(k4_xboole_0(A_342, k1_xboole_0), k4_xboole_0(A_342, k1_xboole_0))) | ~r2_hidden(D_70, k3_xboole_0(k3_xboole_0(A_342, A_342), A_342)))), inference(superposition, [status(thm), theory('equality')], [c_9868, c_322])).
% 11.68/4.39  tff(c_10352, plain, (![D_349, A_350]: (~r2_hidden(D_349, k4_xboole_0(k4_xboole_0(A_350, k1_xboole_0), A_350)) | ~r2_hidden(D_349, k4_xboole_0(A_350, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1689, c_2, c_472, c_9901])).
% 11.68/4.39  tff(c_10391, plain, (![D_8]: (~r2_hidden(D_8, k4_xboole_0(k1_xboole_0, k1_xboole_0)))), inference(resolution, [status(thm)], [c_1800, c_10352])).
% 11.68/4.39  tff(c_10458, plain, (![D_8]: (~r2_hidden(D_8, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_1678, c_10391])).
% 11.68/4.39  tff(c_222, plain, (![A_63]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_63))), inference(superposition, [status(thm), theory('equality')], [c_96, c_188])).
% 11.68/4.39  tff(c_238, plain, (![B_19]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k3_xboole_0(k1_xboole_0, B_19))), inference(superposition, [status(thm), theory('equality')], [c_222, c_44])).
% 11.68/4.39  tff(c_252, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_96, c_238])).
% 11.68/4.39  tff(c_197, plain, (![A_51]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_51))), inference(superposition, [status(thm), theory('equality')], [c_96, c_188])).
% 11.68/4.39  tff(c_255, plain, (![A_51]: (k4_xboole_0(k1_xboole_0, A_51)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_252, c_197])).
% 11.68/4.39  tff(c_26, plain, (![D_14, A_9, B_10]: (r2_hidden(D_14, A_9) | ~r2_hidden(D_14, k4_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.68/4.39  tff(c_14430, plain, (![A_425, B_426, A_427, B_428]: (r2_hidden('#skF_2'(A_425, B_426, k4_xboole_0(A_427, B_428)), A_427) | r2_hidden('#skF_1'(A_425, B_426, k4_xboole_0(A_427, B_428)), A_425) | k4_xboole_0(A_427, B_428)=k3_xboole_0(A_425, B_426))), inference(resolution, [status(thm)], [c_1991, c_26])).
% 11.68/4.39  tff(c_14625, plain, (![A_425, B_426, A_51]: (r2_hidden('#skF_2'(A_425, B_426, k4_xboole_0(k1_xboole_0, A_51)), k1_xboole_0) | r2_hidden('#skF_1'(A_425, B_426, k1_xboole_0), A_425) | k4_xboole_0(k1_xboole_0, A_51)=k3_xboole_0(A_425, B_426))), inference(superposition, [status(thm), theory('equality')], [c_255, c_14430])).
% 11.68/4.39  tff(c_14685, plain, (![A_425, B_426]: (r2_hidden('#skF_2'(A_425, B_426, k1_xboole_0), k1_xboole_0) | r2_hidden('#skF_1'(A_425, B_426, k1_xboole_0), A_425) | k3_xboole_0(A_425, B_426)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_255, c_255, c_14625])).
% 11.68/4.39  tff(c_14689, plain, (![A_429, B_430]: (r2_hidden('#skF_1'(A_429, B_430, k1_xboole_0), A_429) | k3_xboole_0(A_429, B_430)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_10458, c_14685])).
% 11.68/4.39  tff(c_609, plain, (![A_102, B_103]: (m1_subset_1(k2_pre_topc(A_102, B_103), k1_zfmisc_1(u1_struct_0(A_102))) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.68/4.39  tff(c_46, plain, (![A_20, B_21, C_22]: (k7_subset_1(A_20, B_21, C_22)=k4_xboole_0(B_21, C_22) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.68/4.39  tff(c_13623, plain, (![A_405, B_406, C_407]: (k7_subset_1(u1_struct_0(A_405), k2_pre_topc(A_405, B_406), C_407)=k4_xboole_0(k2_pre_topc(A_405, B_406), C_407) | ~m1_subset_1(B_406, k1_zfmisc_1(u1_struct_0(A_405))) | ~l1_pre_topc(A_405))), inference(resolution, [status(thm)], [c_609, c_46])).
% 11.68/4.39  tff(c_13627, plain, (![C_407]: (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), C_407)=k4_xboole_0(k2_pre_topc('#skF_5', '#skF_6'), C_407) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_60, c_13623])).
% 11.68/4.39  tff(c_13635, plain, (![C_408]: (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), C_408)=k4_xboole_0(k2_pre_topc('#skF_5', '#skF_6'), C_408))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_13627])).
% 11.68/4.39  tff(c_72, plain, (v3_pre_topc('#skF_6', '#skF_5') | k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_111])).
% 11.68/4.39  tff(c_267, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_171, c_72])).
% 11.68/4.39  tff(c_13645, plain, (k4_xboole_0(k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_13635, c_267])).
% 11.68/4.39  tff(c_13692, plain, (![D_14]: (~r2_hidden(D_14, '#skF_6') | ~r2_hidden(D_14, k2_tops_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_13645, c_24])).
% 11.68/4.39  tff(c_17803, plain, (![B_492]: (~r2_hidden('#skF_1'(k2_tops_1('#skF_5', '#skF_6'), B_492, k1_xboole_0), '#skF_6') | k3_xboole_0(k2_tops_1('#skF_5', '#skF_6'), B_492)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14689, c_13692])).
% 11.68/4.39  tff(c_17811, plain, (r2_hidden('#skF_2'(k2_tops_1('#skF_5', '#skF_6'), '#skF_6', k1_xboole_0), k1_xboole_0) | k3_xboole_0(k2_tops_1('#skF_5', '#skF_6'), '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_17803])).
% 11.68/4.39  tff(c_17816, plain, (r2_hidden('#skF_2'(k2_tops_1('#skF_5', '#skF_6'), '#skF_6', k1_xboole_0), k1_xboole_0) | k3_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_17811])).
% 11.68/4.39  tff(c_17817, plain, (k3_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_10458, c_17816])).
% 11.68/4.39  tff(c_38, plain, (![A_9, B_10, C_11]: (r2_hidden('#skF_3'(A_9, B_10, C_11), A_9) | r2_hidden('#skF_4'(A_9, B_10, C_11), C_11) | k4_xboole_0(A_9, B_10)=C_11)), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.68/4.39  tff(c_10485, plain, (![D_353]: (~r2_hidden(D_353, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_1678, c_10391])).
% 11.68/4.39  tff(c_10968, plain, (![A_367, B_368]: (r2_hidden('#skF_3'(A_367, B_368, k1_xboole_0), A_367) | k4_xboole_0(A_367, B_368)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_10485])).
% 11.68/4.39  tff(c_372, plain, (![A_80, B_81, C_82]: (k7_subset_1(A_80, B_81, C_82)=k4_xboole_0(B_81, C_82) | ~m1_subset_1(B_81, k1_zfmisc_1(A_80)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.68/4.39  tff(c_375, plain, (![C_82]: (k7_subset_1(u1_struct_0('#skF_5'), '#skF_6', C_82)=k4_xboole_0('#skF_6', C_82))), inference(resolution, [status(thm)], [c_60, c_372])).
% 11.68/4.39  tff(c_2383, plain, (![A_165, B_166]: (k7_subset_1(u1_struct_0(A_165), B_166, k2_tops_1(A_165, B_166))=k1_tops_1(A_165, B_166) | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0(A_165))) | ~l1_pre_topc(A_165))), inference(cnfTransformation, [status(thm)], [f_99])).
% 11.68/4.39  tff(c_2387, plain, (k7_subset_1(u1_struct_0('#skF_5'), '#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k1_tops_1('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_60, c_2383])).
% 11.68/4.39  tff(c_2391, plain, (k4_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k1_tops_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_375, c_2387])).
% 11.68/4.39  tff(c_2416, plain, (![D_14]: (r2_hidden(D_14, '#skF_6') | ~r2_hidden(D_14, k1_tops_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_2391, c_26])).
% 11.68/4.39  tff(c_12450, plain, (![B_390]: (r2_hidden('#skF_3'(k1_tops_1('#skF_5', '#skF_6'), B_390, k1_xboole_0), '#skF_6') | k4_xboole_0(k1_tops_1('#skF_5', '#skF_6'), B_390)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10968, c_2416])).
% 11.68/4.39  tff(c_12453, plain, (r2_hidden('#skF_4'(k1_tops_1('#skF_5', '#skF_6'), '#skF_6', k1_xboole_0), k1_xboole_0) | k4_xboole_0(k1_tops_1('#skF_5', '#skF_6'), '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_12450, c_36])).
% 11.68/4.39  tff(c_12456, plain, (k4_xboole_0(k1_tops_1('#skF_5', '#skF_6'), '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_10458, c_12453])).
% 11.68/4.39  tff(c_12493, plain, (k4_xboole_0(k1_tops_1('#skF_5', '#skF_6'), k1_xboole_0)=k3_xboole_0(k1_tops_1('#skF_5', '#skF_6'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_12456, c_44])).
% 11.68/4.39  tff(c_12506, plain, (k4_xboole_0(k1_tops_1('#skF_5', '#skF_6'), k1_xboole_0)=k3_xboole_0('#skF_6', k1_tops_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_12493])).
% 11.68/4.39  tff(c_14348, plain, (k3_xboole_0('#skF_6', k1_tops_1('#skF_5', '#skF_6'))=k1_tops_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_13130, c_12506])).
% 11.68/4.39  tff(c_2419, plain, (k4_xboole_0('#skF_6', k1_tops_1('#skF_5', '#skF_6'))=k3_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2391, c_44])).
% 11.68/4.39  tff(c_2658, plain, (k4_xboole_0('#skF_6', k3_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6')))=k3_xboole_0('#skF_6', k1_tops_1('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2419, c_44])).
% 11.68/4.39  tff(c_14350, plain, (k4_xboole_0('#skF_6', k3_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6')))=k1_tops_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_14348, c_2658])).
% 11.68/4.39  tff(c_17819, plain, (k4_xboole_0('#skF_6', k1_xboole_0)=k1_tops_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_17817, c_14350])).
% 11.68/4.39  tff(c_17822, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_13130, c_17819])).
% 11.68/4.39  tff(c_17824, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10483, c_17822])).
% 11.68/4.39  tff(c_17825, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')!=k2_tops_1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_66])).
% 11.68/4.39  tff(c_17826, plain, (v3_pre_topc('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_66])).
% 11.68/4.39  tff(c_56, plain, (![B_38, D_44, C_42, A_30]: (k1_tops_1(B_38, D_44)=D_44 | ~v3_pre_topc(D_44, B_38) | ~m1_subset_1(D_44, k1_zfmisc_1(u1_struct_0(B_38))) | ~m1_subset_1(C_42, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(B_38) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.68/4.39  tff(c_25434, plain, (![C_743, A_744]: (~m1_subset_1(C_743, k1_zfmisc_1(u1_struct_0(A_744))) | ~l1_pre_topc(A_744) | ~v2_pre_topc(A_744))), inference(splitLeft, [status(thm)], [c_56])).
% 11.68/4.39  tff(c_25440, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_60, c_25434])).
% 11.68/4.39  tff(c_25445, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_25440])).
% 11.68/4.39  tff(c_25731, plain, (![B_749, D_750]: (k1_tops_1(B_749, D_750)=D_750 | ~v3_pre_topc(D_750, B_749) | ~m1_subset_1(D_750, k1_zfmisc_1(u1_struct_0(B_749))) | ~l1_pre_topc(B_749))), inference(splitRight, [status(thm)], [c_56])).
% 11.68/4.39  tff(c_25737, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6' | ~v3_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_60, c_25731])).
% 11.68/4.39  tff(c_25741, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_17826, c_25737])).
% 11.68/4.39  tff(c_52, plain, (![A_27, B_29]: (k7_subset_1(u1_struct_0(A_27), k2_pre_topc(A_27, B_29), k1_tops_1(A_27, B_29))=k2_tops_1(A_27, B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.68/4.39  tff(c_25761, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_25741, c_52])).
% 11.68/4.39  tff(c_25765, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_25761])).
% 11.68/4.39  tff(c_25767, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17825, c_25765])).
% 11.68/4.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.68/4.39  
% 11.68/4.39  Inference rules
% 11.68/4.39  ----------------------
% 11.68/4.39  #Ref     : 0
% 11.68/4.39  #Sup     : 5722
% 11.68/4.39  #Fact    : 0
% 11.68/4.39  #Define  : 0
% 11.68/4.39  #Split   : 16
% 11.68/4.39  #Chain   : 0
% 11.68/4.39  #Close   : 0
% 11.68/4.39  
% 11.68/4.39  Ordering : KBO
% 11.68/4.39  
% 11.68/4.39  Simplification rules
% 11.68/4.39  ----------------------
% 11.68/4.39  #Subsume      : 1001
% 11.68/4.39  #Demod        : 6032
% 11.68/4.39  #Tautology    : 2090
% 11.68/4.39  #SimpNegUnit  : 183
% 11.68/4.39  #BackRed      : 174
% 11.68/4.39  
% 11.68/4.39  #Partial instantiations: 0
% 11.68/4.39  #Strategies tried      : 1
% 11.68/4.39  
% 11.68/4.39  Timing (in seconds)
% 11.68/4.39  ----------------------
% 11.68/4.40  Preprocessing        : 0.38
% 11.68/4.40  Parsing              : 0.17
% 11.68/4.40  CNF conversion       : 0.03
% 11.68/4.40  Main loop            : 3.22
% 11.68/4.40  Inferencing          : 0.76
% 11.68/4.40  Reduction            : 1.47
% 11.68/4.40  Demodulation         : 1.23
% 11.68/4.40  BG Simplification    : 0.10
% 11.68/4.40  Subsumption          : 0.65
% 11.68/4.40  Abstraction          : 0.15
% 11.68/4.40  MUC search           : 0.00
% 11.68/4.40  Cooper               : 0.00
% 11.68/4.40  Total                : 3.65
% 11.68/4.40  Index Insertion      : 0.00
% 11.68/4.40  Index Deletion       : 0.00
% 11.68/4.40  Index Matching       : 0.00
% 11.68/4.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
