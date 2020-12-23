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
% DateTime   : Thu Dec  3 10:21:04 EST 2020

% Result     : Theorem 26.68s
% Output     : CNFRefutation 26.89s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 347 expanded)
%              Number of leaves         :   47 ( 133 expanded)
%              Depth                    :   11
%              Number of atoms          :  240 ( 681 expanded)
%              Number of equality atoms :  100 ( 235 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_156,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_123,axiom,(
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

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_144,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_137,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_85,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_74,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_148,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_68,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_241,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_66,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_64,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_62,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_4333,plain,(
    ! [A_192,B_193,C_194] :
      ( k4_subset_1(A_192,B_193,C_194) = k2_xboole_0(B_193,C_194)
      | ~ m1_subset_1(C_194,k1_zfmisc_1(A_192))
      | ~ m1_subset_1(B_193,k1_zfmisc_1(A_192)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4549,plain,(
    ! [B_197] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_197,'#skF_2') = k2_xboole_0(B_197,'#skF_2')
      | ~ m1_subset_1(B_197,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_62,c_4333])).

tff(c_4570,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_2') = k2_xboole_0('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_4549])).

tff(c_4579,plain,(
    ! [A_198,B_199,C_200] :
      ( m1_subset_1(k4_subset_1(A_198,B_199,C_200),k1_zfmisc_1(A_198))
      | ~ m1_subset_1(C_200,k1_zfmisc_1(A_198))
      | ~ m1_subset_1(B_199,k1_zfmisc_1(A_198)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4598,plain,
    ( m1_subset_1(k2_xboole_0('#skF_2','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4570,c_4579])).

tff(c_4606,plain,(
    m1_subset_1(k2_xboole_0('#skF_2','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_62,c_4598])).

tff(c_52,plain,(
    ! [C_62,A_50,D_64,B_58] :
      ( v3_pre_topc(C_62,A_50)
      | k1_tops_1(A_50,C_62) != C_62
      | ~ m1_subset_1(D_64,k1_zfmisc_1(u1_struct_0(B_58)))
      | ~ m1_subset_1(C_62,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(B_58)
      | ~ l1_pre_topc(A_50)
      | ~ v2_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_7779,plain,(
    ! [D_253,B_254] :
      ( ~ m1_subset_1(D_253,k1_zfmisc_1(u1_struct_0(B_254)))
      | ~ l1_pre_topc(B_254) ) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_7782,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4606,c_7779])).

tff(c_7801,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_7782])).

tff(c_8955,plain,(
    ! [C_264,A_265] :
      ( v3_pre_topc(C_264,A_265)
      | k1_tops_1(A_265,C_264) != C_264
      | ~ m1_subset_1(C_264,k1_zfmisc_1(u1_struct_0(A_265)))
      | ~ l1_pre_topc(A_265)
      | ~ v2_pre_topc(A_265) ) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_8976,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_8955])).

tff(c_8986,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_8976])).

tff(c_8987,plain,(
    k1_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_241,c_8986])).

tff(c_2942,plain,(
    ! [A_169,B_170,C_171] :
      ( k7_subset_1(A_169,B_170,C_171) = k4_xboole_0(B_170,C_171)
      | ~ m1_subset_1(B_170,k1_zfmisc_1(A_169)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2951,plain,(
    ! [C_171] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_171) = k4_xboole_0('#skF_2',C_171) ),
    inference(resolution,[status(thm)],[c_62,c_2942])).

tff(c_5536,plain,(
    ! [A_214,B_215] :
      ( k7_subset_1(u1_struct_0(A_214),B_215,k2_tops_1(A_214,B_215)) = k1_tops_1(A_214,B_215)
      | ~ m1_subset_1(B_215,k1_zfmisc_1(u1_struct_0(A_214)))
      | ~ l1_pre_topc(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_5551,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_5536])).

tff(c_5561,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2951,c_5551])).

tff(c_18,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_110,plain,(
    ! [A_78,B_79] : r1_tarski(k4_xboole_0(A_78,B_79),A_78) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_113,plain,(
    ! [A_15] : r1_tarski(A_15,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_110])).

tff(c_160,plain,(
    ! [A_89,B_90] :
      ( k4_xboole_0(A_89,B_90) = k1_xboole_0
      | ~ r1_tarski(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_171,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_113,c_160])).

tff(c_46,plain,(
    ! [A_43,B_44] :
      ( m1_subset_1(A_43,k1_zfmisc_1(B_44))
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_861,plain,(
    ! [A_125,B_126] :
      ( k4_xboole_0(A_125,B_126) = k3_subset_1(A_125,B_126)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(A_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_11038,plain,(
    ! [B_294,A_295] :
      ( k4_xboole_0(B_294,A_295) = k3_subset_1(B_294,A_295)
      | ~ r1_tarski(A_295,B_294) ) ),
    inference(resolution,[status(thm)],[c_46,c_861])).

tff(c_11059,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k3_subset_1(A_15,A_15) ),
    inference(resolution,[status(thm)],[c_113,c_11038])).

tff(c_11075,plain,(
    ! [A_296] : k3_subset_1(A_296,A_296) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_11059])).

tff(c_1675,plain,(
    ! [A_148,B_149] :
      ( k3_subset_1(A_148,k3_subset_1(A_148,B_149)) = B_149
      | ~ m1_subset_1(B_149,k1_zfmisc_1(A_148)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1680,plain,(
    ! [B_44,A_43] :
      ( k3_subset_1(B_44,k3_subset_1(B_44,A_43)) = A_43
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_46,c_1675])).

tff(c_11080,plain,(
    ! [A_296] :
      ( k3_subset_1(A_296,k1_xboole_0) = A_296
      | ~ r1_tarski(A_296,A_296) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11075,c_1680])).

tff(c_11092,plain,(
    ! [A_296] : k3_subset_1(A_296,k1_xboole_0) = A_296 ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_11080])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_13769,plain,(
    ! [B_323,A_324,C_325] :
      ( k7_subset_1(B_323,A_324,C_325) = k4_xboole_0(A_324,C_325)
      | ~ r1_tarski(A_324,B_323) ) ),
    inference(resolution,[status(thm)],[c_46,c_2942])).

tff(c_73357,plain,(
    ! [B_705,A_706,C_707] :
      ( k7_subset_1(B_705,A_706,C_707) = k4_xboole_0(A_706,C_707)
      | k4_xboole_0(A_706,B_705) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_13769])).

tff(c_73407,plain,
    ( k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2')
    | k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_73357,c_148])).

tff(c_73483,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_73407])).

tff(c_48,plain,(
    ! [A_45,B_46] :
      ( m1_subset_1(k2_tops_1(A_45,B_46),k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_5656,plain,(
    ! [A_216,B_217] :
      ( k4_subset_1(u1_struct_0(A_216),B_217,k2_tops_1(A_216,B_217)) = k2_pre_topc(A_216,B_217)
      | ~ m1_subset_1(B_217,k1_zfmisc_1(u1_struct_0(A_216)))
      | ~ l1_pre_topc(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_5671,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_5656])).

tff(c_5681,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_5671])).

tff(c_44,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(A_43,B_44)
      | ~ m1_subset_1(A_43,k1_zfmisc_1(B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_25751,plain,(
    ! [A_411,B_412,C_413] :
      ( r1_tarski(k4_subset_1(A_411,B_412,C_413),A_411)
      | ~ m1_subset_1(C_413,k1_zfmisc_1(A_411))
      | ~ m1_subset_1(B_412,k1_zfmisc_1(A_411)) ) ),
    inference(resolution,[status(thm)],[c_4579,c_44])).

tff(c_25788,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_5681,c_25751])).

tff(c_25807,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_25788])).

tff(c_108242,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_25807])).

tff(c_108245,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_108242])).

tff(c_108252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_108245])).

tff(c_108253,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_25807])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_108285,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_108253,c_6])).

tff(c_108303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73483,c_108285])).

tff(c_108305,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_73407])).

tff(c_73449,plain,
    ( k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2')
    | k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_73357])).

tff(c_108530,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108305,c_73449])).

tff(c_2001,plain,(
    ! [A_156,B_157,C_158] : k4_xboole_0(k3_xboole_0(A_156,B_157),C_158) = k3_xboole_0(A_156,k4_xboole_0(B_157,C_158)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_454,plain,(
    ! [A_109,B_110] : k5_xboole_0(A_109,k3_xboole_0(A_109,B_110)) = k4_xboole_0(A_109,B_110) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_478,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_454])).

tff(c_484,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_478])).

tff(c_494,plain,(
    ! [A_112,B_113,C_114] : k3_xboole_0(k3_xboole_0(A_112,B_113),C_114) = k3_xboole_0(A_112,k3_xboole_0(B_113,C_114)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_553,plain,(
    ! [A_1,C_114] : k3_xboole_0(A_1,k3_xboole_0(A_1,C_114)) = k3_xboole_0(A_1,C_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_494])).

tff(c_28,plain,(
    ! [B_25,A_24] : k2_tarski(B_25,A_24) = k2_tarski(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_342,plain,(
    ! [A_103,B_104] : k1_setfam_1(k2_tarski(A_103,B_104)) = k3_xboole_0(A_103,B_104) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_357,plain,(
    ! [B_105,A_106] : k1_setfam_1(k2_tarski(B_105,A_106)) = k3_xboole_0(A_106,B_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_342])).

tff(c_42,plain,(
    ! [A_41,B_42] : k1_setfam_1(k2_tarski(A_41,B_42)) = k3_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_363,plain,(
    ! [B_105,A_106] : k3_xboole_0(B_105,A_106) = k3_xboole_0(A_106,B_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_42])).

tff(c_996,plain,(
    ! [A_129,B_130] : k5_xboole_0(A_129,k3_xboole_0(B_130,A_129)) = k4_xboole_0(A_129,B_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_454])).

tff(c_1015,plain,(
    ! [A_1,C_114] : k5_xboole_0(k3_xboole_0(A_1,C_114),k3_xboole_0(A_1,C_114)) = k4_xboole_0(k3_xboole_0(A_1,C_114),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_996])).

tff(c_1048,plain,(
    ! [A_1,C_114] : k4_xboole_0(k3_xboole_0(A_1,C_114),A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_484,c_1015])).

tff(c_2027,plain,(
    ! [C_158,B_157] : k3_xboole_0(C_158,k4_xboole_0(B_157,C_158)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2001,c_1048])).

tff(c_108671,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_108530,c_2027])).

tff(c_8,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_620,plain,(
    ! [A_117,C_118] : k3_xboole_0(A_117,k3_xboole_0(A_117,C_118)) = k3_xboole_0(A_117,C_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_494])).

tff(c_640,plain,(
    ! [A_117,C_118] : k5_xboole_0(A_117,k3_xboole_0(A_117,C_118)) = k4_xboole_0(A_117,k3_xboole_0(A_117,C_118)) ),
    inference(superposition,[status(thm),theory(equality)],[c_620,c_8])).

tff(c_688,plain,(
    ! [A_117,C_118] : k4_xboole_0(A_117,k3_xboole_0(A_117,C_118)) = k4_xboole_0(A_117,C_118) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_640])).

tff(c_64144,plain,(
    ! [B_673,A_674] :
      ( k4_xboole_0(B_673,A_674) = k3_subset_1(B_673,A_674)
      | k4_xboole_0(A_674,B_673) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_11038])).

tff(c_64300,plain,(
    ! [A_1,C_114] : k4_xboole_0(A_1,k3_xboole_0(A_1,C_114)) = k3_subset_1(A_1,k3_xboole_0(A_1,C_114)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1048,c_64144])).

tff(c_64390,plain,(
    ! [A_1,C_114] : k3_subset_1(A_1,k3_xboole_0(A_1,C_114)) = k4_xboole_0(A_1,C_114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_688,c_64300])).

tff(c_108720,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_108671,c_64390])).

tff(c_108872,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5561,c_11092,c_108720])).

tff(c_108874,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8987,c_108872])).

tff(c_108875,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_109153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_108875])).

tff(c_109154,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_109242,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109154,c_68])).

tff(c_113069,plain,(
    ! [A_964,B_965,C_966] :
      ( k4_subset_1(A_964,B_965,C_966) = k2_xboole_0(B_965,C_966)
      | ~ m1_subset_1(C_966,k1_zfmisc_1(A_964))
      | ~ m1_subset_1(B_965,k1_zfmisc_1(A_964)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_113492,plain,(
    ! [B_971] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_971,'#skF_2') = k2_xboole_0(B_971,'#skF_2')
      | ~ m1_subset_1(B_971,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_62,c_113069])).

tff(c_113513,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_2') = k2_xboole_0('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_113492])).

tff(c_113522,plain,(
    ! [A_972,B_973,C_974] :
      ( m1_subset_1(k4_subset_1(A_972,B_973,C_974),k1_zfmisc_1(A_972))
      | ~ m1_subset_1(C_974,k1_zfmisc_1(A_972))
      | ~ m1_subset_1(B_973,k1_zfmisc_1(A_972)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_113541,plain,
    ( m1_subset_1(k2_xboole_0('#skF_2','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_113513,c_113522])).

tff(c_113549,plain,(
    m1_subset_1(k2_xboole_0('#skF_2','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_62,c_113541])).

tff(c_54,plain,(
    ! [B_58,D_64,C_62,A_50] :
      ( k1_tops_1(B_58,D_64) = D_64
      | ~ v3_pre_topc(D_64,B_58)
      | ~ m1_subset_1(D_64,k1_zfmisc_1(u1_struct_0(B_58)))
      | ~ m1_subset_1(C_62,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(B_58)
      | ~ l1_pre_topc(A_50)
      | ~ v2_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_116361,plain,(
    ! [C_1014,A_1015] :
      ( ~ m1_subset_1(C_1014,k1_zfmisc_1(u1_struct_0(A_1015)))
      | ~ l1_pre_topc(A_1015)
      | ~ v2_pre_topc(A_1015) ) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_116364,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_113549,c_116361])).

tff(c_116386,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_116364])).

tff(c_117119,plain,(
    ! [B_1025,D_1026] :
      ( k1_tops_1(B_1025,D_1026) = D_1026
      | ~ v3_pre_topc(D_1026,B_1025)
      | ~ m1_subset_1(D_1026,k1_zfmisc_1(u1_struct_0(B_1025)))
      | ~ l1_pre_topc(B_1025) ) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_117140,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_117119])).

tff(c_117150,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_109154,c_117140])).

tff(c_50,plain,(
    ! [A_47,B_49] :
      ( k7_subset_1(u1_struct_0(A_47),k2_pre_topc(A_47,B_49),k1_tops_1(A_47,B_49)) = k2_tops_1(A_47,B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_117166,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_117150,c_50])).

tff(c_117170,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_117166])).

tff(c_117172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109242,c_117170])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:48:40 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 26.68/18.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.81/18.08  
% 26.81/18.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.81/18.08  %$ v3_pre_topc > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 26.81/18.08  
% 26.81/18.08  %Foreground sorts:
% 26.81/18.08  
% 26.81/18.08  
% 26.81/18.08  %Background operators:
% 26.81/18.08  
% 26.81/18.08  
% 26.81/18.08  %Foreground operators:
% 26.81/18.08  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 26.81/18.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 26.81/18.08  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 26.81/18.08  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 26.81/18.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 26.81/18.08  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 26.81/18.08  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 26.81/18.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 26.81/18.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 26.81/18.08  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 26.81/18.08  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 26.81/18.08  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 26.81/18.08  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 26.81/18.08  tff('#skF_2', type, '#skF_2': $i).
% 26.81/18.08  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 26.81/18.08  tff('#skF_1', type, '#skF_1': $i).
% 26.81/18.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 26.81/18.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 26.81/18.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 26.81/18.08  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 26.81/18.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 26.81/18.08  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 26.81/18.08  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 26.81/18.08  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 26.81/18.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 26.81/18.08  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 26.81/18.08  
% 26.89/18.11  tff(f_156, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 26.89/18.11  tff(f_79, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 26.89/18.11  tff(f_69, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 26.89/18.11  tff(f_123, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 26.89/18.11  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 26.89/18.11  tff(f_144, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 26.89/18.11  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 26.89/18.11  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 26.89/18.11  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 26.89/18.11  tff(f_89, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 26.89/18.11  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 26.89/18.11  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 26.89/18.11  tff(f_95, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 26.89/18.11  tff(f_137, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 26.89/18.11  tff(f_49, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 26.89/18.11  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 26.89/18.11  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 26.89/18.11  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 26.89/18.11  tff(f_55, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 26.89/18.11  tff(f_85, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 26.89/18.11  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 26.89/18.11  tff(c_74, plain, (v3_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 26.89/18.11  tff(c_148, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_74])).
% 26.89/18.11  tff(c_68, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 26.89/18.11  tff(c_241, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_68])).
% 26.89/18.11  tff(c_66, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 26.89/18.11  tff(c_64, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 26.89/18.11  tff(c_62, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 26.89/18.11  tff(c_4333, plain, (![A_192, B_193, C_194]: (k4_subset_1(A_192, B_193, C_194)=k2_xboole_0(B_193, C_194) | ~m1_subset_1(C_194, k1_zfmisc_1(A_192)) | ~m1_subset_1(B_193, k1_zfmisc_1(A_192)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 26.89/18.11  tff(c_4549, plain, (![B_197]: (k4_subset_1(u1_struct_0('#skF_1'), B_197, '#skF_2')=k2_xboole_0(B_197, '#skF_2') | ~m1_subset_1(B_197, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_62, c_4333])).
% 26.89/18.11  tff(c_4570, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_2')=k2_xboole_0('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_4549])).
% 26.89/18.11  tff(c_4579, plain, (![A_198, B_199, C_200]: (m1_subset_1(k4_subset_1(A_198, B_199, C_200), k1_zfmisc_1(A_198)) | ~m1_subset_1(C_200, k1_zfmisc_1(A_198)) | ~m1_subset_1(B_199, k1_zfmisc_1(A_198)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 26.89/18.11  tff(c_4598, plain, (m1_subset_1(k2_xboole_0('#skF_2', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4570, c_4579])).
% 26.89/18.11  tff(c_4606, plain, (m1_subset_1(k2_xboole_0('#skF_2', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_62, c_4598])).
% 26.89/18.11  tff(c_52, plain, (![C_62, A_50, D_64, B_58]: (v3_pre_topc(C_62, A_50) | k1_tops_1(A_50, C_62)!=C_62 | ~m1_subset_1(D_64, k1_zfmisc_1(u1_struct_0(B_58))) | ~m1_subset_1(C_62, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(B_58) | ~l1_pre_topc(A_50) | ~v2_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_123])).
% 26.89/18.11  tff(c_7779, plain, (![D_253, B_254]: (~m1_subset_1(D_253, k1_zfmisc_1(u1_struct_0(B_254))) | ~l1_pre_topc(B_254))), inference(splitLeft, [status(thm)], [c_52])).
% 26.89/18.11  tff(c_7782, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4606, c_7779])).
% 26.89/18.11  tff(c_7801, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_7782])).
% 26.89/18.11  tff(c_8955, plain, (![C_264, A_265]: (v3_pre_topc(C_264, A_265) | k1_tops_1(A_265, C_264)!=C_264 | ~m1_subset_1(C_264, k1_zfmisc_1(u1_struct_0(A_265))) | ~l1_pre_topc(A_265) | ~v2_pre_topc(A_265))), inference(splitRight, [status(thm)], [c_52])).
% 26.89/18.11  tff(c_8976, plain, (v3_pre_topc('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_8955])).
% 26.89/18.11  tff(c_8986, plain, (v3_pre_topc('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_8976])).
% 26.89/18.11  tff(c_8987, plain, (k1_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_241, c_8986])).
% 26.89/18.11  tff(c_2942, plain, (![A_169, B_170, C_171]: (k7_subset_1(A_169, B_170, C_171)=k4_xboole_0(B_170, C_171) | ~m1_subset_1(B_170, k1_zfmisc_1(A_169)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 26.89/18.11  tff(c_2951, plain, (![C_171]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_171)=k4_xboole_0('#skF_2', C_171))), inference(resolution, [status(thm)], [c_62, c_2942])).
% 26.89/18.11  tff(c_5536, plain, (![A_214, B_215]: (k7_subset_1(u1_struct_0(A_214), B_215, k2_tops_1(A_214, B_215))=k1_tops_1(A_214, B_215) | ~m1_subset_1(B_215, k1_zfmisc_1(u1_struct_0(A_214))) | ~l1_pre_topc(A_214))), inference(cnfTransformation, [status(thm)], [f_144])).
% 26.89/18.11  tff(c_5551, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_5536])).
% 26.89/18.11  tff(c_5561, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2951, c_5551])).
% 26.89/18.11  tff(c_18, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_45])).
% 26.89/18.11  tff(c_110, plain, (![A_78, B_79]: (r1_tarski(k4_xboole_0(A_78, B_79), A_78))), inference(cnfTransformation, [status(thm)], [f_43])).
% 26.89/18.11  tff(c_113, plain, (![A_15]: (r1_tarski(A_15, A_15))), inference(superposition, [status(thm), theory('equality')], [c_18, c_110])).
% 26.89/18.11  tff(c_160, plain, (![A_89, B_90]: (k4_xboole_0(A_89, B_90)=k1_xboole_0 | ~r1_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_31])).
% 26.89/18.11  tff(c_171, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_113, c_160])).
% 26.89/18.11  tff(c_46, plain, (![A_43, B_44]: (m1_subset_1(A_43, k1_zfmisc_1(B_44)) | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_89])).
% 26.89/18.11  tff(c_861, plain, (![A_125, B_126]: (k4_xboole_0(A_125, B_126)=k3_subset_1(A_125, B_126) | ~m1_subset_1(B_126, k1_zfmisc_1(A_125)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 26.89/18.11  tff(c_11038, plain, (![B_294, A_295]: (k4_xboole_0(B_294, A_295)=k3_subset_1(B_294, A_295) | ~r1_tarski(A_295, B_294))), inference(resolution, [status(thm)], [c_46, c_861])).
% 26.89/18.11  tff(c_11059, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k3_subset_1(A_15, A_15))), inference(resolution, [status(thm)], [c_113, c_11038])).
% 26.89/18.11  tff(c_11075, plain, (![A_296]: (k3_subset_1(A_296, A_296)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_171, c_11059])).
% 26.89/18.11  tff(c_1675, plain, (![A_148, B_149]: (k3_subset_1(A_148, k3_subset_1(A_148, B_149))=B_149 | ~m1_subset_1(B_149, k1_zfmisc_1(A_148)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 26.89/18.11  tff(c_1680, plain, (![B_44, A_43]: (k3_subset_1(B_44, k3_subset_1(B_44, A_43))=A_43 | ~r1_tarski(A_43, B_44))), inference(resolution, [status(thm)], [c_46, c_1675])).
% 26.89/18.11  tff(c_11080, plain, (![A_296]: (k3_subset_1(A_296, k1_xboole_0)=A_296 | ~r1_tarski(A_296, A_296))), inference(superposition, [status(thm), theory('equality')], [c_11075, c_1680])).
% 26.89/18.11  tff(c_11092, plain, (![A_296]: (k3_subset_1(A_296, k1_xboole_0)=A_296)), inference(demodulation, [status(thm), theory('equality')], [c_113, c_11080])).
% 26.89/18.11  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 26.89/18.11  tff(c_13769, plain, (![B_323, A_324, C_325]: (k7_subset_1(B_323, A_324, C_325)=k4_xboole_0(A_324, C_325) | ~r1_tarski(A_324, B_323))), inference(resolution, [status(thm)], [c_46, c_2942])).
% 26.89/18.11  tff(c_73357, plain, (![B_705, A_706, C_707]: (k7_subset_1(B_705, A_706, C_707)=k4_xboole_0(A_706, C_707) | k4_xboole_0(A_706, B_705)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_13769])).
% 26.89/18.11  tff(c_73407, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2') | k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_73357, c_148])).
% 26.89/18.11  tff(c_73483, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_73407])).
% 26.89/18.11  tff(c_48, plain, (![A_45, B_46]: (m1_subset_1(k2_tops_1(A_45, B_46), k1_zfmisc_1(u1_struct_0(A_45))) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_95])).
% 26.89/18.11  tff(c_5656, plain, (![A_216, B_217]: (k4_subset_1(u1_struct_0(A_216), B_217, k2_tops_1(A_216, B_217))=k2_pre_topc(A_216, B_217) | ~m1_subset_1(B_217, k1_zfmisc_1(u1_struct_0(A_216))) | ~l1_pre_topc(A_216))), inference(cnfTransformation, [status(thm)], [f_137])).
% 26.89/18.11  tff(c_5671, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_5656])).
% 26.89/18.11  tff(c_5681, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_5671])).
% 26.89/18.11  tff(c_44, plain, (![A_43, B_44]: (r1_tarski(A_43, B_44) | ~m1_subset_1(A_43, k1_zfmisc_1(B_44)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 26.89/18.11  tff(c_25751, plain, (![A_411, B_412, C_413]: (r1_tarski(k4_subset_1(A_411, B_412, C_413), A_411) | ~m1_subset_1(C_413, k1_zfmisc_1(A_411)) | ~m1_subset_1(B_412, k1_zfmisc_1(A_411)))), inference(resolution, [status(thm)], [c_4579, c_44])).
% 26.89/18.11  tff(c_25788, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_5681, c_25751])).
% 26.89/18.11  tff(c_25807, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_25788])).
% 26.89/18.11  tff(c_108242, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_25807])).
% 26.89/18.11  tff(c_108245, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_108242])).
% 26.89/18.11  tff(c_108252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_108245])).
% 26.89/18.11  tff(c_108253, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_25807])).
% 26.89/18.11  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 26.89/18.11  tff(c_108285, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))=k1_xboole_0), inference(resolution, [status(thm)], [c_108253, c_6])).
% 26.89/18.11  tff(c_108303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73483, c_108285])).
% 26.89/18.11  tff(c_108305, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_73407])).
% 26.89/18.11  tff(c_73449, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2') | k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_148, c_73357])).
% 26.89/18.11  tff(c_108530, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_108305, c_73449])).
% 26.89/18.11  tff(c_2001, plain, (![A_156, B_157, C_158]: (k4_xboole_0(k3_xboole_0(A_156, B_157), C_158)=k3_xboole_0(A_156, k4_xboole_0(B_157, C_158)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 26.89/18.11  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 26.89/18.11  tff(c_454, plain, (![A_109, B_110]: (k5_xboole_0(A_109, k3_xboole_0(A_109, B_110))=k4_xboole_0(A_109, B_110))), inference(cnfTransformation, [status(thm)], [f_33])).
% 26.89/18.11  tff(c_478, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_454])).
% 26.89/18.11  tff(c_484, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_171, c_478])).
% 26.89/18.11  tff(c_494, plain, (![A_112, B_113, C_114]: (k3_xboole_0(k3_xboole_0(A_112, B_113), C_114)=k3_xboole_0(A_112, k3_xboole_0(B_113, C_114)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 26.89/18.11  tff(c_553, plain, (![A_1, C_114]: (k3_xboole_0(A_1, k3_xboole_0(A_1, C_114))=k3_xboole_0(A_1, C_114))), inference(superposition, [status(thm), theory('equality')], [c_2, c_494])).
% 26.89/18.11  tff(c_28, plain, (![B_25, A_24]: (k2_tarski(B_25, A_24)=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_55])).
% 26.89/18.11  tff(c_342, plain, (![A_103, B_104]: (k1_setfam_1(k2_tarski(A_103, B_104))=k3_xboole_0(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_85])).
% 26.89/18.11  tff(c_357, plain, (![B_105, A_106]: (k1_setfam_1(k2_tarski(B_105, A_106))=k3_xboole_0(A_106, B_105))), inference(superposition, [status(thm), theory('equality')], [c_28, c_342])).
% 26.89/18.11  tff(c_42, plain, (![A_41, B_42]: (k1_setfam_1(k2_tarski(A_41, B_42))=k3_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_85])).
% 26.89/18.11  tff(c_363, plain, (![B_105, A_106]: (k3_xboole_0(B_105, A_106)=k3_xboole_0(A_106, B_105))), inference(superposition, [status(thm), theory('equality')], [c_357, c_42])).
% 26.89/18.11  tff(c_996, plain, (![A_129, B_130]: (k5_xboole_0(A_129, k3_xboole_0(B_130, A_129))=k4_xboole_0(A_129, B_130))), inference(superposition, [status(thm), theory('equality')], [c_363, c_454])).
% 26.89/18.11  tff(c_1015, plain, (![A_1, C_114]: (k5_xboole_0(k3_xboole_0(A_1, C_114), k3_xboole_0(A_1, C_114))=k4_xboole_0(k3_xboole_0(A_1, C_114), A_1))), inference(superposition, [status(thm), theory('equality')], [c_553, c_996])).
% 26.89/18.11  tff(c_1048, plain, (![A_1, C_114]: (k4_xboole_0(k3_xboole_0(A_1, C_114), A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_484, c_1015])).
% 26.89/18.11  tff(c_2027, plain, (![C_158, B_157]: (k3_xboole_0(C_158, k4_xboole_0(B_157, C_158))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2001, c_1048])).
% 26.89/18.11  tff(c_108671, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_108530, c_2027])).
% 26.89/18.11  tff(c_8, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 26.89/18.11  tff(c_620, plain, (![A_117, C_118]: (k3_xboole_0(A_117, k3_xboole_0(A_117, C_118))=k3_xboole_0(A_117, C_118))), inference(superposition, [status(thm), theory('equality')], [c_2, c_494])).
% 26.89/18.11  tff(c_640, plain, (![A_117, C_118]: (k5_xboole_0(A_117, k3_xboole_0(A_117, C_118))=k4_xboole_0(A_117, k3_xboole_0(A_117, C_118)))), inference(superposition, [status(thm), theory('equality')], [c_620, c_8])).
% 26.89/18.11  tff(c_688, plain, (![A_117, C_118]: (k4_xboole_0(A_117, k3_xboole_0(A_117, C_118))=k4_xboole_0(A_117, C_118))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_640])).
% 26.89/18.11  tff(c_64144, plain, (![B_673, A_674]: (k4_xboole_0(B_673, A_674)=k3_subset_1(B_673, A_674) | k4_xboole_0(A_674, B_673)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_11038])).
% 26.89/18.11  tff(c_64300, plain, (![A_1, C_114]: (k4_xboole_0(A_1, k3_xboole_0(A_1, C_114))=k3_subset_1(A_1, k3_xboole_0(A_1, C_114)))), inference(superposition, [status(thm), theory('equality')], [c_1048, c_64144])).
% 26.89/18.11  tff(c_64390, plain, (![A_1, C_114]: (k3_subset_1(A_1, k3_xboole_0(A_1, C_114))=k4_xboole_0(A_1, C_114))), inference(demodulation, [status(thm), theory('equality')], [c_688, c_64300])).
% 26.89/18.11  tff(c_108720, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_108671, c_64390])).
% 26.89/18.11  tff(c_108872, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5561, c_11092, c_108720])).
% 26.89/18.11  tff(c_108874, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8987, c_108872])).
% 26.89/18.11  tff(c_108875, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_68])).
% 26.89/18.11  tff(c_109153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_148, c_108875])).
% 26.89/18.11  tff(c_109154, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_74])).
% 26.89/18.11  tff(c_109242, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_109154, c_68])).
% 26.89/18.11  tff(c_113069, plain, (![A_964, B_965, C_966]: (k4_subset_1(A_964, B_965, C_966)=k2_xboole_0(B_965, C_966) | ~m1_subset_1(C_966, k1_zfmisc_1(A_964)) | ~m1_subset_1(B_965, k1_zfmisc_1(A_964)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 26.89/18.11  tff(c_113492, plain, (![B_971]: (k4_subset_1(u1_struct_0('#skF_1'), B_971, '#skF_2')=k2_xboole_0(B_971, '#skF_2') | ~m1_subset_1(B_971, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_62, c_113069])).
% 26.89/18.11  tff(c_113513, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_2')=k2_xboole_0('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_113492])).
% 26.89/18.11  tff(c_113522, plain, (![A_972, B_973, C_974]: (m1_subset_1(k4_subset_1(A_972, B_973, C_974), k1_zfmisc_1(A_972)) | ~m1_subset_1(C_974, k1_zfmisc_1(A_972)) | ~m1_subset_1(B_973, k1_zfmisc_1(A_972)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 26.89/18.11  tff(c_113541, plain, (m1_subset_1(k2_xboole_0('#skF_2', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_113513, c_113522])).
% 26.89/18.11  tff(c_113549, plain, (m1_subset_1(k2_xboole_0('#skF_2', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_62, c_113541])).
% 26.89/18.11  tff(c_54, plain, (![B_58, D_64, C_62, A_50]: (k1_tops_1(B_58, D_64)=D_64 | ~v3_pre_topc(D_64, B_58) | ~m1_subset_1(D_64, k1_zfmisc_1(u1_struct_0(B_58))) | ~m1_subset_1(C_62, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(B_58) | ~l1_pre_topc(A_50) | ~v2_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_123])).
% 26.89/18.11  tff(c_116361, plain, (![C_1014, A_1015]: (~m1_subset_1(C_1014, k1_zfmisc_1(u1_struct_0(A_1015))) | ~l1_pre_topc(A_1015) | ~v2_pre_topc(A_1015))), inference(splitLeft, [status(thm)], [c_54])).
% 26.89/18.11  tff(c_116364, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_113549, c_116361])).
% 26.89/18.11  tff(c_116386, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_116364])).
% 26.89/18.11  tff(c_117119, plain, (![B_1025, D_1026]: (k1_tops_1(B_1025, D_1026)=D_1026 | ~v3_pre_topc(D_1026, B_1025) | ~m1_subset_1(D_1026, k1_zfmisc_1(u1_struct_0(B_1025))) | ~l1_pre_topc(B_1025))), inference(splitRight, [status(thm)], [c_54])).
% 26.89/18.11  tff(c_117140, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_117119])).
% 26.89/18.11  tff(c_117150, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_109154, c_117140])).
% 26.89/18.11  tff(c_50, plain, (![A_47, B_49]: (k7_subset_1(u1_struct_0(A_47), k2_pre_topc(A_47, B_49), k1_tops_1(A_47, B_49))=k2_tops_1(A_47, B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_102])).
% 26.89/18.11  tff(c_117166, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_117150, c_50])).
% 26.89/18.11  tff(c_117170, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_117166])).
% 26.89/18.11  tff(c_117172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109242, c_117170])).
% 26.89/18.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.89/18.11  
% 26.89/18.11  Inference rules
% 26.89/18.11  ----------------------
% 26.89/18.11  #Ref     : 0
% 26.89/18.11  #Sup     : 28878
% 26.89/18.11  #Fact    : 0
% 26.89/18.11  #Define  : 0
% 26.89/18.11  #Split   : 12
% 26.89/18.11  #Chain   : 0
% 26.89/18.11  #Close   : 0
% 26.89/18.11  
% 26.89/18.11  Ordering : KBO
% 26.89/18.11  
% 26.89/18.11  Simplification rules
% 26.89/18.11  ----------------------
% 26.89/18.11  #Subsume      : 209
% 26.89/18.11  #Demod        : 40326
% 26.89/18.11  #Tautology    : 20772
% 26.89/18.11  #SimpNegUnit  : 14
% 26.89/18.11  #BackRed      : 45
% 26.89/18.11  
% 26.89/18.11  #Partial instantiations: 0
% 26.89/18.11  #Strategies tried      : 1
% 26.89/18.11  
% 26.89/18.11  Timing (in seconds)
% 26.89/18.11  ----------------------
% 26.89/18.11  Preprocessing        : 0.37
% 26.89/18.11  Parsing              : 0.19
% 26.89/18.11  CNF conversion       : 0.03
% 26.89/18.11  Main loop            : 16.95
% 26.89/18.11  Inferencing          : 1.78
% 26.89/18.11  Reduction            : 11.14
% 26.89/18.11  Demodulation         : 10.17
% 26.89/18.11  BG Simplification    : 0.19
% 26.89/18.11  Subsumption          : 3.21
% 26.89/18.11  Abstraction          : 0.36
% 26.89/18.11  MUC search           : 0.00
% 26.89/18.11  Cooper               : 0.00
% 26.89/18.11  Total                : 17.37
% 26.89/18.11  Index Insertion      : 0.00
% 26.89/18.11  Index Deletion       : 0.00
% 26.89/18.11  Index Matching       : 0.00
% 26.89/18.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
