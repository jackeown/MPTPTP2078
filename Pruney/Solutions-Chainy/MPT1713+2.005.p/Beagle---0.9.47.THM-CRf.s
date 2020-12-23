%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:30 EST 2020

% Result     : Theorem 6.15s
% Output     : CNFRefutation 6.15s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 672 expanded)
%              Number of leaves         :   44 ( 240 expanded)
%              Depth                    :   18
%              Number of atoms          :  229 (1811 expanded)
%              Number of equality atoms :   44 ( 184 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_28,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_40,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_36,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_135,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ( m1_pre_topc(B,C)
                 => ( ~ r1_tsep_1(B,C)
                    & ~ r1_tsep_1(C,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_90,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(B,A)
          <=> ( r1_tarski(k2_struct_0(B),k2_struct_0(A))
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
                 => ( r2_hidden(C,u1_pre_topc(B))
                  <=> ? [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                        & r2_hidden(D,u1_pre_topc(A))
                        & C = k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(c_4,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_91,plain,(
    ! [A_71,B_72] : r1_tarski(k4_xboole_0(A_71,B_72),A_71) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_99,plain,(
    ! [B_72] : k4_xboole_0(k1_xboole_0,B_72) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_12])).

tff(c_292,plain,(
    ! [A_89,B_90] : k4_xboole_0(A_89,k4_xboole_0(A_89,B_90)) = k3_xboole_0(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_336,plain,(
    ! [B_93] : k3_xboole_0(k1_xboole_0,B_93) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_292])).

tff(c_362,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_336])).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_321,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_292])).

tff(c_547,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_321])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( r1_xboole_0(A_11,B_12)
      | k4_xboole_0(A_11,B_12) != A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_74,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_70,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_195,plain,(
    ! [B_80,A_81] :
      ( l1_pre_topc(B_80)
      | ~ m1_pre_topc(B_80,A_81)
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_198,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_195])).

tff(c_207,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_198])).

tff(c_50,plain,(
    ! [A_54] :
      ( l1_struct_0(A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_161,plain,(
    ! [A_77] :
      ( u1_struct_0(A_77) = k2_struct_0(A_77)
      | ~ l1_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_165,plain,(
    ! [A_54] :
      ( u1_struct_0(A_54) = k2_struct_0(A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(resolution,[status(thm)],[c_50,c_161])).

tff(c_215,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_207,c_165])).

tff(c_54,plain,(
    ! [A_58] :
      ( ~ v1_xboole_0(u1_struct_0(A_58))
      | ~ l1_struct_0(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_233,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_54])).

tff(c_236,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_233])).

tff(c_271,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_236])).

tff(c_274,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_271])).

tff(c_278,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_274])).

tff(c_280,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_236])).

tff(c_756,plain,(
    ! [A_112,B_113] :
      ( r1_xboole_0(u1_struct_0(A_112),u1_struct_0(B_113))
      | ~ r1_tsep_1(A_112,B_113)
      | ~ l1_struct_0(B_113)
      | ~ l1_struct_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_765,plain,(
    ! [B_113] :
      ( r1_xboole_0(k2_struct_0('#skF_5'),u1_struct_0(B_113))
      | ~ r1_tsep_1('#skF_5',B_113)
      | ~ l1_struct_0(B_113)
      | ~ l1_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_756])).

tff(c_5770,plain,(
    ! [B_259] :
      ( r1_xboole_0(k2_struct_0('#skF_5'),u1_struct_0(B_259))
      | ~ r1_tsep_1('#skF_5',B_259)
      | ~ l1_struct_0(B_259) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_765])).

tff(c_5776,plain,
    ( r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_5'))
    | ~ r1_tsep_1('#skF_5','#skF_5')
    | ~ l1_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_5770])).

tff(c_5785,plain,
    ( r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_5'))
    | ~ r1_tsep_1('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_5776])).

tff(c_6049,plain,(
    ~ r1_tsep_1('#skF_5','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_5785])).

tff(c_420,plain,(
    ! [A_97,B_98] :
      ( r1_tsep_1(A_97,B_98)
      | ~ r1_xboole_0(u1_struct_0(A_97),u1_struct_0(B_98))
      | ~ l1_struct_0(B_98)
      | ~ l1_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_426,plain,(
    ! [B_98] :
      ( r1_tsep_1('#skF_5',B_98)
      | ~ r1_xboole_0(k2_struct_0('#skF_5'),u1_struct_0(B_98))
      | ~ l1_struct_0(B_98)
      | ~ l1_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_420])).

tff(c_6166,plain,(
    ! [B_270] :
      ( r1_tsep_1('#skF_5',B_270)
      | ~ r1_xboole_0(k2_struct_0('#skF_5'),u1_struct_0(B_270))
      | ~ l1_struct_0(B_270) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_426])).

tff(c_6175,plain,
    ( r1_tsep_1('#skF_5','#skF_5')
    | ~ r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_6166])).

tff(c_6185,plain,
    ( r1_tsep_1('#skF_5','#skF_5')
    | ~ r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_6175])).

tff(c_6186,plain,(
    ~ r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_6049,c_6185])).

tff(c_6239,plain,(
    k4_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_5')) != k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_6186])).

tff(c_6241,plain,(
    k2_struct_0('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_6239])).

tff(c_66,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_204,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_195])).

tff(c_211,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_204])).

tff(c_64,plain,(
    m1_pre_topc('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_368,plain,(
    ! [B_94,A_95] :
      ( r1_tarski(k2_struct_0(B_94),k2_struct_0(A_95))
      | ~ m1_pre_topc(B_94,A_95)
      | ~ l1_pre_topc(B_94)
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6314,plain,(
    ! [B_275,A_276] :
      ( k3_xboole_0(k2_struct_0(B_275),k2_struct_0(A_276)) = k2_struct_0(B_275)
      | ~ m1_pre_topc(B_275,A_276)
      | ~ l1_pre_topc(B_275)
      | ~ l1_pre_topc(A_276) ) ),
    inference(resolution,[status(thm)],[c_368,c_6])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_219,plain,(
    u1_struct_0('#skF_6') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_211,c_165])).

tff(c_225,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_6'))
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_54])).

tff(c_228,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_6'))
    | ~ l1_struct_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_225])).

tff(c_238,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_241,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_238])).

tff(c_245,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_241])).

tff(c_247,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_62,plain,
    ( r1_tsep_1('#skF_6','#skF_5')
    | r1_tsep_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_79,plain,(
    r1_tsep_1('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_5779,plain,
    ( r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_6'))
    | ~ r1_tsep_1('#skF_5','#skF_6')
    | ~ l1_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_5770])).

tff(c_5787,plain,(
    r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_79,c_5779])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = A_11
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_5810,plain,(
    k4_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_6')) = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_5787,c_16])).

tff(c_14,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_5823,plain,(
    k4_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_5')) = k3_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5810,c_14])).

tff(c_5832,plain,(
    k3_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_547,c_5823])).

tff(c_8,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_455,plain,(
    ! [A_99,B_100] : r1_tarski(k3_xboole_0(A_99,B_100),A_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_8])).

tff(c_495,plain,(
    ! [B_102,A_103] : r1_tarski(k3_xboole_0(B_102,A_103),A_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_455])).

tff(c_1098,plain,(
    ! [B_123,A_124] : k3_xboole_0(k3_xboole_0(B_123,A_124),A_124) = k3_xboole_0(B_123,A_124) ),
    inference(resolution,[status(thm)],[c_495,c_6])).

tff(c_4609,plain,(
    ! [A_224,B_225] : k3_xboole_0(k3_xboole_0(A_224,B_225),A_224) = k3_xboole_0(B_225,A_224) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1098])).

tff(c_4740,plain,(
    ! [A_1,B_225] : k3_xboole_0(A_1,k3_xboole_0(A_1,B_225)) = k3_xboole_0(B_225,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4609])).

tff(c_5856,plain,(
    k3_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_6')) = k3_xboole_0(k2_struct_0('#skF_6'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5832,c_4740])).

tff(c_5898,plain,(
    k3_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_5856])).

tff(c_6320,plain,
    ( k2_struct_0('#skF_5') = k1_xboole_0
    | ~ m1_pre_topc('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_6314,c_5898])).

tff(c_6421,plain,(
    k2_struct_0('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_207,c_64,c_6320])).

tff(c_6423,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6241,c_6421])).

tff(c_6424,plain,(
    r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_5785])).

tff(c_6433,plain,(
    k4_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_5')) = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_6424,c_16])).

tff(c_6435,plain,(
    k2_struct_0('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_6433])).

tff(c_279,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_236])).

tff(c_6449,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6435,c_279])).

tff(c_6461,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6449])).

tff(c_6463,plain,(
    ~ r1_tsep_1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_6578,plain,(
    ! [B_293,A_294] :
      ( l1_pre_topc(B_293)
      | ~ m1_pre_topc(B_293,A_294)
      | ~ l1_pre_topc(A_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6587,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_6578])).

tff(c_6594,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_6587])).

tff(c_6484,plain,(
    ! [A_282] :
      ( u1_struct_0(A_282) = k2_struct_0(A_282)
      | ~ l1_struct_0(A_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6488,plain,(
    ! [A_54] :
      ( u1_struct_0(A_54) = k2_struct_0(A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(resolution,[status(thm)],[c_50,c_6484])).

tff(c_6607,plain,(
    u1_struct_0('#skF_6') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_6594,c_6488])).

tff(c_6636,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_6'))
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_6607,c_54])).

tff(c_6639,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_6'))
    | ~ l1_struct_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_6636])).

tff(c_6661,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_6639])).

tff(c_6664,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_6661])).

tff(c_6668,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6594,c_6664])).

tff(c_6670,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_6639])).

tff(c_6581,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_6578])).

tff(c_6590,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_6581])).

tff(c_6603,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_6590,c_6488])).

tff(c_6628,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6603,c_54])).

tff(c_6631,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_6628])).

tff(c_6646,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_6631])).

tff(c_6649,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_6646])).

tff(c_6653,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6590,c_6649])).

tff(c_6655,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_6631])).

tff(c_6462,plain,(
    r1_tsep_1('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_6709,plain,(
    ! [B_300,A_301] :
      ( r1_tsep_1(B_300,A_301)
      | ~ r1_tsep_1(A_301,B_300)
      | ~ l1_struct_0(B_300)
      | ~ l1_struct_0(A_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_6711,plain,
    ( r1_tsep_1('#skF_5','#skF_6')
    | ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_6462,c_6709])).

tff(c_6714,plain,(
    r1_tsep_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6670,c_6655,c_6711])).

tff(c_6716,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6463,c_6714])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:40:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.15/2.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.15/2.25  
% 6.15/2.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.15/2.26  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 6.15/2.26  
% 6.15/2.26  %Foreground sorts:
% 6.15/2.26  
% 6.15/2.26  
% 6.15/2.26  %Background operators:
% 6.15/2.26  
% 6.15/2.26  
% 6.15/2.26  %Foreground operators:
% 6.15/2.26  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.15/2.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.15/2.26  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 6.15/2.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.15/2.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.15/2.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.15/2.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.15/2.26  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.15/2.26  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.15/2.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.15/2.26  tff('#skF_5', type, '#skF_5': $i).
% 6.15/2.26  tff('#skF_6', type, '#skF_6': $i).
% 6.15/2.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.15/2.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.15/2.26  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.15/2.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.15/2.26  tff('#skF_4', type, '#skF_4': $i).
% 6.15/2.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.15/2.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.15/2.26  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.15/2.26  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.15/2.26  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 6.15/2.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.15/2.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.15/2.26  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 6.15/2.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.15/2.26  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 6.15/2.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.15/2.26  
% 6.15/2.28  tff(f_28, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.15/2.28  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.15/2.28  tff(f_34, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.15/2.28  tff(f_40, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 6.15/2.28  tff(f_42, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.15/2.28  tff(f_36, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 6.15/2.28  tff(f_46, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 6.15/2.28  tff(f_135, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (~r1_tsep_1(B, C) & ~r1_tsep_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_tmap_1)).
% 6.15/2.28  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 6.15/2.28  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.15/2.28  tff(f_50, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 6.15/2.28  tff(f_90, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 6.15/2.28  tff(f_99, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 6.15/2.28  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(B, A) <=> (r1_tarski(k2_struct_0(B), k2_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (r2_hidden(C, u1_pre_topc(B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(D, u1_pre_topc(A))) & (C = k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_pre_topc)).
% 6.15/2.28  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.15/2.28  tff(f_107, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 6.15/2.28  tff(c_4, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 6.15/2.28  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.15/2.28  tff(c_91, plain, (![A_71, B_72]: (r1_tarski(k4_xboole_0(A_71, B_72), A_71))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.15/2.28  tff(c_12, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.15/2.28  tff(c_99, plain, (![B_72]: (k4_xboole_0(k1_xboole_0, B_72)=k1_xboole_0)), inference(resolution, [status(thm)], [c_91, c_12])).
% 6.15/2.28  tff(c_292, plain, (![A_89, B_90]: (k4_xboole_0(A_89, k4_xboole_0(A_89, B_90))=k3_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.15/2.28  tff(c_336, plain, (![B_93]: (k3_xboole_0(k1_xboole_0, B_93)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_99, c_292])).
% 6.15/2.28  tff(c_362, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_336])).
% 6.15/2.28  tff(c_10, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.15/2.28  tff(c_321, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_292])).
% 6.15/2.28  tff(c_547, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_362, c_321])).
% 6.15/2.28  tff(c_18, plain, (![A_11, B_12]: (r1_xboole_0(A_11, B_12) | k4_xboole_0(A_11, B_12)!=A_11)), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.15/2.28  tff(c_74, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.15/2.28  tff(c_70, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.15/2.28  tff(c_195, plain, (![B_80, A_81]: (l1_pre_topc(B_80) | ~m1_pre_topc(B_80, A_81) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.15/2.28  tff(c_198, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_70, c_195])).
% 6.15/2.28  tff(c_207, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_198])).
% 6.15/2.28  tff(c_50, plain, (![A_54]: (l1_struct_0(A_54) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.15/2.28  tff(c_72, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.15/2.28  tff(c_161, plain, (![A_77]: (u1_struct_0(A_77)=k2_struct_0(A_77) | ~l1_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.15/2.28  tff(c_165, plain, (![A_54]: (u1_struct_0(A_54)=k2_struct_0(A_54) | ~l1_pre_topc(A_54))), inference(resolution, [status(thm)], [c_50, c_161])).
% 6.15/2.28  tff(c_215, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_207, c_165])).
% 6.15/2.28  tff(c_54, plain, (![A_58]: (~v1_xboole_0(u1_struct_0(A_58)) | ~l1_struct_0(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.15/2.28  tff(c_233, plain, (~v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_215, c_54])).
% 6.15/2.28  tff(c_236, plain, (~v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_72, c_233])).
% 6.15/2.28  tff(c_271, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_236])).
% 6.15/2.28  tff(c_274, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_50, c_271])).
% 6.15/2.28  tff(c_278, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_207, c_274])).
% 6.15/2.28  tff(c_280, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_236])).
% 6.15/2.28  tff(c_756, plain, (![A_112, B_113]: (r1_xboole_0(u1_struct_0(A_112), u1_struct_0(B_113)) | ~r1_tsep_1(A_112, B_113) | ~l1_struct_0(B_113) | ~l1_struct_0(A_112))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.15/2.28  tff(c_765, plain, (![B_113]: (r1_xboole_0(k2_struct_0('#skF_5'), u1_struct_0(B_113)) | ~r1_tsep_1('#skF_5', B_113) | ~l1_struct_0(B_113) | ~l1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_215, c_756])).
% 6.15/2.28  tff(c_5770, plain, (![B_259]: (r1_xboole_0(k2_struct_0('#skF_5'), u1_struct_0(B_259)) | ~r1_tsep_1('#skF_5', B_259) | ~l1_struct_0(B_259))), inference(demodulation, [status(thm), theory('equality')], [c_280, c_765])).
% 6.15/2.28  tff(c_5776, plain, (r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_5')) | ~r1_tsep_1('#skF_5', '#skF_5') | ~l1_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_215, c_5770])).
% 6.15/2.28  tff(c_5785, plain, (r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_5')) | ~r1_tsep_1('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_280, c_5776])).
% 6.15/2.28  tff(c_6049, plain, (~r1_tsep_1('#skF_5', '#skF_5')), inference(splitLeft, [status(thm)], [c_5785])).
% 6.15/2.28  tff(c_420, plain, (![A_97, B_98]: (r1_tsep_1(A_97, B_98) | ~r1_xboole_0(u1_struct_0(A_97), u1_struct_0(B_98)) | ~l1_struct_0(B_98) | ~l1_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.15/2.28  tff(c_426, plain, (![B_98]: (r1_tsep_1('#skF_5', B_98) | ~r1_xboole_0(k2_struct_0('#skF_5'), u1_struct_0(B_98)) | ~l1_struct_0(B_98) | ~l1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_215, c_420])).
% 6.15/2.28  tff(c_6166, plain, (![B_270]: (r1_tsep_1('#skF_5', B_270) | ~r1_xboole_0(k2_struct_0('#skF_5'), u1_struct_0(B_270)) | ~l1_struct_0(B_270))), inference(demodulation, [status(thm), theory('equality')], [c_280, c_426])).
% 6.15/2.28  tff(c_6175, plain, (r1_tsep_1('#skF_5', '#skF_5') | ~r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_215, c_6166])).
% 6.15/2.28  tff(c_6185, plain, (r1_tsep_1('#skF_5', '#skF_5') | ~r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_280, c_6175])).
% 6.15/2.28  tff(c_6186, plain, (~r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_6049, c_6185])).
% 6.15/2.28  tff(c_6239, plain, (k4_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_5'))!=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_18, c_6186])).
% 6.15/2.28  tff(c_6241, plain, (k2_struct_0('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_547, c_6239])).
% 6.15/2.28  tff(c_66, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.15/2.28  tff(c_204, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_66, c_195])).
% 6.15/2.28  tff(c_211, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_204])).
% 6.15/2.28  tff(c_64, plain, (m1_pre_topc('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.15/2.28  tff(c_368, plain, (![B_94, A_95]: (r1_tarski(k2_struct_0(B_94), k2_struct_0(A_95)) | ~m1_pre_topc(B_94, A_95) | ~l1_pre_topc(B_94) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.15/2.28  tff(c_6, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.15/2.28  tff(c_6314, plain, (![B_275, A_276]: (k3_xboole_0(k2_struct_0(B_275), k2_struct_0(A_276))=k2_struct_0(B_275) | ~m1_pre_topc(B_275, A_276) | ~l1_pre_topc(B_275) | ~l1_pre_topc(A_276))), inference(resolution, [status(thm)], [c_368, c_6])).
% 6.15/2.28  tff(c_68, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.15/2.28  tff(c_219, plain, (u1_struct_0('#skF_6')=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_211, c_165])).
% 6.15/2.28  tff(c_225, plain, (~v1_xboole_0(k2_struct_0('#skF_6')) | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_219, c_54])).
% 6.15/2.28  tff(c_228, plain, (~v1_xboole_0(k2_struct_0('#skF_6')) | ~l1_struct_0('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_68, c_225])).
% 6.15/2.28  tff(c_238, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_228])).
% 6.15/2.28  tff(c_241, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_50, c_238])).
% 6.15/2.28  tff(c_245, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_211, c_241])).
% 6.15/2.28  tff(c_247, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_228])).
% 6.15/2.28  tff(c_62, plain, (r1_tsep_1('#skF_6', '#skF_5') | r1_tsep_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.15/2.28  tff(c_79, plain, (r1_tsep_1('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_62])).
% 6.15/2.28  tff(c_5779, plain, (r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_6')) | ~r1_tsep_1('#skF_5', '#skF_6') | ~l1_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_219, c_5770])).
% 6.15/2.28  tff(c_5787, plain, (r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_247, c_79, c_5779])).
% 6.15/2.28  tff(c_16, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=A_11 | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.15/2.28  tff(c_5810, plain, (k4_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_6'))=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_5787, c_16])).
% 6.15/2.28  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.15/2.28  tff(c_5823, plain, (k4_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_5'))=k3_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_5810, c_14])).
% 6.15/2.28  tff(c_5832, plain, (k3_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_547, c_5823])).
% 6.15/2.28  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.15/2.28  tff(c_455, plain, (![A_99, B_100]: (r1_tarski(k3_xboole_0(A_99, B_100), A_99))), inference(superposition, [status(thm), theory('equality')], [c_292, c_8])).
% 6.15/2.28  tff(c_495, plain, (![B_102, A_103]: (r1_tarski(k3_xboole_0(B_102, A_103), A_103))), inference(superposition, [status(thm), theory('equality')], [c_2, c_455])).
% 6.15/2.28  tff(c_1098, plain, (![B_123, A_124]: (k3_xboole_0(k3_xboole_0(B_123, A_124), A_124)=k3_xboole_0(B_123, A_124))), inference(resolution, [status(thm)], [c_495, c_6])).
% 6.15/2.28  tff(c_4609, plain, (![A_224, B_225]: (k3_xboole_0(k3_xboole_0(A_224, B_225), A_224)=k3_xboole_0(B_225, A_224))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1098])).
% 6.15/2.28  tff(c_4740, plain, (![A_1, B_225]: (k3_xboole_0(A_1, k3_xboole_0(A_1, B_225))=k3_xboole_0(B_225, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4609])).
% 6.15/2.28  tff(c_5856, plain, (k3_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_6'))=k3_xboole_0(k2_struct_0('#skF_6'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5832, c_4740])).
% 6.15/2.28  tff(c_5898, plain, (k3_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_362, c_5856])).
% 6.15/2.28  tff(c_6320, plain, (k2_struct_0('#skF_5')=k1_xboole_0 | ~m1_pre_topc('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_6314, c_5898])).
% 6.15/2.28  tff(c_6421, plain, (k2_struct_0('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_211, c_207, c_64, c_6320])).
% 6.15/2.28  tff(c_6423, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6241, c_6421])).
% 6.15/2.28  tff(c_6424, plain, (r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_5785])).
% 6.15/2.28  tff(c_6433, plain, (k4_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_5'))=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_6424, c_16])).
% 6.15/2.28  tff(c_6435, plain, (k2_struct_0('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_547, c_6433])).
% 6.15/2.28  tff(c_279, plain, (~v1_xboole_0(k2_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_236])).
% 6.15/2.28  tff(c_6449, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6435, c_279])).
% 6.15/2.28  tff(c_6461, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_6449])).
% 6.15/2.28  tff(c_6463, plain, (~r1_tsep_1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_62])).
% 6.15/2.28  tff(c_6578, plain, (![B_293, A_294]: (l1_pre_topc(B_293) | ~m1_pre_topc(B_293, A_294) | ~l1_pre_topc(A_294))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.15/2.28  tff(c_6587, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_66, c_6578])).
% 6.15/2.28  tff(c_6594, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_6587])).
% 6.15/2.28  tff(c_6484, plain, (![A_282]: (u1_struct_0(A_282)=k2_struct_0(A_282) | ~l1_struct_0(A_282))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.15/2.28  tff(c_6488, plain, (![A_54]: (u1_struct_0(A_54)=k2_struct_0(A_54) | ~l1_pre_topc(A_54))), inference(resolution, [status(thm)], [c_50, c_6484])).
% 6.15/2.28  tff(c_6607, plain, (u1_struct_0('#skF_6')=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_6594, c_6488])).
% 6.15/2.28  tff(c_6636, plain, (~v1_xboole_0(k2_struct_0('#skF_6')) | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_6607, c_54])).
% 6.15/2.28  tff(c_6639, plain, (~v1_xboole_0(k2_struct_0('#skF_6')) | ~l1_struct_0('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_68, c_6636])).
% 6.15/2.28  tff(c_6661, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_6639])).
% 6.15/2.28  tff(c_6664, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_50, c_6661])).
% 6.15/2.28  tff(c_6668, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6594, c_6664])).
% 6.15/2.28  tff(c_6670, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_6639])).
% 6.15/2.28  tff(c_6581, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_70, c_6578])).
% 6.15/2.28  tff(c_6590, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_6581])).
% 6.15/2.28  tff(c_6603, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_6590, c_6488])).
% 6.15/2.28  tff(c_6628, plain, (~v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6603, c_54])).
% 6.15/2.28  tff(c_6631, plain, (~v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_72, c_6628])).
% 6.15/2.28  tff(c_6646, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_6631])).
% 6.15/2.28  tff(c_6649, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_50, c_6646])).
% 6.15/2.28  tff(c_6653, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6590, c_6649])).
% 6.15/2.28  tff(c_6655, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_6631])).
% 6.15/2.28  tff(c_6462, plain, (r1_tsep_1('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_62])).
% 6.15/2.28  tff(c_6709, plain, (![B_300, A_301]: (r1_tsep_1(B_300, A_301) | ~r1_tsep_1(A_301, B_300) | ~l1_struct_0(B_300) | ~l1_struct_0(A_301))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.15/2.28  tff(c_6711, plain, (r1_tsep_1('#skF_5', '#skF_6') | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_6462, c_6709])).
% 6.15/2.28  tff(c_6714, plain, (r1_tsep_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6670, c_6655, c_6711])).
% 6.15/2.28  tff(c_6716, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6463, c_6714])).
% 6.15/2.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.15/2.28  
% 6.15/2.28  Inference rules
% 6.15/2.28  ----------------------
% 6.15/2.28  #Ref     : 0
% 6.15/2.28  #Sup     : 1561
% 6.15/2.28  #Fact    : 0
% 6.15/2.28  #Define  : 0
% 6.15/2.28  #Split   : 20
% 6.15/2.28  #Chain   : 0
% 6.15/2.28  #Close   : 0
% 6.15/2.28  
% 6.15/2.28  Ordering : KBO
% 6.15/2.28  
% 6.15/2.28  Simplification rules
% 6.15/2.28  ----------------------
% 6.15/2.28  #Subsume      : 101
% 6.15/2.28  #Demod        : 2115
% 6.15/2.28  #Tautology    : 1112
% 6.15/2.28  #SimpNegUnit  : 49
% 6.15/2.28  #BackRed      : 29
% 6.15/2.28  
% 6.15/2.28  #Partial instantiations: 0
% 6.15/2.28  #Strategies tried      : 1
% 6.15/2.28  
% 6.15/2.28  Timing (in seconds)
% 6.15/2.28  ----------------------
% 6.15/2.28  Preprocessing        : 0.34
% 6.15/2.28  Parsing              : 0.17
% 6.15/2.28  CNF conversion       : 0.03
% 6.15/2.28  Main loop            : 1.11
% 6.15/2.28  Inferencing          : 0.33
% 6.15/2.28  Reduction            : 0.49
% 6.15/2.28  Demodulation         : 0.39
% 6.15/2.28  BG Simplification    : 0.04
% 6.15/2.28  Subsumption          : 0.19
% 6.15/2.28  Abstraction          : 0.05
% 6.15/2.28  MUC search           : 0.00
% 6.15/2.28  Cooper               : 0.00
% 6.15/2.28  Total                : 1.49
% 6.15/2.28  Index Insertion      : 0.00
% 6.15/2.28  Index Deletion       : 0.00
% 6.15/2.28  Index Matching       : 0.00
% 6.15/2.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
