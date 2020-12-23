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
% DateTime   : Thu Dec  3 09:58:46 EST 2020

% Result     : Theorem 3.79s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 154 expanded)
%              Number of leaves         :   43 (  70 expanded)
%              Depth                    :   11
%              Number of atoms          :  134 ( 259 expanded)
%              Number of equality atoms :   19 (  28 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_97,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_55,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_137,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_114,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_126,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_113,plain,(
    ! [A_71,B_72] : r1_tarski(k3_xboole_0(A_71,B_72),A_71) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_116,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_113])).

tff(c_178,plain,(
    ! [B_94,C_95,A_96] :
      ( r2_hidden(B_94,C_95)
      | ~ r1_tarski(k2_tarski(A_96,B_94),C_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_186,plain,(
    ! [B_94,A_96] : r2_hidden(B_94,k2_tarski(A_96,B_94)) ),
    inference(resolution,[status(thm)],[c_116,c_178])).

tff(c_74,plain,(
    ! [A_46,B_47] : k1_setfam_1(k2_tarski(A_46,B_47)) = k3_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_18,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_368,plain,(
    ! [A_153,B_154,C_155] :
      ( r1_tarski(k2_tarski(A_153,B_154),C_155)
      | ~ r2_hidden(B_154,C_155)
      | ~ r2_hidden(A_153,C_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_380,plain,(
    ! [A_17,C_155] :
      ( r1_tarski(k1_tarski(A_17),C_155)
      | ~ r2_hidden(A_17,C_155)
      | ~ r2_hidden(A_17,C_155) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_368])).

tff(c_187,plain,(
    ! [B_97,A_98] : r2_hidden(B_97,k2_tarski(A_98,B_97)) ),
    inference(resolution,[status(thm)],[c_116,c_178])).

tff(c_190,plain,(
    ! [A_17] : r2_hidden(A_17,k1_tarski(A_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_187])).

tff(c_12,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_15,B_16] : r1_xboole_0(k4_xboole_0(A_15,B_16),B_16) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_238,plain,(
    ! [B_127,A_128] :
      ( ~ r1_xboole_0(B_127,A_128)
      | ~ r1_tarski(B_127,A_128)
      | v1_xboole_0(B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_283,plain,(
    ! [A_145,B_146] :
      ( ~ r1_tarski(k4_xboole_0(A_145,B_146),B_146)
      | v1_xboole_0(k4_xboole_0(A_145,B_146)) ) ),
    inference(resolution,[status(thm)],[c_16,c_238])).

tff(c_309,plain,(
    ! [A_149] : v1_xboole_0(k4_xboole_0(A_149,A_149)) ),
    inference(resolution,[status(thm)],[c_12,c_283])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_321,plain,(
    ! [A_150] : k4_xboole_0(A_150,A_150) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_309,c_4])).

tff(c_34,plain,(
    ! [B_36,A_35] :
      ( ~ r2_hidden(B_36,A_35)
      | k4_xboole_0(A_35,k1_tarski(B_36)) != A_35 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_337,plain,(
    ! [B_36] :
      ( ~ r2_hidden(B_36,k1_tarski(B_36))
      | k1_tarski(B_36) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_34])).

tff(c_354,plain,(
    ! [B_36] : k1_tarski(B_36) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_337])).

tff(c_120,plain,(
    ! [A_78,B_79] : k1_setfam_1(k2_tarski(A_78,B_79)) = k3_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_129,plain,(
    ! [A_17] : k3_xboole_0(A_17,A_17) = k1_setfam_1(k1_tarski(A_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_120])).

tff(c_132,plain,(
    ! [A_17] : k1_setfam_1(k1_tarski(A_17)) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_129])).

tff(c_292,plain,(
    ! [B_147,A_148] :
      ( r1_tarski(k1_setfam_1(B_147),k1_setfam_1(A_148))
      | k1_xboole_0 = A_148
      | ~ r1_tarski(A_148,B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_301,plain,(
    ! [B_147,A_17] :
      ( r1_tarski(k1_setfam_1(B_147),A_17)
      | k1_tarski(A_17) = k1_xboole_0
      | ~ r1_tarski(k1_tarski(A_17),B_147) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_292])).

tff(c_1098,plain,(
    ! [B_407,A_408] :
      ( r1_tarski(k1_setfam_1(B_407),A_408)
      | ~ r1_tarski(k1_tarski(A_408),B_407) ) ),
    inference(negUnitSimplification,[status(thm)],[c_354,c_301])).

tff(c_1128,plain,(
    ! [C_415,A_416] :
      ( r1_tarski(k1_setfam_1(C_415),A_416)
      | ~ r2_hidden(A_416,C_415) ) ),
    inference(resolution,[status(thm)],[c_380,c_1098])).

tff(c_1148,plain,(
    ! [A_417,B_418,A_419] :
      ( r1_tarski(k3_xboole_0(A_417,B_418),A_419)
      | ~ r2_hidden(A_419,k2_tarski(A_417,B_418)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_1128])).

tff(c_1165,plain,(
    ! [A_96,B_94] : r1_tarski(k3_xboole_0(A_96,B_94),B_94) ),
    inference(resolution,[status(thm)],[c_186,c_1148])).

tff(c_90,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_78,plain,(
    ! [A_48,B_49] :
      ( m1_subset_1(A_48,k1_zfmisc_1(B_49))
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_247,plain,(
    ! [B_129,A_130] :
      ( v1_relat_1(B_129)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(A_130))
      | ~ v1_relat_1(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_252,plain,(
    ! [A_131,B_132] :
      ( v1_relat_1(A_131)
      | ~ v1_relat_1(B_132)
      | ~ r1_tarski(A_131,B_132) ) ),
    inference(resolution,[status(thm)],[c_78,c_247])).

tff(c_263,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k3_xboole_0(A_6,B_7))
      | ~ v1_relat_1(A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_252])).

tff(c_88,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_92,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_836,plain,(
    ! [C_265,A_266,B_267] :
      ( r1_tarski(k5_relat_1(C_265,A_266),k5_relat_1(C_265,B_267))
      | ~ r1_tarski(A_266,B_267)
      | ~ v1_relat_1(C_265)
      | ~ v1_relat_1(B_267)
      | ~ v1_relat_1(A_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_679,plain,(
    ! [C_217,A_218,B_219] :
      ( r1_tarski(k5_relat_1(C_217,A_218),k5_relat_1(C_217,B_219))
      | ~ r1_tarski(A_218,B_219)
      | ~ v1_relat_1(C_217)
      | ~ v1_relat_1(B_219)
      | ~ v1_relat_1(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_471,plain,(
    ! [A_163,B_164,C_165] :
      ( r1_tarski(A_163,k3_xboole_0(B_164,C_165))
      | ~ r1_tarski(A_163,C_165)
      | ~ r1_tarski(A_163,B_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_86,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k3_xboole_0(k5_relat_1('#skF_3','#skF_4'),k5_relat_1('#skF_3','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_502,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_471,c_86])).

tff(c_546,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_502])).

tff(c_682,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_679,c_546])).

tff(c_688,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_92,c_8,c_682])).

tff(c_692,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_263,c_688])).

tff(c_696,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_692])).

tff(c_697,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_502])).

tff(c_839,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_836,c_697])).

tff(c_845,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_92,c_839])).

tff(c_859,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_845])).

tff(c_862,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_263,c_859])).

tff(c_866,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_862])).

tff(c_867,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_845])).

tff(c_1169,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1165,c_867])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.09  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.08/0.30  % Computer   : n022.cluster.edu
% 0.08/0.30  % Model      : x86_64 x86_64
% 0.08/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.30  % Memory     : 8042.1875MB
% 0.08/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.30  % CPULimit   : 60
% 0.08/0.30  % DateTime   : Tue Dec  1 17:42:25 EST 2020
% 0.08/0.30  % CPUTime    : 
% 0.08/0.30  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.79/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.79/1.54  
% 3.79/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.79/1.54  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 3.79/1.54  
% 3.79/1.54  %Foreground sorts:
% 3.79/1.54  
% 3.79/1.54  
% 3.79/1.54  %Background operators:
% 3.79/1.54  
% 3.79/1.54  
% 3.79/1.54  %Foreground operators:
% 3.79/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.79/1.54  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 3.79/1.54  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 3.79/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.79/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.79/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.79/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.79/1.54  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.79/1.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.79/1.54  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.79/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.79/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.79/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.79/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.79/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.79/1.55  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.79/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.79/1.55  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.79/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.79/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.79/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.79/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.79/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.79/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.79/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.79/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.79/1.55  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.79/1.55  
% 3.79/1.56  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.79/1.56  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.79/1.56  tff(f_69, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.79/1.56  tff(f_97, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.79/1.56  tff(f_55, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.79/1.56  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.79/1.56  tff(f_53, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.79/1.56  tff(f_51, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.79/1.56  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.79/1.56  tff(f_74, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.79/1.56  tff(f_107, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 3.79/1.56  tff(f_137, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relat_1)).
% 3.79/1.56  tff(f_101, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.79/1.56  tff(f_114, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.79/1.56  tff(f_126, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relat_1)).
% 3.79/1.56  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.79/1.56  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.79/1.56  tff(c_113, plain, (![A_71, B_72]: (r1_tarski(k3_xboole_0(A_71, B_72), A_71))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.79/1.56  tff(c_116, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_113])).
% 3.79/1.56  tff(c_178, plain, (![B_94, C_95, A_96]: (r2_hidden(B_94, C_95) | ~r1_tarski(k2_tarski(A_96, B_94), C_95))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.79/1.56  tff(c_186, plain, (![B_94, A_96]: (r2_hidden(B_94, k2_tarski(A_96, B_94)))), inference(resolution, [status(thm)], [c_116, c_178])).
% 3.79/1.56  tff(c_74, plain, (![A_46, B_47]: (k1_setfam_1(k2_tarski(A_46, B_47))=k3_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.79/1.56  tff(c_18, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.79/1.56  tff(c_368, plain, (![A_153, B_154, C_155]: (r1_tarski(k2_tarski(A_153, B_154), C_155) | ~r2_hidden(B_154, C_155) | ~r2_hidden(A_153, C_155))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.79/1.56  tff(c_380, plain, (![A_17, C_155]: (r1_tarski(k1_tarski(A_17), C_155) | ~r2_hidden(A_17, C_155) | ~r2_hidden(A_17, C_155))), inference(superposition, [status(thm), theory('equality')], [c_18, c_368])).
% 3.79/1.56  tff(c_187, plain, (![B_97, A_98]: (r2_hidden(B_97, k2_tarski(A_98, B_97)))), inference(resolution, [status(thm)], [c_116, c_178])).
% 3.79/1.56  tff(c_190, plain, (![A_17]: (r2_hidden(A_17, k1_tarski(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_187])).
% 3.79/1.56  tff(c_12, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.79/1.56  tff(c_16, plain, (![A_15, B_16]: (r1_xboole_0(k4_xboole_0(A_15, B_16), B_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.79/1.56  tff(c_238, plain, (![B_127, A_128]: (~r1_xboole_0(B_127, A_128) | ~r1_tarski(B_127, A_128) | v1_xboole_0(B_127))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.79/1.56  tff(c_283, plain, (![A_145, B_146]: (~r1_tarski(k4_xboole_0(A_145, B_146), B_146) | v1_xboole_0(k4_xboole_0(A_145, B_146)))), inference(resolution, [status(thm)], [c_16, c_238])).
% 3.79/1.56  tff(c_309, plain, (![A_149]: (v1_xboole_0(k4_xboole_0(A_149, A_149)))), inference(resolution, [status(thm)], [c_12, c_283])).
% 3.79/1.56  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.79/1.56  tff(c_321, plain, (![A_150]: (k4_xboole_0(A_150, A_150)=k1_xboole_0)), inference(resolution, [status(thm)], [c_309, c_4])).
% 3.79/1.56  tff(c_34, plain, (![B_36, A_35]: (~r2_hidden(B_36, A_35) | k4_xboole_0(A_35, k1_tarski(B_36))!=A_35)), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.79/1.56  tff(c_337, plain, (![B_36]: (~r2_hidden(B_36, k1_tarski(B_36)) | k1_tarski(B_36)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_321, c_34])).
% 3.79/1.56  tff(c_354, plain, (![B_36]: (k1_tarski(B_36)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_190, c_337])).
% 3.79/1.56  tff(c_120, plain, (![A_78, B_79]: (k1_setfam_1(k2_tarski(A_78, B_79))=k3_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.79/1.56  tff(c_129, plain, (![A_17]: (k3_xboole_0(A_17, A_17)=k1_setfam_1(k1_tarski(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_120])).
% 3.79/1.56  tff(c_132, plain, (![A_17]: (k1_setfam_1(k1_tarski(A_17))=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_129])).
% 3.79/1.56  tff(c_292, plain, (![B_147, A_148]: (r1_tarski(k1_setfam_1(B_147), k1_setfam_1(A_148)) | k1_xboole_0=A_148 | ~r1_tarski(A_148, B_147))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.79/1.56  tff(c_301, plain, (![B_147, A_17]: (r1_tarski(k1_setfam_1(B_147), A_17) | k1_tarski(A_17)=k1_xboole_0 | ~r1_tarski(k1_tarski(A_17), B_147))), inference(superposition, [status(thm), theory('equality')], [c_132, c_292])).
% 3.79/1.56  tff(c_1098, plain, (![B_407, A_408]: (r1_tarski(k1_setfam_1(B_407), A_408) | ~r1_tarski(k1_tarski(A_408), B_407))), inference(negUnitSimplification, [status(thm)], [c_354, c_301])).
% 3.79/1.56  tff(c_1128, plain, (![C_415, A_416]: (r1_tarski(k1_setfam_1(C_415), A_416) | ~r2_hidden(A_416, C_415))), inference(resolution, [status(thm)], [c_380, c_1098])).
% 3.79/1.56  tff(c_1148, plain, (![A_417, B_418, A_419]: (r1_tarski(k3_xboole_0(A_417, B_418), A_419) | ~r2_hidden(A_419, k2_tarski(A_417, B_418)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_1128])).
% 3.79/1.56  tff(c_1165, plain, (![A_96, B_94]: (r1_tarski(k3_xboole_0(A_96, B_94), B_94))), inference(resolution, [status(thm)], [c_186, c_1148])).
% 3.79/1.56  tff(c_90, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.79/1.56  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.79/1.56  tff(c_78, plain, (![A_48, B_49]: (m1_subset_1(A_48, k1_zfmisc_1(B_49)) | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.79/1.56  tff(c_247, plain, (![B_129, A_130]: (v1_relat_1(B_129) | ~m1_subset_1(B_129, k1_zfmisc_1(A_130)) | ~v1_relat_1(A_130))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.79/1.56  tff(c_252, plain, (![A_131, B_132]: (v1_relat_1(A_131) | ~v1_relat_1(B_132) | ~r1_tarski(A_131, B_132))), inference(resolution, [status(thm)], [c_78, c_247])).
% 3.79/1.56  tff(c_263, plain, (![A_6, B_7]: (v1_relat_1(k3_xboole_0(A_6, B_7)) | ~v1_relat_1(A_6))), inference(resolution, [status(thm)], [c_8, c_252])).
% 3.79/1.56  tff(c_88, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.79/1.56  tff(c_92, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.79/1.56  tff(c_836, plain, (![C_265, A_266, B_267]: (r1_tarski(k5_relat_1(C_265, A_266), k5_relat_1(C_265, B_267)) | ~r1_tarski(A_266, B_267) | ~v1_relat_1(C_265) | ~v1_relat_1(B_267) | ~v1_relat_1(A_266))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.79/1.56  tff(c_679, plain, (![C_217, A_218, B_219]: (r1_tarski(k5_relat_1(C_217, A_218), k5_relat_1(C_217, B_219)) | ~r1_tarski(A_218, B_219) | ~v1_relat_1(C_217) | ~v1_relat_1(B_219) | ~v1_relat_1(A_218))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.79/1.56  tff(c_471, plain, (![A_163, B_164, C_165]: (r1_tarski(A_163, k3_xboole_0(B_164, C_165)) | ~r1_tarski(A_163, C_165) | ~r1_tarski(A_163, B_164))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.79/1.56  tff(c_86, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k3_xboole_0(k5_relat_1('#skF_3', '#skF_4'), k5_relat_1('#skF_3', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.79/1.56  tff(c_502, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_5')) | ~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_471, c_86])).
% 3.79/1.56  tff(c_546, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_502])).
% 3.79/1.56  tff(c_682, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_4') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_679, c_546])).
% 3.79/1.56  tff(c_688, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_92, c_8, c_682])).
% 3.79/1.56  tff(c_692, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_263, c_688])).
% 3.79/1.56  tff(c_696, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_692])).
% 3.79/1.56  tff(c_697, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_502])).
% 3.79/1.56  tff(c_839, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_836, c_697])).
% 3.79/1.56  tff(c_845, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_92, c_839])).
% 3.79/1.56  tff(c_859, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_845])).
% 3.79/1.56  tff(c_862, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_263, c_859])).
% 3.79/1.56  tff(c_866, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_862])).
% 3.79/1.56  tff(c_867, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_845])).
% 3.79/1.56  tff(c_1169, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1165, c_867])).
% 3.79/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.79/1.56  
% 3.79/1.56  Inference rules
% 3.79/1.56  ----------------------
% 3.79/1.56  #Ref     : 0
% 3.79/1.56  #Sup     : 247
% 3.79/1.56  #Fact    : 0
% 3.79/1.56  #Define  : 0
% 3.79/1.56  #Split   : 4
% 3.79/1.56  #Chain   : 0
% 3.79/1.56  #Close   : 0
% 3.79/1.56  
% 3.79/1.56  Ordering : KBO
% 3.79/1.56  
% 3.79/1.56  Simplification rules
% 3.79/1.56  ----------------------
% 3.79/1.56  #Subsume      : 33
% 3.79/1.56  #Demod        : 57
% 3.79/1.56  #Tautology    : 82
% 3.79/1.56  #SimpNegUnit  : 13
% 3.79/1.56  #BackRed      : 6
% 3.79/1.56  
% 3.79/1.56  #Partial instantiations: 0
% 3.79/1.56  #Strategies tried      : 1
% 3.79/1.56  
% 3.79/1.56  Timing (in seconds)
% 3.79/1.56  ----------------------
% 3.79/1.56  Preprocessing        : 0.38
% 3.79/1.57  Parsing              : 0.20
% 3.79/1.57  CNF conversion       : 0.03
% 3.79/1.57  Main loop            : 0.49
% 3.79/1.57  Inferencing          : 0.18
% 3.79/1.57  Reduction            : 0.14
% 3.79/1.57  Demodulation         : 0.10
% 3.79/1.57  BG Simplification    : 0.03
% 3.79/1.57  Subsumption          : 0.10
% 3.79/1.57  Abstraction          : 0.03
% 3.79/1.57  MUC search           : 0.00
% 3.79/1.57  Cooper               : 0.00
% 3.79/1.57  Total                : 0.91
% 3.79/1.57  Index Insertion      : 0.00
% 3.79/1.57  Index Deletion       : 0.00
% 3.79/1.57  Index Matching       : 0.00
% 3.79/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
