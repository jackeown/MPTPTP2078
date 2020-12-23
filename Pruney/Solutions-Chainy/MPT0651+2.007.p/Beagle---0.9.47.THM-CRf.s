%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:48 EST 2020

% Result     : Theorem 4.61s
% Output     : CNFRefutation 4.94s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 464 expanded)
%              Number of leaves         :   25 ( 174 expanded)
%              Depth                    :   23
%              Number of atoms          :  216 (1296 expanded)
%              Number of equality atoms :   70 ( 452 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
            & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_36,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_34,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_28,plain,(
    ! [A_15] :
      ( k2_relat_1(k2_funct_1(A_15)) = k1_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_22,plain,(
    ! [A_13] :
      ( v1_relat_1(k2_funct_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_30,plain,(
    ! [A_15] :
      ( k1_relat_1(k2_funct_1(A_15)) = k2_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1117,plain,(
    ! [A_81,B_82] :
      ( k10_relat_1(A_81,k1_relat_1(B_82)) = k1_relat_1(k5_relat_1(A_81,B_82))
      | ~ v1_relat_1(B_82)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1422,plain,(
    ! [A_95,A_96] :
      ( k1_relat_1(k5_relat_1(A_95,k2_funct_1(A_96))) = k10_relat_1(A_95,k2_relat_1(A_96))
      | ~ v1_relat_1(k2_funct_1(A_96))
      | ~ v1_relat_1(A_95)
      | ~ v2_funct_1(A_96)
      | ~ v1_funct_1(A_96)
      | ~ v1_relat_1(A_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1117])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_115,plain,(
    ! [B_29,A_30] :
      ( k5_relat_1(B_29,k6_relat_1(A_30)) = B_29
      | ~ r1_tarski(k2_relat_1(B_29),A_30)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_128,plain,(
    ! [B_29] :
      ( k5_relat_1(B_29,k6_relat_1(k2_relat_1(B_29))) = B_29
      | ~ v1_relat_1(B_29) ) ),
    inference(resolution,[status(thm)],[c_6,c_115])).

tff(c_24,plain,(
    ! [A_14] : v1_relat_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_14,plain,(
    ! [A_10] : k1_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_146,plain,(
    ! [A_32,B_33] :
      ( k10_relat_1(A_32,k1_relat_1(B_33)) = k1_relat_1(k5_relat_1(A_32,B_33))
      | ~ v1_relat_1(B_33)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_158,plain,(
    ! [A_32,A_10] :
      ( k1_relat_1(k5_relat_1(A_32,k6_relat_1(A_10))) = k10_relat_1(A_32,A_10)
      | ~ v1_relat_1(k6_relat_1(A_10))
      | ~ v1_relat_1(A_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_146])).

tff(c_172,plain,(
    ! [A_35,A_36] :
      ( k1_relat_1(k5_relat_1(A_35,k6_relat_1(A_36))) = k10_relat_1(A_35,A_36)
      | ~ v1_relat_1(A_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_158])).

tff(c_190,plain,(
    ! [B_29] :
      ( k10_relat_1(B_29,k2_relat_1(B_29)) = k1_relat_1(B_29)
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(B_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_172])).

tff(c_883,plain,(
    ! [A_64,A_65] :
      ( k1_relat_1(k5_relat_1(A_64,k2_funct_1(A_65))) = k10_relat_1(A_64,k2_relat_1(A_65))
      | ~ v1_relat_1(k2_funct_1(A_65))
      | ~ v1_relat_1(A_64)
      | ~ v2_funct_1(A_65)
      | ~ v1_funct_1(A_65)
      | ~ v1_relat_1(A_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_146])).

tff(c_32,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_62,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_909,plain,
    ( k10_relat_1('#skF_1',k2_relat_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_883,c_62])).

tff(c_927,plain,
    ( k10_relat_1('#skF_1',k2_relat_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_38,c_909])).

tff(c_933,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_927])).

tff(c_936,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_933])).

tff(c_940,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_936])).

tff(c_941,plain,(
    k10_relat_1('#skF_1',k2_relat_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_927])).

tff(c_945,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_941])).

tff(c_949,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_945])).

tff(c_951,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1434,plain,
    ( k10_relat_1('#skF_1',k2_relat_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1422,c_951])).

tff(c_1443,plain,
    ( k10_relat_1('#skF_1',k2_relat_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_38,c_1434])).

tff(c_1447,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1443])).

tff(c_1450,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_1447])).

tff(c_1454,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1450])).

tff(c_1456,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1443])).

tff(c_1002,plain,(
    ! [B_72,A_73] :
      ( k5_relat_1(B_72,k6_relat_1(A_73)) = B_72
      | ~ r1_tarski(k2_relat_1(B_72),A_73)
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1012,plain,(
    ! [B_72] :
      ( k5_relat_1(B_72,k6_relat_1(k2_relat_1(B_72))) = B_72
      | ~ v1_relat_1(B_72) ) ),
    inference(resolution,[status(thm)],[c_6,c_1002])).

tff(c_1440,plain,
    ( k10_relat_1('#skF_1',k2_relat_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_951,c_1422])).

tff(c_1446,plain,
    ( k10_relat_1('#skF_1',k2_relat_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_38,c_1440])).

tff(c_1458,plain,(
    k10_relat_1('#skF_1',k2_relat_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1456,c_1446])).

tff(c_1132,plain,(
    ! [A_81,A_10] :
      ( k1_relat_1(k5_relat_1(A_81,k6_relat_1(A_10))) = k10_relat_1(A_81,A_10)
      | ~ v1_relat_1(k6_relat_1(A_10))
      | ~ v1_relat_1(A_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1117])).

tff(c_1217,plain,(
    ! [A_87,A_88] :
      ( k1_relat_1(k5_relat_1(A_87,k6_relat_1(A_88))) = k10_relat_1(A_87,A_88)
      | ~ v1_relat_1(A_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1132])).

tff(c_8,plain,(
    ! [A_3] :
      ( k9_relat_1(A_3,k1_relat_1(A_3)) = k2_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2385,plain,(
    ! [A_122,A_123] :
      ( k9_relat_1(k5_relat_1(A_122,k6_relat_1(A_123)),k10_relat_1(A_122,A_123)) = k2_relat_1(k5_relat_1(A_122,k6_relat_1(A_123)))
      | ~ v1_relat_1(k5_relat_1(A_122,k6_relat_1(A_123)))
      | ~ v1_relat_1(A_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1217,c_8])).

tff(c_2403,plain,
    ( k9_relat_1(k5_relat_1('#skF_1',k6_relat_1(k2_relat_1('#skF_1'))),k1_relat_1('#skF_1')) = k2_relat_1(k5_relat_1('#skF_1',k6_relat_1(k2_relat_1('#skF_1'))))
    | ~ v1_relat_1(k5_relat_1('#skF_1',k6_relat_1(k2_relat_1('#skF_1'))))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1458,c_2385])).

tff(c_2428,plain,
    ( k9_relat_1(k5_relat_1('#skF_1',k6_relat_1(k2_relat_1('#skF_1'))),k1_relat_1('#skF_1')) = k2_relat_1(k5_relat_1('#skF_1',k6_relat_1(k2_relat_1('#skF_1'))))
    | ~ v1_relat_1(k5_relat_1('#skF_1',k6_relat_1(k2_relat_1('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2403])).

tff(c_2538,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_1',k6_relat_1(k2_relat_1('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_2428])).

tff(c_2541,plain,
    ( ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1012,c_2538])).

tff(c_2544,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_2541])).

tff(c_2546,plain,(
    v1_relat_1(k5_relat_1('#skF_1',k6_relat_1(k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_2428])).

tff(c_2545,plain,(
    k9_relat_1(k5_relat_1('#skF_1',k6_relat_1(k2_relat_1('#skF_1'))),k1_relat_1('#skF_1')) = k2_relat_1(k5_relat_1('#skF_1',k6_relat_1(k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_2428])).

tff(c_2609,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k6_relat_1(k2_relat_1('#skF_1')))) = k9_relat_1('#skF_1',k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1012,c_2545])).

tff(c_2613,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k6_relat_1(k2_relat_1('#skF_1')))) = k9_relat_1('#skF_1',k1_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2609])).

tff(c_16,plain,(
    ! [A_10] : k2_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1005,plain,(
    ! [A_10,A_73] :
      ( k5_relat_1(k6_relat_1(A_10),k6_relat_1(A_73)) = k6_relat_1(A_10)
      | ~ r1_tarski(A_10,A_73)
      | ~ v1_relat_1(k6_relat_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1002])).

tff(c_1011,plain,(
    ! [A_10,A_73] :
      ( k5_relat_1(k6_relat_1(A_10),k6_relat_1(A_73)) = k6_relat_1(A_10)
      | ~ r1_tarski(A_10,A_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1005])).

tff(c_1088,plain,(
    ! [B_79,A_80] :
      ( k9_relat_1(B_79,k2_relat_1(A_80)) = k2_relat_1(k5_relat_1(A_80,B_79))
      | ~ v1_relat_1(B_79)
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1108,plain,(
    ! [A_10,B_79] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_10),B_79)) = k9_relat_1(B_79,A_10)
      | ~ v1_relat_1(B_79)
      | ~ v1_relat_1(k6_relat_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1088])).

tff(c_1137,plain,(
    ! [A_83,B_84] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_83),B_84)) = k9_relat_1(B_84,A_83)
      | ~ v1_relat_1(B_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1108])).

tff(c_1155,plain,(
    ! [A_73,A_10] :
      ( k9_relat_1(k6_relat_1(A_73),A_10) = k2_relat_1(k6_relat_1(A_10))
      | ~ v1_relat_1(k6_relat_1(A_73))
      | ~ r1_tarski(A_10,A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1011,c_1137])).

tff(c_1171,plain,(
    ! [A_85,A_86] :
      ( k9_relat_1(k6_relat_1(A_85),A_86) = A_86
      | ~ r1_tarski(A_86,A_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_16,c_1155])).

tff(c_10,plain,(
    ! [B_6,A_4] :
      ( k9_relat_1(B_6,k2_relat_1(A_4)) = k2_relat_1(k5_relat_1(A_4,B_6))
      | ~ v1_relat_1(B_6)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1178,plain,(
    ! [A_4,A_85] :
      ( k2_relat_1(k5_relat_1(A_4,k6_relat_1(A_85))) = k2_relat_1(A_4)
      | ~ v1_relat_1(k6_relat_1(A_85))
      | ~ v1_relat_1(A_4)
      | ~ r1_tarski(k2_relat_1(A_4),A_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1171,c_10])).

tff(c_1203,plain,(
    ! [A_4,A_85] :
      ( k2_relat_1(k5_relat_1(A_4,k6_relat_1(A_85))) = k2_relat_1(A_4)
      | ~ v1_relat_1(A_4)
      | ~ r1_tarski(k2_relat_1(A_4),A_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1178])).

tff(c_2701,plain,
    ( k9_relat_1('#skF_1',k1_relat_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2613,c_1203])).

tff(c_2737,plain,(
    k9_relat_1('#skF_1',k1_relat_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_38,c_2701])).

tff(c_2759,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k6_relat_1(k2_relat_1('#skF_1')))) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2737,c_2613])).

tff(c_2821,plain,(
    ! [B_6] :
      ( k2_relat_1(k5_relat_1(k5_relat_1('#skF_1',k6_relat_1(k2_relat_1('#skF_1'))),B_6)) = k9_relat_1(B_6,k2_relat_1('#skF_1'))
      | ~ v1_relat_1(B_6)
      | ~ v1_relat_1(k5_relat_1('#skF_1',k6_relat_1(k2_relat_1('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2759,c_10])).

tff(c_3300,plain,(
    ! [B_135] :
      ( k2_relat_1(k5_relat_1(k5_relat_1('#skF_1',k6_relat_1(k2_relat_1('#skF_1'))),B_135)) = k9_relat_1(B_135,k2_relat_1('#skF_1'))
      | ~ v1_relat_1(B_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2546,c_2821])).

tff(c_3349,plain,(
    ! [B_135] :
      ( k9_relat_1(B_135,k2_relat_1('#skF_1')) = k2_relat_1(k5_relat_1('#skF_1',B_135))
      | ~ v1_relat_1(B_135)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1012,c_3300])).

tff(c_3370,plain,(
    ! [B_136] :
      ( k9_relat_1(B_136,k2_relat_1('#skF_1')) = k2_relat_1(k5_relat_1('#skF_1',B_136))
      | ~ v1_relat_1(B_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_3349])).

tff(c_981,plain,(
    ! [A_70] :
      ( k1_relat_1(k2_funct_1(A_70)) = k2_relat_1(A_70)
      | ~ v2_funct_1(A_70)
      | ~ v1_funct_1(A_70)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_987,plain,(
    ! [A_70] :
      ( k9_relat_1(k2_funct_1(A_70),k2_relat_1(A_70)) = k2_relat_1(k2_funct_1(A_70))
      | ~ v1_relat_1(k2_funct_1(A_70))
      | ~ v2_funct_1(A_70)
      | ~ v1_funct_1(A_70)
      | ~ v1_relat_1(A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_981,c_8])).

tff(c_3392,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3370,c_987])).

tff(c_3441,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1456,c_38,c_36,c_34,c_1456,c_3392])).

tff(c_950,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_3463,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3441,c_950])).

tff(c_3493,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_3463])).

tff(c_3497,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_3493])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:11:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.61/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.61/1.88  
% 4.61/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.61/1.89  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 4.61/1.89  
% 4.61/1.89  %Foreground sorts:
% 4.61/1.89  
% 4.61/1.89  
% 4.61/1.89  %Background operators:
% 4.61/1.89  
% 4.61/1.89  
% 4.61/1.89  %Foreground operators:
% 4.61/1.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.61/1.89  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.61/1.89  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.61/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.61/1.89  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.61/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.61/1.89  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.61/1.89  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.61/1.89  tff('#skF_1', type, '#skF_1': $i).
% 4.61/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.61/1.89  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.61/1.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.61/1.89  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.61/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.61/1.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.61/1.89  
% 4.94/1.90  tff(f_92, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 4.94/1.90  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 4.94/1.90  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 4.94/1.90  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 4.94/1.90  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.94/1.90  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 4.94/1.90  tff(f_71, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 4.94/1.90  tff(f_53, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 4.94/1.90  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 4.94/1.90  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 4.94/1.90  tff(c_38, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.94/1.90  tff(c_36, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.94/1.90  tff(c_34, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.94/1.90  tff(c_28, plain, (![A_15]: (k2_relat_1(k2_funct_1(A_15))=k1_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.94/1.90  tff(c_22, plain, (![A_13]: (v1_relat_1(k2_funct_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.94/1.90  tff(c_30, plain, (![A_15]: (k1_relat_1(k2_funct_1(A_15))=k2_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.94/1.90  tff(c_1117, plain, (![A_81, B_82]: (k10_relat_1(A_81, k1_relat_1(B_82))=k1_relat_1(k5_relat_1(A_81, B_82)) | ~v1_relat_1(B_82) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.94/1.90  tff(c_1422, plain, (![A_95, A_96]: (k1_relat_1(k5_relat_1(A_95, k2_funct_1(A_96)))=k10_relat_1(A_95, k2_relat_1(A_96)) | ~v1_relat_1(k2_funct_1(A_96)) | ~v1_relat_1(A_95) | ~v2_funct_1(A_96) | ~v1_funct_1(A_96) | ~v1_relat_1(A_96))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1117])).
% 4.94/1.90  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.94/1.90  tff(c_115, plain, (![B_29, A_30]: (k5_relat_1(B_29, k6_relat_1(A_30))=B_29 | ~r1_tarski(k2_relat_1(B_29), A_30) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.94/1.90  tff(c_128, plain, (![B_29]: (k5_relat_1(B_29, k6_relat_1(k2_relat_1(B_29)))=B_29 | ~v1_relat_1(B_29))), inference(resolution, [status(thm)], [c_6, c_115])).
% 4.94/1.90  tff(c_24, plain, (![A_14]: (v1_relat_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.94/1.90  tff(c_14, plain, (![A_10]: (k1_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.94/1.90  tff(c_146, plain, (![A_32, B_33]: (k10_relat_1(A_32, k1_relat_1(B_33))=k1_relat_1(k5_relat_1(A_32, B_33)) | ~v1_relat_1(B_33) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.94/1.90  tff(c_158, plain, (![A_32, A_10]: (k1_relat_1(k5_relat_1(A_32, k6_relat_1(A_10)))=k10_relat_1(A_32, A_10) | ~v1_relat_1(k6_relat_1(A_10)) | ~v1_relat_1(A_32))), inference(superposition, [status(thm), theory('equality')], [c_14, c_146])).
% 4.94/1.90  tff(c_172, plain, (![A_35, A_36]: (k1_relat_1(k5_relat_1(A_35, k6_relat_1(A_36)))=k10_relat_1(A_35, A_36) | ~v1_relat_1(A_35))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_158])).
% 4.94/1.90  tff(c_190, plain, (![B_29]: (k10_relat_1(B_29, k2_relat_1(B_29))=k1_relat_1(B_29) | ~v1_relat_1(B_29) | ~v1_relat_1(B_29))), inference(superposition, [status(thm), theory('equality')], [c_128, c_172])).
% 4.94/1.90  tff(c_883, plain, (![A_64, A_65]: (k1_relat_1(k5_relat_1(A_64, k2_funct_1(A_65)))=k10_relat_1(A_64, k2_relat_1(A_65)) | ~v1_relat_1(k2_funct_1(A_65)) | ~v1_relat_1(A_64) | ~v2_funct_1(A_65) | ~v1_funct_1(A_65) | ~v1_relat_1(A_65))), inference(superposition, [status(thm), theory('equality')], [c_30, c_146])).
% 4.94/1.90  tff(c_32, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.94/1.90  tff(c_62, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_32])).
% 4.94/1.90  tff(c_909, plain, (k10_relat_1('#skF_1', k2_relat_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_883, c_62])).
% 4.94/1.90  tff(c_927, plain, (k10_relat_1('#skF_1', k2_relat_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_38, c_909])).
% 4.94/1.90  tff(c_933, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_927])).
% 4.94/1.90  tff(c_936, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_933])).
% 4.94/1.90  tff(c_940, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_936])).
% 4.94/1.90  tff(c_941, plain, (k10_relat_1('#skF_1', k2_relat_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_927])).
% 4.94/1.90  tff(c_945, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_190, c_941])).
% 4.94/1.90  tff(c_949, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_945])).
% 4.94/1.90  tff(c_951, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_32])).
% 4.94/1.90  tff(c_1434, plain, (k10_relat_1('#skF_1', k2_relat_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1422, c_951])).
% 4.94/1.90  tff(c_1443, plain, (k10_relat_1('#skF_1', k2_relat_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_38, c_1434])).
% 4.94/1.90  tff(c_1447, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_1443])).
% 4.94/1.90  tff(c_1450, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_1447])).
% 4.94/1.90  tff(c_1454, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1450])).
% 4.94/1.90  tff(c_1456, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_1443])).
% 4.94/1.90  tff(c_1002, plain, (![B_72, A_73]: (k5_relat_1(B_72, k6_relat_1(A_73))=B_72 | ~r1_tarski(k2_relat_1(B_72), A_73) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.94/1.90  tff(c_1012, plain, (![B_72]: (k5_relat_1(B_72, k6_relat_1(k2_relat_1(B_72)))=B_72 | ~v1_relat_1(B_72))), inference(resolution, [status(thm)], [c_6, c_1002])).
% 4.94/1.90  tff(c_1440, plain, (k10_relat_1('#skF_1', k2_relat_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_951, c_1422])).
% 4.94/1.90  tff(c_1446, plain, (k10_relat_1('#skF_1', k2_relat_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_38, c_1440])).
% 4.94/1.90  tff(c_1458, plain, (k10_relat_1('#skF_1', k2_relat_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1456, c_1446])).
% 4.94/1.90  tff(c_1132, plain, (![A_81, A_10]: (k1_relat_1(k5_relat_1(A_81, k6_relat_1(A_10)))=k10_relat_1(A_81, A_10) | ~v1_relat_1(k6_relat_1(A_10)) | ~v1_relat_1(A_81))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1117])).
% 4.94/1.90  tff(c_1217, plain, (![A_87, A_88]: (k1_relat_1(k5_relat_1(A_87, k6_relat_1(A_88)))=k10_relat_1(A_87, A_88) | ~v1_relat_1(A_87))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1132])).
% 4.94/1.90  tff(c_8, plain, (![A_3]: (k9_relat_1(A_3, k1_relat_1(A_3))=k2_relat_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.94/1.90  tff(c_2385, plain, (![A_122, A_123]: (k9_relat_1(k5_relat_1(A_122, k6_relat_1(A_123)), k10_relat_1(A_122, A_123))=k2_relat_1(k5_relat_1(A_122, k6_relat_1(A_123))) | ~v1_relat_1(k5_relat_1(A_122, k6_relat_1(A_123))) | ~v1_relat_1(A_122))), inference(superposition, [status(thm), theory('equality')], [c_1217, c_8])).
% 4.94/1.90  tff(c_2403, plain, (k9_relat_1(k5_relat_1('#skF_1', k6_relat_1(k2_relat_1('#skF_1'))), k1_relat_1('#skF_1'))=k2_relat_1(k5_relat_1('#skF_1', k6_relat_1(k2_relat_1('#skF_1')))) | ~v1_relat_1(k5_relat_1('#skF_1', k6_relat_1(k2_relat_1('#skF_1')))) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1458, c_2385])).
% 4.94/1.90  tff(c_2428, plain, (k9_relat_1(k5_relat_1('#skF_1', k6_relat_1(k2_relat_1('#skF_1'))), k1_relat_1('#skF_1'))=k2_relat_1(k5_relat_1('#skF_1', k6_relat_1(k2_relat_1('#skF_1')))) | ~v1_relat_1(k5_relat_1('#skF_1', k6_relat_1(k2_relat_1('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2403])).
% 4.94/1.90  tff(c_2538, plain, (~v1_relat_1(k5_relat_1('#skF_1', k6_relat_1(k2_relat_1('#skF_1'))))), inference(splitLeft, [status(thm)], [c_2428])).
% 4.94/1.90  tff(c_2541, plain, (~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1012, c_2538])).
% 4.94/1.90  tff(c_2544, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_2541])).
% 4.94/1.90  tff(c_2546, plain, (v1_relat_1(k5_relat_1('#skF_1', k6_relat_1(k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_2428])).
% 4.94/1.90  tff(c_2545, plain, (k9_relat_1(k5_relat_1('#skF_1', k6_relat_1(k2_relat_1('#skF_1'))), k1_relat_1('#skF_1'))=k2_relat_1(k5_relat_1('#skF_1', k6_relat_1(k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_2428])).
% 4.94/1.90  tff(c_2609, plain, (k2_relat_1(k5_relat_1('#skF_1', k6_relat_1(k2_relat_1('#skF_1'))))=k9_relat_1('#skF_1', k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1012, c_2545])).
% 4.94/1.90  tff(c_2613, plain, (k2_relat_1(k5_relat_1('#skF_1', k6_relat_1(k2_relat_1('#skF_1'))))=k9_relat_1('#skF_1', k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2609])).
% 4.94/1.90  tff(c_16, plain, (![A_10]: (k2_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.94/1.90  tff(c_1005, plain, (![A_10, A_73]: (k5_relat_1(k6_relat_1(A_10), k6_relat_1(A_73))=k6_relat_1(A_10) | ~r1_tarski(A_10, A_73) | ~v1_relat_1(k6_relat_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1002])).
% 4.94/1.90  tff(c_1011, plain, (![A_10, A_73]: (k5_relat_1(k6_relat_1(A_10), k6_relat_1(A_73))=k6_relat_1(A_10) | ~r1_tarski(A_10, A_73))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1005])).
% 4.94/1.90  tff(c_1088, plain, (![B_79, A_80]: (k9_relat_1(B_79, k2_relat_1(A_80))=k2_relat_1(k5_relat_1(A_80, B_79)) | ~v1_relat_1(B_79) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.94/1.90  tff(c_1108, plain, (![A_10, B_79]: (k2_relat_1(k5_relat_1(k6_relat_1(A_10), B_79))=k9_relat_1(B_79, A_10) | ~v1_relat_1(B_79) | ~v1_relat_1(k6_relat_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1088])).
% 4.94/1.90  tff(c_1137, plain, (![A_83, B_84]: (k2_relat_1(k5_relat_1(k6_relat_1(A_83), B_84))=k9_relat_1(B_84, A_83) | ~v1_relat_1(B_84))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1108])).
% 4.94/1.90  tff(c_1155, plain, (![A_73, A_10]: (k9_relat_1(k6_relat_1(A_73), A_10)=k2_relat_1(k6_relat_1(A_10)) | ~v1_relat_1(k6_relat_1(A_73)) | ~r1_tarski(A_10, A_73))), inference(superposition, [status(thm), theory('equality')], [c_1011, c_1137])).
% 4.94/1.90  tff(c_1171, plain, (![A_85, A_86]: (k9_relat_1(k6_relat_1(A_85), A_86)=A_86 | ~r1_tarski(A_86, A_85))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_16, c_1155])).
% 4.94/1.90  tff(c_10, plain, (![B_6, A_4]: (k9_relat_1(B_6, k2_relat_1(A_4))=k2_relat_1(k5_relat_1(A_4, B_6)) | ~v1_relat_1(B_6) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.94/1.90  tff(c_1178, plain, (![A_4, A_85]: (k2_relat_1(k5_relat_1(A_4, k6_relat_1(A_85)))=k2_relat_1(A_4) | ~v1_relat_1(k6_relat_1(A_85)) | ~v1_relat_1(A_4) | ~r1_tarski(k2_relat_1(A_4), A_85))), inference(superposition, [status(thm), theory('equality')], [c_1171, c_10])).
% 4.94/1.90  tff(c_1203, plain, (![A_4, A_85]: (k2_relat_1(k5_relat_1(A_4, k6_relat_1(A_85)))=k2_relat_1(A_4) | ~v1_relat_1(A_4) | ~r1_tarski(k2_relat_1(A_4), A_85))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1178])).
% 4.94/1.90  tff(c_2701, plain, (k9_relat_1('#skF_1', k1_relat_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1') | ~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2613, c_1203])).
% 4.94/1.90  tff(c_2737, plain, (k9_relat_1('#skF_1', k1_relat_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_38, c_2701])).
% 4.94/1.90  tff(c_2759, plain, (k2_relat_1(k5_relat_1('#skF_1', k6_relat_1(k2_relat_1('#skF_1'))))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2737, c_2613])).
% 4.94/1.90  tff(c_2821, plain, (![B_6]: (k2_relat_1(k5_relat_1(k5_relat_1('#skF_1', k6_relat_1(k2_relat_1('#skF_1'))), B_6))=k9_relat_1(B_6, k2_relat_1('#skF_1')) | ~v1_relat_1(B_6) | ~v1_relat_1(k5_relat_1('#skF_1', k6_relat_1(k2_relat_1('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_2759, c_10])).
% 4.94/1.90  tff(c_3300, plain, (![B_135]: (k2_relat_1(k5_relat_1(k5_relat_1('#skF_1', k6_relat_1(k2_relat_1('#skF_1'))), B_135))=k9_relat_1(B_135, k2_relat_1('#skF_1')) | ~v1_relat_1(B_135))), inference(demodulation, [status(thm), theory('equality')], [c_2546, c_2821])).
% 4.94/1.90  tff(c_3349, plain, (![B_135]: (k9_relat_1(B_135, k2_relat_1('#skF_1'))=k2_relat_1(k5_relat_1('#skF_1', B_135)) | ~v1_relat_1(B_135) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1012, c_3300])).
% 4.94/1.90  tff(c_3370, plain, (![B_136]: (k9_relat_1(B_136, k2_relat_1('#skF_1'))=k2_relat_1(k5_relat_1('#skF_1', B_136)) | ~v1_relat_1(B_136))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_3349])).
% 4.94/1.90  tff(c_981, plain, (![A_70]: (k1_relat_1(k2_funct_1(A_70))=k2_relat_1(A_70) | ~v2_funct_1(A_70) | ~v1_funct_1(A_70) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.94/1.90  tff(c_987, plain, (![A_70]: (k9_relat_1(k2_funct_1(A_70), k2_relat_1(A_70))=k2_relat_1(k2_funct_1(A_70)) | ~v1_relat_1(k2_funct_1(A_70)) | ~v2_funct_1(A_70) | ~v1_funct_1(A_70) | ~v1_relat_1(A_70))), inference(superposition, [status(thm), theory('equality')], [c_981, c_8])).
% 4.94/1.90  tff(c_3392, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3370, c_987])).
% 4.94/1.90  tff(c_3441, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1456, c_38, c_36, c_34, c_1456, c_3392])).
% 4.94/1.90  tff(c_950, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_32])).
% 4.94/1.90  tff(c_3463, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3441, c_950])).
% 4.94/1.90  tff(c_3493, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28, c_3463])).
% 4.94/1.90  tff(c_3497, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_3493])).
% 4.94/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.94/1.90  
% 4.94/1.90  Inference rules
% 4.94/1.90  ----------------------
% 4.94/1.90  #Ref     : 0
% 4.94/1.90  #Sup     : 783
% 4.94/1.90  #Fact    : 0
% 4.94/1.90  #Define  : 0
% 4.94/1.90  #Split   : 6
% 4.94/1.90  #Chain   : 0
% 4.94/1.90  #Close   : 0
% 4.94/1.90  
% 4.94/1.90  Ordering : KBO
% 4.94/1.90  
% 4.94/1.90  Simplification rules
% 4.94/1.90  ----------------------
% 4.94/1.90  #Subsume      : 103
% 4.94/1.90  #Demod        : 772
% 4.94/1.90  #Tautology    : 326
% 4.94/1.90  #SimpNegUnit  : 0
% 4.94/1.90  #BackRed      : 5
% 4.94/1.91  
% 4.94/1.91  #Partial instantiations: 0
% 4.94/1.91  #Strategies tried      : 1
% 4.94/1.91  
% 4.94/1.91  Timing (in seconds)
% 4.94/1.91  ----------------------
% 4.94/1.91  Preprocessing        : 0.32
% 4.94/1.91  Parsing              : 0.18
% 4.94/1.91  CNF conversion       : 0.02
% 4.94/1.91  Main loop            : 0.81
% 4.94/1.91  Inferencing          : 0.29
% 4.94/1.91  Reduction            : 0.29
% 4.94/1.91  Demodulation         : 0.22
% 4.94/1.91  BG Simplification    : 0.04
% 4.94/1.91  Subsumption          : 0.14
% 4.94/1.91  Abstraction          : 0.05
% 4.94/1.91  MUC search           : 0.00
% 4.94/1.91  Cooper               : 0.00
% 4.94/1.91  Total                : 1.17
% 4.94/1.91  Index Insertion      : 0.00
% 4.94/1.91  Index Deletion       : 0.00
% 4.94/1.91  Index Matching       : 0.00
% 4.94/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
