%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0723+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:46 EST 2020

% Result     : Theorem 11.67s
% Output     : CNFRefutation 11.73s
% Verified   : 
% Statistics : Number of formulae       :   37 (  55 expanded)
%              Number of leaves         :   14 (  26 expanded)
%              Depth                    :   15
%              Number of atoms          :   74 ( 137 expanded)
%              Number of equality atoms :   22 (  50 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > #nlpp > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r2_hidden(A,B)
          & r2_hidden(B,C)
          & r2_hidden(C,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_ordinal1)).

tff(f_39,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_52,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(c_34,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_32,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_30,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4,plain,(
    ! [E_7,A_1,B_2] : r2_hidden(E_7,k1_enumset1(A_1,B_2,E_7)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [E_7,B_2,C_3] : r2_hidden(E_7,k1_enumset1(E_7,B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [E_7,A_1,C_3] : r2_hidden(E_7,k1_enumset1(A_1,E_7,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_3'(A_8,B_9),B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_45,plain,(
    ! [E_29,C_30,B_31,A_32] :
      ( E_29 = C_30
      | E_29 = B_31
      | E_29 = A_32
      | ~ r2_hidden(E_29,k1_enumset1(A_32,B_31,C_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_81,plain,(
    ! [A_52,A_53,B_54,C_55] :
      ( '#skF_3'(A_52,k1_enumset1(A_53,B_54,C_55)) = C_55
      | '#skF_3'(A_52,k1_enumset1(A_53,B_54,C_55)) = B_54
      | '#skF_3'(A_52,k1_enumset1(A_53,B_54,C_55)) = A_53
      | ~ r2_hidden(A_52,k1_enumset1(A_53,B_54,C_55)) ) ),
    inference(resolution,[status(thm)],[c_28,c_45])).

tff(c_3753,plain,(
    ! [E_180,B_181,C_182] :
      ( '#skF_3'(E_180,k1_enumset1(E_180,B_181,C_182)) = C_182
      | '#skF_3'(E_180,k1_enumset1(E_180,B_181,C_182)) = B_181
      | '#skF_3'(E_180,k1_enumset1(E_180,B_181,C_182)) = E_180 ) ),
    inference(resolution,[status(thm)],[c_8,c_81])).

tff(c_26,plain,(
    ! [D_14,A_8,B_9] :
      ( ~ r2_hidden(D_14,'#skF_3'(A_8,B_9))
      | ~ r2_hidden(D_14,B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4035,plain,(
    ! [D_14,E_180,B_181,C_182] :
      ( ~ r2_hidden(D_14,E_180)
      | ~ r2_hidden(D_14,k1_enumset1(E_180,B_181,C_182))
      | ~ r2_hidden(E_180,k1_enumset1(E_180,B_181,C_182))
      | '#skF_3'(E_180,k1_enumset1(E_180,B_181,C_182)) = C_182
      | '#skF_3'(E_180,k1_enumset1(E_180,B_181,C_182)) = B_181 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3753,c_26])).

tff(c_18612,plain,(
    ! [D_442,E_443,B_444,C_445] :
      ( ~ r2_hidden(D_442,E_443)
      | ~ r2_hidden(D_442,k1_enumset1(E_443,B_444,C_445))
      | '#skF_3'(E_443,k1_enumset1(E_443,B_444,C_445)) = C_445
      | '#skF_3'(E_443,k1_enumset1(E_443,B_444,C_445)) = B_444 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_4035])).

tff(c_18646,plain,(
    ! [E_446,A_447,C_448] :
      ( ~ r2_hidden(E_446,A_447)
      | '#skF_3'(A_447,k1_enumset1(A_447,E_446,C_448)) = C_448
      | '#skF_3'(A_447,k1_enumset1(A_447,E_446,C_448)) = E_446 ) ),
    inference(resolution,[status(thm)],[c_6,c_18612])).

tff(c_18971,plain,(
    ! [D_14,C_448,A_447,E_446] :
      ( ~ r2_hidden(D_14,C_448)
      | ~ r2_hidden(D_14,k1_enumset1(A_447,E_446,C_448))
      | ~ r2_hidden(A_447,k1_enumset1(A_447,E_446,C_448))
      | ~ r2_hidden(E_446,A_447)
      | '#skF_3'(A_447,k1_enumset1(A_447,E_446,C_448)) = E_446 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18646,c_26])).

tff(c_20664,plain,(
    ! [D_452,C_453,A_454,E_455] :
      ( ~ r2_hidden(D_452,C_453)
      | ~ r2_hidden(D_452,k1_enumset1(A_454,E_455,C_453))
      | ~ r2_hidden(E_455,A_454)
      | '#skF_3'(A_454,k1_enumset1(A_454,E_455,C_453)) = E_455 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18971])).

tff(c_21731,plain,(
    ! [E_464,C_465,B_466] :
      ( ~ r2_hidden(E_464,C_465)
      | ~ r2_hidden(B_466,E_464)
      | '#skF_3'(E_464,k1_enumset1(E_464,B_466,C_465)) = B_466 ) ),
    inference(resolution,[status(thm)],[c_8,c_20664])).

tff(c_22132,plain,(
    ! [D_14,B_466,E_464,C_465] :
      ( ~ r2_hidden(D_14,B_466)
      | ~ r2_hidden(D_14,k1_enumset1(E_464,B_466,C_465))
      | ~ r2_hidden(E_464,k1_enumset1(E_464,B_466,C_465))
      | ~ r2_hidden(E_464,C_465)
      | ~ r2_hidden(B_466,E_464) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21731,c_26])).

tff(c_22587,plain,(
    ! [D_475,B_476,E_477,C_478] :
      ( ~ r2_hidden(D_475,B_476)
      | ~ r2_hidden(D_475,k1_enumset1(E_477,B_476,C_478))
      | ~ r2_hidden(E_477,C_478)
      | ~ r2_hidden(B_476,E_477) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_22132])).

tff(c_22615,plain,(
    ! [E_479,B_480,A_481] :
      ( ~ r2_hidden(E_479,B_480)
      | ~ r2_hidden(A_481,E_479)
      | ~ r2_hidden(B_480,A_481) ) ),
    inference(resolution,[status(thm)],[c_4,c_22587])).

tff(c_22643,plain,(
    ! [A_482] :
      ( ~ r2_hidden(A_482,'#skF_6')
      | ~ r2_hidden('#skF_4',A_482) ) ),
    inference(resolution,[status(thm)],[c_30,c_22615])).

tff(c_22654,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_22643])).

tff(c_22661,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_22654])).

%------------------------------------------------------------------------------
